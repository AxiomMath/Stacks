module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.TruncationQuasiIsoSheaf
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Vanishing07LMProof

/-!
# The de Rham complex of a crystal as a complex of abelian sheaves, and its truncation

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF] and a sheaf of
`𝒪_{X/S}`-modules `F` on the small crystalline site.  [Stacks, Proposition 60.23.1, Tag 07LM]
speaks of the complex

`F → F ⊗_{𝒪_{X/S}} Ω¹_{X/S} → F ⊗_{𝒪_{X/S}} Ω²_{X/S} → ⋯`

and of its truncation map to `F[0]`.  Its terms are the abelian sheaves
`...SmallSite.tensorDifferentialFormsSheaf F i`; the differentials are maps of *sheaves*: the
canonical connection of [Stacks, Lemma 60.15.1, Tag 07J6] is a map on the sections of the presheaf
tensor product only over the affine-over-affine objects, and the differentials are glued from
those.

This module takes the family of differentials as the datum `CrystalDeRhamSheafData` — the maps
together with the only property the proposition's leading assertion uses of them, that consecutive
ones compose to zero — assembles the complex, its truncation map to `F[0]`, and **proves the
leading assertion of [Stacks, Tag 07LM] for it**, the vanishing clause of the same tag being a
theorem of `SmallSite/Vanishing07LMProof.lean`.

The datum is constructed for a crystal in quasi-coherent modules, with the differentials of its
canonical connection, as `...SmallSite.crystalDeRhamSheafData` of
`SmallSite/CrystalDeRhamDifferentials.lean`, and the proposition is `...SmallSite.stacks07LM` of
`SmallSite/Proposition07LM.lean`.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `CrystalDeRhamSheafData` — the differentials of the de Rham complex of `F`, as maps of abelian
  sheaves on `Cris(X/S)`, with `d ∘ d = 0`.
* `CrystalDeRhamSheafData.natComplex`, `...complex` — the complex, `ℕ`-indexed and then extended
  to `ℤ` by zero.
* `CrystalDeRhamSheafData.singleComplex` — `F[0]`.
* `CrystalDeRhamSheafData.truncation` — the truncation map of the proposition.

## Main results

* `tensorDifferentialFormsSheafZeroIso` — `F ⊗_{𝒪_{X/S}} Ω^0_{X/S} = F` on abelian sheaves, which
  is what makes the degree-zero component of the truncation map an isomorphism.
* `CrystalDeRhamSheafData.isIso_derivedZariskiDirectImage_map_truncation` — **the leading
  assertion of [Stacks, Tag 07LM] for the complex of the datum**: the truncation map becomes an
  isomorphism of `D⁺(Ab(X_{Zar}))` after `Ru_{X/S, *}`, for every `F` satisfying conditions (1)
  and (2) of [Stacks, Tag 07JN] — in particular for every crystal in quasi-coherent modules.

## Implementation notes

The coefficient universe of the cohomology of `Cris(X/S)` is `u + 1`, so the abelian sheaf
underlying `F` has to be lifted along `AddCommGrpCat.uliftFunctor`; lifting preserves limits, so
it carries sheaves to sheaves (`Presheaf.isSheaf_comp_of_isSheaf`).  In degree zero the
sheafification that defines `...tensorDifferentialFormsSheaf` is therefore an isomorphism, by
`CategoryTheory.isIso_toSheafify`.

## References

* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-- **`F ⊗_{𝒪_{X/S}} Ω^0_{X/S} = F` on abelian sheaves.**  In degree zero the crystalline forms
are the structure sheaf, so the presheaf tensor product is `F` itself, which is already a sheaf;
the sheafification that defines `tensorDifferentialFormsSheaf` is therefore an isomorphism. -/
def tensorDifferentialFormsSheafZeroIso (F : SheafOfModules.{u} (structureSheaf S)) :
    tensorDifferentialFormsSheaf F 0 ≅ abelianSheaf F :=
  (presheafToSheaf (smallTopology S) AddCommGrpCat.{u + 1}).mapIso
      (Functor.isoWhiskerRight
        ((PresheafOfModules.toPresheaf _).mapIso (tensorDifferentialFormsZeroIso
          (F.val : PresheafOfModules.{u}
            (structurePresheaf S ⋙ forget₂ CommRingCat RingCat))))
        AddCommGrpCat.uliftFunctor.{u + 1, u}) ≪≫
    (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1}).preimageIso
      (isoSheafify (smallTopology S) (abelianSheaf F).property).symm

/-- **The differentials of the de Rham complex of `F`, as maps of abelian sheaves on
`Cris(X/S)`.**  The terms are the sheaves `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` of
`...SmallSite.tensorDifferentialFormsSheaf`, and the only property carried is the one the leading
assertion of [Stacks, Tag 07LM] uses, that consecutive differentials compose to zero. -/
structure CrystalDeRhamSheafData (F : SheafOfModules.{u} (structureSheaf S)) where
  /-- The degree-`i` differential `F ⊗ Ω^i_{X/S} ⟶ F ⊗ Ω^{i+1}_{X/S}`. -/
  d (i : ℕ) : tensorDifferentialFormsSheaf F i ⟶ tensorDifferentialFormsSheaf F (i + 1)
  /-- Consecutive differentials compose to zero. -/
  d_comp (i : ℕ) : d i ≫ d (i + 1) = 0

namespace CrystalDeRhamSheafData

variable {S} {F : SheafOfModules.{u} (structureSheaf S)} (data : CrystalDeRhamSheafData S F)

/-- **The de Rham complex of `F`, `ℕ`-indexed.** -/
def natComplex : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ :=
  CochainComplex.of (fun i ↦ tensorDifferentialFormsSheaf F i) data.d data.d_comp

/-- The degree-`i` term of `natComplex` is `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`. -/
@[simp]
theorem natComplex_X (i : ℕ) : data.natComplex.X i = tensorDifferentialFormsSheaf F i := rfl

/-- **The de Rham complex of `F`**, extended from `ℕ` to `ℤ` by zero. -/
def complex : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℤ :=
  data.natComplex.extend ComplexShape.embeddingUpNat

/-- The de Rham complex of `F` is concentrated in degrees `≥ 0`. -/
instance complex_isStrictlyGE : data.complex.IsStrictlyGE 0 :=
  inferInstanceAs (CochainComplex.IsStrictlyGE
    (data.natComplex.extend ComplexShape.embeddingUpNat) 0)

/-- In degree `i ≥ 0` the term of the complex is `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`. -/
def complexXIso (i : ℕ) : data.complex.X (i : ℤ) ≅ tensorDifferentialFormsSheaf F i :=
  HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat (i := i) (by simp)

/-- **`F[0]`**, the complex with the abelian sheaf underlying `F` in degree zero. -/
def singleComplex : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℤ :=
  ((CochainComplex.single₀ (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})).obj
    (abelianSheaf F)).extend ComplexShape.embeddingUpNat

/-- The complex `F[0]` is concentrated in degrees `≥ 0`. -/
instance singleComplex_isStrictlyGE :
    (singleComplex (F := F)).IsStrictlyGE 0 :=
  inferInstanceAs (CochainComplex.IsStrictlyGE
    (((CochainComplex.single₀ (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})).obj
      (abelianSheaf F)).extend ComplexShape.embeddingUpNat) 0)

/-- Outside degree zero the complex `F[0]` vanishes. -/
theorem isZero_singleComplex_X (n : ℤ) (hn : n ≠ 0) :
    IsZero ((singleComplex (F := F)).X n) := by
  rcases lt_or_gt_of_ne hn with h | h
  · exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat n
      (fun i hi => by simp only [ComplexShape.embeddingUpNat_f] at hi; omega)
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h.le
    refine IsZero.of_iso ?_
      (HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat (i := k) (by simp))
    exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 _ k (by omega)

/-- **The truncation map of [Stacks, Tag 07LM]**, `(F → F ⊗ Ω¹ → ⋯) ⟶ F[0]`: the identification
`F ⊗_{𝒪_{X/S}} Ω^0_{X/S} = F` in degree zero, and zero above.  A map of `ℕ`-indexed cochain
complexes into a complex concentrated in degree zero is exactly a map out of the degree-zero term,
`CochainComplex.toSingle₀Equiv`, so this is the whole content of the truncation map. -/
def natTruncation :
    data.natComplex ⟶
      (CochainComplex.single₀ (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})).obj
        (abelianSheaf F) :=
  (CochainComplex.toSingle₀Equiv _ _).symm (tensorDifferentialFormsSheafZeroIso S F).hom

/-- The degree-zero component of the truncation map is the identification
`F ⊗_{𝒪_{X/S}} Ω^0_{X/S} = F`. -/
theorem natTruncation_f_zero :
    data.natTruncation.f 0 = (tensorDifferentialFormsSheafZeroIso S F).hom := rfl

/-- The truncation map, in the `ℤ`-indexed spelling. -/
def truncation : data.complex ⟶ singleComplex (F := F) :=
  HomologicalComplex.extendMap data.natTruncation ComplexShape.embeddingUpNat

/-- **The degree-zero component of the truncation map is an isomorphism**: it is the
identification `F ⊗_{𝒪_{X/S}} Ω^0_{X/S} = F`. -/
theorem isIso_truncation_f_zero : IsIso (data.truncation.f 0) := by
  rw [show data.truncation.f 0 = _ from
    HomologicalComplex.extendMap_f data.natTruncation ComplexShape.embeddingUpNat
      (i := 0) (by simp)]
  have : IsIso (data.natTruncation.f 0) := by
    rw [data.natTruncation_f_zero]
    exact inferInstanceAs (IsIso (tensorDifferentialFormsSheafZeroIso S F).hom)
  exact IsIso.comp_isIso' (Iso.isIso_hom _) (IsIso.comp_isIso' inferInstance (Iso.isIso_inv _))

section Derived

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]

/-- Under conditions (1) and (2) of [Stacks, Tag 07JN], `Ru_{X/S, *}` kills the terms of the
de Rham complex in positive degrees.  This is the vanishing clause of [Stacks, Tag 07LM] at the
generality of [Stacks, Tag 07LN], `vanishing07LM`. -/
theorem isZero_derivedZariskiDirectImage_complex_X (hqc : IsLocallyQuasiCoherent F)
    (hsurj : CohomologyRestriction.IsSurjectiveComparison F.val) (n : ℤ) (hn : 1 ≤ n) :
    IsZero ((derivedZariskiDirectImage S).obj (data.complex.X n)) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) := ⟨n.toNat, by omega⟩
  exact IsZero.of_iso (vanishing07LM S F hqc hsurj k (by omega))
    ((derivedZariskiDirectImage S).mapIso (data.complexXIso k))

/-- **Stacks Project, Proposition 60.23.1, Tag 07LM, the leading assertion, for the complex of a
`CrystalDeRhamSheafData`.**  The truncation map

`(F → F ⊗_{𝒪_{X/S}} Ω¹_{X/S} → F ⊗_{𝒪_{X/S}} Ω²_{X/S} → ⋯) ⟶ F[0]`

becomes an isomorphism of `D⁺(Ab(X_{Zar}))` after `Ru_{X/S, *}` — that is, a quasi-isomorphism —
for every sheaf of `𝒪_{X/S}`-modules `F` satisfying conditions (1) and (2) of
[Stacks, Tag 07JN], in particular for every crystal in quasi-coherent modules.

The proof is the source's: the truncation map sits in a degreewise split short exact sequence
`0 ⟶ σ^{≥1}K ⟶ K ⟶ F[0] ⟶ 0`, hence in a distinguished triangle whose first vertex is
`Ru_{X/S, *}(σ^{≥1}K)`, and that vanishes because `Ru_{X/S, *}` kills each term of `σ^{≥1}K` by
the vanishing clause of the same tag, `vanishing07LM`.  This is
`isIso_derivedZariskiDirectImageFunctor_map_sheafPlusTruncation`.

It is stated for an arbitrary datum; at the datum of a crystal in quasi-coherent modules,
`...SmallSite.crystalDeRhamSheafData`, it is the leading assertion of the proposition, which
`...SmallSite.stacks07LM` registers. -/
theorem isIso_derivedZariskiDirectImage_map_truncation (hqc : IsLocallyQuasiCoherent F)
    (hsurj : CohomologyRestriction.IsSurjectiveComparison F.val) :
    IsIso ((derivedZariskiDirectImageFunctor S).map
      (DerivedCategory.Plus.Qh.map
        ((HomotopyCategory.Plus.quotient _).map
          (sheafPlusTruncation S data.complex (singleComplex (F := F)) data.truncation)))) :=
  isIso_derivedZariskiDirectImageFunctor_map_sheafPlusTruncation S data.complex
    (singleComplex (F := F)) data.truncation (isZero_singleComplex_X (F := F))
    data.isIso_truncation_f_zero
    (data.isZero_derivedZariskiDirectImage_complex_X hqc hsurj)

end Derived

end CrystalDeRhamSheafData

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
