module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffinePositiveDegree

/-!
# Flat base change on the intersections of an affine cover of a quasi-separated scheme

Let

```
Y --p--> X
|        |
kY       iX
v        v
T --q--> S
```

be a cartesian square of schemes with `S` and `T` affine, let `q` be flat, let `iX` be
quasi-compact and **quasi-separated**, and let `F` be a quasi-coherent `𝒪_X`-module.  This file
supplies the geometric input to the third paragraph of the proof of [Stacks, Tag 02KH] part (2):
`X` has a finite cover by affine opens all of whose nonempty finite intersections are
quasi-compact and separated over `S`, and on every one of those intersections flat base change
for cohomology holds in every degree.

The second paragraph of the source's proof — the **separated** case, in every degree — is
`AlgebraicGeometry.nonempty_cohomologyBaseChangeIso` of `AffinePositiveDegree.lean`.
[Stacks, Tag 02KH] in full is
`Stacks.AlgebraicGeometry.FlatBaseChangeDerived.isIso_baseChangeMap_of_flat`,
`Stacks.AlgebraicGeometry.FlatBaseChangeDerived.isIso_higherBaseChangeMap` and
`Stacks.AlgebraicGeometry.FlatBaseChangeDerived.cohomologyBaseChangeIso`, in
`StacksFrontier/AlgebraicGeometry/FlatBaseChangeCohomology/Derived/FlatBaseChange.lean`.

## Main definitions

* `AlgebraicGeometry.CohomologyBaseChangeOn`: the assertion of [Stacks, Tag 02KH] part (2) for an
  open `W` of `X` in a single degree, namely that
  `Γ(T, ⊤) ⊗_{Γ(S, ⊤)} Hⁿ(W, F|_W) ≅ Hⁿ(p⁻¹W, (F|_W) pulled back)` as `Γ(p⁻¹W, ⊤)`-modules.

## Main results

* `AlgebraicGeometry.quasiCompact_iInf_ι_comp`: a nonempty finite intersection of affine opens of
  a scheme quasi-compact and quasi-separated over an affine base is quasi-compact over that base.
* `AlgebraicGeometry.isSeparated_iInf_ι_comp`: and it is separated over that base.
* `AlgebraicGeometry.exists_finite_affineOpen_cover_separated_inter_of_isAffine`: a scheme
  quasi-compact and quasi-separated over an affine base has a finite cover by affine opens all of
  whose nonempty finite intersections are quasi-compact and separated over the base.
* `AlgebraicGeometry.cohomologyBaseChangeOn_of_quasiCompact_of_isSeparated`: flat base change for
  cohomology holds in every degree on an open that is quasi-compact and separated over the base.
* `AlgebraicGeometry.cohomologyBaseChangeOn_iInf`: hence on every nonempty finite intersection of
  affine opens of `X`.

## Implementation notes

Separatedness of an intersection `W = ⨅ j, U (s j)` over the affine base is read off the
factorisation `W.ι ≫ iX = X.homOfLE _ ≫ ((U (s 0)).ι ≫ iX)`: the first factor is an open
immersion, hence a monomorphism, hence separated, and the second is a morphism between affine
schemes, hence affine, hence separated.  This is where the index type `Fin (r + 1)` rather than
`Fin r` matters: the empty intersection is `⊤`, which is separated over `S` only when `X` is, and
that is precisely the hypothesis the quasi-separated case does not have.

Quasi-compactness is `TopologicalSpace.QuasiSeparatedSpace.isCompact_sInter_of_nonempty` applied
to the (finite, nonempty) range of `fun j => (U (s j) : Set X)`, each member open and compact
because affine; `AlgebraicGeometry.quasiCompact_iff_compactSpace` then converts the compactness of
the space into quasi-compactness of the morphism to the affine base.

`CohomologyBaseChangeOn` is a `Prop`-valued definition rather than an inlined `Nonempty`: the
statement names six functors and two right-derived evaluations, and stating it once keeps the
results below legible and lets a consumer quantify over `W`.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 01ES](https://stacks.math.columbia.edu/tag/01ES)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.SectionsBaseChange (baseRestrictScalars baseExtendScalars)

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-! ### A nonempty finite intersection of affine opens is quasi-compact and separated -/

variable {S T X Y : Scheme.{u}}

/-- **A nonempty finite intersection of affine opens of a scheme quasi-compact and
quasi-separated over an affine base is quasi-compact over that base.**  The space is
quasi-separated, so a finite nonempty intersection of quasi-compact opens is quasi-compact, and
over an affine base quasi-compactness of a morphism is compactness of the source. -/
theorem quasiCompact_iInf_ι_comp [IsAffine S] (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {ι : Type*} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) {r : ℕ}
    (s : Fin (r + 1) → ι) : QuasiCompact ((⨅ j, U (s j)).ι ≫ f) := by
  have : QuasiSeparatedSpace X := (quasiSeparated_iff_quasiSeparatedSpace f).mp inferInstance
  have hc : IsCompact ((⨅ j, U (s j) : X.Opens) : Set X) := by
    rw [Opens.coe_iInf, ← Set.sInter_range]
    refine QuasiSeparatedSpace.isCompact_sInter_of_nonempty (Set.finite_range _)
      ⟨_, Set.mem_range_self 0⟩ ?_ ?_
    · rintro t ⟨j, rfl⟩
      exact Or.inl (U (s j)).2
    · rintro t ⟨j, rfl⟩
      exact (hU (s j)).isCompact
  have : CompactSpace (⨅ j, U (s j) : X.Opens).toScheme := isCompact_iff_compactSpace.mp hc
  exact (quasiCompact_iff_compactSpace _).mpr inferInstance

/-- **A nonempty finite intersection of affine opens of a scheme over an affine base is separated
over that base.**  The intersection is contained in the affine open `U (s 0)`, so the inclusion
factors as an open immersion into `U (s 0)` followed by a morphism of affine schemes; the first is
a monomorphism and the second is an affine morphism, and both are therefore separated.

No quasi-compactness or quasi-separatedness of `f` is used, and `Fin (r + 1)` is essential: for an
empty index type the intersection is `⊤` and the statement is separatedness of `f` itself. -/
theorem isSeparated_iInf_ι_comp [IsAffine S] (f : X ⟶ S) {ι : Type*} (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) {r : ℕ} (s : Fin (r + 1) → ι) :
    IsSeparated ((⨅ j, U (s j)).ι ≫ f) := by
  have hle : (⨅ j, U (s j)) ≤ U (s 0) := iInf_le _ 0
  have : IsAffine (U (s 0)).toScheme := hU (s 0)
  have hfac : (⨅ j, U (s j)).ι ≫ f = X.homOfLE hle ≫ ((U (s 0)).ι ≫ f) := by
    rw [← Category.assoc, X.homOfLE_ι]
  rw [hfac]
  have : IsSeparated ((U (s 0)).ι ≫ f) := IsSeparated.of_isAffineHom _
  infer_instance

/-- **A scheme quasi-compact and quasi-separated over an affine base has a finite cover by affine
opens all of whose nonempty finite intersections are quasi-compact and separated over the base.**

This is the cover the third paragraph of the proof of [Stacks, Tag 02KH] part (2) chooses.  It is
the quasi-separated counterpart of
`AlgebraicGeometry.exists_finite_affineOpen_cover_inter_of_isAffine`, which under the stronger
hypothesis that `f` is separated gets intersections that are themselves *affine*. -/
theorem exists_finite_affineOpen_cover_separated_inter_of_isAffine [IsAffine S] (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → X.Opens), (⊤ : X.Opens) = ⨆ i, U i ∧
      (∀ i, IsAffineOpen (U i)) ∧
      ∀ (r : ℕ) (s : Fin (r + 1) → ι),
        QuasiCompact ((⨅ j, U (s j)).ι ≫ f) ∧ IsSeparated ((⨅ j, U (s j)).ι ≫ f) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨ι, hι, V, hVaff, hVcov⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_finite_affineOpen_cover X
  refine ⟨ι, hι, V, ?_, hVaff, fun r s =>
    ⟨quasiCompact_iInf_ι_comp f V hVaff s, isSeparated_iInf_ι_comp f V hVaff s⟩⟩
  refine le_antisymm ?_ le_top
  intro x _
  obtain ⟨a, ha⟩ := hVcov x
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, ha⟩

/-! ### Flat base change for cohomology on an open of `X` -/

section On

variable {q : T ⟶ S} {iX : X ⟶ S} {p : Y ⟶ X} {kY : Y ⟶ T}

/-- **The assertion of [Stacks, Tag 02KH] part (2) for an open `W` of `X`, in a single degree.**
For the cartesian square `p, kY, iX, q` and a module `F` on `X`, this says that

`Γ(T, ⊤) ⊗_{Γ(S, ⊤)} Hⁿ(W, F|_W) ≅ Hⁿ(p ⁻¹ᵁ W, (p ∣_ W)^* (F|_W))`

as `Γ(p ⁻¹ᵁ W, ⊤)`-modules, where the tensor product is the composite of the two change-of-rings
functors along `Γ(S, ⊤) ⟶ Γ(T, ⊤)` and cohomology is the right-derived evaluation at `⊤`.

Only an existence statement, because the comparison is assembled from a chosen Čech cover; see the
implementation notes of `AffinePositiveDegree.lean`. -/
def CohomologyBaseChangeOn (q : T ⟶ S) (iX : X ⟶ S) (p : Y ⟶ X) (kY : Y ⟶ T) (F : X.Modules)
    (W : X.Opens) (n : ℕ) : Prop :=
  Nonempty
    ((baseRestrictScalars (W.ι ≫ iX) ⋙ baseExtendScalars q).obj
        (((SheafOfModules.evaluation.{u} (W : Scheme.{u}).ringCatSheaf
          (op (⊤ : (W : Scheme.{u}).Opens))).rightDerived n).obj
            ((Scheme.Modules.pullback W.ι).obj F)) ≅
      (baseRestrictScalars ((p ⁻¹ᵁ W).ι ≫ kY)).obj
        (((SheafOfModules.evaluation.{u} ((p ⁻¹ᵁ W : Y.Opens) : Scheme.{u}).ringCatSheaf
          (op (⊤ : ((p ⁻¹ᵁ W : Y.Opens) : Scheme.{u}).Opens))).rightDerived n).obj
            ((Scheme.Modules.pullback (p ∣_ W)).obj ((Scheme.Modules.pullback W.ι).obj F))))

/-- **Flat base change for cohomology, in every degree, on an open that is quasi-compact and
separated over the base.**  Restricting the cartesian square to `W` and to its preimage leaves a
cartesian square — `CategoryTheory.IsPullback.paste_vert` applied to the restriction square of `p`
over `W` — whose right-hand vertical morphism `W.ι ≫ iX` is separated and quasi-compact, so the
separated case `AlgebraicGeometry.nonempty_cohomologyBaseChangeIso` applies to it. -/
theorem cohomologyBaseChangeOn_of_quasiCompact_of_isSeparated [IsAffine S] [IsAffine T] [Flat q]
    (H : IsPullback p kY iX q) (F : X.Modules) [F.IsQuasicoherent] (W : X.Opens)
    [QuasiCompact (W.ι ≫ iX)] [IsSeparated (W.ι ≫ iX)] (n : ℕ) :
    CohomologyBaseChangeOn q iX p kY F W n :=
  have : ((Scheme.Modules.pullback W.ι).obj F).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback W.ι F inferInstance
  nonempty_cohomologyBaseChangeIso ((isPullback_morphismRestrict p W).paste_vert H)
    ((Scheme.Modules.pullback W.ι).obj F) n

/-- **Flat base change for cohomology holds in every degree on every nonempty finite intersection
of affine opens of a scheme quasi-compact and quasi-separated over an affine base.**

This is the conclusion the second paragraph of the proof of [Stacks, Tag 02KH] part (2) supplies
to the third, which then runs the Čech-to-cohomology spectral sequence of [Stacks, Tag 01ES] over
such a cover.  That last step is not carried out; `AffinePositiveDegree.lean` records what is
missing. -/
theorem cohomologyBaseChangeOn_iInf [IsAffine S] [IsAffine T] [Flat q]
    (H : IsPullback p kY iX q) [QuasiCompact iX] [QuasiSeparated iX]
    (F : X.Modules) [F.IsQuasicoherent] {ι : Type*} (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) {r : ℕ} (s : Fin (r + 1) → ι) (n : ℕ) :
    CohomologyBaseChangeOn q iX p kY F (⨅ j, U (s j)) n :=
  have := quasiCompact_iInf_ι_comp iX U hU s
  have := isSeparated_iInf_ι_comp iX U hU s
  cohomologyBaseChangeOn_of_quasiCompact_of_isSeparated H F _ n

end On

end AlgebraicGeometry

end
