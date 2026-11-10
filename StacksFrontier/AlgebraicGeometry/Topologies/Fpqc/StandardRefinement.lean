module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Sites.QuasiCompact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Characterization

/-!
# Standard fpqc refinements of fpqc coverings

Every fpqc covering of an affine scheme admits a finite refinement by affine schemes which are
flat over the target, and the refining schemes may be chosen as affine open subschemes of
members of the original covering.  Such a finite flat affine covering of an affine scheme is
itself an fpqc covering, so the standard fpqc coverings of an affine scheme are cofinal among
its fpqc coverings.  Over a general target the refinement is available above every affine open.

Together with the criterion by refinements after affine base change this gives a
characterization: a flat family is an fpqc covering exactly when it admits a finite flat affine
refinement after every base change to an affine scheme.

## Main results

* `AlgebraicGeometry.presieve₀_mem_fpqcPrecoverage_of_finite_affineCover` — a finite flat affine
  covering of an affine scheme is an fpqc covering.
* `AlgebraicGeometry.exists_finite_affineCover_flat_refinement` — the refinement of an fpqc
  covering of an affine scheme; this is the form that carries the `022E` attribute.
* `AlgebraicGeometry.exists_finite_affineCover_flat_hom_of_mem_fpqcPrecoverage` — the same
  refinement with the refining family indexed by an arbitrary finite type.
* `AlgebraicGeometry.exists_fin_affineCover_flat_hom_of_mem_fpqcPrecoverage` — the same
  refinement with the refining family indexed by `Fin n`, which is the indexing of the source.
* `AlgebraicGeometry.exists_finite_affineCover_flat_refinement_over_affineOpen` — the refinement
  above an affine open of an arbitrary target.
* `AlgebraicGeometry.presieve₀_mem_fpqcPrecoverage_iff_affine_refinements` — the resulting
  characterization.

## Implementation notes

A *standard fpqc covering* of an affine scheme, Stacks 022F, is a finite jointly surjective
family of flat morphisms whose sources are affine.  No new definition is introduced for it: it
is an `AlgebraicGeometry.Scheme.AffineCover` for `AlgebraicGeometry.Flat` with finite index
type over an affine base, which is the spelling already used by
`AlgebraicGeometry.isStandardVCovering_of_flat_affineCover` and by the refinement hypothesis of
`AlgebraicGeometry.presieve₀_mem_fpqcPrecoverage_of_affine_refinements`.  A refinement is a
`CategoryTheory.PreZeroHypercover.Hom`, whose index universes may differ.

The refinement is extracted from `AlgebraicGeometry.QuasiCompactCover.exists_hom`, whose
hypotheses an fpqc covering of an affine scheme meets: the quasi-compactness of the covering is
one of the two halves of membership in `AlgebraicGeometry.Scheme.fpqcPrecoverage`, an affine
scheme is a compact space, and flatness is preserved by precomposition with an open immersion.
That lemma produces a refinement whose index type is the one of the covering it refines; since
the refinement is finite, its index is transported to a type in the lowest universe by
`AlgebraicGeometry.Scheme.AffineCover.reindex`, which is the shape the characterization needs.

Three spellings of the refinement are kept, differing only in how the finiteness of the index of
the refining family is presented: `Finite` on an index in `Type 0`, `Finite` on an index in the
universe `QuasiCompactCover.exists_hom` hands back, and an identification of the index with
`Fin n`.  They are interchangeable by `Finite.exists_equiv_fin`.

## References

* [Stacks Project, Tag 022E](https://stacks.math.columbia.edu/tag/022E)
* [Stacks Project, Tag 022F](https://stacks.math.columbia.edu/tag/022F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

/-- Transport the index type of an affine cover along an equivalence. -/
public noncomputable def Scheme.AffineCover.reindex {S : Scheme.{u}}
    {P : MorphismProperty Scheme.{u}} (𝒱 : S.AffineCover.{v} P) {ι : Type w} (e : ι ≃ 𝒱.I₀) :
    S.AffineCover.{w} P where
  I₀ := ι
  X i := 𝒱.X (e i)
  f i := 𝒱.f (e i)
  idx x := e.symm (𝒱.idx x)
  covers x := by
    rw [e.apply_symm_apply]
    exact 𝒱.covers x
  map_prop i := 𝒱.map_prop _

/-- The index type of `𝒱.reindex e` is the domain of `e`. -/
@[simp]
public lemma Scheme.AffineCover.reindex_I₀ {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    (𝒱 : S.AffineCover.{v} P) {ι : Type w} (e : ι ≃ 𝒱.I₀) : (𝒱.reindex e).I₀ = ι :=
  rfl

/-- The morphism of `𝒱.reindex e` at `i` is the morphism of `𝒱` at `e i`. -/
@[simp]
public lemma Scheme.AffineCover.reindex_f {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    (𝒱 : S.AffineCover.{v} P) {ι : Type w} (e : ι ≃ 𝒱.I₀) (i : ι) :
    (𝒱.reindex e).f i = 𝒱.f (e i) :=
  rfl

/-- A standard fpqc covering, Stacks 022F, is an fpqc covering: a finite jointly surjective
family of flat morphisms from affine schemes to an affine scheme is quasi-compact, hence belongs
to the fpqc precoverage. -/
@[sga "3 IV 6.3.1" "(v), special case"]
public lemma presieve₀_mem_fpqcPrecoverage_of_finite_affineCover {T : Scheme.{u}} [IsAffine T]
    (𝒱 : T.AffineCover.{v} (@Flat.{u})) [Finite 𝒱.I₀] :
    𝒱.cover.presieve₀ ∈ Scheme.fpqcPrecoverage T := by
  have hjs : Scheme.JointlySurjective (Scheme.precoverage (@Flat.{u})) :=
    @AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage.{u} (@Flat.{u})
  have hfin : Finite 𝒱.cover.I₀ := ‹Finite 𝒱.I₀›
  have hqcmap (i : 𝒱.cover.I₀) : AlgebraicGeometry.QuasiCompact (𝒱.cover.f i) :=
    inferInstanceAs (AlgebraicGeometry.QuasiCompact (𝒱.f i))
  have hqc : QuasiCompactCover 𝒱.cover.toPreZeroHypercover := QuasiCompactCover.of_finite
  change 𝒱.cover.presieve₀ ∈ Scheme.qcPrecoverage T ∧
    𝒱.cover.presieve₀ ∈ Scheme.precoverage (@Flat.{u}) T
  exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr hqc, 𝒱.cover.mem₀⟩

/-- Refinement of an fpqc covering of an affine scheme by a finite flat affine cover. -/
private theorem exists_finite_affineCover_flat_hom
    {T : Scheme.{u}} [IsAffine T] (𝒰 : PreZeroHypercover.{v} T)
    (h𝒰 : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage T) :
    ∃ (𝒱 : T.AffineCover.{v} (@Flat : MorphismProperty Scheme.{u}))
      (φ : 𝒱.cover.toPreZeroHypercover.Hom 𝒰),
      Finite 𝒱.I₀ ∧
        𝒱.cover.toPreZeroHypercover.presieve₀ ∈ Scheme.fpqcPrecoverage T ∧
        ∀ j, IsOpenImmersion (φ.h₀ j) := by
  have hmem : 𝒰.presieve₀ ∈ Scheme.qcPrecoverage T ∧
      𝒰.presieve₀ ∈ Scheme.precoverage (@Flat.{u} : MorphismProperty Scheme.{u}) T := h𝒰
  let 𝒰' : T.Cover (Scheme.precoverage (@Flat : MorphismProperty Scheme.{u})) :=
    { toPreZeroHypercover := 𝒰, mem₀ := hmem.2 }
  have hqc : QuasiCompactCover 𝒰'.toPreZeroHypercover :=
    Scheme.presieve₀_mem_qcPrecoverage_iff.mp hmem.1
  have hrl : MorphismProperty.RespectsLeft
      (@Flat : MorphismProperty Scheme.{u}) @IsOpenImmersion :=
    (inferInstance : MorphismProperty.Respects (@Flat.{u}) @IsOpenImmersion).toRespectsLeft
  obtain ⟨𝒱, φ, hfin, hopen⟩ := QuasiCompactCover.exists_hom 𝒰'
  exact ⟨𝒱, φ, hfin, presieve₀_mem_fpqcPrecoverage_of_finite_affineCover 𝒱, hopen⟩

/-- The refinement of an fpqc covering of an affine scheme, indexed by `Fin n`. -/
private theorem exists_fin_affineCover_flat_hom
    {T : Scheme.{u}} [IsAffine T] (𝒰 : PreZeroHypercover.{v} T)
    (h𝒰 : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage T) :
    ∃ (n : ℕ) (𝒱 : T.AffineCover.{0} (@Flat : MorphismProperty Scheme.{u}))
      (φ : 𝒱.cover.toPreZeroHypercover.Hom 𝒰),
      𝒱.I₀ = Fin n ∧
        𝒱.cover.toPreZeroHypercover.presieve₀ ∈ Scheme.fpqcPrecoverage T ∧
        ∀ j, IsOpenImmersion (φ.h₀ j) := by
  classical
  obtain ⟨𝒱, φ, hfin, -, hopen⟩ :=
    exists_finite_affineCover_flat_hom 𝒰 h𝒰
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin 𝒱.I₀
  let 𝒲 : T.AffineCover.{0} (@Flat : MorphismProperty Scheme.{u}) := 𝒱.reindex e.symm
  have h𝒲 : Finite 𝒲.I₀ := inferInstanceAs (Finite (Fin n))
  refine ⟨n, 𝒲,
    { s₀ j := φ.s₀ (e.symm j)
      h₀ j := φ.h₀ (e.symm j)
      w₀ j := φ.w₀ (e.symm j) }, rfl,
    presieve₀_mem_fpqcPrecoverage_of_finite_affineCover 𝒲, fun j ↦ hopen (e.symm j)⟩

/-- An fpqc covering of an affine scheme admits a refinement by a standard fpqc
covering: a finite jointly surjective family of flat morphisms from affine schemes, again an
fpqc covering, whose members are affine open subschemes of members of the given covering. -/
@[stacks 022E]
public theorem exists_finite_affineCover_flat_refinement {T : Scheme.{u}} [IsAffine T]
    (U : PreZeroHypercover.{v} T) (hU : U.presieve₀ ∈ Scheme.fpqcPrecoverage T) :
    ∃ (V : T.AffineCover.{0} (@Flat.{u})) (refinement : V.cover.toPreZeroHypercover.Hom U),
      Finite V.I₀ ∧ V.cover.presieve₀ ∈ Scheme.fpqcPrecoverage T ∧
        ∀ j, IsOpenImmersion (refinement.h₀ j) := by
  obtain ⟨n, V, φ, hV, hmem, hopen⟩ := exists_fin_affineCover_flat_hom U hU
  exact ⟨V, φ, hV ▸ inferInstanceAs (Finite (Fin n)), hmem, hopen⟩

/-- An fpqc covering of an affine scheme `T` is refined, along open immersions, by a finite
family of flat morphisms to `T` with affine sources; that family is again an fpqc covering.

This is the form of Stacks 022E with the refining family indexed by an arbitrary finite type;
`AlgebraicGeometry.exists_finite_affineCover_flat_refinement` is the form whose index lies in
`Type 0` and carries the attribute, and
`AlgebraicGeometry.exists_fin_affineCover_flat_hom_of_mem_fpqcPrecoverage` the form indexed by
`Fin n`. -/
public theorem exists_finite_affineCover_flat_hom_of_mem_fpqcPrecoverage
    {T : Scheme.{u}} [IsAffine T] (𝒰 : PreZeroHypercover.{v} T)
    (h𝒰 : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage T) :
    ∃ (𝒱 : T.AffineCover.{v} (@Flat : MorphismProperty Scheme.{u}))
      (φ : 𝒱.cover.toPreZeroHypercover.Hom 𝒰),
      Finite 𝒱.I₀ ∧
        𝒱.cover.toPreZeroHypercover.presieve₀ ∈ Scheme.fpqcPrecoverage T ∧
        ∀ j, IsOpenImmersion (φ.h₀ j) :=
  exists_finite_affineCover_flat_hom 𝒰 h𝒰

/-- An fpqc covering `𝒰` of an affine scheme `T` is refined by a standard fpqc covering
`{U_j ⟶ T}_{j = 1, …, n}`: finitely many flat morphisms with affine sources whose images cover
`T`, again an fpqc covering.  Moreover each `U_j` is an open affine of one of the members of
`𝒰`, which is recorded by the refinement morphisms `φ.h₀ j` being open immersions.

This is the form of Stacks 022E with the refining family indexed by `Fin n`, as in the source;
`AlgebraicGeometry.exists_finite_affineCover_flat_refinement` is the form carrying the
attribute. -/
public theorem exists_fin_affineCover_flat_hom_of_mem_fpqcPrecoverage
    {T : Scheme.{u}} [IsAffine T] (𝒰 : PreZeroHypercover.{v} T)
    (h𝒰 : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage T) :
    ∃ (n : ℕ) (𝒱 : T.AffineCover.{0} (@Flat : MorphismProperty Scheme.{u}))
      (φ : 𝒱.cover.toPreZeroHypercover.Hom 𝒰),
      𝒱.I₀ = Fin n ∧
        𝒱.cover.toPreZeroHypercover.presieve₀ ∈ Scheme.fpqcPrecoverage T ∧
        ∀ j, IsOpenImmersion (φ.h₀ j) :=
  exists_fin_affineCover_flat_hom 𝒰 h𝒰

/-- **Stacks 022E over an affine open.** Above any affine open of the target, an fpqc covering of
an arbitrary scheme restricts to a covering which admits a standard fpqc refinement. -/
public theorem exists_finite_affineCover_flat_refinement_over_affineOpen {S : Scheme.{u}}
    (U : PreZeroHypercover.{v} S) (hU : U.presieve₀ ∈ Scheme.fpqcPrecoverage S)
    (V : S.affineOpens) :
    ∃ (W : (V.1.toScheme).AffineCover.{0} (@Flat.{u}))
      (refinement : W.cover.toPreZeroHypercover.Hom (U.pullback₁ V.1.ι)),
      Finite W.I₀ ∧ W.cover.presieve₀ ∈ Scheme.fpqcPrecoverage V.1.toScheme ∧
        ∀ j, IsOpenImmersion (refinement.h₀ j) := by
  have : IsAffine (V.1.toScheme) := V.2
  exact exists_finite_affineCover_flat_refinement (U.pullback₁ V.1.ι)
    ((⟨U, hU⟩ : Scheme.fpqcPrecoverage.ZeroHypercover S).pullback₁ V.1.ι).mem₀

/-- **Stacks 022E, as a characterization.** A family of morphisms of schemes is an fpqc covering
if and only if its members are flat and, after base change to any affine scheme, it admits a
refinement by a standard fpqc covering.  The forward implication is Stacks 022E applied to the
base-changed family, the converse is
`AlgebraicGeometry.presieve₀_mem_fpqcPrecoverage_of_affine_refinements`. -/
public theorem presieve₀_mem_fpqcPrecoverage_iff_affine_refinements {T : Scheme.{u}}
    (U : PreZeroHypercover.{v} T) :
    U.presieve₀ ∈ Scheme.fpqcPrecoverage T ↔
      ((∀ i, Flat (U.f i)) ∧
        ∀ {Z : Scheme.{u}} [IsAffine Z] (h : Z ⟶ T),
          ∃ V : Z.AffineCover.{0} (@Flat.{u}), Finite V.I₀ ∧
            Nonempty (V.cover.toPreZeroHypercover.Hom (U.pullback₂ h))) := by
  refine ⟨fun hU ↦ ?_, fun ⟨hflat, hrefine⟩ ↦
    presieve₀_mem_fpqcPrecoverage_of_affine_refinements U hflat hrefine⟩
  have hU' : U.presieve₀ ∈ Scheme.qcPrecoverage T ∧
      U.presieve₀ ∈ Scheme.precoverage (@Flat.{u}) T := hU
  refine ⟨fun i ↦ (Scheme.presieve₀_mem_precoverage_iff U).mp hU'.2 |>.2 i,
    fun {Z} _ h ↦ ?_⟩
  obtain ⟨V, refinement, hfin, -, -⟩ :=
    exists_finite_affineCover_flat_refinement (U.pullback₂ h)
      ((⟨U, hU⟩ : Scheme.fpqcPrecoverage.ZeroHypercover T).pullback₂ h).mem₀
  exact ⟨V, hfin, ⟨refinement⟩⟩

end AlgebraicGeometry

end
