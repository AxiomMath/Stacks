module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.Sites.Pretopology.CombinatorialEquivalence
public import StacksFrontier.CategoryTheory.Sites.Pretopology.EquivalenceComparison
public import StacksCore.Tactic.StacksAttribute

/-!
# Representing fppf coverings inside a big fppf site

A big fppf site chooses a set-sized collection of covering families on a size-bounded full
subcategory of schemes.  An arbitrary fppf covering of one of its objects need not be one
of the chosen families, since its source schemes need not even be objects of the site.
This file shows that nothing is lost: every fppf covering of an object of the site is
refined by a chosen family, and a standard fppf covering or a Zariski covering is already
tautologically equivalent to one.

## Main results

* `AlgebraicGeometry.exists_isCovering_tautologicallyEquivalent_of_sources_iso`: an fppf
  family whose sources are represented in the site is tautologically equivalent to a chosen
  covering.
* `AlgebraicGeometry.exists_isCovering_refining_fppfCovering`: every fppf covering of an
  object of the site is refined by a chosen covering.
* `AlgebraicGeometry.exists_isCovering_tautologicallyEquivalent_standardFppfCovering` and
  `AlgebraicGeometry.exists_isCovering_tautologicallyEquivalent_openCover`: standard fppf
  coverings and Zariski coverings are tautologically equivalent to chosen coverings.

## Implementation notes

Families are `CategoryTheory.PreZeroHypercover`s, and the comparisons retain the
family-level tautological equivalence — the index bijections together with the compatible
isomorphisms of source schemes — rather than merely equality of the generated covering
sieves.  Because the sources of the given family need not lie in the size-bounded
subcategory, every comparison is made after applying the site's inclusion functor to the
internal family.

## References

* [Stacks Project, Tag 03WX](https://stacks.math.columbia.edu/tag/03WX)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v w w'

namespace AlgebraicGeometry

/-- If every member of `E` is isomorphic over `S` to a member of `F`, then every arrow of the
presieve of `E` is isomorphic to an arrow of the presieve of `F`. -/
private lemma exists_iso_presieve₀_of_exists_iso
    {C : Type u} [Category.{v} C] {S : C}
    {E : PreZeroHypercover.{w} S} {F : PreZeroHypercover.{w'} S}
    (h : ∃ α : E.I₀ → F.I₀, ∀ i, ∃ e : E.X i ≅ F.X (α i), e.hom ≫ F.f (α i) = E.f i)
    ⦃Z : C⦄ (g : Z ⟶ S) (hg : E.presieve₀ g) :
    ∃ (Y : C) (e : Y ≅ Z), F.presieve₀ (e.hom ≫ g) := by
  obtain ⟨i⟩ := hg
  obtain ⟨α, hα⟩ := h
  obtain ⟨e, he⟩ := hα i
  exact ⟨F.X (α i), e.symm, by simp [← he]⟩

/-- Tautologically equivalent families generate the same membership in a precoverage that
respects isomorphisms. -/
private lemma mem_precoverage_of_tautologicallyEquivalent
    {C : Type u} [Category.{v} C] (J : Precoverage C) [J.RespectsIso]
    {S : C} {E : PreZeroHypercover.{w} S} {F : PreZeroHypercover.{w'} S}
    (h : PreZeroHypercover.TautologicallyEquivalent E F)
    (hE : E.presieve₀ ∈ J S) : F.presieve₀ ∈ J S :=
  Precoverage.RespectsIso.of_forall_exists_iso (J := J)
    (exists_iso_presieve₀_of_exists_iso h.1) (exists_iso_presieve₀_of_exists_iso h.2) hE

/-- Index maps with equalities `E.X i = F.X (α i)` compatible with the arrows give, after
applying a functor, the isomorphisms required for a tautological equivalence. -/
private lemma map_exists_iso_of_eqToHom {C : Type u} [Category.{v} C] {D : Type*} [Category D]
    (G : C ⥤ D) {S : C} {E : PreZeroHypercover.{w} S} {F : PreZeroHypercover.{w'} S}
    (α : E.I₀ → F.I₀) (hα : ∀ i, E.X i = F.X (α i))
    (h : ∀ i, eqToHom (hα i) ≫ F.f (α i) = E.f i) :
    ∃ α : (E.map G).I₀ → (F.map G).I₀, ∀ i : E.I₀, ∃ e : (E.map G).X i ≅ (F.map G).X (α i),
      e.hom ≫ (F.map G).f (α i) = (E.map G).f i :=
  ⟨α, fun i ↦ ⟨G.mapIso (eqToIso (hα i)), by
    change G.map (eqToHom (hα i)) ≫ G.map (F.f (α i)) = G.map (E.f i)
    rw [← Functor.map_comp, h]⟩⟩

/-- An fppf covering family whose sources are represented, over the target, by objects of a
big fppf site is tautologically equivalent to one of the site's chosen coverings. -/
public theorem exists_isCovering_tautologicallyEquivalent_of_sources_iso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (T : B.Schemes)
    (U : PreZeroHypercover.{w} (B.inclusion.obj T))
    (hU : U.presieve₀ ∈ Scheme.fppfPrecoverage (B.inclusion.obj T))
    (hrep : ∀ i, ∃ V : B.Schemes, ∃ g : V ⟶ T,
      ∃ e : U.X i ≅ B.inclusion.obj V,
        e.hom ≫ B.inclusion.map g = U.f i) :
    ∃ V : PreZeroHypercover.{u + 1} T,
      B.IsCovering ⟨T, V⟩ ∧
        PreZeroHypercover.TautologicallyEquivalent U (V.map B.inclusion) := by
  classical
  choose X g e he using hrep
  let W : PreZeroHypercover.{w} T :=
    { I₀ := U.I₀
      X := X
      f := g }
  have hUW : PreZeroHypercover.TautologicallyEquivalent U (W.map B.inclusion) := by
    constructor
    · refine ⟨id, fun i ↦ ⟨e i, ?_⟩⟩
      change (e i).hom ≫ B.inclusion.map (g i) = U.f i
      exact he i
    · refine ⟨id, fun i ↦ ⟨(e i).symm, ?_⟩⟩
      change (e i).inv ≫ U.f i = B.inclusion.map (g i)
      rw [← he i, Iso.inv_hom_id_assoc]
  have hW : (W.map B.inclusion).presieve₀ ∈ Scheme.fppfPrecoverage (B.inclusion.obj T) :=
    mem_precoverage_of_tautologicallyEquivalent _ hUW hU
  have hWshrink : PreZeroHypercover.TautologicallyEquivalent
      (W.map B.inclusion) (W.shrink.map B.inclusion) := by
    constructor
    · refine map_exists_iso_of_eqToHom _ W.toShrink.s₀ (fun i ↦ rfl) fun i ↦ ?_
      exact W.toShrink.w₀ i
    · refine map_exists_iso_of_eqToHom _ W.fromShrink.s₀
        (fun i ↦ (Presieve.ofArrows_surj W.f i.1.2 i.2).choose_spec.1.symm) fun i ↦ ?_
      exact W.fromShrink.w₀ i
  have hWs : (W.shrink.map B.inclusion).presieve₀ ∈
      Scheme.fppfPrecoverage (B.inclusion.obj T) :=
    mem_precoverage_of_tautologicallyEquivalent _ hWshrink hW
  have hWs' : AlgebraicGeometry.IsFppfCovering ⟨T, W.shrink⟩ := by
    rw [AlgebraicGeometry.IsFppfCovering, Precoverage.mem_comap_iff,
      ← PreZeroHypercover.presieve₀_map]
    exact hWs
  obtain ⟨Vcov, hV, hcombCov⟩ :=
    B.fppf_has_representative ⟨T, W.shrink⟩ hWs'
  rcases Vcov with ⟨T', V⟩
  rcases hcombCov with ⟨htarget, hcomb⟩
  cases htarget
  refine ⟨V, hV, ?_⟩
  apply PreZeroHypercover.tautologicallyEquivalent_trans U (W.map B.inclusion)
    (V.map B.inclusion) hUW
  apply PreZeroHypercover.tautologicallyEquivalent_trans (W.map B.inclusion)
    (W.shrink.map B.inclusion) (V.map B.inclusion) hWshrink
  rcases hcomb with ⟨⟨α, hα, hfα⟩, β, hβ, hfβ⟩
  exact ⟨map_exists_iso_of_eqToHom _ α hα fun i ↦ (hfα i).symm,
    map_exists_iso_of_eqToHom _ β hβ fun i ↦ (hfβ i).symm⟩

/-- A standard fppf covering of an object of a big fppf site is tautologically equivalent to a
covering belonging to that site. -/
@[stacks 03WX "standard_equivalence"]
public theorem exists_isCovering_tautologicallyEquivalent_standardFppfCovering
    (B : AlgebraicGeometry.BigFppfSite.{u}) (T : B.Schemes)
    (U : PreZeroHypercover.{w} (B.inclusion.obj T))
    (hU : U.presieve₀ ∈ Scheme.fppfPrecoverage (B.inclusion.obj T))
    (hstandard : AlgebraicGeometry.IsStandardFppfCovering U.X U.f) :
    ∃ V : PreZeroHypercover.{u + 1} T,
      B.IsCovering ⟨T, V⟩ ∧
        PreZeroHypercover.TautologicallyEquivalent U (V.map B.inclusion) := by
  apply exists_isCovering_tautologicallyEquivalent_of_sources_iso B T U hU
  intro i
  let : LocallyOfFinitePresentation (U.f i) := (hstandard.finite_presentation i).1
  let : LocallyOfFiniteType (U.f i) := inferInstance
  let : QuasiCompact (U.f i) := (hstandard.finite_presentation i).2.1
  exact ⟨⟨U.X i, Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (U.f i) T.2⟩,
    ⟨U.f i⟩, Iso.refl _, rfl⟩

/-- A Zariski covering of an object of a big fppf site is tautologically equivalent to a
covering belonging to that site. -/
@[stacks 03WX "zariski_equivalence"]
public theorem exists_isCovering_tautologicallyEquivalent_openCover
    (B : AlgebraicGeometry.BigFppfSite.{u}) (T : B.Schemes)
    (U : (B.inclusion.obj T).OpenCover.{w}) :
    ∃ V : PreZeroHypercover.{u + 1} T,
      B.IsCovering ⟨T, V⟩ ∧
        PreZeroHypercover.TautologicallyEquivalent U.toPreZeroHypercover
          (V.map B.inclusion) :=
  exists_isCovering_tautologicallyEquivalent_of_sources_iso B T
    U.toPreZeroHypercover (Scheme.zariskiPrecoverage_le_fppfPrecoverage _ U.mem₀)
    (fun i => ⟨⟨U.X i, Scheme.size_lt_of_isOpenImmersion (U.f i) T.2⟩,
      ⟨U.f i⟩, Iso.refl _, rfl⟩)

/-- Every point of the source of a morphism has an affine open neighbourhood mapping into
an affine open of the target. -/
private lemma exists_affine_neighborhood_subordinate {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (V : Y.Opens) (_ : IsAffineOpen V),
      x ∈ U ∧ U ≤ f ⁻¹ᵁ V := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y)
    (x := f.base x) (U := (⊤ : Y.Opens)) trivial
  obtain ⟨U, hU, hxU, hUsub⟩ := exists_isAffineOpen_mem_and_subset (X := X)
    (x := x) (U := f ⁻¹ᵁ V) hxV
  exact ⟨U, hU, V, hV, hxU, hUsub⟩

/-- An arbitrary fppf covering of an object of a big fppf site is refined by a covering
belonging to that site. -/
@[stacks 03WX "site_refinement"]
public theorem exists_isCovering_refining_fppfCovering
    (B : AlgebraicGeometry.BigFppfSite.{u}) (T : B.Schemes)
    (E : PreZeroHypercover.{w} (B.inclusion.obj T))
    (hE : E.presieve₀ ∈ Scheme.fppfPrecoverage (B.inclusion.obj T)) :
    ∃ V : PreZeroHypercover.{u + 1} T,
      B.IsCovering ⟨T, V⟩ ∧ Nonempty ((V.map B.inclusion).Hom E) := by
  classical
  let S := B.inclusion.obj T
  have hdata := (Scheme.presieve₀_mem_precoverage_iff E).mp
    (by simpa [Scheme.fppfPrecoverage] using hE)
  let i (x : S) : E.I₀ := (hdata.1 x).choose
  have hxrange (x : S) : x ∈ Set.range (E.f (i x)) := (hdata.1 x).choose_spec
  let y (x : S) : E.X (i x) := (Set.mem_range.mp (hxrange x)).choose
  have hy (x : S) : E.f (i x) (y x) = x :=
    (Set.mem_range.mp (hxrange x)).choose_spec
  choose A hA W hW hxA hAW using fun x : S =>
    exists_affine_neighborhood_subordinate (E.f (i x)) (y x)
  let E' : PreZeroHypercover.{u + 1} S :=
    { I₀ := ULift.{u + 1} S
      X := fun x => (A x.down).toScheme
      f := fun x => (A x.down).ι ≫ E.f (i x.down) }
  have hE' : E'.presieve₀ ∈ Scheme.fppfPrecoverage S := by
    refine (Scheme.presieve₀_mem_precoverage_iff E').2 ⟨?_, ?_⟩
    · intro x
      refine ⟨ULift.up x, ⟨y x, hxA x⟩, ?_⟩
      change E.f (i x) ((A x).ι ⟨y x, hxA x⟩) = x
      simpa using hy x
    · intro z
      let : Flat (E.f (i z.down)) := hdata.2 (i z.down) |>.1
      let : LocallyOfFinitePresentation (E.f (i z.down)) :=
        hdata.2 (i z.down) |>.2
      exact ⟨inferInstance, inferInstance⟩
  have hsize : ∀ z, (E'.X z).size < B.cutoff := by
    intro z
    let f := E.f (i z.down)
    let q : (A z.down).toScheme ⟶ (W z.down).toScheme :=
      (E.X (i z.down)).homOfLE (hAW z.down) ≫ f ∣_ (W z.down)
    let : LocallyOfFinitePresentation f := hdata.2 (i z.down) |>.2
    let : IsAffine (A z.down).toScheme := hA z.down
    let : IsAffine (W z.down).toScheme := hW z.down
    let : IsAffineHom q := inferInstance
    let : QuasiCompact q := inferInstance
    exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact q
      (Scheme.size_lt_of_isOpenImmersion (W z.down).ι T.2)
  obtain ⟨V, hV, htaut⟩ :=
    exists_isCovering_tautologicallyEquivalent_of_sources_iso B T E' hE'
      (fun z => ⟨⟨E'.X z, hsize z⟩, ⟨E'.f z⟩, Iso.refl _, rfl⟩)
  rcases htaut.2 with ⟨β, hβ⟩
  refine ⟨V, hV, ⟨PreZeroHypercover.Hom.mk
    (fun j => i (β j).down)
    (fun j => (hβ j).choose.hom ≫ (A (β j).down).ι)
    (fun j => ?_)⟩⟩
  simpa [E', Category.assoc] using (hβ j).choose_spec

end AlgebraicGeometry
