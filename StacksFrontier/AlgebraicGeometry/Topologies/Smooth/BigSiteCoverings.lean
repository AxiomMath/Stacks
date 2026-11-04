module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.BigSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.StandardCovering
public import StacksFrontier.CategoryTheory.Sites.Hypercover.ZeroOver
public import StacksFrontier.CategoryTheory.Sites.Pretopology.CombinatorialEquivalence

/-!
# Coverings of a big smooth site

A big smooth site admits only set-many covering families, chosen with a bound on their index
types. This file shows that nothing is lost: every covering family one actually meets is
accounted for by one of the chosen families.

Three cases, in increasing strength. An arbitrary smooth covering family of an object of the
site, formed in the ambient category of schemes, is *refined* by a chosen family. A standard
smooth covering — a finite affine one — and a Zariski covering are, more strongly,
*tautologically equivalent* to a chosen family, so they agree with it up to isomorphisms of the
source schemes.

## Main results

* `AlgebraicGeometry.exists_covering_refining_smooth_cover` — an internal refinement of an
  arbitrary ambient smooth covering family.
* `AlgebraicGeometry.exists_covering_tautologicallyEquivalent_standardSmoothCover` — a standard
  smooth covering is tautologically equivalent to a chosen family.
* `AlgebraicGeometry.exists_covering_tautologicallyEquivalent_openCover` — a Zariski covering is
  tautologically equivalent to a chosen family.

## Implementation notes

A family of morphisms over a fixed object is a `CategoryTheory.PreZeroHypercover`. The given
family has sources in the ambient category of schemes, whereas a chosen family has sources in
the site's cutoff category; the latter is therefore mapped along the canonical inclusion before
the two are compared. A refinement is a morphism of pre-zero-hypercovers.

For the refinement statement the given family is first replaced by one indexed by points of the
target, each member being an affine open of the corresponding source; such an affine open is
small enough to lie in the cutoff category because a smooth morphism with affine source is of
finite type, which bounds the size of the source by that of the target.

In the two tautological-equivalence statements the given family is already small enough — the
sources of a Zariski covering are open subschemes of the target, and those of a standard smooth
covering are affine and of finite type over it — so after deduplicating the index type with
`CategoryTheory.PreZeroHypercover.shrink` the family transfers into the cutoff category
directly, and only its combinatorial representative has to be found.

## References

* [Stacks Project, Tag 03WZ](https://stacks.math.columbia.edu/tag/03WZ)
-/

@[expose] public section

open CategoryTheory

universe u v

/-- Combinatorial equivalence is preserved by mapping both families along a functor. -/
lemma CategoryTheory.PreZeroHypercover.CombinatoriallyEquivalent.map {C D : Type*} [Category C]
    [Category D] (F : C ⥤ D) {U : C} {E : PreZeroHypercover.{v} U}
    {E' : PreZeroHypercover.{u} U} (h : CombinatoriallyEquivalent E E') :
    CombinatoriallyEquivalent (E.map F) (E'.map F) := by
  obtain ⟨⟨α, hX, hf⟩, ⟨β, hY, hg⟩⟩ := h
  refine ⟨⟨α, fun i => congrArg F.obj (hX i), fun i => ?_⟩,
    ⟨β, fun j => congrArg F.obj (hY j), fun j => ?_⟩⟩
  · change F.map (E.f i) = _ ≫ F.map (E'.f (α i))
    rw [hf i, F.map_comp, eqToHom_map]
    rfl
  · change F.map (E'.f j) = _ ≫ F.map (E.f (β j))
    rw [hg j, F.map_comp, eqToHom_map]
    rfl

namespace AlgebraicGeometry

private lemma size_lt_of_shrink {S : Scheme.{u}} (E : PreZeroHypercover.{v} S)
    {κ : Cardinal.{u}} (hsize : ∀ i, (E.X i).size < κ) :
    ∀ i, (E.shrink.X i).size < κ := by
  intro i
  obtain ⟨j, hX, _⟩ := Presieve.ofArrows_surj E.f _ i.2
  change (i.1.1).size < κ
  rw [← hX]
  exact hsize j

private lemma tautologicallyEquivalent_shrink {S : Scheme.{u}}
    (E : PreZeroHypercover.{v} S) :
    PreZeroHypercover.TautologicallyEquivalent E E.shrink := by
  constructor
  · refine ⟨E.toShrink.s₀, fun i => ⟨Iso.refl _, ?_⟩⟩
    simpa [PreZeroHypercover.toShrink] using E.toShrink.w₀ i
  · refine ⟨E.fromShrink.s₀, fun i => ?_⟩
    let h := Presieve.ofArrows_surj E.f _ i.2
    refine ⟨eqToIso (show E.shrink.X i = E.X (E.fromShrink.s₀ i) from ?_), ?_⟩
    · change (i.1.1) = E.X h.choose
      exact h.choose_spec.1.symm
    convert E.fromShrink.w₀ i using 1
    rfl

private lemma size_lt_of_smooth_affine_source {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine X] [Smooth f] {κ : Cardinal.{u}} (hY : Y.size < κ) : X.size < κ :=
  (Scheme.size_le_of_locallyOfFiniteType f).trans_lt hY

/-- A smooth covering family of an object of a big smooth site whose sources already lie below
the site's cutoff is tautologically equivalent to a chosen covering family. -/
private theorem exists_site_cover_tautologicallyEquivalent
    (B : BigSmoothSite.{u}) {T : B.category}
    (E : PreZeroHypercover.{u + 1} T.1)
    (hE : E.presieve₀ ∈ Scheme.precoverage (@Smooth.{u}) T.1)
    (hsize : ∀ i, (E.X i).size < B.cutoff) :
    ∃ V : PreZeroHypercover.{u + 1} T,
      B.IsCovering ⟨T, V⟩ ∧
        PreZeroHypercover.TautologicallyEquivalent E (V.map (ObjectProperty.ι _)) := by
  let W : PreZeroHypercover.{u + 1} T :=
    { I₀ := E.I₀
      X := fun i => ⟨E.X i, hsize i⟩
      f := fun i => ⟨E.f i⟩ }
  have hW : SmoothCovering B.cutoff ⟨T, W⟩ := by
    change (W.map (ObjectProperty.ι _)).presieve₀ ∈
      Scheme.precoverage (@Smooth.{u}) T.1
    simpa [W, PreZeroHypercover.map] using hE
  obtain ⟨W', hW', ht, hcomb⟩ := B.has_coveringRepresentative ⟨T, W⟩ hW
  cases ht
  refine ⟨W'.2, hW', ?_⟩
  change PreZeroHypercover.CombinatoriallyEquivalent W W'.2 at hcomb
  have hE : E = W.map (ObjectProperty.ι _) := by
    cases E
    rfl
  rw [hE]
  exact PreZeroHypercover.tautologicallyEquivalent_of_combinatoriallyEquivalent _ _
    (hcomb.map (ObjectProperty.ι _))

/-- A smooth covering family of an object of a big smooth site whose sources lie below the site's
cutoff is tautologically equivalent to a chosen covering family, whatever its index universe. -/
private theorem exists_site_cover_tautologicallyEquivalent_of_small
    (B : BigSmoothSite.{u}) {T : B.category}
    (E : PreZeroHypercover.{v} T.1)
    (hE : E.presieve₀ ∈ Scheme.precoverage (@Smooth.{u}) T.1)
    (hsize : ∀ i, (E.X i).size < B.cutoff) :
    ∃ V : PreZeroHypercover.{u + 1} T,
      B.IsCovering ⟨T, V⟩ ∧
        PreZeroHypercover.TautologicallyEquivalent E (V.map (ObjectProperty.ι _)) := by
  obtain ⟨V, hV, hSV⟩ := exists_site_cover_tautologicallyEquivalent B E.shrink
    (by rwa [PreZeroHypercover.presieve₀_shrink]) (size_lt_of_shrink E hsize)
  exact ⟨V, hV, PreZeroHypercover.tautologicallyEquivalent_trans E E.shrink _
    (tautologicallyEquivalent_shrink E) hSV⟩

/-- **Stacks Project, Tag 03WZ, part (1).** Every smooth covering family of an object of a
big smooth site is refined by a covering family belonging to the site. -/
@[stacks 03WZ "part (1)"]
public theorem exists_covering_refining_smooth_cover
    (B : BigSmoothSite.{u}) {T : B.category}
    (U : PreZeroHypercover.{v} ((ObjectProperty.ι _).obj T))
    (hU : U.presieve₀ ∈ Scheme.precoverage (@Smooth.{u}) ((ObjectProperty.ι _).obj T)) :
    ∃ V : PreZeroHypercover.{u + 1} T,
      B.IsCovering ⟨T, V⟩ ∧ Nonempty ((V.map (ObjectProperty.ι _)).Hom U) := by
  classical
  let S := (ObjectProperty.ι _).obj T
  obtain ⟨hcover, hsm⟩ := (Scheme.presieve₀_mem_precoverage_iff U).mp hU
  choose i hi using hcover
  choose y hy using fun x => Set.mem_range.mp (hi x)
  choose A hA hyA _ using fun x : S =>
    exists_isAffineOpen_mem_and_subset (x := y x) (U := ⊤) trivial
  let E : PreZeroHypercover.{u + 1} S :=
    { I₀ := ULift.{u + 1} (↥S)
      X := fun x => (A x.down).toScheme
      f := fun x => (A x.down).ι ≫ U.f (i x.down) }
  have hE : E.presieve₀ ∈ Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}) S := by
    apply (Scheme.presieve₀_mem_precoverage_iff E).2
    refine ⟨fun x => ?_, fun x => ?_⟩
    · refine ⟨ULift.up x, ⟨y x, hyA x⟩, ?_⟩
      change U.f (i x) ((A x).ι.base ⟨y x, hyA x⟩) = x
      simpa using hy x
    · have : Smooth (U.f (i x.down)) := hsm (i x.down)
      infer_instance
  have hsize : ∀ x, (E.X x).size < B.cutoff := by
    intro x
    have : IsAffine (E.X x) := hA x.down
    have : Smooth (E.f x) := by
      dsimp [E]
      infer_instance
    exact size_lt_of_smooth_affine_source (E.f x) T.2
  obtain ⟨V, hV, htaut⟩ := exists_site_cover_tautologicallyEquivalent B E hE hsize
  obtain ⟨β, hβ⟩ := htaut.2
  exact ⟨V, hV, ⟨PreZeroHypercover.Hom.mk (fun j => i (β j).down)
    (fun j => (hβ j).choose.hom ≫ (A (β j).down).ι) (fun j => (hβ j).choose_spec)⟩⟩

/-- **Stacks Project, Tag 03WZ, part (2).** A standard smooth covering of an object of a
big smooth site is tautologically equivalent to a covering family belonging to the site. -/
@[stacks 03WZ "part (2)"]
public theorem exists_covering_tautologicallyEquivalent_standardSmoothCover
    (B : BigSmoothSite.{u}) {T : B.category}
    [IsAffine ((ObjectProperty.ι _).obj T)]
    (U : PreZeroHypercover.{v} ((ObjectProperty.ι _).obj T)) [Finite U.I₀]
    [∀ i, IsAffine (U.X i)]
    (hU : IsStandardSmoothCovering (fun i ↦ U.X i) (fun i ↦ U.f i)) :
    ∃ V : PreZeroHypercover.{u + 1} T,
      B.IsCovering ⟨T, V⟩ ∧
        PreZeroHypercover.TautologicallyEquivalent U (V.map (ObjectProperty.ι _)) := by
  classical
  have hsm (i) : Smooth (U.f i) :=
    (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).2
      (RingHom.IsStandardSmooth.smooth (hU.1 i))
  have hUmem : U.presieve₀ ∈ Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})
      ((ObjectProperty.ι _).obj T) := by
    refine (Scheme.presieve₀_mem_precoverage_iff U).2 ⟨fun x => ?_, hsm⟩
    have hx : x ∈ ⋃ i, Set.range (U.f i) := hU.2.symm ▸ Set.mem_univ x
    exact Set.mem_iUnion.mp hx
  exact exists_site_cover_tautologicallyEquivalent_of_small B U hUmem fun i =>
    have := hsm i; size_lt_of_smooth_affine_source (U.f i) T.2

/-- **Stacks Project, Tag 03WZ, part (3).** A Zariski covering of an object of a big smooth
site is tautologically equivalent to a covering family belonging to the site. -/
@[stacks 03WZ "part (3)"]
public theorem exists_covering_tautologicallyEquivalent_openCover
    (B : BigSmoothSite.{u}) (T : B.category)
    (U : ((ObjectProperty.ι _).obj T).OpenCover.{v}) :
    ∃ V : PreZeroHypercover.{u + 1} T,
      B.IsCovering ⟨T, V⟩ ∧
        PreZeroHypercover.TautologicallyEquivalent U.toPreZeroHypercover
          (V.map (ObjectProperty.ι _)) := by
  classical
  refine exists_site_cover_tautologicallyEquivalent_of_small B U.toPreZeroHypercover ?_
    fun i => Scheme.size_lt_of_isOpenImmersion (U.f i) T.2
  exact Scheme.precoverage_mono (P := @IsOpenImmersion) (Q := @Smooth)
    (fun _ _ _ _ => inferInstance) _ U.mem₀

end AlgebraicGeometry
