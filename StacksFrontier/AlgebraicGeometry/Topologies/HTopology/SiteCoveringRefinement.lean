module

public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AffineSiteEquivalence
public import StacksCore.Tactic.StacksAttribute

/-!
# Realizing arbitrary h coverings inside a big h site

A big h site retains only a set-sized collection of h covering families on a size-bounded
full subcategory of schemes.  An arbitrary h covering of one of its objects therefore need
not be among the chosen families, nor even be a family of objects of the site.  This file
shows that it is nevertheless refined by a chosen family, and that a Zariski covering is
even tautologically equivalent to one.

## Main results

* `AlgebraicGeometry.BigHSite.exists_isCovering_tautologicallyEquivalent_openCover`: a Zariski
  covering of an object of a big h site is tautologically equivalent to a covering belonging
  to the site.
* `AlgebraicGeometry.exists_isCovering_refinement_of_isHCovering`: an arbitrary h covering of
  an object of a big h site is refined by a covering belonging to the site.

The remaining case, a standard h covering of an affine object, is
`AlgebraicGeometry.exists_isCovering_tautologicallyEquivalent_standardHCovering`.

## Implementation notes

A family is transported into the site by bounding the sizes of its sources, after which the
site's representability axiom replaces it by a chosen family combinatorially equivalent to
it.  For a Zariski covering the sources are open subschemes of the target, so
`AlgebraicGeometry.Scheme.size_lt_of_isOpenImmersion` bounds them; the given family is first
deduplicated by `CategoryTheory.PreZeroHypercover.shrink`, which brings its index type into
the site's index universe without leaving its tautological equivalence class.

The refinement is assembled from the two tautological-equivalence cases by the site's own
composition axiom.  The affine opens of the target form a Zariski covering, hence are
tautologically equivalent to a chosen family `G`; each member of `G` is affine, so the base
change of the given h covering to it is an h covering of an affine scheme
(`AlgebraicGeometry.isHCovering_pullback_of_forall_exists_isAffineOpen`, applicable because
that member maps into a single affine open of the target), and Stacks 0ETU in the form
`AlgebraicGeometry.exists_isStandardHCovering_refinement` refines that base change by a
standard h covering, which the affine case realizes inside the site.  Composing the realized
families along `CategoryTheory.PreZeroHypercover.bind` gives the refinement.

Composing h coverings of *schemes* and realizing the result afterwards would need the
unconditional composition of h coverings over a non-affine base; nothing of the kind is used
here, exactly as in the ph analogue `AlgebraicGeometry.exists_isCovering_refinement`.

## References

* [Stacks Project, Tag 0EU0](https://stacks.math.columbia.edu/tag/0EU0)
* [Stacks Project, Tag 0DBK](https://stacks.math.columbia.edu/tag/0DBK)
* [Stacks Project, Tag 0ETU](https://stacks.math.columbia.edu/tag/0ETU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry

/-- An h covering of an object of a big h site whose sources are small enough to be objects of
the site is tautologically equivalent to a covering belonging to the site. -/
private theorem exists_isCovering_tautologicallyEquivalent_of_size_lt
    (B : BigHSite.{u}) (T : B.Schemes) (𝒰 : PreZeroHypercover.{u + 1} (B.inclusion.obj T))
    (h𝒰 : IsHCovering 𝒰.X 𝒰.f) (hsmall : ∀ i, (𝒰.X i).size < B.cutoff) :
    ∃ 𝒱 : PreZeroHypercover.{u + 1} T,
      B.IsCovering ⟨T, 𝒱⟩ ∧
        PreZeroHypercover.TautologicallyEquivalent 𝒰 (𝒱.map B.inclusion) := by
  let W : PreZeroHypercover.{u + 1} T :=
    { I₀ := 𝒰.I₀
      X i := B.obj (𝒰.X i) (hsmall i)
      f i := ObjectProperty.homMk (𝒰.f i) }
  have hW : IsHCoveringInCutoff (κ := B.cutoff) ⟨T, W⟩ := h𝒰
  obtain ⟨⟨T', 𝒱⟩, h𝒱, hT, hcomb⟩ := B.covering_representative ⟨T, W⟩ hW
  cases hT
  refine ⟨𝒱, h𝒱, PreZeroHypercover.tautologicallyEquivalent_trans 𝒰 (W.map B.inclusion)
    (𝒱.map B.inclusion) (PreZeroHypercover.tautologicallyEquivalent_refl _) ?_⟩
  apply PreZeroHypercover.tautologicallyEquivalent_of_combinatoriallyEquivalent
  obtain ⟨⟨α, hX, hf⟩, ⟨β, hY, hg⟩⟩ :
    PreZeroHypercover.CombinatoriallyEquivalent W 𝒱 := hcomb
  refine ⟨⟨α, fun i ↦ congrArg B.inclusion.obj (hX i), fun i ↦ ?_⟩,
    ⟨β, fun j ↦ congrArg B.inclusion.obj (hY j), fun j ↦ ?_⟩⟩
  · simpa [PreZeroHypercover.map] using congrArg B.inclusion.map (hf i)
  · simpa [PreZeroHypercover.map] using congrArg B.inclusion.map (hg j)

/-- **Stacks 0EU0, part (3).** A Zariski covering of an object of a big h site is
tautologically equivalent to a covering belonging to that site. -/
@[stacks 0EU0 "part (3)"]
public theorem BigHSite.exists_isCovering_tautologicallyEquivalent_openCover
    (B : BigHSite.{u}) (T : B.Schemes) (𝒰 : (B.inclusion.obj T).OpenCover.{v}) :
    ∃ 𝒱 : PreZeroHypercover.{u + 1} T,
      B.IsCovering ⟨T, 𝒱⟩ ∧
        PreZeroHypercover.TautologicallyEquivalent 𝒰.toPreZeroHypercover
          (𝒱.map B.inclusion) := by
  classical
  let S := B.inclusion.obj T
  let E := 𝒰.toPreZeroHypercover
  let E' := E.shrink
  have hopen (i : E'.I₀) : IsOpenImmersion (E'.f i) := by
    obtain ⟨j, hX, hf⟩ := Presieve.ofArrows_surj E.f _ i.2
    show IsOpenImmersion i.1.2
    rw [hf]
    infer_instance
  have hcover : ∀ x : S, ∃ i, x ∈ Set.range (E'.f i) := by
    intro x
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
    refine ⟨E.toShrink.s₀ i, ?_⟩
    have hf : (E.toShrink.h₀ i ≫ E'.f (E.toShrink.s₀ i)) y = x :=
      (congrArg (fun f ↦ f y) (E.toShrink.w₀ i)).trans hy
    exact ⟨E.toShrink.h₀ i y, by simpa only [Scheme.Hom.comp_apply] using hf⟩
  let V : S.OpenCover.{u + 1} :=
    { I₀ := E'.I₀
      X := E'.X
      f := E'.f
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨hcover, hopen⟩ }
  have hV : IsHCovering V.X V.f := ⟨fun _ ↦ inferInstance, IsPHCovering.of_openCover V⟩
  obtain ⟨𝒱, h𝒱, htaut⟩ := exists_isCovering_tautologicallyEquivalent_of_size_lt B T
    V.toPreZeroHypercover hV fun i ↦ Scheme.size_lt_of_isOpenImmersion (V.f i) T.2
  -- `E` is tautologically equivalent to its deduplication: the two canonical refinements
  -- between them are built from identities and from the equalities of sources recorded by
  -- `CategoryTheory.PreZeroHypercover.fromShrink`.
  have hshrink : PreZeroHypercover.TautologicallyEquivalent E E.shrink :=
    ⟨⟨E.toShrink.s₀, fun i ↦ ⟨Iso.refl _, E.toShrink.w₀ i⟩⟩,
      ⟨E.fromShrink.s₀, fun i ↦
        ⟨eqToIso (Presieve.ofArrows_surj E.f _ i.2).choose_spec.1.symm, E.fromShrink.w₀ i⟩⟩⟩
  exact ⟨𝒱, h𝒱, PreZeroHypercover.tautologicallyEquivalent_trans E V.toPreZeroHypercover
    (𝒱.map B.inclusion) hshrink htaut⟩

/-- **Stacks 0EU0, part (1).** An arbitrary h covering of an object of a big h site is refined
by one of the site's own covering families.

The affine opens of the target are a Zariski covering, hence by part (3) tautologically
equivalent to a chosen family `G`.  Each member of `G` is isomorphic over the target to an
affine open, so the base change of the given family to it is an h covering of an affine
scheme; Stacks 0ETU refines that base change by a standard h covering, which part (2)
realizes inside the site.  The site's composition axiom assembles the realized families into
the required covering. -/
@[stacks 0EU0 "part (1)"]
public theorem exists_isCovering_refinement_of_isHCovering
    (B : BigHSite.{u}) (T : B.Schemes) (𝒰 : PreZeroHypercover.{v} (B.inclusion.obj T))
    (h𝒰 : IsHCovering 𝒰.X 𝒰.f) :
    ∃ 𝒱 : PreZeroHypercover.{u + 1} T,
      B.IsCovering ⟨T, 𝒱⟩ ∧ Nonempty ((𝒱.map B.inclusion).Hom 𝒰) := by
  classical
  let S := B.inclusion.obj T
  let O : S.OpenCover.{u + 1} :=
    { I₀ := ULift.{u + 1, u} (↑S.affineOpens : Type u)
      X i := i.down.1.toScheme
      f i := i.down.1.ι
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x ↦ ?_, fun i ↦ inferInstance⟩
        obtain ⟨V, hxV⟩ := TopologicalSpace.Opens.mem_iSup.mp
          (by rw [iSup_affineOpens_eq_top S]; trivial : x ∈ ⨆ V : (↑S.affineOpens : Type u), V.1)
        exact ⟨ULift.up V, ⟨⟨x, hxV⟩, rfl⟩⟩ }
  obtain ⟨G, hG, htaut⟩ := BigHSite.exists_isCovering_tautologicallyEquivalent_openCover B T O
  obtain ⟨β, hβ⟩ := htaut.2
  choose ε hε using hβ
  have hGaffine (j : G.I₀) : IsAffine (B.inclusion.obj (G.X j)) :=
    @IsAffine.of_isIso _ _ (ε j).hom (CategoryTheory.Iso.isIso_hom (ε j)) (β j).down.2
  have hrange (j : G.I₀) :
      Set.range (B.inclusion.map (G.f j)).base ⊆ ((β j).down.1 : Set S) := by
    have hfac : (ε j).hom ≫ (β j).down.1.ι = B.inclusion.map (G.f j) := hε j
    rintro x ⟨y, rfl⟩
    rw [← Scheme.Opens.range_ι (β j).down.1]
    refine ⟨(ε j).hom y, ?_⟩
    rw [← hfac]
    exact (Scheme.Hom.comp_apply _ _ y).symm
  have hpb (j : G.I₀) : IsHCovering
      (fun i ↦ pullback (𝒰.f i) (B.inclusion.map (G.f j)))
      (fun i ↦ pullback.snd (𝒰.f i) (B.inclusion.map (G.f j))) := by
    refine isHCovering_pullback_of_forall_exists_isAffineOpen h𝒰 _ fun U' _ ↦
      ⟨(β j).down.1, (β j).down.2, ?_⟩
    rintro x ⟨y, rfl⟩
    exact hrange j ⟨U'.ι.base y, by simp⟩
  have hstdref (j : G.I₀) :
      ∃ P : PreZeroHypercover.{u + 1} (B.inclusion.obj (G.X j)),
        @IsStandardHCovering _ (hGaffine j) _ P.X P.f ∧
          ∀ k, ∃ (i : 𝒰.I₀) (h : P.X k ⟶ 𝒰.X i),
            h ≫ 𝒰.f i = P.f k ≫ B.inclusion.map (G.f j) := by
    have : IsAffine (B.inclusion.obj (G.X j)) := hGaffine j
    obtain ⟨K, V, q, hstd, ⟨φ⟩⟩ :=
      exists_isStandardHCovering_refinement.{u, v, u + 1}
        (fun i ↦ pullback (𝒰.f i) (B.inclusion.map (G.f j)))
        (fun i ↦ pullback.snd (𝒰.f i) (B.inclusion.map (G.f j))) (hpb j)
    refine ⟨⟨K, V, q⟩, hstd, fun k ↦
      ⟨φ.s₀ k, φ.h₀ k ≫ pullback.fst (𝒰.f (φ.s₀ k)) (B.inclusion.map (G.f j)), ?_⟩⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, φ.w₀ k]
  choose P hP hPref using hstdref
  choose idx hom hcomm using fun j ↦ hPref j
  have hreal (j : G.I₀) : ∃ H : PreZeroHypercover.{u + 1} (G.X j),
      B.IsCovering ⟨G.X j, H⟩ ∧
        PreZeroHypercover.TautologicallyEquivalent (P j) (H.map B.inclusion) :=
    have := hGaffine j
    exists_isCovering_tautologicallyEquivalent_standardHCovering B (G.X j) (P j) (hP j)
  choose H hH htautH using hreal
  choose γ hγ using fun j ↦ (htautH j).2
  choose δ hδ using fun j ↦ hγ j
  refine ⟨G.bind fun j ↦ (H j).pushforward (eqToHom rfl),
    B.isSite.2.1 ⟨T, G⟩ hG (fun j ↦ ⟨G.X j, H j⟩) hH (fun _ ↦ rfl), ⟨?_⟩⟩
  refine ⟨fun s ↦ idx s.1 (γ s.1 s.2),
    fun s ↦ (δ s.1 s.2).hom ≫ hom s.1 (γ s.1 s.2), fun s ↦ ?_⟩
  have h1 : ((δ s.1 s.2).hom ≫ hom s.1 (γ s.1 s.2)) ≫ 𝒰.f (idx s.1 (γ s.1 s.2))
      = B.inclusion.map ((H s.1).f s.2) ≫ B.inclusion.map (G.f s.1) := by
    rw [Category.assoc, hcomm s.1 (γ s.1 s.2), ← Category.assoc, hδ s.1 s.2]
    rfl
  refine h1.trans ?_
  have h2 : ((H s.1).f s.2 ≫ eqToHom (rfl : G.X s.1 = G.X s.1)) ≫ G.f s.1
      = (H s.1).f s.2 ≫ G.f s.1 := by simp
  rw [← Functor.map_comp]
  exact congrArg B.inclusion.map h2.symm

end AlgebraicGeometry

end
