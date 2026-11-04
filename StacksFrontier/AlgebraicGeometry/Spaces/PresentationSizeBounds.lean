module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.Coverings
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.CoveringRefinesSieve
public import StacksFrontier.CategoryTheory.Sites.LocallySurjectiveBaseChange

/-!
# Size bounds for presentations of an algebraic space

A locally surjective map of presheaves on the big fppf site of `S` between two representable
presheaves is, on underlying schemes, refined by an fppf covering that factors through it; so
the target of such a map is no larger than its source. This file turns that observation into
the size bounds a presentation of an algebraic space by objects of a *smaller* big fppf site
needs: given a locally surjective map `h_U ⟶ F` from a representable presheaf to an algebraic
space, there is an étale atlas of `F` no larger than `U`, and the kernel pair of a presentation
is bounded by the diagonal and the lifted cover.

## Main results

* `CategoryTheory.Presheaf.isLocallySurjective_of_isPullback` — local surjectivity is stable
  under base change; proved in
  `StacksFrontier.CategoryTheory.Sites.LocallySurjectiveBaseChange` and used throughout here.
* `AlgebraicGeometry.Space.isLocallySurjective_yoneda_map_of_fppf` — a flat, surjective
  morphism of the site which is locally of finite presentation induces a locally surjective map
  of representable presheaves, and `AlgebraicGeometry.Space.surjective_of_isLocallySurjective`
  is the converse on underlying schemes.
* `AlgebraicGeometry.Space.size_le_of_isLocallySurjective` — the target of a locally surjective
  map of representable presheaves is no larger than its source.
* `AlgebraicGeometry.exists_bounded_etale_neighborhood` — a surjective étale morphism `p` to `U`
  together with a map `a` to `V` is dominated by a surjective étale `t : T ⟶ U` whose source,
  and whose image inside `V`, are both of size at most that of `U`.
* `AlgebraicGeometry.Space.exists_atlas_size_le` — an algebraic space with a locally surjective
  map from `h_U` has a surjective étale atlas whose source is of size at most that of `U`.
* `AlgebraicGeometry.Space.exists_bounded_fppf_lift` and
  `AlgebraicGeometry.Space.size_kernelPair_le` — the covering and the kernel-pair bounds.

## Implementation notes

The two size inputs are Stacks 0AHK (`AlgebraicGeometry.Scheme.size_le_of_fpqc_factorsThrough`)
and Stacks 0AHL (`AlgebraicGeometry.exists_fppf_refinement_schemeSize_le`); both are stated for
fpqc respectively fppf coverings of schemes, so the work here is to produce such a covering from
local surjectivity in the fppf topology of the site, and to cut it down to a quasi-compact piece
before the finite-type size bound `AlgebraicGeometry.Scheme.size_le_of_locallyOfFiniteType` is
applied.

`AlgebraicGeometry.exists_bounded_etale_neighborhood` is where the size of the *second* member
of a presentation is controlled: a quasi-compact piece of the étale cover is chosen over each
affine open of `U`, and its image in `V` is covered by finitely many affine opens, so that both
resulting coproducts are indexed by the affine opens of `U`.

## References

* [Stacks Project, Tag 0AHK](https://stacks.math.columbia.edu/tag/0AHK)
* [Stacks Project, Tag 0AHL](https://stacks.math.columbia.edu/tag/0AHL)
* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Cardinal TopologicalSpace Opposite

universe v u

namespace AlgebraicGeometry

/-- An fppf covering of a scheme is an fpqc covering in the sense of Stacks 03L7: its members
are flat, and each affine open of the target is a finite union of images of affine opens of the
members, because the members are open maps. -/
theorem isFpqcCovering_of_fppfCovering {T : Scheme.{u}} (E : FppfCovering.{v} T) :
    IsFpqcCovering E.X E.f := by
  refine ⟨E.flat, fun U hU => ?_⟩
  obtain ⟨n, a, V, hV, hcover⟩ := E.exists_finite_affineOpens_cover ⟨U, hU⟩
  refine ⟨n, a, V, hV, fun i => ?_, hcover.symm⟩
  rw [← hcover]
  exact fun x hx => Set.mem_iUnion.mpr ⟨i, hx⟩


/-- A finite union of compact opens is compact. -/
private theorem isCompact_iSup_opens {X : Scheme.{u}} {n : ℕ} (D : Fin n → X.Opens)
    (hD : ∀ i, IsCompact (D i : Set X)) : IsCompact ((⨆ i, D i : X.Opens) : Set X) := by
  simpa using isCompact_iUnion hD

/-- A size bound from a compact source. If `V` is quasi-compact, `p : W ⟶ U` is locally of
finite type, and some fppf covering of `V` factors through a map `f : W ⟶ V`, then
`V.size ≤ U.size`.

The covering is first replaced by one indexed by a finite family of affine opens of its members,
so that the part of `W` the covering factors through may be shrunk to a quasi-compact open; the
finite-type bound `AlgebraicGeometry.Scheme.size_le_of_locallyOfFiniteType` then applies. -/
theorem size_le_of_compact_of_fppf_factorsThrough {V W U : Scheme.{u}} [CompactSpace V]
    (p : W ⟶ U) [LocallyOfFiniteType p] (f : W ⟶ V) (E : FppfCovering V)
    (g : ∀ i, E.X i ⟶ W) (w : ∀ i, g i ≫ f = E.f i) : V.size ≤ U.size := by
  classical
  have hc : IsCompactOpenCovered (E.f ·) (Set.univ : Set V) :=
    .of_isOpenMap (fun i => (E.f i).continuous) E.isOpenMap
      (fun v _ => E.jointly_surjective v) isOpen_univ isCompact_univ
  obtain ⟨n, a, A, hA, hcover⟩ := hc.exists_mem_of_isBasis
    (fun i => (E.X i).isBasis_affineOpens) (fun _ _ hA => hA.isCompact)
  change (i : Fin n) → (E.X (a i)).Opens at A
  change ∀ i, IsAffineOpen (A i) at hA
  let K : Set W := ⋃ i : Fin n, (g (a i)) '' (A i : Set (E.X (a i)))
  have hK : IsCompact K := isCompact_iUnion fun i =>
    (hA i).isCompact.image (g (a i)).continuous
  obtain ⟨m, D, _, hKD⟩ := exists_affineOpens_cover_of_isCompact W K hK ⊤ (Set.subset_univ K)
  let O : W.Opens := ⨆ i, (D i).1
  have hO : IsCompact (O : Set W) := isCompact_iSup_opens _ fun i => (D i).2.isCompact
  have : CompactSpace O.toScheme := isCompact_iff_compactSpace.mp hO
  have hfactors (i : Fin n) : Set.range ((A i).ι ≫ g (a i)) ⊆ (O : Set W) := by
    rintro _ ⟨x, rfl⟩
    have hx : (g (a i)) x.1 ∈ K := Set.mem_iUnion.mpr ⟨i, x.1, x.2, rfl⟩
    show (g (a i)) ((A i).ι x) ∈ (O : Set W)
    rw [(A i).ι_apply x]
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hKD hx)
    exact (le_iSup (fun j => (D j).1) j) hj
  let lifts (i : Fin n) : (A i).toScheme ⟶ O.toScheme :=
    IsOpenImmersion.lift O.ι ((A i).ι ≫ g (a i)) (by simpa using hfactors i)
  let E₀ : FppfCovering V := {
    ι := Fin n
    X := fun i => (A i).toScheme
    f := fun i => (A i).ι ≫ E.f (a i)
    flat := fun i => by have := E.flat (a i); infer_instance
    lfp := fun i => by have := E.lfp (a i); infer_instance
    jointly_surjective := by
      intro x
      have hx : x ∈ ⋃ i, (E.f (a i)) '' (A i : Set (E.X (a i))) := by
        rw [hcover]; trivial
      obtain ⟨i, y, hy, hyx⟩ := Set.mem_iUnion.mp hx
      exact ⟨i, ⟨y, hy⟩, hyx⟩ }
  have hbound : V.size ≤ O.toScheme.size :=
    Scheme.size_le_of_fpqc_factorsThrough (O.ι ≫ f) E₀.X E₀.f
      (isFpqcCovering_of_fppfCovering E₀) (fun i => ⟨lifts i, by
        dsimp [E₀, lifts]
        rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, w]⟩)
  exact hbound.trans (Scheme.size_le_of_locallyOfFiniteType (O.ι ≫ p))

/-- A surjective étale morphism `p : W ⟶ U` together with a morphism `a : W ⟶ V` is dominated by
a bounded one: there are a surjective étale `t : T ⟶ U` factoring through `p`, an étale
`v : V₀ ⟶ V` and a map `b : T ⟶ V₀` over `a`, with `T.size ≤ U.size` and `V₀.size ≤ U.size`.

The hypothesis `hsize` is the bound on quasi-compact opens of `V` which
`AlgebraicGeometry.size_le_of_compact_of_fppf_factorsThrough` supplies in the intended
application. Both `T` and `V₀` are coproducts indexed by the affine opens of `U`, which is why
their size is controlled. -/
theorem exists_bounded_etale_neighborhood {W U V : Scheme.{u}} (p : W ⟶ U) (a : W ⟶ V)
    [Etale p] [Surjective p]
    (hsize : ∀ O : V.Opens, IsCompact (O : Set V) → O.toScheme.size ≤ U.size) :
    ∃ (T V₀ : Scheme.{u}) (t : T ⟶ U) (b : T ⟶ V₀) (v : V₀ ⟶ V) (w : T ⟶ W),
      Etale t ∧ Surjective t ∧ Etale v ∧ w ≫ p = t ∧
      b ≫ v = w ≫ a ∧ T.size ≤ U.size ∧ V₀.size ≤ U.size := by
  classical
  let E : FppfCovering.{0} U := ⟨PUnit, fun _ => W, fun _ => p,
    fun _ => inferInstance, fun _ => inferInstance,
    fun x => ⟨PUnit.unit, (Surjective.surj (f := p) x).choose,
      (Surjective.surj (f := p) x).choose_spec⟩⟩
  have hE (A : U.affineOpens) := E.exists_finite_affineOpens_cover A
  choose n k D hD hc using hE
  change (A : U.affineOpens) → Fin (n A) → W.Opens at D
  change ∀ A j, IsAffineOpen (D A j) at hD
  let L (A : U.affineOpens) : W.Opens := ⨆ j : Fin (n A), D A j
  have hL (A : U.affineOpens) : IsCompact (L A : Set W) :=
    isCompact_iSup_opens _ fun j => (hD A j).isCompact
  have hchoose (A : U.affineOpens) := exists_affineOpens_cover_of_isCompact V
    (a '' (L A : Set W)) ((hL A).image a.continuous) ⊤ (Set.subset_univ _)
  choose m O hO hcover using hchoose
  let N (A : U.affineOpens) : V.Opens := ⨆ j : Fin (m A), (O A j).1
  have hN (A : U.affineOpens) : IsCompact (N A : Set V) :=
    isCompact_iSup_opens _ fun j => (O A j).2.isCompact
  have hfac (A : U.affineOpens) : Set.range ((L A).ι ≫ a) ⊆ (N A : Set V) := by
    rintro _ ⟨x, rfl⟩
    have hx := hcover A (show a x.1 ∈ a '' (L A : Set W) from ⟨x.1, x.2, rfl⟩)
    show a x.1 ∈ (N A : Set V)
    simpa only [N, Opens.coe_iSup] using hx
  let b₀ (A : U.affineOpens) : (L A).toScheme ⟶ (N A).toScheme :=
    IsOpenImmersion.lift (N A).ι ((L A).ι ≫ a) (by simpa using hfac A)
  let T := ∐ (fun A : U.affineOpens => (L A).toScheme)
  let V₀ := ∐ (fun A : U.affineOpens => (N A).toScheme)
  let w : T ⟶ W := Sigma.desc (fun A => (L A).ι)
  let t : T ⟶ U := Sigma.desc (fun A => (L A).ι ≫ p)
  let v : V₀ ⟶ V := Sigma.desc (fun A => (N A).ι)
  let b : T ⟶ V₀ :=
    Sigma.desc (fun A => b₀ A ≫ Sigma.ι (fun A : U.affineOpens => (N A).toScheme) A)
  let : IsZariskiLocalAtSource (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u})
  have ht : Etale t :=
    IsZariskiLocalAtSource.sigmaDesc (P := @Etale.{u}) (fun A => by infer_instance)
  have hv : Etale v :=
    IsZariskiLocalAtSource.sigmaDesc (P := @Etale.{u}) (fun A => by infer_instance)
  have hs : Surjective t := by
    refine Surjective.sigmaDesc_of_union_range_eq_univ (Set.eq_univ_iff_forall.mpr fun x => ?_)
    obtain ⟨A, hx⟩ := Set.mem_iUnion.mp (show x ∈ ⋃ A : U.affineOpens, (A.1 : Set U) by
      simp only [← Opens.coe_iSup, iSup_affineOpens_eq_top, Opens.coe_top, Set.mem_univ])
    have hx' : x ∈ ⋃ j, p '' (D A j : Set W) := by
      show x ∈ ⋃ j, (E.f (k A j)) '' (D A j : Set (E.X (k A j)))
      rw [hc A]
      exact hx
    obtain ⟨j, y, hy, hyx⟩ := Set.mem_iUnion.mp hx'
    exact Set.mem_iUnion.mpr ⟨A, ⟨y, (le_iSup (D A) j) hy⟩, hyx⟩
  refine ⟨T, V₀, t, b, v, w, ht, hs, hv, ?_, ?_, ?_, ?_⟩
  · exact Sigma.hom_ext _ _ fun A => by simp [w, t]
  · exact Sigma.hom_ext _ _ fun A => by simp [b, w, v, b₀]
  · apply schemeSize_coproduct_le _ _ U.aleph0_le_size U.mk_affineOpens_le_size
    intro A
    have : CompactSpace (L A).toScheme := isCompact_iff_compactSpace.mp (hL A)
    exact Scheme.size_le_of_locallyOfFiniteType ((L A).ι ≫ p)
  · exact schemeSize_coproduct_le _ _ U.aleph0_le_size U.mk_affineOpens_le_size
      (fun A => hsize (N A) (hN A))

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The sieve generated by an fppf covering family of a big fppf site belongs to its
Grothendieck topology: the family is combinatorially equivalent to one of the site's chosen
bounded families, which generates the same sieve. -/
theorem generate_mem_of_isFppfCovering {X : B.Schemes} (E : PreZeroHypercover.{u + 1} X)
    (hE : IsFppfCovering ⟨X, E⟩) : Sieve.generate E.presieve₀ ∈ B.topology X := by
  obtain ⟨⟨Y, F⟩, hF, heq, hequiv⟩ := B.fppf_has_representative ⟨X, E⟩ hE
  cases heq
  rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hequiv]
  exact Precoverage.generate_mem_toGrothendieck (show F.presieve₀ ∈ B.precoverage X from
    ⟨F, rfl, hF⟩)

/-- A single flat, surjective morphism of the big fppf site of `S` which is locally of finite
presentation generates a covering sieve. -/
theorem singleton_mem_of_fppf {X Y : BigFppfOver B S hS} (f : X ⟶ Y)
    [Flat f.left.hom] [LocallyOfFinitePresentation f.left.hom] [Surjective f.left.hom] :
    Sieve.generate (Presieve.singleton f) ∈ BigFppfOver.topology B S hS Y := by
  rw [GrothendieckTopology.mem_over_iff, ← Presieve.ofArrows_pUnit.{u + 1},
    Sieve.overEquiv_ofArrows]
  apply generate_mem_of_isFppfCovering B (PreZeroHypercover.singleton f.left)
  rw [IsFppfCovering, Precoverage.mem_comap_iff]
  simp

/-- A flat, surjective morphism of the big fppf site of `S` which is locally of finite
presentation induces a locally surjective map of representable presheaves. -/
theorem isLocallySurjective_yoneda_map_of_fppf {X Y : BigFppfOver B S hS} (f : X ⟶ Y)
    [Flat f.left.hom] [LocallyOfFinitePresentation f.left.hom] [Surjective f.left.hom] :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (yoneda.map f) := by
  let J := BigFppfOver.topology B S hS
  refine ⟨fun {T} s => J.superset_covering ?_
    (J.pullback_stable s (singleton_mem_of_fppf B S hS f))⟩
  intro W a ha
  obtain ⟨V, b, c, ⟨⟩, hw⟩ := ha
  exact ⟨b, by simpa using hw⟩

/-- A locally surjective map of representable presheaves on the big fppf site of `S` is refined
by an fppf covering of the target whose members factor through it. -/
theorem exists_fppfCovering_of_isLocallySurjective {X Y : BigFppfOver B S hS} (f : X ⟶ Y)
    (hf : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (yoneda.map f)) :
    ∃ E : FppfCovering.{u + 1} Y.left.obj,
      ∀ j, ∃ a : E.X j ⟶ X.left.obj, a ≫ f.left.hom = E.f j := by
  have hcov := hf.imageSieve_mem (𝟙 Y)
  rw [GrothendieckTopology.mem_over_iff] at hcov
  obtain ⟨E, hE, hER⟩ := CategoryTheory.exists_covering_refining_sieve B.IsCovering B.precoverage
    (fun ⟨E, hEq, hE⟩ => ⟨E, hE, hEq⟩) B.coverings_isSite hcov
  have hEF := B.isFppfCovering_of_isCovering hE
  rw [IsFppfCovering, Precoverage.mem_comap_iff, PreZeroHypercover.presieve₀,
    Presieve.map_ofArrows, Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hEF
  refine ⟨⟨E.I₀, fun j => (E.X j).obj, fun j => (E.f j).hom,
    fun j => (hEF.2 j).1, fun j => (hEF.2 j).2, hEF.1⟩, ?_⟩
  intro j
  obtain ⟨a, ha⟩ := (Sieve.overEquiv_iff _ _).mp (hER _ _ ⟨j⟩)
  exact ⟨a.left.hom, congrArg (fun k => k.left.hom) ha⟩

/-- A locally surjective map of representable presheaves is surjective on underlying schemes. -/
theorem surjective_of_isLocallySurjective {X Y : BigFppfOver B S hS} (f : X ⟶ Y)
    (hf : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (yoneda.map f)) :
    Surjective f.left.hom := by
  obtain ⟨E, hE⟩ := exists_fppfCovering_of_isLocallySurjective B S hS f hf
  refine ⟨fun y => ?_⟩
  obtain ⟨j, x, rfl⟩ := E.jointly_surjective y
  obtain ⟨a, ha⟩ := hE j
  exact ⟨a x, by rw [← Scheme.Hom.comp_apply, ha]⟩

/-- The target of a locally surjective map of representable presheaves on the big fppf site of
`S` is no larger than its source. -/
theorem size_le_of_isLocallySurjective {X Y : BigFppfOver B S hS} (f : X ⟶ Y)
    (hf : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (yoneda.map f)) :
    Y.left.obj.size ≤ X.left.obj.size := by
  obtain ⟨E, hE⟩ := exists_fppfCovering_of_isLocallySurjective B S hS f hf
  exact Scheme.size_le_of_fpqc_factorsThrough f.left.hom E.X E.f
    (isFpqcCovering_of_fppfCovering E) hE

/-- The object of the big fppf site of `S` given by a scheme `T` of size at most that of `U`,
with structure map `t ≫ V.hom`. -/
private noncomputable def mkOver (U V : BigFppfOver B S hS) {T : Scheme.{u}}
    (t : T ⟶ V.left.obj) (h : T.size ≤ U.left.obj.size) : BigFppfOver B S hS :=
  Over.mk (Y := B.obj (h.trans_lt U.left.property)) (X := B.obj hS) ⟨t ≫ V.hom.hom⟩

/-- The morphism `mkOver U V t h ⟶ V` given by `t`. -/
private noncomputable def mkOverHom (U V : BigFppfOver B S hS) {T : Scheme.{u}}
    (t : T ⟶ V.left.obj) (h : T.size ≤ U.left.obj.size) : mkOver B S hS U V t h ⟶ V :=
  Over.homMk ⟨t⟩

/-- A scheme map `w` lifting `t` through `f : W ⟶ V` gives a morphism `mkOver U V t h ⟶ W`. -/
private noncomputable def mkOverLift (U : BigFppfOver B S hS) {V W : BigFppfOver B S hS}
    (f : W ⟶ V) {T : Scheme.{u}} (t : T ⟶ V.left.obj) (h : T.size ≤ U.left.obj.size)
    (w : T ⟶ W.left.obj) (hw : w ≫ f.left.hom = t) : mkOver B S hS U V t h ⟶ W :=
  Over.homMk ⟨w⟩ (by
    apply ObjectProperty.hom_ext
    change w ≫ W.hom.hom = t ≫ V.hom.hom
    rw [← hw, Category.assoc]
    exact congrArg (w ≫ ·) (congrArg InducedCategory.Hom.hom (Over.w f)).symm)

private theorem mkOverLift_comp (U : BigFppfOver B S hS) {V W : BigFppfOver B S hS}
    (f : W ⟶ V) {T : Scheme.{u}} (t : T ⟶ V.left.obj) (h : T.size ≤ U.left.obj.size)
    (w : T ⟶ W.left.obj) (hw : w ≫ f.left.hom = t) :
    mkOverLift B S hS U f t h w hw ≫ f = mkOverHom B S hS U V t h :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ hw)

/-- **Stacks 04W1, the size of an atlas.** An algebraic space over `S` which receives a locally
surjective map from a representable presheaf `h_U` has a surjective étale atlas whose source is
of size at most that of `U`.

The atlas is produced from an arbitrary one by base change along the given map and then by
`AlgebraicGeometry.exists_bounded_etale_neighborhood`, whose compact-open size hypothesis is
discharged by `AlgebraicGeometry.size_le_of_compact_of_fppf_factorsThrough`. -/
theorem exists_atlas_size_le {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) {U : BigFppfOver B S hS} (f : yoneda.obj U ⟶ F)
    (hf : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f) :
    ∃ (V : BigFppfOver B S hS) (q : yoneda.obj V ⟶ F),
      V.left.obj.size ≤ U.left.obj.size ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) q ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) q := by
  let J := BigFppfOver.topology B S hS
  let A := BigFppfOver.toScheme B S hS
  obtain ⟨V, q, hqs, hqe⟩ := hF.exists_atlas
  let W := hqe.rep.pullback f
  let a : W ⟶ V := hqe.rep.fst' f
  let p : W ⟶ U := hqe.rep.snd f
  have hw : IsPullback (yoneda.map a) (yoneda.map p) q f := hqe.rep.isPullback' f
  have hep : Etale p.left.hom := hqe.property f (yoneda.map a) p hw
  have hsp : Surjective p.left.hom := hqs.property f (yoneda.map a) p hw
  have ha : Presheaf.IsLocallySurjective J (yoneda.map a) :=
    Presheaf.isLocallySurjective_of_isPullback J hw (hf := hf)
  have hsize (O : V.left.obj.Opens) (hO : IsCompact (O : Set V.left.obj)) :
      O.toScheme.size ≤ U.left.obj.size := by
    let O' : BigFppfOver B S hS :=
      Over.mk (Y := B.obj ((Scheme.size_coe_opens_le _ O).trans_lt V.left.property))
        (X := B.obj hS) ⟨O.ι ≫ V.hom.hom⟩
    let o : O' ⟶ V := Over.homMk ⟨O.ι⟩
    let P := pullback a o
    let r : P ⟶ W := pullback.fst a o
    let s : P ⟶ O' := pullback.snd a o
    have hpb : IsPullback (A.map r) (A.map s) (A.map a) (A.map o) :=
      (IsPullback.of_hasPullback a o).map A
    have : IsOpenImmersion (A.map o) := inferInstanceAs (IsOpenImmersion O.ι)
    have : IsOpenImmersion (A.map r) := MorphismProperty.of_isPullback hpb.flip ‹_›
    have hs : Presheaf.IsLocallySurjective J (yoneda.map s) :=
      Presheaf.isLocallySurjective_of_isPullback J
        (((IsPullback.of_hasPullback a o).map yoneda).flip) (hf := ha)
    obtain ⟨E, hE⟩ := exists_fppfCovering_of_isLocallySurjective B S hS s hs
    choose g hg using hE
    have : CompactSpace O.toScheme := isCompact_iff_compactSpace.mp hO
    exact size_le_of_compact_of_fppf_factorsThrough (A.map r ≫ p.left.hom) s.left.hom E g hg
  have : Etale p.left.hom := hep
  have : Surjective p.left.hom := hsp
  obtain ⟨T, V₀, t, b, v, w, ht, hts, hv, hwp, hbv, hT, hV⟩ :=
    exists_bounded_etale_neighborhood p.left.hom a.left.hom hsize
  let T' := mkOver B S hS U U t hT
  let V' := mkOver B S hS U V v hV
  let t' := mkOverHom B S hS U U t hT
  let v' := mkOverHom B S hS U V v hV
  let w' := mkOverLift B S hS U p t hT w hwp
  let b' : T' ⟶ V' := Over.homMk ⟨b⟩ (by
    apply ObjectProperty.hom_ext
    show b ≫ v ≫ V.hom.hom = t ≫ U.hom.hom
    rw [← Category.assoc, hbv, Category.assoc,
      show a.left.hom ≫ V.hom.hom = W.hom.hom from congrArg InducedCategory.Hom.hom (Over.w a)]
    exact congrArg InducedCategory.Hom.hom (Over.w w'))
  have hw'p : w' ≫ p = t' := mkOverLift_comp B S hS U p t hT w hwp
  have hb'v : b' ≫ v' = w' ≫ a := Over.OverMorphism.ext (ObjectProperty.hom_ext _ hbv)
  let q' := yoneda.map v' ≫ q
  have hqe' := etale_comp_of_scheme B S hS v' q hv hqe
  have hfac : yoneda.map b' ≫ q' = yoneda.map t' ≫ f := by
    dsimp [q']
    rw [← Category.assoc, ← yoneda.map_comp, hb'v, yoneda.map_comp, Category.assoc, hw.w,
      ← Category.assoc, ← yoneda.map_comp, hw'p]
  have hq' : Presheaf.IsLocallySurjective J q' := by
    have : Etale t'.left.hom := ht
    have : Surjective t'.left.hom := hts
    have := isLocallySurjective_yoneda_map_of_fppf B S hS t'
    exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac
  exact ⟨V', q', hV, presheaf_surjective_of_isLocallySurjective B S hS hqe'.rep hq', hqe'⟩

/-- **Stacks 04W1, the size of a covering.** A locally surjective morphism `f : W ⟶ V` of the
big fppf site of `S` is dominated by one whose source is of size at most that of `V`: the
fppf refinement of Stacks 0AHL, assembled into a single morphism of the site. -/
theorem exists_bounded_fppf_lift {W V : BigFppfOver B S hS} (f : W ⟶ V)
    (hf : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (yoneda.map f)) :
    ∃ (T : BigFppfOver B S hS) (t : T ⟶ V) (w : T ⟶ W),
      w ≫ f = t ∧ T.left.obj.size ≤ V.left.obj.size ∧
      Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (yoneda.map t) := by
  classical
  obtain ⟨C, hC⟩ := exists_fppfCovering_of_isLocallySurjective B S hS f hf
  obtain ⟨E, hEC, hsize⟩ := exists_fppf_refinement_schemeSize_le V.left.obj C
  choose j a ha using hEC
  choose b hb using hC
  let t := Sigma.desc E.f
  let w := Sigma.desc (fun i => a i ≫ b (j i))
  have hw : w ≫ f.left.hom = t := Sigma.hom_ext _ _ fun i => by simp [w, t, hb, ha]
  let : IsZariskiLocalAtSource (@Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat.{u})
  let : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation.{u})
  have htflat : Flat t := IsZariskiLocalAtSource.sigmaDesc E.flat
  have htlfp : LocallyOfFinitePresentation t := IsZariskiLocalAtSource.sigmaDesc E.lfp
  have hts : Surjective t := Surjective.sigmaDesc_of_union_range_eq_univ
    (Set.eq_univ_iff_forall.mpr (fun x => Set.mem_iUnion.mpr (E.jointly_surjective x)))
  let T := mkOver B S hS V V t hsize
  let t' := mkOverHom B S hS V V t hsize
  refine ⟨T, t', mkOverLift B S hS V f t hsize w hw, mkOverLift_comp B S hS V f t hsize w hw,
    hsize, ?_⟩
  have : Flat t'.left.hom := htflat
  have : LocallyOfFinitePresentation t'.left.hom := htlfp
  have : Surjective t'.left.hom := hts
  exact isLocallySurjective_yoneda_map_of_fppf B S hS t'

/-- Base change of a kernel pair. If `R` is the kernel pair of `f : h_U ⟶ F` and `a : T ⟶ U` is
any morphism, then the iterated fibre product displayed below is the kernel pair of
`h_a ≫ f`. -/
theorem isPullback_baseChange_kernelPair {C : Type*} [Category.{u} C] [HasPullbacks C]
    {F : Cᵒᵖ ⥤ Type u} {R U T : C} {s t : R ⟶ U} {f : yoneda.obj U ⟶ F}
    (hR : IsPullback (yoneda.map s) (yoneda.map t) f f) (a : T ⟶ U) :
    IsPullback (yoneda.map (pullback.fst (pullback.fst t a ≫ s) a ≫ pullback.snd t a))
      (yoneda.map (pullback.snd (pullback.fst t a ≫ s) a))
      (yoneda.map a ≫ f) (yoneda.map a ≫ f) := by
  have h₁ := ((IsPullback.of_hasPullback t a).map yoneda).paste_horiz hR
  simp only [← yoneda.map_comp] at h₁
  have h₂ := ((IsPullback.of_hasPullback (pullback.fst t a ≫ s) a).map yoneda).paste_horiz h₁.flip
  simpa only [← yoneda.map_comp] using h₂

/-- The underlying scheme of a fibre product in the big fppf site of `S` is no larger than the
larger of the two sources. -/
theorem size_pullback_le {X Y Z : BigFppfOver B S hS} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullback f g).left.obj.size ≤ max X.left.obj.size Y.left.obj.size := by
  let A := BigFppfOver.toScheme B S hS
  have : PreservesLimitsOfShape WalkingCospan A := by
    dsimp only [A, BigFppfOver.toScheme]
    infer_instance
  have hpb := (IsPullback.of_hasPullback f g).map A
  show (A.obj (pullback f g)).size ≤ _
  rw [Scheme.size_congr hpb.isoPullback]
  exact Scheme.size_pullback_le _ _

/-- **Stacks 04W1, the size of a kernel pair.** Let `D` be the kernel pair of `f : h_U ⟶ F` and
`Q` the kernel pair of `g : h_V ⟶ F`. If a morphism `t : T ⟶ V` with `h_t` locally surjective
sits over a morphism `a : T ⟶ U`, then `Q` is no larger than the larger of `D` and `T`. -/
theorem size_kernelPair_le {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {D U Q V T : BigFppfOver B S hS} {s d : D ⟶ U} {r q : Q ⟶ V}
    {f : yoneda.obj U ⟶ F} {g : yoneda.obj V ⟶ F}
    (hD : IsPullback (yoneda.map s) (yoneda.map d) f f)
    (hQ : IsPullback (yoneda.map r) (yoneda.map q) g g)
    (a : T ⟶ U) (t : T ⟶ V) (hw : yoneda.map a ≫ f = yoneda.map t ≫ g)
    (ht : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (yoneda.map t)) :
    Q.left.obj.size ≤ max D.left.obj.size T.left.obj.size := by
  let J := BigFppfOver.topology B S hS
  let cD := pullback.fst d a ≫ s
  let cQ := pullback.fst q t ≫ r
  let P := pullback cD a
  let P' := pullback cQ t
  have hP := isPullback_baseChange_kernelPair hD a
  have hP' := isPullback_baseChange_kernelPair hQ t
  rw [hw] at hP
  let e : P ≅ P' := yoneda.preimageIso (hP.isoPullback ≪≫ hP'.isoPullback.symm)
  have hbc {X : BigFppfOver B S hS} (u : X ⟶ V) :
      Presheaf.IsLocallySurjective J (yoneda.map (pullback.fst u t)) :=
    Presheaf.isLocallySurjective_of_isPullback J
      ((IsPullback.of_hasPullback u t).map yoneda) (hf := ht)
  have hs : Presheaf.IsLocallySurjective J
      (yoneda.map (pullback.fst cQ t ≫ pullback.fst q t)) := by
    rw [yoneda.map_comp]
    let := hbc q
    let := hbc cQ
    infer_instance
  have hsize := size_le_of_isLocallySurjective B S hS _ hs
  have hsizeP : P.left.obj.size ≤ max D.left.obj.size T.left.obj.size :=
    (size_pullback_le B S hS cD a).trans (max_le (size_pullback_le B S hS d a) (le_max_right _ _))
  have he : P.left.obj.size = P'.left.obj.size :=
    Scheme.size_congr ((BigFppfOver.toScheme B S hS).mapIso e)
  exact hsize.trans (he ▸ hsizeP)

end Space

end AlgebraicGeometry

end
