module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeSupport
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ProperRelativeCycles
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.ProperFinitePresentationRefinement
public import StacksCore.Tactic.StacksAttribute

/-!
# h descent for proper relative cycles

Let `S` be a locally Noetherian scheme, let `f : X ⟶ S` be locally of finite type, let `r ≥ 0`
and let `α` be a relative `r`-cycle on `X/S`. If `{g i : S i ⟶ S}` is an h covering, then `α` is
a proper relative cycle if and only if each base change `(g i)^*α` is a proper relative cycle.

Properness of a relative cycle says that its support is contained in a closed subset proper over
the base, and the support of a base change is the inverse image of the support. So the content of
the statement is purely geometric: for a subset `A ⊆ X`, being contained in a closed subset
proper over `S` is a condition local for the h topology on `S`. That geometric statement is
proved first and is what carries the work.

## Main results

* `AlgebraicGeometry.isProperOver_of_openCover` — properness of a closed subset over the base is
  local on the base for the Zariski topology.
* `AlgebraicGeometry.exists_isProperOver_of_isPullback` — properness of a subset transfers from
  one base change of `X/S` to a base change factoring through it.
* `AlgebraicGeometry.exists_isProperOver_of_isHCovering` — a subset of `X` is contained in a
  closed subset proper over `S` as soon as its inverse image in `X ×_S S i` is contained in a
  closed subset proper over `S i` for every member of an h covering `{S i ⟶ S}`.
* `Stacks.Chow.isProperRelativeCycle_iff_forall_baseChangeFamily` — **Stacks Project, Lemma
  0H63**.

## Implementation notes

The geometric descent statement is proved in three steps, mirroring the argument of the source.

Properness over the base is local on the base, so one reduces to `S` affine. The reduction base
changes the given h covering along an affine open `U ⟶ S`, which is legitimate because every
affine open of `U` is carried into the affine open `U` of `S`; this is the confined case of
Stacks 0ETY part (3) available in this development, and it is all that is needed here.

Over an affine base an h covering is refined by the affine opens of a single proper surjective
morphism `p : Y ⟶ S` of finite presentation (Stacks 0ETU). The inverse image of the subset in
`X ×_S Y` is then, open piece by open piece, contained in the inverse image of one of the given
closed subsets, hence its closure is proper over `Y`. Since `p` is proper, that closure is proper
over `S` as well, and its image in `X` under the projection — proper over `S` by Stacks 0CYQ and
containing the subset because the projection is surjective — is the closed subset asked for.

The passage from a base change of `X/S` to a base change factoring through it uses no fibre
product comparison isomorphisms: the factoring morphism is produced by the universal property
through `CategoryTheory.IsPullback.of_right'`, which simultaneously gives that the resulting
square is cartesian, so Stacks 0CYP applies to it directly.

Neither the geometric statements nor properness of the support of a family of cycles involves the
locally Noetherian hypothesis on `S` or the valuative condition defining a relative cycle. The
Lemma is therefore stated for an arbitrary family of cycles on the fibres, with the locally
Noetherian hypothesis kept as in the source.

## References

* [Stacks Project, Lemma 0H63](https://stacks.math.columbia.edu/tag/0H63)
* [Stacks Project, Lemma 0H62](https://stacks.math.columbia.edu/tag/0H62)
* [Stacks Project, Lemma 0H4V](https://stacks.math.columbia.edu/tag/0H4V)
* [Stacks Project, Lemma 0CYQ](https://stacks.math.columbia.edu/tag/0CYQ)
* [Stacks Project, Lemma 0ETU](https://stacks.math.columbia.edu/tag/0ETU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

/-! ### Subsets contained in a closed subset proper over the base -/

/-- A subset of `X` is contained in a closed subset of `X` proper over `S` exactly when its
closure is proper over `S`. -/
theorem isProperOver_closure_iff_exists_isProperOver {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (A : Set X) :
    IsProperOver f (Closeds.closure A) ↔
      ∃ W : Closeds X, A ⊆ (W : Set X) ∧ IsProperOver f W := by
  refine ⟨fun h ↦ ⟨Closeds.closure A, subset_closure, h⟩, ?_⟩
  rintro ⟨W, hAW, hW⟩
  exact isProperOver_of_le f (closure_minimal hAW W.isClosed) hW

/-- Properness of a closed subset over the base is local on the base: if the inverse image of
`Z ⊆ X` in `X ×_S U` is proper over `U` for every member `U` of an open cover of `S`, then `Z` is
proper over `S`. -/
theorem isProperOver_of_openCover {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (𝒰 : S.OpenCover) (Z : Closeds X)
    (hZ : ∀ i, IsProperOver (pullback.snd f (𝒰.f i))
      (Z.preimage (pullback.fst f (𝒰.f i)).continuous)) :
    IsProperOver f Z := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  change IsProper (I.subschemeι ≫ f)
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsProper) 𝒰).2 fun i ↦ ?_
  let q := pullback.fst f (𝒰.f i)
  let f' := pullback.snd f (𝒰.f i)
  have hsupport : (I.comap q).support = Z.preimage q.continuous := by
    rw [Scheme.IdealSheafData.support_comap]
    exact congrArg (fun W : Closeds X ↦ W.preimage q.continuous)
      (Closeds.ext (Scheme.IdealSheafData.coe_support_vanishingIdeal Z))
  have hproper : IsProper ((I.comap q).subschemeι ≫ f') :=
    (exists_isProper_iff_forall_isProper f' (Z.preimage q.continuous)).1
      ((isProperOver_iff_exists_isProper f' (Z.preimage q.continuous)).1 (hZ i))
      (I.comap q) hsupport
  have hcomap : IsPullback (I.comap q).subschemeι
      ((I.comapIso q).hom ≫ pullback.snd q I.subschemeι) q I.subschemeι := by
    refine IsPullback.of_iso_pullback ?_ (I.comapIso q) (by simp) rfl
    exact ⟨by simp⟩
  have hpaste : IsPullback ((I.comapIso q).hom ≫ pullback.snd q I.subschemeι)
      ((I.comap q).subschemeι ≫ f') (I.subschemeι ≫ f) (𝒰.f i) := by
    simpa only [Category.assoc] using
      hcomap.flip.paste_vert (IsPullback.of_hasPullback f (𝒰.f i))
  change IsProper (pullback.snd (I.subschemeι ≫ f) (𝒰.f i))
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsProper)
    hpaste.isoPullback.hom (pullback.snd (I.subschemeι ≫ f) (𝒰.f i))).1
      (by rwa [hpaste.isoPullback_hom_snd])

/-- Properness of a subset transfers from one base change of `X/S` to a base change factoring
through it: if `X' ⟶ V` is the base change of `f : X ⟶ S` along a morphism `V ⟶ S` which factors
as `V ⟶ T ⟶ S`, and the inverse image of `A ⊆ X` in `X ×_S T` is contained in a closed subset
proper over `T`, then the inverse image of `A` in `X'` is contained in a closed subset proper
over `V`. -/
theorem exists_isProperOver_of_isPullback {X X' S T V : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : T ⟶ S) (π : X' ⟶ X) (f' : X' ⟶ V) [LocallyOfFiniteType f']
    (h : V ⟶ T) (hsq : IsPullback π f' f (h ≫ g)) (A : Set X)
    (hA : ∃ W : Closeds (pullback f g : Scheme.{u}),
      pullback.fst f g ⁻¹' A ⊆ (W : Set (pullback f g : Scheme.{u})) ∧
      IsProperOver (pullback.snd f g) W) :
    ∃ W : Closeds X', π ⁻¹' A ⊆ (W : Set X') ∧ IsProperOver f' W := by
  obtain ⟨W, hAW, hW⟩ := hA
  obtain ⟨θ, hθsq, hθfst⟩ : ∃ θ : X' ⟶ pullback f g,
      IsPullback θ f' (pullback.snd f g) h ∧ θ ≫ pullback.fst f g = π :=
    ⟨_, IsPullback.of_right' hsq (IsPullback.of_hasPullback f g),
      (IsPullback.of_hasPullback f g).lift_fst _ _ _⟩
  refine ⟨W.preimage θ.continuous, fun x hx ↦ ?_,
    isProperOver_preimage_baseChange θ f' (pullback.snd f g) h hθsq W hW⟩
  have hpt : pullback.fst f g (θ x) = π x := by
    simpa using congrArg (fun m : X' ⟶ X ↦ m x) hθfst
  exact hAW (Set.mem_preimage.2 (hpt ▸ hx))

/-- Transfer of properness along a morphism `j : V ⟶ Y` over `S` which factors through `g`. -/
private theorem exists_isProperOver_pullback_snd {X S T Y V : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : T ⟶ S) (p : Y ⟶ S) (h : V ⟶ T) (j : V ⟶ Y) (hj : h ≫ g = j ≫ p)
    (A : Set X)
    (hA : ∃ W : Closeds (pullback f g : Scheme.{u}),
      pullback.fst f g ⁻¹' A ⊆ (W : Set (pullback f g : Scheme.{u})) ∧
      IsProperOver (pullback.snd f g) W) :
    ∃ W : Closeds (pullback (pullback.snd f p) j : Scheme.{u}),
      (pullback.fst (pullback.snd f p) j ≫ pullback.fst f p) ⁻¹' A ⊆ (W : Set _) ∧
      IsProperOver (pullback.snd (pullback.snd f p) j) W := by
  refine exists_isProperOver_of_isPullback f g _ _ h ?_ A hA
  rw [hj]
  exact (IsPullback.of_hasPullback _ j).paste_horiz (IsPullback.of_hasPullback f p)

/-- If `a` is an open embedding and `W` is closed with `a ⁻¹' A ⊆ W`, then `a ⁻¹' closure A ⊆ W`. -/
private theorem preimage_closure_subset_of_preimage_subset {U X : Type*} [TopologicalSpace U]
    [TopologicalSpace X] {a : U → X} (ha : Topology.IsOpenEmbedding a) {A : Set X} {W : Set U}
    (hW : IsClosed W) (h : a ⁻¹' A ⊆ W) : a ⁻¹' closure A ⊆ W :=
  fun _ hx ↦ closure_minimal h hW (ha.isOpenMap.preimage_closure_subset_closure_preimage hx)

/-- The affine case of h descent for subsets contained in a closed subset proper over the base.

An h covering of an affine scheme `S` is refined by the affine opens of a single proper surjective
morphism `p : Y ⟶ S` of finite presentation, and properness over `Y` of the closure of the
inverse image of `A` in `X ×_S Y` can be checked on those opens. -/
private theorem exists_isProperOver_of_isHCovering_of_isAffine {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsAffine S] (A : Set X) {I : Type v} (S' : I → Scheme.{u})
    (g : ∀ i, S' i ⟶ S) (hg : IsHCovering S' g)
    (hA : ∀ i, ∃ W : Closeds (pullback f (g i) : Scheme.{u}),
      pullback.fst f (g i) ⁻¹' A ⊆ (W : Set (pullback f (g i) : Scheme.{u})) ∧
        IsProperOver (pullback.snd f (g i)) W) :
    ∃ W : Closeds X, A ⊆ (W : Set X) ∧ IsProperOver f W := by
  classical
  obtain ⟨J, Y, p, V, j, hJ, hp, hpsurj, hpfp, hVaff, hjopen, hjcover, hfactor⟩ :=
    exists_finitePresentation_proper_refinement_of_isHCovering S' g hg
  have : IsProper p := hp
  have : Surjective p := hpsurj
  let fY := pullback.snd f p
  let qY := pullback.fst f p
  have hsq : IsPullback qY fY f p := IsPullback.of_hasPullback f p
  have : IsProper qY := MorphismProperty.of_isPullback hsq.flip hp
  have : Surjective qY := MorphismProperty.of_isPullback hsq.flip hpsurj
  let WY : Closeds (pullback f p : Scheme.{u}) := Closeds.closure (qY ⁻¹' A)
  have hcovers : ∀ y : Y, ∃ (k : J) (z : V k), (j k) z = y := fun y ↦ by
    simpa only [Set.mem_iUnion, Set.mem_range] using Set.eq_univ_iff_forall.1 hjcover y
  have hWY : IsProperOver fY WY := by
    refine isProperOver_of_openCover fY (Scheme.Cover.mkOfCovers J V j hcovers hjopen) WY
      fun k ↦ ?_
    obtain ⟨i₀, hk, hhk⟩ := hfactor k
    have : IsOpenImmersion (j k) := hjopen k
    have hqk : IsOpenImmersion (pullback.fst fY (j k)) :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback fY (j k)).flip inferInstance
    obtain ⟨Z, hZsub, hZ⟩ := exists_isProperOver_pullback_snd f (g i₀) p hk (j k) hhk A (hA i₀)
    exact isProperOver_of_le (pullback.snd fY (j k))
      (preimage_closure_subset_of_preimage_subset (pullback.fst fY (j k)).isOpenEmbedding
        Z.isClosed hZsub) hZ
  have hcomp : IsProperOver (qY ≫ f) WY := by
    have h₂ : IsProper ((Scheme.IdealSheafData.vanishingIdeal WY).subschemeι ≫ fY ≫ p) := by
      rw [← Category.assoc]
      exact MorphismProperty.IsStableUnderComposition.comp_mem _ _ hWY hp
    rwa [← hsq.w] at h₂
  have : LocallyOfFiniteType (qY ≫ f) := by
    rw [hsq.w]
    infer_instance
  refine ⟨qY.closedImage WY, fun x hx ↦ ?_, isProperOver_closedImage qY f WY hcomp⟩
  obtain ⟨z, hz⟩ := qY.surjective x
  exact ⟨z, subset_closure (Set.mem_preimage.2 (hz ▸ hx)), hz⟩

/-- **The geometric content of Stacks Project, Lemma 0H63.** Being contained in a closed subset
proper over the base is a condition local for the h topology on the base: if `{g i : S i ⟶ S}` is
an h covering and the inverse image of `A ⊆ X` in `X ×_S S i` is contained in a closed subset
proper over `S i` for every `i`, then `A` is contained in a closed subset of `X` proper over
`S`. -/
theorem exists_isProperOver_of_isHCovering {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (A : Set X) {I : Type v} (S' : I → Scheme.{u}) (g : ∀ i, S' i ⟶ S)
    (hg : IsHCovering S' g)
    (hA : ∀ i, ∃ W : Closeds (pullback f (g i) : Scheme.{u}),
      pullback.fst f (g i) ⁻¹' A ⊆ (W : Set (pullback f (g i) : Scheme.{u})) ∧
        IsProperOver (pullback.snd f (g i)) W) :
    ∃ W : Closeds X, A ⊆ (W : Set X) ∧ IsProperOver f W := by
  rw [← isProperOver_closure_iff_exists_isProperOver]
  refine isProperOver_of_openCover f S.affineCover (Closeds.closure A) fun i ↦ ?_
  let u := S.affineCover.f i
  let a := pullback.fst f u
  let fU := pullback.snd f u
  have hsq : IsPullback a fU f u := IsPullback.of_hasPullback f u
  have : IsOpenImmersion a := MorphismProperty.of_isPullback hsq.flip inferInstance
  have hgU : IsHCovering (fun k ↦ pullback (g k) u) (fun k ↦ pullback.snd (g k) u) :=
    isHCovering_pullback_of_forall_exists_isAffineOpen hg u fun U' _ ↦
      ⟨u.opensRange, isAffineOpen_opensRange u, by
        rintro x ⟨y, rfl⟩
        exact ⟨U'.ι y, rfl⟩⟩
  have hAU : ∀ k, ∃ W : Closeds (pullback fU (pullback.snd (g k) u) : Scheme.{u}),
      pullback.fst fU (pullback.snd (g k) u) ⁻¹' (a ⁻¹' A) ⊆
          (W : Set (pullback fU (pullback.snd (g k) u) : Scheme.{u})) ∧
        IsProperOver (pullback.snd fU (pullback.snd (g k) u)) W := fun k ↦
    exists_isProperOver_pullback_snd f (g k) u (pullback.fst (g k) u) (pullback.snd (g k) u)
      pullback.condition A (hA k)
  obtain ⟨WU, hWUsub, hWU⟩ := exists_isProperOver_of_isHCovering_of_isAffine fU (a ⁻¹' A)
    (fun k ↦ pullback (g k) u) (fun k ↦ pullback.snd (g k) u) hgU hAU
  exact isProperOver_of_le fU
    (preimage_closure_subset_of_preimage_subset a.isOpenEmbedding WU.isClosed hWUsub) hWU

end AlgebraicGeometry

namespace Stacks.Chow

/-! ### h descent for proper relative cycles -/

/-- **Stacks Project, Lemma 0H63.** Let `S` be locally Noetherian, let `f : X ⟶ S` be locally of
finite type and let `α` be a family of `r`-cycles on the fibres of `X/S`. Let `{g i : S i ⟶ S}`
be an h covering. Then `α` is a proper relative cycle if and only if each base change
`(g i)^*α` is a proper relative cycle.

Properness of a relative cycle is a condition on its support alone, so neither the valuative
condition defining a relative `r`-cycle nor any hypothesis on the members of the covering beyond
the h-covering condition enters. -/
@[stacks 0H63]
theorem isProperRelativeCycle_iff_forall_baseChangeFamily {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (r : ℕ) (α : FamilyOfCycles f r)
    {I : Type v} (S' : I → Scheme.{u}) (g : ∀ i, S' i ⟶ S) (hg : IsHCovering S' g) :
    IsProperRelativeCycle f r α ↔
      ∀ i, IsProperRelativeCycle (pullback.snd f (g i)) r (baseChangeFamily f (g i) r α) := by
  refine ⟨fun hα i ↦
    isProperRelativeCycle_baseChangeFamily_of_isProperRelativeCycle f r hα (g i), fun hα ↦ ?_⟩
  refine exists_isProperOver_of_isHCovering f (supportOfFamily f α) S' g hg fun i ↦ ?_
  obtain ⟨W, hW, hWproper⟩ := hα i
  exact ⟨W, by rwa [← supportOfFamily_baseChangeFamily f (g i) r α], hWproper⟩

end Stacks.Chow

end
