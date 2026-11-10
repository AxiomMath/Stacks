module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupsAtClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.SubfunctorSectionLifting

/-!
# The top of a tower of blowings up is a modification, and the bottom of a tower peels off

Let `S` be a scheme, let `X` be an algebraic space over `S` and let `T ⊆ |X|` be a set of
points.  A tower

`Zₘ ⟶ Zₘ₋₁ ⟶ … ⟶ Z₁ ⟶ Z₀ = X`

of blowings up at closed points all of whose centres lie over `T` — the datum
`AlgebraicGeometry.Space.BlowupTower` with
`AlgebraicGeometry.Space.BlowupTower.CentersOver` — is an isomorphism over any subspace of `X`
whose points avoid `T`, because a blowing up at a closed point is an isomorphism away from that
point (Stacks 085T, part (1)).  Taking `T = {x₁, …, xₙ}` and the subspace to be
`X ∖ {x₁, …, xₙ}`, the top of such a tower is an object of the category `C_{X, {x₁, …, xₙ}}`
of Stacks 0BHA: this is the statement that lets the functor `F` of Stacks 0BHA be applied to a
tower, and hence the statement without which the fullness of `F` cannot be used on the two
sides of Stacks 0BHF.

`AlgebraicGeometry.Space.BlowupTower.step` adds a blowing up on *top* of a tower, so case
analysis on a tower peels the top step.  The induction in the "if" direction of Stacks 0BHF
peels the *bottom* step instead: it writes a tower of length `m + 1` over `X` as one blowing up
`X₁ ⟶ X` at a closed point of `X` followed by a tower of length `m` over `X₁`.  That
decomposition is the second half of this file, with the compatibility of
`AlgebraicGeometry.Space.BlowupTower.proj` and of
`AlgebraicGeometry.Space.BlowupTower.CentersOver` proved explicitly: the centres of the whole
tower lie over `T` exactly when the peeled bottom centre does and the centres of the remaining
tower lie over the inverse image of `T`.

## Main results

* `AlgebraicGeometry.Space.isIso_pullback_snd_of_isBlowupAtClosedPoint`: a blowing up at a
  closed point is an isomorphism over any subspace of the base whose points avoid that point.
* `AlgebraicGeometry.Space.BlowupTower.isIso_pullback_snd_proj`: a tower of blowings up with
  centres over `T` is an isomorphism over any subspace of the base whose points avoid `T`.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.isModification_proj_of_centersOver` and
  `AlgebraicGeometry.Space.ClosedPointNeighborhoods.isModification_of_blowupFactorization`: the
  top of a tower over `X` with centres over `{x₁, …, xₙ}`, and the source of a morphism factored
  by such a tower, are objects of `C_{X, {x₁, …, xₙ}}`.
* `AlgebraicGeometry.Space.BlowupTower.exists_bottom_step` and
  `AlgebraicGeometry.Space.BlowupFactorization.exists_bottom_step`: the bottom-peeling
  decomposition, for a tower and for a factorization.
* `AlgebraicGeometry.Space.BlowupTower.exists_isBlowupAtClosedPoint_of_length_eq_one`: a tower
  of length one is a single blowing up at a closed point, followed by the identification of the
  bottom of the tower with the base.
* `AlgebraicGeometry.Space.BlowupTower.rebase`: transport of a tower along an isomorphism of its
  base, with `AlgebraicGeometry.Space.BlowupTower.proj_rebase`,
  `AlgebraicGeometry.Space.BlowupTower.length_rebase` and
  `AlgebraicGeometry.Space.BlowupTower.centersOver_rebase`.
* `AlgebraicGeometry.Space.isClosed_singleton_pointsMap_of_iso`: a closed point stays closed
  under an isomorphism, which is what lets a centre be carried across the identification a
  bottom peel produces.
* `AlgebraicGeometry.Space.IsBlowupAtClosedPoint.exists_iso`: any two blowings up at the same
  closed point are isomorphic over the base.

## Implementation notes

### Being an isomorphism over a subspace

`AlgebraicGeometry.Space.IsModification` records "is an isomorphism over `W₀`" as
`CategoryTheory.Limits.pullback.snd` of the structure morphism along the inclusion of `W₀` being
invertible, whereas Stacks 085T, part (1) is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupIsomorphismOffCentre.lean` for
`CategoryTheory.Subfunctor.fromPreimage`, the inclusion-indexed model of the same base change.
`AlgebraicGeometry.Space.isIso_pullback_snd_of_isIso_fromPreimage` passes between them along the
cartesian square of Stacks 083Q, and
`AlgebraicGeometry.Space.isIso_pullback_snd_comp_left` is the composition rule: a composite is
an isomorphism over `W₀` as soon as the lower morphism is and the upper one is an isomorphism
over the inverse image of `W₀`.  Both are needed because a tower is a composite of blowings up
and the subspace over which it is to be an isomorphism lives at the bottom.

Openness of the subspace is never used: what the argument consumes is only that the points of
the subspace avoid the centres, through
`AlgebraicGeometry.Space.le_of_range_pointsMap_ι_subset`, which needs openness of the *open
complement of the centre* and not of the given subspace.  The statements are therefore made for
an arbitrary subfunctor.

### Why the bottom step carries an identification of the base

A tower is an inductive type whose base case carries an isomorphism `Z₀ ≅ X` rather than an
equality, so the bottom blowing up of a tower over `X` is literally a blowing up of `Z₀` at a
closed point of `Z₀`, not of `X` at a closed point of `X`.  Rather than transport the universal
property of Stacks 085U along `Z₀ ≅ X` — which would mean transporting the reduced closed
subspace of Stacks 03IQ, the effective Cartier condition of Stacks 083Y and terminality in the
category `𝒞` of Stacks 085U, all for a statement that no consumer needs in that form — the
decomposition is stated with the length-one tower `u : BlowupTower B S hS X X₁` as the bottom
step, and
`AlgebraicGeometry.Space.BlowupTower.exists_isBlowupAtClosedPoint_of_length_eq_one` exhibits the
blowing up and the identification `Z₀ ≅ X` inside it.  The same device handles the
identifications the induction produces downstream:
`AlgebraicGeometry.Space.BlowupTower.rebase` moves a tower across an isomorphism of its base by
composing into that bottom identification, so no transport of the universal property is needed
there either.  At the level of
`AlgebraicGeometry.Space.BlowupFactorization` the identification is absorbed entirely:
`AlgebraicGeometry.Space.BlowupFactorization.exists_bottom_step` writes a factorization of
length `m + 1` as a factorization of length one of a morphism `X₁ ⟶ X` followed by a
factorization of length `m`, and is the exact inverse of
`AlgebraicGeometry.Space.BlowupFactorization.comp`.

## References

* [Stacks Project, Tag 085T](https://stacks.math.columbia.edu/tag/085T)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 0BHA](https://stacks.math.columbia.edu/tag/0BHA)
* [Stacks Project, Tag 0BHE](https://stacks.math.columbia.edu/tag/0BHE)
* [Stacks Project, Tag 0BHF](https://stacks.math.columbia.edu/tag/0BHF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Being an isomorphism over a subspace -/

/-- A morphism whose base change along one leg of a pullback square is an isomorphism, and whose
target is an isomorphism over a subspace, is itself an isomorphism over that subspace: the two
base changes compose. -/
theorem isIso_pullback_snd_comp_left {C : Type*} [Category C] [HasPullbacks C]
    {X Y Z W : C} (f : Y ⟶ Z) (g : W ⟶ Z) (f' : X ⟶ Y)
    (h₁ : IsIso (pullback.snd f g)) (h₂ : IsIso (pullback.snd f' (pullback.fst f g))) :
    IsIso (pullback.snd (f' ≫ f) g) := by
  have := h₁
  have := h₂
  have : IsIso ((pullbackRightPullbackFstIso f g f').hom ≫ pullback.snd (f' ≫ f) g) := by
    rw [pullbackRightPullbackFstIso_hom_snd]
    infer_instance
  exact IsIso.of_isIso_comp_left (pullbackRightPullbackFstIso f g f').hom _

/-- An isomorphism is an isomorphism over every subspace of its target. -/
theorem isIso_pullback_snd_of_isIso {C : Type*} [Category C] [HasPullbacks C] {X Y Z : C}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : IsIso f) : IsIso (pullback.snd f g) := by
  have := h
  exact (IsPullback.of_hasPullback f g).isIso_snd_of_isIso

/-- Precomposing with an isomorphism does not affect being an isomorphism over a subspace. -/
private theorem isIso_pullback_snd_comp_of_isIso_left {C : Type*} [Category C] [HasPullbacks C]
    {X Y Z W : C} (f : Y ⟶ Z) (g : W ⟶ Z) (f' : X ⟶ Y) [IsIso f']
    (h : IsIso (pullback.snd f g)) : IsIso (pullback.snd (f' ≫ f) g) :=
  isIso_pullback_snd_comp_left f g f' h (isIso_pullback_snd_of_isIso _ _ inferInstance)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A blowing up is an isomorphism over any subspace of the base avoiding the centre.**  The
subspace is contained in the open complement of the centre by Stacks 03BZ, and the blowing up is
an isomorphism there by Stacks 085T, part (1). -/
theorem isIso_pullback_snd_of_isBlowupAlong {X X' : AlgebraicSpaces B S hS}
    {Z : ClosedSubspaces B S hS X.obj} {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b)
    (V : Subfunctor X.obj)
    (hV : subspacePointSet B S hS X.obj V ⊆ (subspacePointSet B S hS X.obj Z.1)ᶜ) :
    IsIso (pullback.snd b.hom V.ι) := by
  have hle : V ≤ (openComplementOfClosedSubspace B S hS X Z).1 := by
    refine le_of_range_pointsMap_ι_subset B S hS
      (openComplementOfClosedSubspace B S hS X Z).2 ?_
    change subspacePointSet B S hS X.obj V ⊆
      subspacePointSet B S hS X.obj (openComplementOfClosedSubspace B S hS X Z).1
    rw [subspacePointSet_openComplement]
    exact hV
  exact isIso_pullback_snd_of_factor _ (Subfunctor.homOfLe hle) (Subfunctor.homOfLe_ι hle)
    (isIso_pullback_snd_of_isIso_fromPreimage B S hS b.hom _
      (isIso_fromPreimage_openComplement hb))

/-- **A blowing up at a closed point is an isomorphism over any subspace of the base whose
points avoid that point.**

The centre of the blowing up at a closed point has point set that point, by property (a) of
Stacks 03IQ, so this is `AlgebraicGeometry.Space.isIso_pullback_snd_of_isBlowupAlong`; the
isomorphism over the base carried by
`AlgebraicGeometry.Space.IsBlowupAtClosedPoint` is absorbed by
`AlgebraicGeometry.Space.isIso_pullback_snd_comp_left`. -/
theorem isIso_pullback_snd_of_isBlowupAtClosedPoint {X X' : AlgebraicSpaces B S hS}
    {z : points B S hS X.obj} {hz : IsClosed ({z} : Set (points B S hS X.obj))}
    {b : X' ⟶ X} (hb : IsBlowupAtClosedPoint B S hS z hz b) (V : Subfunctor X.obj)
    (hzV : z ∉ subspacePointSet B S hS X.obj V) :
    IsIso (pullback.snd b.hom V.ι) := by
  obtain ⟨W, b₀, hb₀, e, he⟩ := hb
  have hsub : subspacePointSet B S hS X.obj V ⊆
      (subspacePointSet B S hS X.obj (closedPointSubspace B S hS z hz).1)ᶜ := by
    rw [show subspacePointSet B S hS X.obj (closedPointSubspace B S hS z hz).1 = {z} from
      range_pointsMap_ι_reducedClosedSubspace B S hS X.obj X.property {z} hz]
    rintro y hy (rfl : y = z)
    exact hzV hy
  have hbe : b.hom = e.hom.hom ≫ b₀.hom := by
    rw [← he, ObjectProperty.FullSubcategory.comp_hom]
  rw [hbe]
  exact isIso_pullback_snd_comp_of_isIso_left b₀.hom V.ι e.hom.hom
    (isIso_pullback_snd_of_isBlowupAlong hb₀ V hsub)

/-- **Any two blowings up of `X` at the same closed point are isomorphic over `X`.**

Both are isomorphic over `X` to a blowing up of `X` in the reduced closed subspace supported on
that point, and any two of those are isomorphic over `X` by the universal property of Stacks
085U.  This is what identifies the base change of a global step with a prescribed local one:
the two are blowings up of the same space at the same point, so they agree. -/
theorem IsBlowupAtClosedPoint.exists_iso {X Y Y' : AlgebraicSpaces B S hS}
    {z : points B S hS X.obj} {hz : IsClosed ({z} : Set (points B S hS X.obj))}
    {f : Y ⟶ X} {f' : Y' ⟶ X} (h : IsBlowupAtClosedPoint B S hS z hz f)
    (h' : IsBlowupAtClosedPoint B S hS z hz f') : ∃ e : Y ≅ Y', e.hom ≫ f' = f := by
  obtain ⟨W, b, hb, d, hd⟩ := h'
  obtain ⟨e, he⟩ := h.exists_iso_blowup W b hb
  refine ⟨e ≪≫ d.symm, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← hd, Iso.inv_hom_id_assoc, he]

/-- **A closed point stays closed under an isomorphism.**  The map on points of an isomorphism
of presheaves carries the singleton on a point to the inverse image of that singleton along the
map on points of the inverse, and the maps on points are continuous. -/
theorem isClosed_singleton_pointsMap_of_iso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    {x : points B S hS F} (hx : IsClosed ({x} : Set (points B S hS F))) :
    IsClosed ({pointsMap B S hS F e.hom x} : Set (points B S hS G)) := by
  have h : ({pointsMap B S hS F e.hom x} : Set (points B S hS G)) =
      pointsMap B S hS G e.inv ⁻¹' {x} := by
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro rfl
      rw [← pointsMap_comp_apply, e.hom_inv_id]
      exact congrFun (pointsMap_id B S hS F) x
    · rintro rfl
      rw [← pointsMap_comp_apply, e.inv_hom_id]
      exact (congrFun (pointsMap_id B S hS G) y).symm
  rw [h]
  exact hx.preimage (continuous_pointsMap B S hS _)

/-! ### A tower of blowings up is an isomorphism away from its centres -/

namespace BlowupTower

variable {X X' : AlgebraicSpaces B S hS}

/-- **A tower of blowings up at closed points over `T` is an isomorphism over any subspace of
the base whose points avoid `T`.**

By induction on the tower: the empty tower is an isomorphism, and a step is a blowing up at a
closed point lying over `T`, hence an isomorphism over the inverse image of the subspace, that
inverse image avoiding the centre because the centre lies over `T`. -/
theorem isIso_pullback_snd_proj {Z : AlgebraicSpaces B S hS}
    (t : BlowupTower B S hS X Z) {T : Set (points B S hS X.obj)} {W₀ : Subfunctor X.obj}
    (hdisj : Disjoint (subspacePointSet B S hS X.obj W₀) T) (hcent : t.CentersOver T) :
    IsIso (pullback.snd t.proj.hom W₀.ι) := by
  induction t with
  | base e =>
      rw [proj_base]
      exact isIso_pullback_snd_of_isIso e.hom.hom _ inferInstance
  | step t b z hz hb ih =>
      rw [centersOver_step] at hcent
      obtain ⟨hc, hzT⟩ := hcent
      have hV : z ∉ subspacePointSet B S hS _ (W₀.preimage t.proj.hom) := by
        rintro ⟨y, hy⟩
        refine Set.disjoint_left.1 hdisj ?_ hzT
        refine ⟨pointsMap B S hS _ (W₀.fromPreimage t.proj.hom) y, ?_⟩
        rw [← pointsMap_comp_apply, Subfunctor.fromPreimage_ι, pointsMap_comp_apply, hy]
      have hp := (Subfunctor.isPullback_preimage t.proj.hom W₀).flip
      rw [proj_step, ObjectProperty.FullSubcategory.comp_hom]
      exact isIso_pullback_snd_comp_left t.proj.hom W₀.ι b.hom (ih hc)
        (isIso_pullback_snd_of_factor _ hp.isoPullback.inv
          ((Iso.inv_comp_eq _).2 hp.isoPullback_hom_fst.symm)
          (isIso_pullback_snd_of_isBlowupAtClosedPoint hb _ hV))

/-! ### Transporting a tower along an isomorphism of its base -/

/-- **Transport a tower along an isomorphism of its base.**  A tower over `X` and an isomorphism
`X ≅ X'` give a tower over `X'` with the same steps and the same centres: only the
identification of the bottom of the tower with the base changes.

`AlgebraicGeometry.Space.BlowupTower.comap` is the same operation at the other end of the
tower, for an isomorphism of its top.  Together they are what makes it unnecessary to transport
the universal property of Stacks 085U along an isomorphism: a tower absorbs an isomorphism at
either end. -/
def rebase : {Z : AlgebraicSpaces B S hS} → (X ≅ X') → BlowupTower B S hS X Z →
    BlowupTower B S hS X' Z
  | _, h, .base e => .base (e ≪≫ h)
  | _, h, .step t b z hz hb => .step (rebase h t) b z hz hb

/-- The projection of a transported tower `rebase h t` is the projection of `t` followed by
`h.hom`. -/
@[simp]
theorem proj_rebase : {Z : AlgebraicSpaces B S hS} → (h : X ≅ X') →
    (t : BlowupTower B S hS X Z) → (rebase h t).proj = t.proj ≫ h.hom
  | _, h, .base e => by simp [rebase]
  | _, h, .step t b z hz hb => by simp [rebase, proj_rebase h t]

/-- Transporting a tower along an isomorphism of its base does not change its length. -/
@[simp]
theorem length_rebase : {Z : AlgebraicSpaces B S hS} → (h : X ≅ X') →
    (t : BlowupTower B S hS X Z) → (rebase h t).length = t.length
  | _, _, .base _ => rfl
  | _, h, .step t b z hz hb => by rw [rebase, length_step, length_step, length_rebase h t]

/-- The centres of a transported tower lie over `T` exactly when those of the original lie over
the inverse image of `T`. -/
theorem centersOver_rebase : {Z : AlgebraicSpaces B S hS} → (h : X ≅ X') →
    (t : BlowupTower B S hS X Z) → (T : Set (points B S hS X'.obj)) →
    ((rebase h t).CentersOver T ↔
      t.CentersOver (pointsMap B S hS X.obj h.hom.hom ⁻¹' T))
  | _, _, .base _, _ => by simp [rebase]
  | _, h, .step t b z hz hb, T => by
      rw [rebase, centersOver_step, centersOver_step, centersOver_rebase h t T, proj_rebase,
        ObjectProperty.FullSubcategory.comp_hom, pointsMap_comp]
      simp only [Set.mem_preimage, Function.comp_apply]

/-! ### Peeling the bottom step off a tower -/

/-- **A tower of length one is a single blowing up at a closed point.**  It is the blowing up
`b : Z ⟶ X₀` of the bottom `X₀` of the tower at a closed point `x` of `X₀`, together with the
identification `e : X₀ ≅ X` of that bottom with the base; the projection of the tower is
`b ≫ e`, and the tower has its centre over `T` exactly when `e x ∈ T`. -/
theorem exists_isBlowupAtClosedPoint_of_length_eq_one {Z : AlgebraicSpaces B S hS}
    (u : BlowupTower B S hS X Z) (hlen : u.length = 1) :
    ∃ (X₀ : AlgebraicSpaces B S hS) (e : X₀ ≅ X) (b : Z ⟶ X₀) (x : points B S hS X₀.obj)
      (hx : IsClosed ({x} : Set (points B S hS X₀.obj))),
      IsBlowupAtClosedPoint B S hS x hx b ∧ u.proj = b ≫ e.hom ∧
        ∀ T : Set (points B S hS X.obj),
          (u.CentersOver T ↔ pointsMap B S hS X₀.obj e.hom.hom x ∈ T) := by
  cases u with
  | base e =>
      rw [length_base] at hlen
      omega
  | step t b z hz hb =>
      cases t with
      | base e =>
          refine ⟨_, e, b, z, hz, hb, by rw [proj_step, proj_base], fun T => ?_⟩
          rw [centersOver_step, proj_base]
          exact and_iff_right trivial
      | step t' b' z' hz' hb' =>
          rw [length_step, length_step] at hlen
          omega

/-- **The bottom step of a tower peels off.**  A tower of blowings up over `X` with at least one
step is a tower `u` of length one over `X`, with top `X₁`, followed by a tower `s` over `X₁`
with one step fewer; the projections compose, and the centres of the whole tower lie over `T`
exactly when the centre of `u` does and those of `s` lie over the inverse image of `T` along the
projection of `u`.

`AlgebraicGeometry.Space.BlowupTower.exists_isBlowupAtClosedPoint_of_length_eq_one` unfolds `u`
into a single blowing up at a closed point. -/
theorem exists_bottom_step : {Z : AlgebraicSpaces B S hS} → (t : BlowupTower B S hS X Z) →
    t.length ≠ 0 →
    ∃ (X₁ : AlgebraicSpaces B S hS) (u : BlowupTower B S hS X X₁)
      (s : BlowupTower B S hS X₁ Z),
      u.length = 1 ∧ s.length + 1 = t.length ∧ s.proj ≫ u.proj = t.proj ∧
        ∀ T : Set (points B S hS X.obj),
          (t.CentersOver T ↔ u.CentersOver T ∧
            s.CentersOver (pointsMap B S hS X₁.obj u.proj.hom ⁻¹' T))
  | _, .base e, hlen => by
      rw [length_base] at hlen
      omega
  | _, .step t b z hz hb, _ => by
      by_cases ht : t.length = 0
      · refine ⟨_, .step t b z hz hb, .base (Iso.refl _), by rw [length_step, ht],
          by rw [length_base, length_step, ht], ?_, fun T => ?_⟩
        · rw [proj_base, Iso.refl_hom, Category.id_comp]
        · rw [centersOver_base]
          exact (and_iff_left trivial).symm
      · obtain ⟨X₁, u, s, hu, hs, hproj, hcent⟩ := exists_bottom_step t ht
        have hpt : pointsMap B S hS X₁.obj u.proj.hom
              (pointsMap B S hS _ s.proj.hom z) = pointsMap B S hS _ t.proj.hom z := by
          rw [← pointsMap_comp_apply, ← ObjectProperty.FullSubcategory.comp_hom, hproj]
        refine ⟨X₁, u, .step s b z hz hb, hu, by rw [length_step, length_step, hs], ?_,
          fun T => ?_⟩
        · rw [proj_step, proj_step, Category.assoc, hproj]
        · rw [centersOver_step, centersOver_step, hcent T, Set.mem_preimage, hpt]
          tauto

end BlowupTower

namespace BlowupFactorization

variable {X Y : AlgebraicSpaces B S hS}

/-- **The bottom step of a factorization peels off.**  A morphism factored as a sequence of
`m + 1` blowings up at closed points lying over `T` is a morphism factored by `m` of them over
the inverse image of `T`, followed by a single blowing up at a closed point over `T`.

This is the exact inverse of `AlgebraicGeometry.Space.BlowupFactorization.comp`, and it is the
form the induction in the "if" direction of Stacks 0BHF consumes: the identification of the
bottom of the tower with `X` is absorbed into the length-one factorization of `b`. -/
theorem exists_bottom_step {T : Set (points B S hS X.obj)} {f : Y ⟶ X}
    (F : BlowupFactorization B S hS T f) (hlen : F.length ≠ 0) :
    ∃ (X₁ : AlgebraicSpaces B S hS) (b : X₁ ⟶ X) (g : Y ⟶ X₁)
      (G : BlowupFactorization B S hS T b)
      (H : BlowupFactorization B S hS (pointsMap B S hS X₁.obj b.hom ⁻¹' T) g),
      g ≫ b = f ∧ G.length = 1 ∧ H.length + 1 = F.length := by
  obtain ⟨X₁, u, s, hu, hs, hproj, hcent⟩ := F.tower.exists_bottom_step hlen
  obtain ⟨hcu, hcs⟩ := (hcent T).1 F.centersOver
  refine ⟨X₁, u.proj, F.iso.hom ≫ s.proj,
    ⟨X₁, u, hcu, Iso.refl X₁, Category.id_comp _⟩,
    ⟨F.top, s, hcs, F.iso, rfl⟩, ?_, hu, hs⟩
  rw [Category.assoc, hproj, F.iso_proj]

end BlowupFactorization

/-! ### The top of a tower is a modification away from the chosen points -/

namespace ClosedPointNeighborhoods

variable {n : ℕ} (D : ClosedPointNeighborhoods B S hS n)

/-- The points of `X ∖ {x₁, …, xₙ}` avoid the chosen points. -/
theorem disjoint_subspacePointSet_openAwayFromPoints :
    Disjoint (subspacePointSet B S hS D.space.obj D.openAwayFromPoints)
      (Set.range D.point) := by
  rw [show subspacePointSet B S hS D.space.obj D.openAwayFromPoints = (Set.range D.point)ᶜ from
    D.range_pointsMap_ι_openAwayFromPoints]
  exact disjoint_compl_left

/-- **The top of a tower of blowings up over `X` with centres over `{x₁, …, xₙ}` is an object of
the category `C_{X, {x₁, …, xₙ}}` of Stacks 0BHA.**

The projection of the tower is an isomorphism over `X ∖ {x₁, …, xₙ}` by
`AlgebraicGeometry.Space.BlowupTower.isIso_pullback_snd_proj`, the points of that open subspace
avoiding the centres; and the top of the tower is an algebraic space by construction. -/
theorem isModification_proj_of_centersOver {Z : AlgebraicSpaces B S hS}
    (t : BlowupTower B S hS D.space Z) (hcent : t.CentersOver (Set.range D.point)) :
    IsModification B S hS D.openAwayFromPoints (Over.mk t.proj.hom) :=
  ⟨Z.property,
    t.isIso_pullback_snd_proj D.disjoint_subspacePointSet_openAwayFromPoints hcent⟩

/-- **The source of a morphism factored as a sequence of blowings up at closed points lying over
`{x₁, …, xₙ}` is an object of the category `C_{X, {x₁, …, xₙ}}` of Stacks 0BHA.**

This is the statement that lets the functor `F` of Stacks 0BHA, and hence its fullness, be
applied to the two sides of Stacks 0BHF: without it a global sequence of blowings up is not
known to be an object of the source category of `F`. -/
theorem isModification_of_blowupFactorization {Y : AlgebraicSpaces B S hS} {f : Y ⟶ D.space}
    (F : D.GlobalBlowupFactorization f) :
    IsModification B S hS D.openAwayFromPoints (Over.mk f.hom) := by
  refine ⟨Y.property, ?_⟩
  have hf : F.iso.hom.hom ≫ F.tower.proj.hom = f.hom := by
    rw [← ObjectProperty.FullSubcategory.comp_hom, F.iso_proj]
  change IsIso (pullback.snd f.hom D.openAwayFromPoints.ι)
  rw [← hf]
  exact isIso_pullback_snd_comp_of_isIso_left _ _ _
    (F.tower.isIso_pullback_snd_proj D.disjoint_subspacePointSet_openAwayFromPoints
      F.centersOver)

/-- The object of `C_{X, {x₁, …, xₙ}}` given by a morphism factored as a sequence of blowings up
at closed points lying over `{x₁, …, xₙ}`. -/
def modificationOfBlowupFactorization {Y : AlgebraicSpaces B S hS} {f : Y ⟶ D.space}
    (F : D.GlobalBlowupFactorization f) : D.modificationsAwayFromPoints :=
  ⟨Over.mk f.hom, D.isModification_of_blowupFactorization F⟩

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space

end
