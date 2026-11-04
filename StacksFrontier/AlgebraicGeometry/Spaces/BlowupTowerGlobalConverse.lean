module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupTowerEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupTowerGlobalStepAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPointsFullyFaithful

/-!
# Assembling a global sequence of blowings up out of the local ones

Let `S` be a scheme, let `X` be a decent algebraic space over `S`, let `x₁, …, xₙ ∈ |X|` be
pairwise distinct closed points and let `(Uᵢ, uᵢ) → (X, xᵢ)` be the elementary étale
neighborhoods chosen in Stacks 0BH9, that is a term `D : ClosedPointNeighborhoods B S hS n`.
Let `f : Y ⟶ X` be an object of the category `C_{X, {x₁, …, xₙ}}` of Stacks 0BHA and let
`gᵢ : Yᵢ ⟶ Uᵢ` be its base changes.  If every `gᵢ` factors as a finite sequence of blowings up
at closed points lying over `uᵢ`, then `f` factors as a finite sequence of blowings up at
closed points lying over `{x₁, …, xₙ}`.

This is the **"if" direction of Stacks 0BHF**; the converse, which is the "only if" direction,
is `AlgebraicGeometry.Space.ClosedPointNeighborhoods.nonempty_localBlowupFactorization`.

## Main definitions

* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.BlowupStage` is the invariant of the
  induction: a tower of blowings up over `X` with centres over `{x₁, …, xₙ}` and top `Z`,
  cartesian squares exhibiting a space `Pᵢ` as `Z ×_X Uᵢ`, and a factorization of a morphism
  `Yᵢ ⟶ Pᵢ` as a sequence of blowings up at closed points over `uᵢ`, compatible with `gᵢ`.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.BlowupStage.totalLength` is the sum of the
  lengths of those local factorizations, the quantity the induction decreases.

## Main results

* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.BlowupStage.exists_step`: one step of the
  induction — if some local factorization is nonempty, there is a stage of strictly smaller
  total length.
* `nonempty_globalBlowupFactorization`, in the namespace
  `AlgebraicGeometry.Space.ClosedPointNeighborhoods.BlowupStage`: the end of the induction — a
  stage all of whose local factorizations are empty produces a global factorization of `f`, by
  the full faithfulness of the functor `F` of Stacks 0BHA.
* `nonempty_globalBlowupFactorization_of_isPullback` and
  `nonempty_globalBlowupFactorization_restrictionComponent`, both in the namespace
  `AlgebraicGeometry.Space.ClosedPointNeighborhoods`: **the "if" direction of Stacks 0BHF**,
  for arbitrary base changes of `f` and for the base changes given by the functor `F` of
  Stacks 0BHA.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.nonempty_globalBlowupFactorization_iff`:
  the equivalence of Stacks 0BHF, both directions together.

## Implementation notes

### The shape of the induction

The source builds the global tower one step at a time, peeling the bottom blowing up off one
of the local sequences and realizing it globally.  Carrying that out needs an invariant
relating the partially built global tower to what is left of the local ones, and that is
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.BlowupStage`: at each stage the global tower
has top `Z`, each `Pᵢ` is `Z ×_X Uᵢ`, and what remains of the `i`th local sequence is a
factorization of a morphism `Yᵢ ⟶ Pᵢ` whose centres lie over the fibre of `uᵢ` in `Pᵢ`.  The
induction is a strong induction on the sum of the lengths of those factorizations.

The induction is **not** a recursion on `D`.  Over an intermediate `Z` the permitted centres
are the points of the fibres over `{x₁, …, xₙ}`, of which there are in general infinitely
many, so there is no term of `AlgebraicGeometry.Space.ClosedPointNeighborhoods` over `Z`; in
particular `AlgebraicGeometry.Space.ClosedPointNeighborhoods.eq_of_map_eq_point`, which is
verbatim the hypothesis of Stacks 0BH9 that `uᵢ` is the only point of `Uᵢ` above `xᵢ`, fails
there.  The datum `D` is therefore fixed throughout and only the tower grows.

### Where the base identification of a tower is absorbed

The bottom of a tower is identified with its base by an isomorphism rather than an equality, so
peeling the bottom step off the `i`th local sequence produces a blowing up `X₁ ⟶ X₀` of a space
`X₀` merely *isomorphic* to `Pᵢ`, at a closed point of `X₀`.  Rather than transport the
universal property of Stacks 085U along `X₀ ≅ Pᵢ`, the cartesian square exhibiting `Pᵢ` as
`Z ×_X Uᵢ` is moved onto `X₀` — a cartesian square absorbs an isomorphism of its apex, which is
`CategoryTheory.IsPullback.of_iso` with identities at the other three corners — and the global
blowing up is taken over `X₀`.
The new local base is `Pᵢ ×_Z Z'`, which is a blowing up of `X₀` at the same point after the
same isomorphism is undone, by
`AlgebraicGeometry.Space.isPullback_comp_iso_corner`; two blowings up at one closed point are
isomorphic over the base (`AlgebraicGeometry.Space.IsBlowupAtClosedPoint.exists_iso`), and
`AlgebraicGeometry.Space.BlowupTower.rebase` carries the remaining local tower across that
isomorphism.  At the indices `j ≠ i` the new local base `P_j ×_Z Z'` maps isomorphically to
`P_j`, by
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.isIso_of_ne_of_isBlowupAtClosedPoint`, and
the same transport applies.  Both cases are
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.BlowupStage.exists_rebase`.

The global step is taken with
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_isBlowupAtClosedPoint_restricting`
rather than with
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_blowupTower_step`: the latter hides
the global centre and the fact that the new step is the blowing up at it, and both are needed
to see that the step leaves the other neighborhoods untouched.

### What the end of the induction uses

When every local factorization has length zero each `Yᵢ ⟶ Pᵢ` is an isomorphism, so `Y` and
the top `Z` of the global tower have the same image under the functor `F` of Stacks 0BHA — `Z`
being an object of `C_{X, {x₁, …, xₙ}}` by
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.isModification_proj_of_centersOver`.  The
identification `Y ≅ Z` over `X` is then `CategoryTheory.Functor.preimageIso` for `F`, whose
fullness and faithfulness are
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.full_restrictionFunctor` and
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.faithful_restrictionFunctor`.  This is the
only place where full faithfulness is used.

### Sheafification on the big fppf site

Each step of the induction consumes
`AlgebraicGeometry.Space.exists_isBlowupAtClosedPoint_unconditional`, the existence of the
blowing up of an algebraic space at a closed point, whose statement takes
`[HasSheafify (BigFppfOver.topology B S hS) (Type u)]` as an instance argument.  Nothing here
takes it: the big fppf site over `S` is essentially small, so presheaves of types in the
universe of the sections sheafify on it outright, which is
`AlgebraicGeometry.BigFppfOver.hasSheafify_type`, and each statement below installs that as a
local instance in its own proof.  The equivalence of the tag is therefore available with no
hypothesis beyond those of the source, and carries the `@[stacks 0BHF]` attribute.

## References

* [Stacks Project, Tag 0BHF](https://stacks.math.columbia.edu/tag/0BHF)
* [Stacks Project, Tag 0BHE](https://stacks.math.columbia.edu/tag/0BHE)
* [Stacks Project, Tag 0BHB](https://stacks.math.columbia.edu/tag/0BHB)
* [Stacks Project, Tag 0BHA](https://stacks.math.columbia.edu/tag/0BHA)
* [Stacks Project, Tag 0BH9](https://stacks.math.columbia.edu/tag/0BH9)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Transporting a cartesian square along an isomorphism -/

/-- **A cartesian square absorbs an isomorphism of the corner being pulled back.**  Replacing
the morphism that is pulled back by its composite with an isomorphism changes the square only
by that isomorphism on the upper left corner. -/
theorem isPullback_comp_iso_corner {C : Type*} [Category C] {P' P Q Z Z' : C} {r : P' ⟶ P}
    {s : P' ⟶ Z'} {p : P ⟶ Z} {b : Z' ⟶ Z} (h : IsPullback r s p b) (ε : P ≅ Q) :
    IsPullback (r ≫ ε.hom) s (ε.inv ≫ p) b := by
  have ht : IsPullback ε.hom p (ε.inv ≫ p) (𝟙 Z) := IsPullback.of_horiz_isIso ⟨by simp⟩
  have h2 := h.paste_horiz ht
  rwa [Category.comp_id] at h2

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ClosedPointNeighborhoods

variable {n : ℕ} (D : ClosedPointNeighborhoods B S hS n)

/-! ### The invariant of the induction -/

/-- **A stage of the induction building the global sequence of blowings up.**

Fix a family of morphisms `gᵢ : Yᵢ ⟶ Uᵢ`.  A stage consists of a tower of blowings up over `X`
with centres over `{x₁, …, xₙ}` and top `Z`, for each `i` a space `Pᵢ` presented as the fibre
product `Z ×_X Uᵢ`, and for each `i` a morphism `Yᵢ ⟶ Pᵢ` whose composite with `Pᵢ ⟶ Uᵢ` is
`gᵢ`, factored as a sequence of blowings up at closed points lying over the fibre of `uᵢ`
in `Pᵢ`.

The induction starts from `AlgebraicGeometry.Space.ClosedPointNeighborhoods.initialBlowupStage`,
where the tower is empty and `Pᵢ = Uᵢ`, and decreases
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.BlowupStage.totalLength`. -/
structure BlowupStage {Yl : Fin n → AlgebraicSpaces B S hS}
    (g : ∀ i, Yl i ⟶ D.neighborhoodSpace i) where
  /-- The top `Z` of the global tower built so far. -/
  space : AlgebraicSpaces B S hS
  /-- The global tower of blowings up built so far. -/
  tower : BlowupTower B S hS D.space space
  /-- Its centres lie over the chosen points. -/
  centersOver : tower.CentersOver (Set.range D.point)
  /-- The local base `Pᵢ`, which is `Z ×_X Uᵢ`. -/
  base : Fin n → AlgebraicSpaces B S hS
  /-- The projection `Pᵢ ⟶ Z`. -/
  baseProj : ∀ i, base i ⟶ space
  /-- The projection `Pᵢ ⟶ Uᵢ`. -/
  baseNbhd : ∀ i, base i ⟶ D.neighborhoodSpace i
  /-- The two projections exhibit `Pᵢ` as `Z ×_X Uᵢ`. -/
  isPullback_base : ∀ i, IsPullback (baseProj i) (baseNbhd i) tower.proj (D.toSpaceHom i)
  /-- What is left of the `i`th local sequence: a morphism `Yᵢ ⟶ Pᵢ`. -/
  lift : ∀ i, Yl i ⟶ base i
  /-- It lies over `gᵢ`. -/
  lift_comp : ∀ i, lift i ≫ baseNbhd i = g i
  /-- Its factorization as a sequence of blowings up at closed points over the fibre of `uᵢ`. -/
  fact : ∀ i, BlowupFactorization B S hS
    (pointsMap B S hS (base i).obj (baseNbhd i).hom ⁻¹'
      ({D.neighborhoodPoint i} : Set (points B S hS (D.neighborhoodSpace i).obj))) (lift i)

namespace BlowupStage

variable {D} {Yl : Fin n → AlgebraicSpaces B S hS} {g : ∀ i, Yl i ⟶ D.neighborhoodSpace i}

/-- The sum of the lengths of the local factorizations of a stage: the quantity the induction
of the "if" direction of Stacks 0BHF decreases. -/
def totalLength (st : D.BlowupStage g) : ℕ := ∑ i, (st.fact i).length

end BlowupStage

/-- **The stage the induction starts from.**  The global tower is empty, so `Z = X` and
`Pᵢ = Uᵢ`, and the local factorizations are the given ones. -/
def initialBlowupStage {Yl : Fin n → AlgebraicSpaces B S hS}
    (g : ∀ i, Yl i ⟶ D.neighborhoodSpace i) (G : ∀ i, D.LocalBlowupFactorization i (g i)) :
    D.BlowupStage g where
  space := D.space
  tower := .base (Iso.refl D.space)
  centersOver := trivial
  base i := D.neighborhoodSpace i
  baseProj i := D.toSpaceHom i
  baseNbhd _ := 𝟙 _
  isPullback_base i := D.isPullback_toSpaceHom_id i
  lift := g
  lift_comp i := Category.comp_id _
  fact i := (G i).mono (by simp)

/-- The total length of the initial stage is the sum of the lengths of the given local
factorizations. -/
@[simp]
theorem totalLength_initialBlowupStage {Yl : Fin n → AlgebraicSpaces B S hS}
    (g : ∀ i, Yl i ⟶ D.neighborhoodSpace i) (G : ∀ i, D.LocalBlowupFactorization i (g i)) :
    (D.initialBlowupStage g G).totalLength = ∑ i, (G i).length := rfl

namespace BlowupStage

variable {D} {Yl : Fin n → AlgebraicSpaces B S hS} {g : ∀ i, Yl i ⟶ D.neighborhoodSpace i}

/-! ### Re-pointing one local factorization onto a new local base -/

/-- **Carrying what is left of one local sequence onto a new local base.**

Let `tw` be a tower over a space `Q` with top the top of the `i`th local factorization of a
stage, let `h : Q ≅ R` be an isomorphism and let `c : R ⟶ Pᵢ` be a morphism such that the
projection of `tw` followed by `h` and `c` is the projection of that local factorization, and
such that the centres of `tw` lie over the fibre of `uᵢ` pulled back along `h ≫ c`.  Then there
is a morphism `Yᵢ ⟶ R` over `gᵢ` factored by a tower over `R` of the same length as `tw`, with
centres over the fibre of `uᵢ` in `R`.

Both halves of the inductive step are this lemma:  at the index where the step is taken, `R` is
the new local base, `Q` is the top of the peeled bottom blowing up and `h` identifies the two;
at the other indices `R` is again the new local base, `Q = Pᵢ` and `h` is the inverse of the
projection, which is an isomorphism there. -/
theorem exists_rebase (st : D.BlowupStage g) (i : Fin n) {Q R : AlgebraicSpaces B S hS}
    (tw : BlowupTower B S hS Q (st.fact i).top) (h : Q ≅ R) (c : R ⟶ st.base i)
    (hproj : tw.proj ≫ h.hom ≫ c = (st.fact i).tower.proj)
    (hc : tw.CentersOver (pointsMap B S hS Q.obj (h.hom ≫ c).hom ⁻¹'
      (pointsMap B S hS (st.base i).obj (st.baseNbhd i).hom ⁻¹'
        ({D.neighborhoodPoint i} : Set (points B S hS (D.neighborhoodSpace i).obj))))) :
    ∃ (l : Yl i ⟶ R) (F : BlowupFactorization B S hS
        (pointsMap B S hS R.obj (c ≫ st.baseNbhd i).hom ⁻¹'
          ({D.neighborhoodPoint i} : Set (points B S hS (D.neighborhoodSpace i).obj))) l),
      l ≫ c ≫ st.baseNbhd i = g i ∧ F.length = tw.length := by
  have hset : pointsMap B S hS Q.obj (h.hom ≫ c).hom ⁻¹'
        (pointsMap B S hS (st.base i).obj (st.baseNbhd i).hom ⁻¹'
          ({D.neighborhoodPoint i} : Set (points B S hS (D.neighborhoodSpace i).obj))) =
      pointsMap B S hS Q.obj h.hom.hom ⁻¹'
        (pointsMap B S hS R.obj (c ≫ st.baseNbhd i).hom ⁻¹'
          ({D.neighborhoodPoint i} : Set (points B S hS (D.neighborhoodSpace i).obj))) := by
    ext τ
    simp only [Set.mem_preimage, Set.mem_singleton_iff,
      ObjectProperty.FullSubcategory.comp_hom, ← pointsMap_comp_apply, Category.assoc]
  refine ⟨(st.fact i).iso.hom ≫ (BlowupTower.rebase h tw).proj,
    { top := (st.fact i).top
      tower := BlowupTower.rebase h tw
      centersOver := ?_
      iso := (st.fact i).iso
      iso_proj := rfl }, ?_, BlowupTower.length_rebase h tw⟩
  · rw [BlowupTower.centersOver_rebase]
    exact hset ▸ hc
  · calc ((st.fact i).iso.hom ≫ (BlowupTower.rebase h tw).proj) ≫ c ≫ st.baseNbhd i
        = ((st.fact i).iso.hom ≫ tw.proj ≫ h.hom ≫ c) ≫ st.baseNbhd i := by
          rw [BlowupTower.proj_rebase]; simp only [Category.assoc]
      _ = ((st.fact i).iso.hom ≫ (st.fact i).tower.proj) ≫ st.baseNbhd i := by rw [hproj]
      _ = st.lift i ≫ st.baseNbhd i := by rw [(st.fact i).iso_proj]
      _ = g i := st.lift_comp i

/-! ### One step of the induction -/

/-- **One step of the induction of the "if" direction of Stacks 0BHF.**

If the `i`th local factorization of a stage has at least one blowing up, there is a stage of
total length one less.  Its bottom blowing up is peeled off, carried to a closed point of the
intermediate space `Z` lying over `xᵢ` and blown up there; the new global tower is one step
longer, the new local base at `i` is the blowing up prescribed locally, and at the other
indices the new local base maps isomorphically to the old one. -/
theorem exists_step
    (st : D.BlowupStage g) (i : Fin n) (hlen : (st.fact i).length ≠ 0) :
    ∃ st' : D.BlowupStage g, st'.totalLength + 1 = st.totalLength := by
  classical
  let := BigFppfOver.hasSheafify_type B S hS
  obtain ⟨X₁, u, s, hu, hs, hsu, hcent⟩ := (st.fact i).tower.exists_bottom_step hlen
  obtain ⟨X₀, e, b₀, x, hx, hb₀, hup, hiff⟩ :=
    BlowupTower.exists_isBlowupAtClosedPoint_of_length_eq_one u hu
  obtain ⟨hcu, hcs⟩ := (hcent _).1 (st.fact i).centersOver
  have hxq : pointsMap B S hS X₀.obj (e.hom ≫ st.baseNbhd i).hom x =
      D.neighborhoodPoint i := by
    rw [ObjectProperty.FullSubcategory.comp_hom, pointsMap_comp]
    exact (hiff _).1 hcu
  have sqe : IsPullback (e.hom ≫ st.baseProj i) (e.hom ≫ st.baseNbhd i) st.tower.proj
      (D.toSpaceHom i) :=
    (st.isPullback_base i).of_iso e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
      (by simp) (by simp) (by simp)
  obtain ⟨w, hw, Z', b', hgw, hb, hrest⟩ :=
    D.exists_isBlowupAtClosedPoint_restricting sqe hx hxq
  have htcent : (BlowupTower.step st.tower b' w hw hb).CentersOver (Set.range D.point) := by
    rw [BlowupTower.centersOver_step]
    exact ⟨st.centersOver, ⟨i, hgw.symm⟩⟩
  have nsq : ∀ j, IsPullback (pullback.snd (st.baseProj j) b')
      (pullback.fst (st.baseProj j) b' ≫ st.baseNbhd j) (b' ≫ st.tower.proj)
      (D.toSpaceHom j) := fun j =>
    D.isPullback_comp_of_isPullback (st.isPullback_base j) (IsPullback.of_hasPullback _ _)
  have key : ∀ j, ∃ (l : Yl j ⟶ pullback (st.baseProj j) b') (F : BlowupFactorization B S hS
      (pointsMap B S hS (pullback (st.baseProj j) b').obj
          (pullback.fst (st.baseProj j) b' ≫ st.baseNbhd j).hom ⁻¹'
        ({D.neighborhoodPoint j} : Set (points B S hS (D.neighborhoodSpace j).obj))) l),
      l ≫ pullback.fst (st.baseProj j) b' ≫ st.baseNbhd j = g j ∧
        F.length + (if j = i then 1 else 0) = (st.fact j).length := by
    intro j
    rcases eq_or_ne j i with rfl | hji
    · rw [ite_eq_left rfl]
      have hbr : IsBlowupAtClosedPoint B S hS x hx
          (pullback.fst (st.baseProj j) b' ≫ e.inv) :=
        hrest (isPullback_comp_iso_corner (IsPullback.of_hasPullback (st.baseProj j) b') e.symm)
      obtain ⟨d, hd⟩ := hb₀.exists_iso hbr
      have hdf : d.hom ≫ pullback.fst (st.baseProj j) b' = u.proj := by
        rw [hup, ← hd]; simp
      obtain ⟨l, F, hl, hF⟩ := st.exists_rebase j s d (pullback.fst (st.baseProj j) b')
        (by rwa [hdf]) (by rwa [hdf])
      exact ⟨l, F, hl, by rwa [hF]⟩
    · rw [ite_eq_right hji]
      have hr : IsIso (pullback.fst (st.baseProj j) b') :=
        D.isIso_of_ne_of_isBlowupAtClosedPoint hji (st.isPullback_base j) hgw hb
          (IsPullback.of_hasPullback _ _)
      have hid : (asIso (pullback.fst (st.baseProj j) b')).symm.hom ≫
          pullback.fst (st.baseProj j) b' = 𝟙 (st.base j) := by simp
      obtain ⟨l, F, hl, hF⟩ := st.exists_rebase j (st.fact j).tower
        (asIso (pullback.fst (st.baseProj j) b')).symm (pullback.fst (st.baseProj j) b')
        (by rw [hid, Category.comp_id])
        (by
          rw [hid, ObjectProperty.FullSubcategory.id_hom, pointsMap_id, Set.preimage_id]
          exact (st.fact j).centersOver)
      exact ⟨l, F, hl, hF⟩
  choose l F hl hF using key
  refine ⟨{ space := Z'
            tower := BlowupTower.step st.tower b' w hw hb
            centersOver := htcent
            base := fun j => pullback (st.baseProj j) b'
            baseProj := fun j => pullback.snd (st.baseProj j) b'
            baseNbhd := fun j => pullback.fst (st.baseProj j) b' ≫ st.baseNbhd j
            isPullback_base := nsq
            lift := l
            lift_comp := hl
            fact := F }, ?_⟩
  change (∑ j, (F j).length) + 1 = ∑ j, (st.fact j).length
  calc (∑ j, (F j).length) + 1
      = (∑ j : Fin n, (F j).length) + ∑ j : Fin n, (if j = i then 1 else 0) := by simp
    _ = ∑ j : Fin n, ((F j).length + (if j = i then 1 else 0)) := Finset.sum_add_distrib.symm
    _ = ∑ j, (st.fact j).length := Finset.sum_congr rfl fun j _ => hF j

/-! ### The end of the induction -/

/-- **The end of the induction of the "if" direction of Stacks 0BHF.**

If every local factorization of a stage is empty then each `Yᵢ ⟶ Pᵢ` is an isomorphism, so the
functor `F` of Stacks 0BHA carries `Y` and the top `Z` of the global tower to the same object;
`Z` is an object of its source category because the centres of the tower lie over
`{x₁, …, xₙ}`, and `F` is fully faithful, so `Y ≅ Z` over `X` and the global tower factors
`f`. -/
theorem nonempty_globalBlowupFactorization (st : D.BlowupStage g)
    {Y : AlgebraicSpaces B S hS} {f : Y ⟶ D.space}
    (hf : IsModification B S hS D.openAwayFromPoints (Over.mk f.hom))
    {a : ∀ i, Yl i ⟶ Y} (sq : ∀ i, IsPullback (a i) (g i) f (D.toSpaceHom i))
    (h0 : ∀ i, (st.fact i).length = 0) :
    Nonempty (D.GlobalBlowupFactorization f) := by
  have hli : ∀ i, IsIso (st.lift i) := fun i => (st.fact i).isIso_of_length_eq_zero (h0 i)
  let MY : D.modificationsAwayFromPoints := ⟨Over.mk f.hom, hf⟩
  let MZ : D.modificationsAwayFromPoints :=
    ⟨Over.mk st.tower.proj.hom, D.isModification_proj_of_centersOver st.tower st.centersOver⟩
  have hcomp : ∀ i, ∃ k : st.base i ⟶ Y, IsPullback k (st.baseNbhd i) f (D.toSpaceHom i) := by
    intro i
    refine ⟨(asIso (st.lift i)).symm.hom ≫ a i, ?_⟩
    have h : IsPullback ((asIso (st.lift i)).symm.hom ≫ a i) ((asIso (st.lift i)).symm.hom ≫ g i)
        f (D.toSpaceHom i) :=
      (sq i).of_iso (asIso (st.lift i)) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
        (by simp) (by simp) (by simp)
    have hid : (asIso (st.lift i)).symm.hom ≫ st.lift i = 𝟙 (st.base i) :=
      (asIso (st.lift i)).inv_hom_id
    rwa [← st.lift_comp i, ← Category.assoc, hid, Category.id_comp] at h
  have hiso : ∀ i, (D.restrictionComponent i).obj MY ≅ (D.restrictionComponent i).obj MZ := by
    intro i
    have hY := AlgebraicSpaces.isPullback_hom B S hS (hcomp i).choose_spec
    have hZ := AlgebraicSpaces.isPullback_hom B S hS (st.isPullback_base i)
    have hγ : ((IsPullback.of_hasPullback f.hom (D.toSpaceHom i).hom).isoIsPullback
            Y.obj (D.neighborhoodSpace i).obj hY ≪≫
          hZ.isoIsPullback st.space.obj (D.neighborhoodSpace i).obj
            (IsPullback.of_hasPullback st.tower.proj.hom (D.toSpaceHom i).hom)).hom ≫
          pullback.snd st.tower.proj.hom (D.toSpaceHom i).hom =
        pullback.snd f.hom (D.toSpaceHom i).hom := by
      simp
    exact ObjectProperty.isoMk _ (Over.isoMk _ hγ)
  have := D.full_restrictionFunctor
  have := D.faithful_restrictionFunctor
  let Ψ : MY ≅ MZ := D.restrictionFunctor.preimageIso (Pi.isoMk hiso)
  let eY := ((ObjectProperty.ι (IsModification B S hS D.openAwayFromPoints)) ⋙
    Over.forget D.space.obj).mapIso Ψ
  exact ⟨{ top := st.space
           tower := st.tower
           centersOver := st.centersOver
           iso := ObjectProperty.isoMk _ eY
           iso_proj := by exact ObjectProperty.hom_ext _ (Over.w Ψ.hom.hom) }⟩

end BlowupStage

/-! ### The "if" direction of Stacks 0BHF -/

/-- **The "if" direction of Stacks 0BHF.**  Let `X, xᵢ, Uᵢ ⟶ X, uᵢ` be as in Stacks 0BH9, let
`f : Y ⟶ X` be an object of the category `C_{X, {x₁, …, xₙ}}` of Stacks 0BHA and let
`gᵢ : Yᵢ ⟶ Uᵢ` be base changes of `f` along the chosen neighborhoods.  If every `gᵢ` factors as
a finite sequence of blowings up at closed points lying over `uᵢ`, then `f` factors as a finite
sequence of blowings up at closed points lying over `{x₁, …, xₙ}`.

The proof is a strong induction on the sum of the lengths of the local factorizations; see the
implementation notes of this file. -/
theorem nonempty_globalBlowupFactorization_of_isPullback
    {Y : AlgebraicSpaces B S hS}
    {f : Y ⟶ D.space} (hf : IsModification B S hS D.openAwayFromPoints (Over.mk f.hom))
    {Yl : Fin n → AlgebraicSpaces B S hS} {a : ∀ i, Yl i ⟶ Y}
    {g : ∀ i, Yl i ⟶ D.neighborhoodSpace i}
    (sq : ∀ i, IsPullback (a i) (g i) f (D.toSpaceHom i))
    (G : ∀ i, D.LocalBlowupFactorization i (g i)) :
    Nonempty (D.GlobalBlowupFactorization f) := by
  suffices h : ∀ N : ℕ, ∀ st : D.BlowupStage g, st.totalLength ≤ N →
      Nonempty (D.GlobalBlowupFactorization f) from
    h _ (D.initialBlowupStage g G) le_rfl
  intro N
  induction N with
  | zero =>
      intro st hN
      refine st.nonempty_globalBlowupFactorization hf sq fun i => ?_
      refine Nat.le_zero.1 (le_trans ?_ hN)
      exact Finset.single_le_sum (f := fun j => (st.fact j).length)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  | succ N ih =>
      intro st hN
      by_cases h0 : ∀ i, (st.fact i).length = 0
      · exact st.nonempty_globalBlowupFactorization hf sq h0
      · obtain ⟨i, hi⟩ := not_forall.1 h0
        obtain ⟨st', hst'⟩ := st.exists_step i hi
        exact ih st' (by omega)

/-- **The "if" direction of Stacks 0BHF, for the functor `F` of Stacks 0BHA.**  Let
`X, xᵢ, Uᵢ ⟶ X, uᵢ` be as in Stacks 0BH9 and let `f : Y ⟶ X` be an object of
`C_{X, {x₁, …, xₙ}}` corresponding to `gᵢ : Yᵢ ⟶ Uᵢ` under `F`.  If every `gᵢ` factors as a
finite sequence of blowings up at closed points lying over `uᵢ`, then `f` factors as a finite
sequence of blowings up at closed points lying over `{x₁, …, xₙ}`.

This is
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.nonempty_globalBlowupFactorization_of_isPullback`
at the cartesian square presenting the base change computing `F`. -/
theorem nonempty_globalBlowupFactorization_restrictionComponent
    (M : D.modificationsAwayFromPoints)
    (G : ∀ i, D.LocalBlowupFactorization i (ObjectProperty.homMk
      ((D.restrictionComponent i).obj M).obj.hom :
      (⟨((D.restrictionComponent i).obj M).obj.left,
          ((D.restrictionComponent i).obj M).property.1⟩ : AlgebraicSpaces B S hS) ⟶
        D.neighborhoodSpace i)) :
    Nonempty (D.GlobalBlowupFactorization (ObjectProperty.homMk M.obj.hom :
      (⟨M.obj.left, M.property.1⟩ : AlgebraicSpaces B S hS) ⟶ D.space)) := by
  refine D.nonempty_globalBlowupFactorization_of_isPullback M.property
    (a := fun i => ObjectProperty.homMk (pullback.fst M.obj.hom (D.toSpaceHom i).hom))
    (fun i => ?_) G
  exact IsPullback.of_map_of_faithful
    (F := ObjectProperty.ι (fun T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS T))
    (IsPullback.of_hasPullback M.obj.hom (D.toSpaceHom i).hom)

/-- **Stacks 0BHF.**  Let `X, xᵢ, Uᵢ ⟶ X, uᵢ` be as in Stacks 0BH9 and let `f : Y ⟶ X` be an
object of the category `C_{X, {x₁, …, xₙ}}` of Stacks 0BHA.  Then `f` factors as a finite
sequence of blowings up at closed points lying over `{x₁, …, xₙ}` if and only if, for every
`i`, the morphism `gᵢ = F(f)ᵢ` factors as a finite sequence of blowings up at closed points
lying over `uᵢ`.

The "only if" direction is `nonempty_localBlowupFactorization_restrictionComponent` and the
"if" direction is `nonempty_globalBlowupFactorization_restrictionComponent`. -/
@[stacks 0BHF]
theorem nonempty_globalBlowupFactorization_iff (M : D.modificationsAwayFromPoints) :
    Nonempty (D.GlobalBlowupFactorization (ObjectProperty.homMk M.obj.hom :
        (⟨M.obj.left, M.property.1⟩ : AlgebraicSpaces B S hS) ⟶ D.space)) ↔
      ∀ i, Nonempty (D.LocalBlowupFactorization i (ObjectProperty.homMk
        ((D.restrictionComponent i).obj M).obj.hom :
        (⟨((D.restrictionComponent i).obj M).obj.left,
            ((D.restrictionComponent i).obj M).property.1⟩ : AlgebraicSpaces B S hS) ⟶
          D.neighborhoodSpace i)) :=
  ⟨fun hF i => D.nonempty_localBlowupFactorization_restrictionComponent M i hF.some,
    fun h => D.nonempty_globalBlowupFactorization_restrictionComponent M fun i => (h i).some⟩

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space

end
