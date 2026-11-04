module

public import StacksFrontier.AlgebraicGeometry.AmpleThickeningLimit.Basic
public import StacksFrontier.AlgebraicGeometry.TwistedThickeningLift.SectionsLift
public import StacksFrontier.AlgebraicGeometry.Limits.ClosedSubschemeImageLimit
public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianApproximation.Absolute
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.ConstructibleImage
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.InvertibleUnconditional
public import StacksFrontier.AlgebraicGeometry.AmpleLimit.Unconditional
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower

/-!
# Stacks Tag 09MW: ampleness across a thickening, unconditionally

Let `i : Z ⟶ X` be a closed immersion of schemes inducing a homeomorphism of underlying spaces and
let `L` be an invertible `𝒪_X`-module. [Stacks, Tag 09MW] asserts that `i^* L` is ample on `Z` if
and only if `L` is ample on `X`, with no Noetherian hypothesis.

The implication `L` ample `⟹` `i^* L` ample is
`Stacks.AmpleThickeningLimit.isAmple_modulePullback`. This file proves the converse with no
hypothesis beyond the source's, by the source's limit argument:

* `Z` is quasi-compact and separated ([Stacks, Tag 01PS], [Stacks, Tag 09MP]); since `i` is
  surjective and universally closed, `X` is quasi-compact and separated ([Stacks, Tag 09MQ]);
* `X = lim X_k` with `X_k` of finite type over `ℤ` and affine transition morphisms
  ([Stacks, Tag 01ZA]), and `L` is the pullback of an invertible `L_j` on some `X_j`
  ([Stacks, Tag 01ZR]);
* the scheme-theoretic images `Z_k ⊆ X_k` of `Z` have `lim Z_k = Z`
  (`AlgebraicGeometry.isLimit_closedSubschemeImageCone`), so `L_{j'}|_{Z_{j'}}` is ample for some
  `j'` ([Stacks, Tag 09MT]);
* `X ⟶ X_{j'}` lands in the closed subset `Z_{j'}`, so some `X_k ⟶ X_{j'}` does
  ([Stacks, Tag 05F4]); the scheme-theoretic inverse image `T ⊆ X_k` of `Z_{j'}` is then a
  surjective closed immersion carrying the ample `L_k|_T` (pulled back along the affine
  `T ⟶ Z_{j'}`, [Stacks, Tag 0892]);
* so `L_k` is ample on the Noetherian `X_k` by [Stacks, Tag 09MS], whose converse is
  `Stacks.TwistedThickeningLift.isAmple_of_isAmple_modulePullback`, and `L` is ample, being its
  pullback along the affine `X ⟶ X_k`.

## Main results

* `Stacks.AmpleThickeningLimit.isAmple_of_isAmple_modulePullback_of_isHomeomorph`: the converse.
* `Stacks.AmpleThickeningLimit.isAmple_modulePullback_iff_of_isHomeomorph`: **[Stacks, Tag 09MW]**.

## References

* [Stacks Project, Tag 09MW](https://stacks.math.columbia.edu/tag/09MW)
* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
* [Stacks Project, Tag 09MT](https://stacks.math.columbia.edu/tag/09MT)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 05F4](https://stacks.math.columbia.edu/tag/05F4)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.AmpleTheory

universe u

namespace Stacks.AmpleThickeningLimit

/-! ### Bookkeeping for pullbacks -/

/-- Pulling back along `f` and then `g`, for `f ≫ g = h`, is pulling back along `h`. -/
def pullbackCompEqIso {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C) (e : f ≫ g = h)
    (M : C.Modules) :
    (modulePullback f.toLRSHom.toShHom).obj ((modulePullback g.toLRSHom.toShHom).obj M) ≅
      (modulePullback h.toLRSHom.toShHom).obj M :=
  (Scheme.Modules.pullbackComp f g).app M ≪≫
    eqToIso (congrArg (fun q : A ⟶ C => (Scheme.Modules.pullback q).obj M) e)

/-- Ampleness is carried by pullback along an affine morphism ([Stacks, Tag 0892]). -/
theorem isAmple_modulePullback_of_isAffineHom {A B : Scheme.{u}} (f : A ⟶ B) [IsAffineHom f]
    (M : B.Modules) [IsInvertibleModule B M] (h : IsAmple B M) :
    IsAmple A ((modulePullback f.toLRSHom.toShHom).obj M) := by
  have : IsQuasiAffineHom f := by
    refine ⟨fun U hU => ?_⟩
    have : IsAffine (f ⁻¹ᵁ U).toScheme := hU.preimage f
    infer_instance
  exact Stacks.SectionRatioNoAmple.isAmple_modulePullback_of_isQuasiAffineHom f M h

/-- Ampleness transported along an isomorphism of invertible modules. -/
theorem isAmple_of_iso' {A : Scheme.{u}} {M N : A.Modules} [IsInvertibleModule A M]
    [IsInvertibleModule A N] (e : M ≅ N) (h : IsAmple A M) : IsAmple A N :=
  (Stacks.RelativeVeryAmple.isAmple_congr M N e).mp h

/-- Ampleness of a double pullback depends only on the composite of the two morphisms. -/
private theorem isAmple_pullback_pullback_of_comp_eq {A B B' C : Scheme.{u}} (f : A ⟶ B)
    (g : B ⟶ C) (f' : A ⟶ B') (g' : B' ⟶ C) (e : f ≫ g = f' ≫ g') (M : C.Modules)
    [IsInvertibleModule C M]
    (h : IsAmple A ((modulePullback f.toLRSHom.toShHom).obj
      ((modulePullback g.toLRSHom.toShHom).obj M))) :
    IsAmple A ((modulePullback f'.toLRSHom.toShHom).obj
      ((modulePullback g'.toLRSHom.toShHom).obj M)) :=
  isAmple_of_iso' (pullbackCompEqIso f g _ rfl M ≪≫
    (pullbackCompEqIso f' g' _ e.symm M).symm) h

variable {Z X : Scheme.{u}} (i : Z ⟶ X) (L : X.Modules) [IsInvertibleModule X L]

/-- **The implication `i^* L` ample `⟹` `L` ample of [Stacks, Tag 09MW]**, with no hypothesis
beyond the source's. See the module docstring for the limit argument. -/
theorem isAmple_of_isAmple_modulePullback_of_isHomeomorph [IsClosedImmersion i]
    (hi : IsHomeomorph i.base) (h : IsAmple Z ((modulePullback i.toLRSHom.toShHom).obj L)) :
    IsAmple X L := by
  classical
  have : Surjective i := ⟨hi.surjective⟩
  have : CompactSpace Z := h.compactSpace
  have : Z.IsSeparated := Stacks.TwistedThickeningLift.isSeparated_of_isAmple _ h
  have : X.IsSeparated := Scheme.isSeparated_of_surjective_universallyClosed i
  have : CompactSpace X :=
    Stacks.AmpleClosedImmersion.compactSpace_of_surjective i inferInstance inferInstance
  obtain ⟨I, _, _, _, D, c, hDaff, hft, hqc, ⟨hc⟩, hpt⟩ :=
    AlgebraicGeometry.exists_isLimit_finiteType X
  subst hpt
  have hDaff' : ∀ {j k : Iᵒᵖ} (v : j ⟶ k), IsAffineHom (D.map v) := hDaff
  have hDN : ∀ j, IsNoetherian (D.obj j) := fun j =>
    isNoetherian_of_locallyOfFiniteType_terminalFrom _ (hft j) (hqc j)
  -- `L` descends to a stage
  obtain ⟨j, Lj, hLj, ⟨eL⟩⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_isInvertible_pullback_iso_of_isLimit D c hc L
      ‹IsInvertibleModule c.pt L›
  have : IsInvertibleModule (D.obj j) Lj := hLj
  -- the system of images of `Z`
  let E := closedSubschemeImageSystem D c i
  let ι := closedSubschemeImageSystemι D c i
  let cZ := closedSubschemeImageCone D c i
  have hEN : ∀ k, IsNoetherian (E.obj k) := fun k => by
    have : IsLocallyNoetherian (E.obj k) := LocallyOfFiniteType.isLocallyNoetherian (ι.app k)
    have : CompactSpace (E.obj k) := QuasiCompact.compactSpace_of_compactSpace (ι.app k)
    exact {}
  let Mj := (modulePullback (ι.app j).toLRSHom.toShHom).obj Lj
  -- its pullback to `Z` is `i^* L`, hence ample
  have hZM : IsAmple Z ((modulePullback (cZ.π.app j).toLRSHom.toShHom).obj Mj) :=
    isAmple_pullback_pullback_of_comp_eq i (c.π.app j) (cZ.π.app j) (ι.app j)
      (closedSubschemeImageCone_π_app_comp_imageι D c i j).symm Lj
      (isAmple_of_iso' ((modulePullback i.toLRSHom.toShHom).mapIso eL) h)
  -- [Stacks, Tag 09MT] on the system of images
  obtain ⟨j', g, hj'⟩ :=
    Stacks.AlgebraicGeometry.AmpleLimit.exists_isAmple_pullback_map_of_isLimit_of_qcqs E cZ
      (isLimit_closedSubschemeImageCone D c i hc)
      j Mj ((Stacks.AmpleBridge.isAmple_iff_isAmple cZ.pt
        ((modulePullback (cZ.π.app j).toLRSHom.toShHom).obj Mj)).mp hZM)
  let Lj' := (modulePullback (D.map g).toLRSHom.toShHom).obj Lj
  have hj'' : IsAmple (E.obj j') ((modulePullback (ι.app j').toLRSHom.toShHom).obj Lj') :=
    isAmple_pullback_pullback_of_comp_eq (E.map g) (ι.app j) (ι.app j') (D.map g)
      (ι.naturality g) Lj
      ((Stacks.AmpleBridge.isAmple_iff_isAmple (E.obj j')
        ((modulePullback (E.map g).toLRSHom.toShHom).obj Mj)).mpr hj')
  -- [Stacks, Tag 05F4]: a later stage maps into the image
  let d : AlgebraicGeometry.DescentSituation.{u, u} I :=
    { system := D
      transition_affine := fun f => inferInstance
      quasiCompact := fun k => inferInstance
      quasiSeparated := fun k => inferInstance
      limitCone := c
      isLimit := hc
      base := j'.unop }
  let S : Set (D.obj j') := Set.range (ι.app j')
  have hS : Topology.IsLocallyConstructible S := by
    apply Topology.IsConstructible.isLocallyConstructible
    apply Topology.IsConstructible.of_compl
    have hcl : IsClosed S := (ι.app j').isClosedEmbedding.isClosed_range
    exact (TopologicalSpace.NoetherianSpace.isCompact _).isConstructible hcl.isOpen_compl
  have hlim : Set.range (d.limitCone.π.app (op d.base)).base ⊆ S := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := i.surjective x
    refine ⟨(cZ.π.app j') z, ?_⟩
    show ((cZ.π.app j') ≫ ι.app j').base z = _
    rw [closedSubschemeImageCone_π_app_comp_imageι]
    rfl
  obtain ⟨k, hk, hkS⟩ :=
    (AlgebraicGeometry.eventually_range_transition_subset_of_isLocallyConstructible d S hS
      hlim).exists
  let gk : op k ⟶ j' := (homOfLE hk).op
  let q := pullback.fst (D.map gk) (ι.app j')
  let r := pullback.snd (D.map gk) (ι.app j')
  have : IsAffineHom (D.map gk) := hDaff' gk
  have : IsAffineHom r :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback (D.map gk) (ι.app j')) (hDaff' gk)
  have : Surjective q := by
    rw [surjective_iff]
    intro x
    have hx : (D.map gk).base x ∈ Set.range (ι.app j') := hkS ⟨x, rfl⟩
    have : x ∈ Set.range q := by
      simpa only [q, Scheme.Pullback.range_fst, Set.mem_preimage] using hx
    exact this
  let Lk := (modulePullback (D.map gk).toLRSHom.toShHom).obj Lj'
  have hT : IsAmple (pullback (D.map gk) (ι.app j')) ((modulePullback q.toLRSHom.toShHom).obj Lk) :=
    isAmple_pullback_pullback_of_comp_eq r (ι.app j') q (D.map gk)
      pullback.condition.symm Lj' (isAmple_modulePullback_of_isAffineHom r _ hj'')
  -- [Stacks, Tag 09MS] at the Noetherian stage
  have hk' : IsAmple (D.obj (op k)) Lk :=
    Stacks.TwistedThickeningLift.isAmple_of_isAmple_modulePullback q Lk hT
  -- pull back to `X`
  have : IsAffineHom (c.π.app (op k)) := isAffineHom_π_app D c hc (op k)
  have hX := isAmple_modulePullback_of_isAffineHom (c.π.app (op k)) Lk hk'
  exact isAmple_of_iso' (pullbackCompEqIso (c.π.app (op k)) (D.map gk) _ (c.w gk) Lj' ≪≫
    pullbackCompEqIso (c.π.app j') (D.map g) _ (c.w g) Lj ≪≫ eL.symm) hX

/-- **[Stacks, Tag 09MW].** Let `i : Z ⟶ X` be a closed immersion of schemes inducing a
homeomorphism of underlying topological spaces, and let `L` be an invertible `𝒪_X`-module. Then
`i^* L` is ample on `Z` if and only if `L` is ample on `X`.

No hypothesis beyond the source's: neither Noetherianness nor separatedness nor
quasi-compactness of either scheme is assumed. The `mpr` half is
`Stacks.AmpleThickeningLimit.isAmple_modulePullback`; the `mp` half is
`Stacks.AmpleThickeningLimit.isAmple_of_isAmple_modulePullback_of_isHomeomorph`. -/
@[stacks 09MW]
theorem isAmple_modulePullback_iff_of_isHomeomorph [IsClosedImmersion i]
    (hi : IsHomeomorph i.base) :
    IsAmple Z ((modulePullback i.toLRSHom.toShHom).obj L) ↔ IsAmple X L :=
  ⟨isAmple_of_isAmple_modulePullback_of_isHomeomorph i L hi, isAmple_modulePullback i L hi⟩

end Stacks.AmpleThickeningLimit

end
