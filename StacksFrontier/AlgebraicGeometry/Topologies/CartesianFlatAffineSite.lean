module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalPresentationTransport
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianModulesOnAffineSite
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianOfGlobalPresentation
public import StacksFrontier.CategoryTheory.Sites.Modules.CartesianCancellation
public import StacksFrontier.CategoryTheory.Sites.Modules.CartesianLocalOnCoverOfPullbacks
public import StacksFrontier.CategoryTheory.Sites.Modules.CartesianSheafCondition

/-!
# Cartesian modules on a site of affine schemes with fibre products along its coverings

Let `C` be a category with a functor `L : C ⥤ Scheme` taking affine values, and let `Q` be a class
of morphisms of `C` along which fibre products exist, which is stable under base change and
composition, whose members are flat on the underlying schemes, and along which `L` preserves
fibre products. Suppose the topology `J` of `C` is the one whose covering sieves are those
containing a finite jointly surjective family of members of `Q`. The structure presheaf is the
presheaf of global functions `X ↦ Γ(L X, 𝒪)`.

This is the shape of the subsite of affine objects of the lisse-étale and of the flat-fppf site
of an algebraic stack: these sites do **not** have fibre products in general (a fibre product
`U₁ ×_{U₃} U₂` of smooth objects need not be smooth over the stack), but they have them along
their covering morphisms. The results below are the parts of Stacks 03DX, 0H04 and 023M which
use only those fibre products.

## Main results

* `isSheaf_of_cartesian`, `isSheaf_of_cartesian_over`: a cartesian presheaf of modules is a
  sheaf, also on a slice.
* `isIso_restrictionBaseChange_of_isCover`: being cartesian over a flat morphism is local on a
  covering of its target.
* `isIso_restrictionBaseChange_of_isQuasicoherentOnSite`: a quasi-coherent module is cartesian.
* `isIso_restrictionBaseChange_colimit`: a colimit of cartesian sheaves of modules is cartesian.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w m u u₁ v₁

namespace Stacks.FlatAffineSite

open Stacks.PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] (L : C ⥤ Scheme.{u}) (Q : MorphismProperty C)

/-- The presheaf of rings of global functions `X ↦ Γ(L X, 𝒪)`. -/
abbrev rings : Cᵒᵖ ⥤ CommRingCat.{u} := L.op ⋙ Scheme.Γ

/-- `L` carries fibre product squares along a morphism of `Q` to fibre product squares. -/
def PreservesPullbacksAlong : Prop :=
  ∀ ⦃X Y Z P : C⦄ ⦃fst : P ⟶ X⦄ ⦃snd : P ⟶ Y⦄ ⦃f : X ⟶ Z⦄ ⦃g : Y ⟶ Z⦄,
    IsPullback fst snd f g → Q f → IsPullback (L.map fst) (L.map snd) (L.map f) (L.map g)

/-- A family of morphisms with common target is jointly surjective on the underlying schemes. -/
def IsJointlySurjective {X : C} {I : Type*} {W : I → C} (g : ∀ i, W i ⟶ X) : Prop :=
  ∀ x : L.obj X, ∃ i, ∃ y : L.obj (W i), L.map (g i) y = x

/-- A *cover*: a finite jointly surjective family of members of `Q`. -/
structure IsCover {X : C} {I : Type*} {W : I → C} (g : ∀ i, W i ⟶ X) : Prop where
  /-- The index type of the family is finite. -/
  finite : Finite I
  /-- Every member of the family satisfies `Q`. -/
  mem : ∀ i, Q (g i)
  /-- The family is jointly surjective on the underlying schemes. -/
  surj : IsJointlySurjective L g

variable (J : GrothendieckTopology C)

/-- Every covering sieve contains a cover, indexed in the universe `w`. -/
def HasCoverRefinements : Prop :=
  ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X →
    ∃ (I : Type w) (W : I → C) (g : ∀ i, W i ⟶ X), IsCover L Q g ∧ ∀ i, S (g i)

/-- Every cover generates a covering sieve. -/
def CoversAreCovering : Prop :=
  ∀ ⦃X : C⦄ {I : Type w} (W : I → C) (g : ∀ i, W i ⟶ X), IsCover L Q g →
    Sieve.ofArrows W g ∈ J X

variable {L Q J}

section Rings

variable [∀ X, IsAffine (L.obj X)]

omit [∀ X, IsAffine (L.obj X)] in
/-- The ring map of a morphism with flat underlying morphism of affine schemes is flat. -/
theorem flat_rings_map {X Y : C} [IsAffine (L.obj X)] [IsAffine (L.obj Y)] (a : X ⟶ Y)
    (ha : Flat (L.map a)) : ((rings L).map a.op).hom.Flat := by
  change (L.map a).appTop.hom.Flat
  exact HasRingHomProperty.appTop (P := @Flat) _ ha

/-- The rings of a cover form a faithfully flat family. -/
theorem faithfullyFlat_rings (hQ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → Flat (L.map f))
    {X : C} {I : Type*} {W : I → C} {g : ∀ i, W i ⟶ X} (hg : IsCover L Q g) :
    (RingHom.pi (fun i => ((rings L).map (g i).op).hom)).FaithfullyFlat := by
  have := hg.finite
  have : ∀ i, Flat (L.map (g i)) := fun i => hQ _ (hg.mem i)
  have : IsAffine (unop (L.op.obj (op X))) := inferInstanceAs (IsAffine (L.obj X))
  exact Scheme.faithfullyFlat_pi_appTop (U := L.obj X) (fun i => L.obj (W i))
    (fun i => L.map (g i)) hg.surj

/-- A fibre product square carried by `L` to a fibre product square becomes a pushout square of
rings. -/
theorem isPushout_rings {X Y Z P : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback (L.map fst) (L.map snd) (L.map f) (L.map g)) :
    IsPushout ((rings L).map f.op) ((rings L).map g.op) ((rings L).map fst.op)
      ((rings L).map snd.op) := by
  have : IsAffine (unop (L.op.obj (op X))) := inferInstanceAs (IsAffine (L.obj X))
  have : IsAffine (unop (L.op.obj (op Y))) := inferInstanceAs (IsAffine (L.obj Y))
  have : IsAffine (unop (L.op.obj (op Z))) := inferInstanceAs (IsAffine (L.obj Z))
  exact isPushout_appTop_of_isPullback h

end Rings

section BaseChange

variable [Q.HasPullbacks] [Q.IsStableUnderBaseChange]

omit [Q.IsStableUnderBaseChange] in
/-- The fibre product along a member of `Q`, in the order `pullback f g`. -/
theorem hasPullback_left {X Y Z : C} {f : X ⟶ Z} (hf : Q f) (g : Y ⟶ Z) : HasPullback f g :=
  MorphismProperty.HasPullbacks.hasPullback g hf

omit [Q.IsStableUnderBaseChange] in
/-- The fibre product along a member of `Q`, in the order `pullback g f`. -/
theorem hasPullback_right {X Y Z : C} {f : X ⟶ Z} (hf : Q f) (g : Y ⟶ Z) : HasPullback g f :=
  have := hasPullback_left hf g
  hasPullback_symmetry f g

/-- A family of morphisms whose pullbacks along a fixed morphism are carried to fibre products
by `L` has jointly surjective projections. -/
private theorem isJointlySurjective_of_isPullback {X Y : C} {I : Type*} {W P : I → C}
    {g : ∀ i, W i ⟶ X} (hg : IsJointlySurjective L g) (f : Y ⟶ X) {fst : ∀ i, P i ⟶ W i}
    {snd : ∀ i, P i ⟶ Y}
    (h : ∀ i, IsPullback (L.map (fst i)) (L.map (snd i)) (L.map (g i)) (L.map f)) :
    IsJointlySurjective L snd := by
  intro y
  obtain ⟨i, w, hw⟩ := hg (L.map f y)
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback w y hw
  refine ⟨i, (h i).isoPullback.inv z, ?_⟩
  rwa [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd]

/-- A cover pulls back to a cover. -/
theorem IsCover.pullback (hL : PreservesPullbacksAlong L Q) {X Y : C} {I : Type*} {W : I → C}
    {g : ∀ i, W i ⟶ X} (hg : IsCover L Q g) (f : Y ⟶ X) :
    letI := fun i => hasPullback_left (hg.mem i) f
    IsCover L Q (fun i => pullback.snd (g i) f) := by
  let := fun i => hasPullback_left (hg.mem i) f
  exact ⟨hg.finite, fun i => MorphismProperty.pullback_snd _ _ (hg.mem i),
    isJointlySurjective_of_isPullback hg.surj f fun i =>
      hL (IsPullback.of_hasPullback (g i) f) (hg.mem i)⟩

end BaseChange

section Sheaf

variable [∀ X, IsAffine (L.obj X)] [Q.HasPullbacks] [Q.IsStableUnderBaseChange]

omit [Q.IsStableUnderBaseChange] in
/-- **A cartesian presheaf of modules satisfies the sheaf axiom for a cover.** -/
theorem isSheafFor_of_cartesian_of_isCover
    (hQ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → Flat (L.map f)) (hL : PreservesPullbacksAlong L Q)
    (M : PresheafOfModules.{max m u} (rings L ⋙ forget₂ CommRingCat RingCat))
    (hM : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), IsIso (restrictionBaseChange M f))
    {X : C} {I : Type*} {W : I → C} {g : ∀ i, W i ⟶ X} (hg : IsCover L Q g) :
    Presieve.IsSheafFor (M.presheaf ⋙ forget AddCommGrpCat) (Presieve.ofArrows W g) := by
  have := hg.finite
  let := fun i j => hasPullback_left (hg.mem i) (g j)
  exact isSheafFor_of_isIso_restrictionBaseChange (rings L) M W g
    (fun i j => pullback (g i) (g j)) (fun i j => pullback.fst _ _) (fun i j => pullback.snd _ _)
    (fun i j => pullback.condition) (faithfullyFlat_rings hQ hg)
    (fun i j => isPushout_rings (hL (IsPullback.of_hasPullback (g i) (g j)).flip (hg.mem j)).flip)
    (fun i => hM _) (fun i j => hM _)

/-- **A cartesian presheaf of modules is a sheaf.** -/
theorem isSheaf_of_cartesian
    (hQ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → Flat (L.map f)) (hL : PreservesPullbacksAlong L Q)
    (hJ : HasCoverRefinements.{w} L Q J)
    (M : PresheafOfModules.{max m u} (rings L ⋙ forget₂ CommRingCat RingCat))
    (hM : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), IsIso (restrictionBaseChange M f)) :
    Presheaf.IsSheaf J M.presheaf := by
  apply Presheaf.isSheaf_of_isSheaf_comp J M.presheaf (forget AddCommGrpCat.{max m u})
  rw [isSheaf_iff_isSheaf_of_type]
  intro V S hS
  obtain ⟨I, W, g, hg, hgS⟩ := hJ S hS
  refine Presieve.isSheafFor_subsieve _ (S := Sieve.ofArrows W g) ?_ ?_
  · rintro _ _ ⟨_, a, b, ⟨i⟩, rfl⟩
    exact S.downward_closed (hgS i) a
  · intro Y f
    let := fun i => hasPullback_left (hg.mem i) f
    have h := isSheafFor_of_cartesian_of_isCover hQ hL M hM (hg.pullback hL f)
    rwa [Presieve.ofArrows_pullback, Presieve.isSheafFor_iff_generate,
      Sieve.pullbackArrows_comm] at h

end Sheaf

/-! ### Slices -/

section Over

variable (U : C)

/-- The morphisms of the slice over `U` whose underlying morphism lies in `Q`. -/
def overProp (Q : MorphismProperty C) (U : C) : MorphismProperty (Over U) :=
  fun _ _ f => Q f.left

/-- A morphism of the slice lies in `overProp Q U` exactly when its underlying morphism lies in
`Q`. -/
theorem overProp_iff {U : C} {X Y : Over U} (f : X ⟶ Y) : overProp Q U f ↔ Q f.left := Iff.rfl

/-- A cospan in the slice over `U` has a fibre product when the underlying cospan in `C` has
one. -/
theorem hasPullback_over {X Y Z : Over U} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f.left g.left] :
    HasPullback f g := by
  have : HasPullback ((Over.forget U).map f) ((Over.forget U).map g) :=
    inferInstanceAs (HasPullback f.left g.left)
  have : HasLimit (cospan f g ⋙ Over.forget U) :=
    hasLimit_of_iso (cospanCompIso (Over.forget U) f g).symm
  exact hasLimit_of_created (cospan f g) (Over.forget U)

/-- Fibre products along members of `overProp Q U` exist when they exist along members of `Q`. -/
instance overProp_hasPullbacks [Q.HasPullbacks] : (overProp Q U).HasPullbacks where
  hasPullback g hf := by
    have := MorphismProperty.HasPullbacks.hasPullback (P := Q) g.left hf
    exact hasPullback_over U _ g

/-- `overProp Q U` is stable under base change when `Q` is. -/
instance overProp_isStableUnderBaseChange [Q.IsStableUnderBaseChange] :
    (overProp Q U).IsStableUnderBaseChange where
  of_isPullback sq hg := Q.of_isPullback (sq.map (Over.forget U)) hg

/-- `overProp Q U` is stable under composition when `Q` is. -/
instance overProp_isStableUnderComposition [Q.IsStableUnderComposition] :
    (overProp Q U).IsStableUnderComposition where
  comp_mem f g hf hg := Q.comp_mem f.left g.left hf hg

/-- If `L` preserves fibre products along members of `Q`, then `Over.forget U ⋙ L` preserves
fibre products along members of `overProp Q U`. -/
theorem preservesPullbacksAlong_over (hL : PreservesPullbacksAlong L Q) :
    PreservesPullbacksAlong (Over.forget U ⋙ L) (overProp Q U) :=
  fun _ _ _ _ _ _ _ _ h hf => hL (h.map (Over.forget U)) hf

/-- If every covering sieve of `J` contains a cover, then every covering sieve of `J.over U`
contains a cover for `Over.forget U ⋙ L` and `overProp Q U`. -/
theorem hasCoverRefinements_over (hJ : HasCoverRefinements.{w} L Q J) :
    HasCoverRefinements.{w} (Over.forget U ⋙ L) (overProp Q U) (J.over U) := by
  intro X S hS
  obtain ⟨I, W, g, hg, hgS⟩ := hJ _ ((J.mem_over_iff S).mp hS)
  refine ⟨I, fun i => Over.mk (g i ≫ X.hom), fun i => Over.homMk (g i), ⟨hg.finite, hg.mem,
    hg.surj⟩, fun i => ?_⟩
  exact (Sieve.overEquiv_iff S (g i)).mp (hgS i)

/-- If every cover generates a covering sieve of `J`, then every cover for `Over.forget U ⋙ L`
and `overProp Q U` generates a covering sieve of `J.over U`. -/
theorem coversAreCovering_over (hJ : CoversAreCovering.{w} L Q J) :
    CoversAreCovering.{w} (Over.forget U ⋙ L) (overProp Q U) (J.over U) := by
  intro X I W g hg
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact hJ _ _ ⟨hg.finite, hg.mem, hg.surj⟩

/-- The schemes attached by `Over.forget U ⋙ L` to the objects of the slice over `U` are
affine. -/
instance [∀ X, IsAffine (L.obj X)] (X : Over U) : IsAffine ((Over.forget U ⋙ L).obj X) :=
  inferInstanceAs (IsAffine (L.obj X.left))

/-- **A cartesian presheaf of modules on a slice is a sheaf.** -/
theorem isSheaf_of_cartesian_over [∀ X, IsAffine (L.obj X)] [Q.HasPullbacks]
    [Q.IsStableUnderBaseChange]
    (hQ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → Flat (L.map f)) (hL : PreservesPullbacksAlong L Q)
    (hJ : HasCoverRefinements.{w} L Q J)
    (M : PresheafOfModules.{max m u} (rings (Over.forget U ⋙ L) ⋙ forget₂ CommRingCat RingCat))
    (hM : ∀ {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y), IsIso (restrictionBaseChange M f)) :
    Presheaf.IsSheaf (J.over U) M.presheaf :=
  isSheaf_of_cartesian (Q := overProp Q U) (fun _ _ f hf => hQ f.left hf)
    (preservesPullbacksAlong_over U hL) (hasCoverRefinements_over U hJ) M hM

end Over

/-- A quasi-coherent module has a cover by objects over which it has a global presentation. -/
private theorem exists_cover_hasGlobalPresentation
    (hR : Presheaf.IsSheaf J (rings L ⋙ forget₂ CommRingCat RingCat))
    (hJ : HasCoverRefinements.{w} L Q J)
    (M : SheafOfModules.{max u₁ v₁ u m}
      (⟨rings L ⋙ forget₂ CommRingCat RingCat, hR⟩ : Sheaf J RingCat.{u}))
    (hM : M.IsQuasicoherentOnSite) (V : C) :
    ∃ (I : Type w) (W : I → C) (g : ∀ i, W i ⟶ V), IsCover L Q g ∧
      ∀ i, (M.over (W i)).HasGlobalPresentation := by
  obtain ⟨I₀, W₀, g₀, hcover₀, hpres₀⟩ := hM.locally_hasGlobalPresentation V
  obtain ⟨I, W, g, hg, hgS⟩ := hJ _ hcover₀
  refine ⟨I, W, g, hg, fun i => ?_⟩
  obtain ⟨Z, a, b, ⟨j⟩, hab⟩ := hgS i
  exact Stacks.SheafOfModules.hasGlobalPresentation_overMap M a (hpres₀ j)

/-! ### Locality of the cartesian condition, and quasi-coherent modules -/

section Locality

variable [∀ X, IsAffine (L.obj X)] [Q.HasPullbacks] [Q.IsStableUnderBaseChange]
  [Q.IsStableUnderComposition]

/-- **Being cartesian over a flat morphism is local on a cover of its target.** -/
theorem isIso_restrictionBaseChange_of_isCover
    (_hQ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → Flat (L.map f)) (hL : PreservesPullbacksAlong L Q)
    (hcov : CoversAreCovering.{w} L Q J)
    (M : PresheafOfModules.{max m u} (rings L ⋙ forget₂ CommRingCat RingCat))
    (hs : Presheaf.IsSheaf J M.presheaf)
    {V : C} {I : Type w} {W : I → C} {g : ∀ i, W i ⟶ V} (hg : IsCover L Q g)
    (hcart : ∀ (i : I) {X Y : C} (x : X ⟶ W i) (y : Y ⟶ W i) (a : X ⟶ Y), a ≫ y = x →
      IsIso (restrictionBaseChange M a.op))
    {U : C} (f : U ⟶ V) (hflat : Flat (L.map f)) :
    IsIso (restrictionBaseChange M f.op) := by
  classical
  have := hg.finite
  have hsT : Presieve.IsSheaf J (M.presheaf ⋙ forget AddCommGrpCat) :=
    Presieve.isSheaf_iso J
      (Functor.isoWhiskerLeft M.presheaf AddCommGrpCat.coyonedaObjIsoForget)
      (hs (AddCommGrpCat.of (ULift.{max m u} ℤ)))
  let := fun i => hasPullback_right (hg.mem i) f
  let := fun i => hasPullback_left (hg.mem i) f
  let := fun i j => hasPullback_left (hg.mem i) (g j)
  have hQc : ∀ c : I × I, Q (pullback.fst (g c.1) (g c.2) ≫ g c.1) := fun c =>
    Q.comp_mem _ _ (MorphismProperty.pullback_fst _ _ (hg.mem c.2)) (hg.mem c.1)
  let := fun c : I × I => hasPullback_right (hQc c) f
  have hQf : ∀ i, Q (pullback.fst f (g i)) := fun i =>
    MorphismProperty.pullback_fst _ _ (hg.mem i)
  let := fun i j => hasPullback_left (hQf i) (pullback.fst f (g j))
  have hgU : IsCover L Q (fun i => pullback.fst f (g i)) := by
    exact ⟨hg.finite, hQf, isJointlySurjective_of_isPullback hg.surj f fun i =>
      hL (IsPullback.of_hasPullback f (g i)).flip (hg.mem i)⟩
  have hsfV : Presieve.IsSheafFor (M.presheaf ⋙ forget AddCommGrpCat)
      (Presieve.ofArrows W g) :=
    (Presieve.isSheafFor_iff_generate _).mpr (hsT _ (hcov W g hg))
  have hsfU : Presieve.IsSheafFor (M.presheaf ⋙ forget AddCommGrpCat)
      (Presieve.ofArrows (fun i => pullback f (g i)) (fun i => pullback.fst f (g i))) :=
    (Presieve.isSheafFor_iff_generate _).mpr (hsT _ (hcov _ _ hgU))
  exact isIso_restrictionBaseChange_of_cover_of_hasPullback M f W g
    (flat_rings_map f hflat) hsfV hsfU
    (fun i => isPushout_rings ((hL (IsPullback.of_hasPullback f (g i)).flip (hg.mem i)).flip))
    (fun c => isPushout_rings ((hL (IsPullback.of_hasPullback f _).flip (hQc c)).flip))
    (fun i => hcart i (pullback.snd f (g i)) (𝟙 _) (pullback.snd f (g i)) (by simp))
    (fun c => hcart c.1 (pullback.snd f (pullback.fst (g c.1) (g c.2) ≫ g c.1) ≫
      pullback.fst (g c.1) (g c.2)) (pullback.fst (g c.1) (g c.2))
      (pullback.snd f (pullback.fst (g c.1) (g c.2) ≫ g c.1)) rfl)

variable (hR : Presheaf.IsSheaf J (rings L ⋙ forget₂ CommRingCat RingCat))

omit [Q.IsStableUnderComposition] in
/-- A global presentation on a slice makes the module cartesian over the morphisms of that
slice. -/
theorem isIso_restrictionBaseChange_over_of_hasGlobalPresentation
    (hQ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → Flat (L.map f)) (hL : PreservesPullbacksAlong L Q)
    (hJ : HasCoverRefinements.{w} L Q J)
    (M : SheafOfModules.{max u₁ v₁ u m}
      (⟨rings L ⋙ forget₂ CommRingCat RingCat, hR⟩ : Sheaf J RingCat.{u}))
    (U : C) (hM : (M.over U).HasGlobalPresentation) {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y) :
    IsIso (restrictionBaseChange.{max u₁ v₁, v₁, u, max u₁ v₁ u m}
      (R := (Over.forget U).op ⋙ rings L) (M.over U).val f) :=
  isIso_restrictionBaseChange_of_hasGlobalPresentation.{max u₁ v₁, v₁, u, m}
    ((Over.forget U).op ⋙ rings L)
    (Sheaf.over (⟨rings L ⋙ forget₂ CommRingCat RingCat, hR⟩ : Sheaf J RingCat.{u}) U).property
    (fun N hN => isSheaf_of_cartesian_over.{w, max u₁ v₁ m, u, u₁, v₁} U hQ hL hJ N hN)
    (M.over U) hM f

/-- **A quasi-coherent module is cartesian over every flat morphism.** -/
theorem isIso_restrictionBaseChange_of_isQuasicoherentOnSite_flat
    (hQ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → Flat (L.map f)) (hL : PreservesPullbacksAlong L Q)
    (hJ : HasCoverRefinements.{w} L Q J) (hcov : CoversAreCovering.{w} L Q J)
    (M : SheafOfModules.{max u₁ v₁ u m}
      (⟨rings L ⋙ forget₂ CommRingCat RingCat, hR⟩ : Sheaf J RingCat.{u}))
    (hM : M.IsQuasicoherentOnSite) {U V : C} (f : U ⟶ V) (hflat : Flat (L.map f)) :
    IsIso (restrictionBaseChange.{u₁, v₁, u, max u₁ v₁ m} M.val f.op) := by
  obtain ⟨I, W, g, hg, hpres⟩ := exists_cover_hasGlobalPresentation.{w, m, u, u₁, v₁} hR hJ M hM V
  refine isIso_restrictionBaseChange_of_isCover.{w, max u₁ v₁ m, u, u₁, v₁} hQ hL hcov M.val
    M.isSheaf hg ?_ f hflat
  intro i X Y x y a ha
  exact isIso_restrictionBaseChange_over_of_hasGlobalPresentation.{w, m, u, u₁, v₁} hR hQ hL hJ M
    (W i) (hpres i) (Quiver.Hom.op (Over.homMk (U := Over.mk x) (V := Over.mk y) a ha))

/-- **A quasi-coherent module is cartesian over every morphism.** -/
theorem isIso_restrictionBaseChange_of_isQuasicoherentOnSite
    (hQ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → Flat (L.map f)) (hL : PreservesPullbacksAlong L Q)
    (hJ : HasCoverRefinements.{w} L Q J) (hcov : CoversAreCovering.{w} L Q J)
    (M : SheafOfModules.{max u₁ v₁ u m}
      (⟨rings L ⋙ forget₂ CommRingCat RingCat, hR⟩ : Sheaf J RingCat.{u}))
    (hM : M.IsQuasicoherentOnSite) {U V : C} (f : U ⟶ V) :
    IsIso (restrictionBaseChange.{u₁, v₁, u, max u₁ v₁ m} M.val f.op) := by
  obtain ⟨I, W, g, hg, hpres⟩ := exists_cover_hasGlobalPresentation.{w, m, u, u₁, v₁} hR hJ M hM V
  have := hg.finite
  let := fun i => hasPullback_left (hg.mem i) f
  have hflatCart : ∀ {X Y : C} (a : X ⟶ Y), Flat (L.map a) →
      IsIso (restrictionBaseChange.{u₁, v₁, u, max u₁ v₁ m} M.val a.op) := fun a ha =>
    isIso_restrictionBaseChange_of_isQuasicoherentOnSite_flat.{w, m, u, u₁, v₁} hR hQ hL hJ hcov M
      hM a ha
  have hq : ∀ i, IsIso (restrictionBaseChange.{u₁, v₁, u, max u₁ v₁ m} M.val
      (pullback.snd (g i) f).op) := fun i =>
    hflatCart _ (hQ _ (MorphismProperty.pullback_snd _ _ (hg.mem i)))
  have hc : ∀ i, IsIso (restrictionBaseChange.{u₁, v₁, u, max u₁ v₁ m} M.val
      (pullback.snd (g i) f ≫ f).op) := by
    intro i
    rw [← pullback.condition, op_comp]
    refine isIso_restrictionBaseChange_comp.{u₁, v₁, u, max u₁ v₁ m} M.val (g i).op
      (pullback.fst (g i) f).op (hflatCart _ (hQ _ (hg.mem i))) ?_
    exact isIso_restrictionBaseChange_over_of_hasGlobalPresentation.{w, m, u, u₁, v₁} hR hQ hL hJ M
      (W i) (hpres i) (Quiver.Hom.op (Over.homMk (U := Over.mk (pullback.fst (g i) f))
        (V := Over.mk (𝟙 (W i))) (pullback.fst (g i) f) (by simp)))
  exact isIso_restrictionBaseChange_of_faithfullyFlat_family.{u₁, v₁, u, max u₁ v₁ m} M.val f
    (fun i => pullback (g i) f) (fun i => pullback.snd (g i) f)
    (faithfullyFlat_rings hQ (hg.pullback hL f)) hq hc

end Locality

/-! ### Colimits -/

/-- **A colimit of cartesian sheaves of modules is cartesian.** -/
theorem isIso_restrictionBaseChange_colimit [∀ X, IsAffine (L.obj X)] [Q.HasPullbacks]
    [Q.IsStableUnderBaseChange]
    (hQ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → Flat (L.map f)) (hL : PreservesPullbacksAlong L Q)
    (hJ : HasCoverRefinements.{w} L Q J)
    (hR : Presheaf.IsSheaf J (rings L ⋙ forget₂ CommRingCat RingCat))
    {D : Type*} [Category D] [HasColimitsOfShape D AddCommGrpCat.{max u m}]
    (K : D ⥤ SheafOfModules.{max u m}
      (⟨rings L ⋙ forget₂ CommRingCat RingCat, hR⟩ : Sheaf J RingCat.{u}))
    (c : Cocone K) (hc : IsColimit c)
    (hK : ∀ i {X Y : Cᵒᵖ} (f : X ⟶ Y), IsIso (restrictionBaseChange (K.obj i).val f))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    IsIso (restrictionBaseChange c.pt.val f) :=
  isIso_restrictionBaseChange_sheafColimit (rings L) hR
    (fun N hN => isSheaf_of_cartesian hQ hL hJ N hN) K c hc hK f

end Stacks.FlatAffineSite

end
