module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyCompactPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeApproximationOfNoetherianApproximation

/-!
# Approximation by algebraic spaces of finite presentation over a base

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` with `X` quasi-compact and
quasi-separated and `Y` quasi-separated. Stacks 09NS writes `X` as the limit of a directed inverse
system of algebraic spaces of finite presentation over `Y` with affine transition morphisms. This
file proves it from absolute Noetherian approximation over `Spec ℤ` (Stacks 07SU), which is the
one input taken as a hypothesis.

## Main results

* `exists_isLimit_isFinitePresentation_isAffineHom_of_noetherianApproximation`: Stacks 09NS,
  granted Stacks 07SU over `Spec ℤ`.
* `exists_isOpenSubspace_isQuasiCompactSpace_factor`: a morphism out of a quasi-compact algebraic
  space factors through a quasi-compact open subspace of its target.
* `isFinitePresentation_of_relocalizeMap` and `isAffineHom_of_relocalizeMap_of_isAlgebraicSpace`:
  finite presentation and affineness are inherited from the lower-shriek extension to a larger
  base.
* `isLimitPullbackSystemCone`: the base change of a cofiltered system of arrows to the limit of its
  targets has the limit of its sources as its limit (Stacks 002M).
* `isAffineHom_pullback_map_of_isAffineHom`: the induced morphism of fibre products along affine
  morphisms is affine.

All names are in the namespace `AlgebraicGeometry.Space`.

## Implementation notes

The source works with algebraic spaces over `Spec ℤ` for the relative approximation of Stacks
0GS3 and leaves the change of base implicit. Here it is explicit: the spaces over `S` are viewed
over `Spec ℤ` along the lower-shriek extension of Stacks 03I5, the stages are built there, and
they are brought back over `S` by the equivalence of Stacks 04SG between algebraic spaces over `S`
and algebraic spaces over `Spec ℤ` with a morphism to `S`. The quasi-compact open subspace of the
source's first step is taken over `Spec ℤ` as well.

## References

* [Stacks Project, Tag 09NS](https://stacks.math.columbia.edu/tag/09NS)
* [Stacks Project, Tag 0GS3](https://stacks.math.columbia.edu/tag/0GS3)
* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 002M](https://stacks.math.columbia.edu/tag/002M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v₁ v₂ u₁ u₂

namespace AlgebraicGeometry.Space

attribute [local instance] RelativeApproximation.preorder RelativeApproximation.nonempty
  RelativeApproximation.isDirected

/-! ### A quasi-compact open subspace through which a morphism factors -/

section Shrink

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- A morphism from a quasi-compact algebraic space to an algebraic space factors through a
quasi-compact open subspace of the target: the image of the point space of the source is
compact, so it is covered by finitely many quasi-compact open neighbourhoods (Stacks 04NN), whose
union is the point set of a quasi-compact open subspace (Stacks 03BZ, 03E4), and a morphism
whose image on points lies in an open subspace factors through it (Stacks 03IE). -/
theorem exists_isOpenSubspace_isQuasiCompactSpace_factor
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXqc : IsQuasiCompactSpace B S hS X) (f : X ⟶ Y) :
    ∃ V : Subfunctor Y, IsOpenSubspace B S hS V ∧ IsQuasiCompactSpace B S hS V.toFunctor ∧
      ∃ fV : X ⟶ V.toFunctor, fV ≫ V.ι = f := by
  classical
  have hcX : CompactSpace (points B S hS X) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS X hX).1 hXqc
  have hK : IsCompact (Set.range (pointsMap B S hS X f)) := by
    rw [← Set.image_univ]
    exact isCompact_univ.image (continuous_pointsMap B S hS f)
  have hnb : ∀ y ∈ Set.range (pointsMap B S hS X f),
      ∃ W : Set (points B S hS Y), IsOpen W ∧ IsCompact W ∧ y ∈ W := fun y _ =>
    let ⟨W, hW, _⟩ := (hasBasis_nhds_isOpen_isCompact B S hS Y hY y).mem_iff.mp Filter.univ_mem
    ⟨W, hW⟩
  choose! W hWo hWc hyW using hnb
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover W
    (fun y hy => (hWo y hy).mem_nhds (hyW y hy))
  have hopen : IsOpen (⋃ y ∈ t, W y) :=
    isOpen_biUnion fun y hy => hWo y (htK y hy)
  have hcompact : IsCompact (⋃ y ∈ t, W y) :=
    t.finite_toSet.isCompact_biUnion fun y hy => hWc y (htK y hy)
  obtain ⟨V, hV, hVrange⟩ := exists_isOpenSubspace_range_pointsMap_eq B S hS hY _ hopen
  refine ⟨V, hV, isQuasiCompactSpace_of_isCompact_range B S hS hY hV (hVrange ▸ hcompact), ?_⟩
  refine (factorsThrough_openSubspace_iff_points B S hS hY hX V hV f).2 ?_
  rw [hVrange]
  exact hcov

/-- The inclusion of a quasi-compact open subspace of a quasi-separated algebraic space is of
finite presentation: it is an open immersion, hence locally of finite presentation (Stacks 06CN);
it is quasi-compact by Stacks 073B, part (1); and it is a monomorphism, so its diagonal is an
isomorphism. -/
theorem isFinitePresentation_ι_of_isQuasiCompactSpace (hZ : B.Contains (⊤_ Scheme.{u}))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y) (V : Subfunctor Y)
    (hV : IsOpenSubspace B S hS V) (hVqc : IsQuasiCompactSpace B S hS V.toFunctor) :
    IsFinitePresentation B S hS V.ι := by
  refine ⟨isLocallyOfFinitePresentation_of_isOpenImmersion B S hS hV.2,
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hY hYqs hVqc V.ι, ?_⟩
  intro T _ hTqc g
  have : IsIso (pullback.diagonal V.ι) := (pullback.isIso_diagonal_iff V.ι).2 inferInstance
  exact isQuasiCompactSpace_of_iso B S hS (asIso (pullback.fst g (pullback.diagonal V.ι))).symm
    hTqc

end Shrink

/-! ### Reflecting finite presentation and affineness along the lower-shriek extension -/

section Reflect

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS)

/-- **A morphism of presheaves on the big fppf site of `W` is of finite presentation as soon as
its lower-shriek extension along `h : W ⟶ S` is.** Local finite presentation is an
every-étale-chart condition, which the extension does not change, and quasi-compactness and
quasi-separatedness are inherited from the extension. -/
theorem isFinitePresentation_of_relocalizeMap {X Y : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    (k : X ⟶ Y)
    (hk : IsFinitePresentation B S hS ((OverShriek.relocalizePresheafFunctor h).map k)) :
    IsFinitePresentation B W hW k :=
  ⟨(holdsOnEveryEtaleChart_relocalizeMap_iff B W S hW hS h _ k).1 hk.1,
    isQuasiCompact_of_relocalizeMap B W S hW hS h k hk.2.1,
    isQuasiSeparated_of_relocalizeMap B W S hW hS h k hk.2.2⟩

/-- **A morphism of algebraic spaces over `W` is affine as soon as its lower-shriek extension
along `h : W ⟶ S` is.** The extension of an affine morphism of algebraic spaces is representable
with affine representable base changes (Stacks 03WG), that property of representable base
changes is inherited from the extension, and it makes the original morphism affine. -/
theorem isAffineHom_of_relocalizeMap_of_isAlgebraicSpace
    {X Y : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u} (k : X ⟶ Y)
    (hX : IsAlgebraicSpace B W hW X) (hY : IsAlgebraicSpace B W hW Y)
    (hk : IsAffineHom B S hS ((OverShriek.relocalizePresheafFunctor h).map k)) :
    IsAffineHom B W hW k := by
  have : MorphismProperty.RespectsIso @_root_.AlgebraicGeometry.IsAffineHom.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨-, hp⟩ := ((isAffineHom_tfae_of_isAlgebraicSpace B S hS
    ((OverShriek.relocalizePresheafFunctor h).map k)
    (isAlgebraicSpace_viewOver B W S hW hS h X hX)
    (isAlgebraicSpace_viewOver B W S hW hS h Y hY)).out 2 1).mp hk
  exact isAffineHom_of_presheaf (presheaf_relocalizeMap_of B W S hW hS h _ k hp)

end Reflect

/-! ### Properties of isomorphic arrows -/

section ArrowIso

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- Affineness of a morphism depends only on its arrow up to isomorphism: two isomorphic arrows
form a cartesian square (Stacks 03WI). -/
theorem isAffineHom_of_iso_arrowMk (e : Arrow.mk f ≅ Arrow.mk f') (hf : IsAffineHom B S hS f) :
    IsAffineHom B S hS f' :=
  IsAffineHom.of_isPullback (IsPullback.of_horiz_isIso ⟨Arrow.w e.inv⟩) hf

end ArrowIso

/-! ### Base change of an inverse system of arrows to the limit of the targets -/

section PullbackSystem

variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C] {J : Type u₂} [Category.{v₂} J]
  (D : J ⥤ Arrow C) {X V : C} (f : X ⟶ V) (π : (Functor.const J).obj (Arrow.mk f) ⟶ D)

/-- The right component `V ⟶ Y_j` of a cone over an inverse system of arrows. -/
def arrowConeRight (j : J) : V ⟶ (D.obj j).right := (π.app j).right

/-- The left component `X ⟶ X_j` of a cone over an inverse system of arrows. -/
def arrowConeLeft (j : J) : X ⟶ (D.obj j).left := (π.app j).left

omit [HasPullbacks C] in
/-- The right components of a cone over an inverse system of arrows are compatible with the
transition morphisms of the targets. -/
@[reassoc (attr := simp)]
lemma arrowConeRight_comp {j j' : J} (a : j ⟶ j') :
    arrowConeRight D f π j ≫ (D.map a).right = arrowConeRight D f π j' := by
  simpa [arrowConeRight] using (congrArg (fun φ => φ.right) (π.naturality a)).symm

omit [HasPullbacks C] in
/-- The left components of a cone over an inverse system of arrows are compatible with the
transition morphisms of the sources. -/
@[reassoc (attr := simp)]
lemma arrowConeLeft_comp {j j' : J} (a : j ⟶ j') :
    arrowConeLeft D f π j ≫ (D.map a).left = arrowConeLeft D f π j' := by
  simpa [arrowConeLeft] using (congrArg (fun φ => φ.left) (π.naturality a)).symm

omit [HasPullbacks C] in
/-- The square of a leg of a cone over an inverse system of arrows. -/
@[reassoc]
lemma arrowConeLeft_hom (j : J) :
    arrowConeLeft D f π j ≫ (D.obj j).hom = f ≫ arrowConeRight D f π j :=
  Arrow.w (π.app j)

/-- The inverse system `j ↦ X_j ×_{Y_j} V` of base changes of the arrows `X_j ⟶ Y_j` of an
inverse system along the projections `V ⟶ Y_j` of the vertex of a cone. -/
@[reducible] noncomputable def pullbackSystem : J ⥤ C where
  obj j := pullback (D.obj j).hom (arrowConeRight D f π j)
  map {j j'} a := pullback.map _ _ _ _ (D.map a).left (𝟙 V) (D.map a).right
    (Arrow.w (D.map a)).symm (by simp)
  map_id j := by
    apply pullback.hom_ext <;> simp
  map_comp a b := by
    apply pullback.hom_ext <;> simp

/-- The object of `pullbackSystem D f π` at `j` is the fibre product `X_j ×_{Y_j} V`. -/
lemma pullbackSystem_obj (j : J) :
    (pullbackSystem D f π).obj j = pullback (D.obj j).hom (arrowConeRight D f π j) := rfl

/-- The transition morphisms of `pullbackSystem D f π` commute with the first projections. -/
@[reassoc (attr := simp)]
lemma pullbackSystem_map_fst {j j' : J} (a : j ⟶ j') :
    (pullbackSystem D f π).map a ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (D.map a).left :=
  pullback.lift_fst _ _ _

/-- The transition morphisms of `pullbackSystem D f π` commute with the second projections to
`V`. -/
@[reassoc (attr := simp)]
lemma pullbackSystem_map_snd {j j' : J} (a : j ⟶ j') :
    (pullbackSystem D f π).map a ≫ pullback.snd _ _ = pullback.snd _ _ :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The morphism `X ⟶ X_j ×_{Y_j} V` induced by the projection `X ⟶ X_j` and by `f`. -/
noncomputable def pullbackSystemLift (j : J) : X ⟶ (pullbackSystem D f π).obj j :=
  pullback.lift (arrowConeLeft D f π j) f (arrowConeLeft_hom D f π j)

/-- The first projection of `pullbackSystemLift D f π j` is the projection `X ⟶ X_j`. -/
@[reassoc (attr := simp)]
lemma pullbackSystemLift_fst (j : J) :
    pullbackSystemLift D f π j ≫ (pullback.fst _ _ : (pullbackSystem D f π).obj j ⟶ _) =
      arrowConeLeft D f π j :=
  pullback.lift_fst _ _ _

/-- The second projection of `pullbackSystemLift D f π j` is `f`. -/
@[reassoc (attr := simp)]
lemma pullbackSystemLift_snd (j : J) :
    pullbackSystemLift D f π j ≫ (pullback.snd _ _ : (pullbackSystem D f π).obj j ⟶ _) = f :=
  pullback.lift_snd _ _ _

/-- The cone with vertex `X` over the base-changed system, whose legs are induced by the
projections `X ⟶ X_j` and by `f`. -/
@[reducible] noncomputable def pullbackSystemCone : Cone (pullbackSystem D f π) where
  pt := X
  π :=
    { app j := pullbackSystemLift D f π j
      naturality a b g := by
        apply pullback.hom_ext <;> simp }

/-- The first projection of the leg of `pullbackSystemCone D f π` at `j` is the projection
`X ⟶ X_j`. -/
@[reassoc (attr := simp)]
lemma pullbackSystemCone_π_fst (j : J) :
    (pullbackSystemCone D f π).π.app j ≫ (pullback.fst _ _ : (pullbackSystem D f π).obj j ⟶ _) =
      arrowConeLeft D f π j :=
  pullback.lift_fst _ _ _

/-- The second projection of the leg of `pullbackSystemCone D f π` at `j` is `f`. -/
@[reassoc (attr := simp)]
lemma pullbackSystemCone_π_snd (j : J) :
    (pullbackSystemCone D f π).π.app j ≫ (pullback.snd _ _ : (pullbackSystem D f π).obj j ⟶ _) =
      f :=
  pullback.lift_snd _ _ _

/-- The projections `X_j ×_{Y_j} V ⟶ X_j`, a morphism to the system of sources. -/
noncomputable def pullbackSystemFst : pullbackSystem D f π ⟶ D ⋙ Comma.fst (𝟭 C) (𝟭 C) where
  app _ := pullback.fst _ _
  naturality _ _ _ := pullback.lift_fst _ _ _

/-- **Limits commute with base change (Stacks 002M).** If the sources and the targets of a
cofiltered system of arrows have limits `X` and `V` along a cone with vertex `f : X ⟶ V`, then
`X` is the limit of the base changes `X_j ×_{Y_j} V`. -/
noncomputable def isLimitPullbackSystemCone [IsCofiltered J]
    (hl : IsLimit ((Comma.fst (𝟭 C) (𝟭 C)).mapCone (Cone.mk (Arrow.mk f) π)))
    (hr : IsLimit ((Comma.snd (𝟭 C) (𝟭 C)).mapCone (Cone.mk (Arrow.mk f) π))) :
    IsLimit (pullbackSystemCone D f π) := by
  have hconst (s : Cone (pullbackSystem D f π)) (j j' : J) :
      s.π.app j ≫ pullback.snd _ _ = s.π.app j' ≫ pullback.snd _ _ := by
    rw [← s.w (IsCofiltered.minToLeft j j'), ← s.w (IsCofiltered.minToRight j j')]
    simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
  let lft (s : Cone (pullbackSystem D f π)) : s.pt ⟶ X :=
    hl.lift (Cone.mk s.pt (s.π ≫ pullbackSystemFst D f π))
  have hlft (s : Cone (pullbackSystem D f π)) (j : J) :
      lft s ≫ arrowConeLeft D f π j = s.π.app j ≫ pullback.fst _ _ :=
    hl.fac _ j
  have hsnd (s : Cone (pullbackSystem D f π)) (j : J) :
      lft s ≫ f = s.π.app j ≫ pullback.snd _ _ := by
    refine hr.hom_ext fun j' => ?_
    change (lft s ≫ f) ≫ arrowConeRight D f π j' =
      (s.π.app j ≫ pullback.snd _ _) ≫ arrowConeRight D f π j'
    rw [Category.assoc, ← arrowConeLeft_hom, ← Category.assoc, hlft, hconst s j j',
      Category.assoc, Category.assoc, pullback.condition]
  refine
    { lift := lft
      fac := fun s j => by
        apply pullback.hom_ext
        · change (lft s ≫ pullbackSystemLift D f π j) ≫ _ = _
          rw [Category.assoc, pullbackSystemLift_fst, hlft]
        · change (lft s ≫ pullbackSystemLift D f π j) ≫ _ = _
          rw [Category.assoc, pullbackSystemLift_snd, hsnd s j]
      uniq := fun s m hm => by
        refine hl.hom_ext fun j => ?_
        change m ≫ arrowConeLeft D f π j = lft s ≫ arrowConeLeft D f π j
        rw [hlft, ← hm j]
        simp }

end PullbackSystem

/-! ### Reading arrows through the equivalence of Stacks 04SG -/

section Transport

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- The lower-shriek extension of a morphism of presheaves on the big fppf site of `S` to the
big fppf site of `Spec ℤ` is, as an arrow, the underlying morphism of its image under the
equivalence of Stacks 04SG. -/
noncomputable def relocalizeArrowIso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : F ⟶ G) :
    Arrow.mk ((OverShriek.relocalizePresheafFunctor (integersMap B S hS hZ)).map k) ≅
      Arrow.mk ((smallerBasePresheafEquivalence B S (⊤_ Scheme.{u}) hS hZ
        (integersMap B S hS hZ)).functor.map k).left :=
  Arrow.isoMk ((smallerBasePresheafForgetIso B S (⊤_ Scheme.{u}) hS hZ
      (integersMap B S hS hZ)).app F).symm
    ((smallerBasePresheafForgetIso B S (⊤_ Scheme.{u}) hS hZ (integersMap B S hS hZ)).app G).symm
    ((smallerBasePresheafForgetIso B S (⊤_ Scheme.{u}) hS hZ
      (integersMap B S hS hZ)).inv.naturality k)

/-- The image under the equivalence of Stacks 04SG of the quasi-inverse image of a morphism `ψ`
of presheaves over the representable presheaf of `S` is, as an arrow, the underlying morphism of
`ψ`: the counit identifies the two. -/
noncomputable def counitArrowIso
    {A A' : Over (yoneda.obj (Over.mk (integersMap B S hS hZ)) :
      (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (ψ : A ⟶ A') :
    Arrow.mk ((smallerBasePresheafEquivalence B S (⊤_ Scheme.{u}) hS hZ
        (integersMap B S hS hZ)).functor.map
      ((smallerBasePresheafEquivalence B S (⊤_ Scheme.{u}) hS hZ
        (integersMap B S hS hZ)).inverse.map ψ)).left ≅ Arrow.mk ψ.left :=
  Arrow.isoMk ((Over.forget _).mapIso ((smallerBasePresheafEquivalence B S (⊤_ Scheme.{u}) hS hZ
      (integersMap B S hS hZ)).counitIso.app A))
    ((Over.forget _).mapIso ((smallerBasePresheafEquivalence B S (⊤_ Scheme.{u}) hS hZ
      (integersMap B S hS hZ)).counitIso.app A'))
    (congrArg CommaMorphism.left
      ((smallerBasePresheafEquivalence B S (⊤_ Scheme.{u}) hS hZ
        (integersMap B S hS hZ)).counitIso.hom.naturality ψ)).symm

/-- Composing with the inverse of the unit at the target does not change the image of a
morphism under the equivalence of Stacks 04SG, as an arrow. -/
noncomputable def unitInvArrowIso
    {A : Over (yoneda.obj (Over.mk (integersMap B S hS hZ)) :
      (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (φ : A ⟶ (smallerBasePresheafEquivalence B S (⊤_ Scheme.{u}) hS hZ
      (integersMap B S hS hZ)).functor.obj Y) :
    Arrow.mk ((smallerBasePresheafEquivalence B S (⊤_ Scheme.{u}) hS hZ
        (integersMap B S hS hZ)).functor.map
      ((smallerBasePresheafEquivalence B S (⊤_ Scheme.{u}) hS hZ
        (integersMap B S hS hZ)).inverse.map φ ≫
        (smallerBasePresheafEquivalence B S (⊤_ Scheme.{u}) hS hZ
          (integersMap B S hS hZ)).unitIso.inv.app Y)).left ≅
      Arrow.mk ((smallerBasePresheafEquivalence B S (⊤_ Scheme.{u}) hS hZ
        (integersMap B S hS hZ)).functor.map
      ((smallerBasePresheafEquivalence B S (⊤_ Scheme.{u}) hS hZ
        (integersMap B S hS hZ)).inverse.map φ)).left :=
  Arrow.isoMk (Iso.refl _) ((Over.forget _).mapIso
    ((smallerBasePresheafEquivalence B S (⊤_ Scheme.{u}) hS hZ
      (integersMap B S hS hZ)).functor.mapIso
      ((smallerBasePresheafEquivalence B S (⊤_ Scheme.{u}) hS hZ
        (integersMap B S hS hZ)).unitIso.app Y))) (by
    simp only [Arrow.mk_left, Arrow.mk_right, Iso.refl_hom, Category.id_comp, Arrow.mk_hom,
      Functor.mapIso_hom, Over.forget_map, Iso.app_hom]
    rw [← Over.comp_left, ← Functor.map_comp, Category.assoc, Iso.inv_hom_id_app]
    simp)

end Transport

/-! ### The base-changed stages of a relative approximation over `Spec ℤ` -/

section OverIntegers

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}
  {X V : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} {f : X ⟶ V}

/-- The morphisms `f_i : X_i ⟶ Y_i` of a relative approximation are of finite presentation: the
stages are quasi-compact, quasi-separated and of finite type over `Spec ℤ`, hence locally of
finite presentation over it (Stacks 06G4), so `f_i` is locally of finite presentation by Stacks
05WT, quasi-compact by Stacks 073B, part (1), and quasi-separated by Stacks 073B, part (2). -/
theorem RelativeApproximation.isFinitePresentation_hom (R : RelativeApproximation B hZ f)
    (j : R.Iᵒᵖ) : IsFinitePresentation B (⊤_ Scheme.{u}) hZ (R.diagram.obj j).hom := by
  have hX := R.isAlgebraicSpace_left j
  have hY := R.isAlgebraicSpace_right j
  have hlX := isLocallyOfFinitePresentation_terminal_of_isLocallyOfFiniteType_viewOverIntegers B hZ
    hX (R.isFiniteTypeOverIntegers_left j).1
  have hlY := isLocallyOfFinitePresentation_terminal_of_isLocallyOfFiniteType_viewOverIntegers B hZ
    hY (R.isFiniteTypeOverIntegers_right j).1
  refine ⟨isLocallyOfFinitePresentation_of_comp B (⊤_ Scheme.{u}) hZ hX hY
      (isAlgebraicSpace_terminal B (⊤_ Scheme.{u}) hZ) _ (terminal.from _)
      (by rwa [terminal.comp_from])
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B (⊤_ Scheme.{u}) hZ hlY),
    isQuasiCompact_of_isQuasiCompactSpace B (⊤_ Scheme.{u}) hZ hZ hY
      (R.isAbsolutelyQuasiSeparated_right j)
      (isQuasiCompactSpace_of_isQuasiCompact_viewOverIntegers B hZ
        (R.isFiniteTypeOverIntegers_left j).2) _,
    isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B (⊤_ Scheme.{u}) hZ hZ hX
      (R.isAbsolutelyQuasiSeparated_left j) _⟩

/-- **The induced morphism of fibre products over an affine morphism of bases is affine.**
Given a commutative diagram of algebraic spaces in which `i₁ : A ⟶ A'` and `i₃ : Y ⟶ Y'` are
affine and the second legs `V ⟶ Y ⟶ Y'` and `V ⟶ Y'` agree, the morphism
`A ×_Y V ⟶ A' ×_{Y'} V` factors as the base change of the diagonal of `i₃`, a closed immersion
because `i₃` is affine hence separated (Stacks 07U2), followed by the base change of `i₁`
(Stacks 03WI), and affine morphisms compose (Stacks 03WH). -/
theorem isAffineHom_pullback_map_of_isAffineHom (S : Scheme.{u}) (hS : B.Contains S)
    {A A' Y Y' V' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hj : A ⟶ Y) (rj : V' ⟶ Y)
    (hj' : A' ⟶ Y') (rj' : V' ⟶ Y') (i₁ : A ⟶ A') (i₃ : Y ⟶ Y')
    (w₁ : hj ≫ i₃ = i₁ ≫ hj') (w₂ : rj ≫ i₃ = 𝟙 _ ≫ rj')
    (hY : IsAlgebraicSpace B S hS Y) (hY' : IsAlgebraicSpace B S hS Y')
    (hi₁ : IsAffineHom B S hS i₁) (hi₃ : IsAffineHom B S hS i₃) :
    IsAffineHom B S hS (pullback.map hj rj hj' rj' i₁ (𝟙 _) i₃ w₁ w₂) := by
  have e₁ : (hj ≫ i₃) ≫ 𝟙 _ = i₁ ≫ hj' := by rw [Category.comp_id, w₁]
  have e₂ : (rj ≫ i₃) ≫ 𝟙 _ = 𝟙 _ ≫ rj' := by rw [Category.comp_id, w₂]
  let m₁ := pullback.map hj rj (hj ≫ i₃) (rj ≫ i₃) (𝟙 _) (𝟙 _) i₃
    (Category.id_comp _).symm (Category.id_comp _).symm
  let m₂ := pullback.map (hj ≫ i₃) (rj ≫ i₃) hj' rj' i₁ (𝟙 _) (𝟙 _) e₁ e₂
  have hm : pullback.map hj rj hj' rj' i₁ (𝟙 _) i₃ w₁ w₂ = m₁ ≫ m₂ := by
    apply pullback.hom_ext <;> simp [m₁, m₂]
  have hΔ : IsAffineHom B S hS (pullback.diagonal i₃) :=
    isAffineHom_of_isClosedImmersion B S hS _ (isSeparated_of_isAffineHom B S hS i₃ hY hY' hi₃)
  have h₁ : IsAffineHom B S hS m₁ :=
    IsAffineHom.of_isPullback (pullback_map_diagonal_isPullback hj rj i₃) hΔ
  have e₂' : rj ≫ i₃ = rj' := by rw [w₂, Category.id_comp]
  have h0 := (congrArg₂ (IsPullback (pullback.fst (hj ≫ i₃) (rj ≫ i₃))
    (pullback.snd (hj ≫ i₃) (rj ≫ i₃))) w₁ e₂').mp (IsPullback.of_hasPullback _ _)
  have hsnd : m₂ ≫ pullback.snd hj' rj' = pullback.snd (hj ≫ i₃) (rj ≫ i₃) := by
    simp [m₂]
  have hsq : IsPullback m₂ (pullback.fst (hj ≫ i₃) (rj ≫ i₃)) (pullback.fst hj' rj') i₁ :=
    IsPullback.of_right (by rw [hsnd]; exact h0.flip) (by simp [m₂])
      (IsPullback.of_hasPullback hj' rj').flip
  have h₂ : IsAffineHom B S hS m₂ := IsAffineHom.of_isPullback hsq.flip hi₁
  rw [hm]
  exact isAffineHom_comp B S hS m₁ m₂ h₁ h₂

/-- The transition morphisms of the base changes `X_j ×_{Y_j} V` of a relative approximation
are affine. -/
theorem RelativeApproximation.isAffineHom_pullbackSystem_map (R : RelativeApproximation B hZ f)
    {j j' : R.Iᵒᵖ} (a : j ⟶ j') :
    IsAffineHom B (⊤_ Scheme.{u}) hZ ((pullbackSystem R.diagram f R.π).map a) :=
  isAffineHom_pullback_map_of_isAffineHom (⊤_ Scheme.{u}) hZ _ _ _ _ _ _
    (Arrow.w (R.diagram.map a)).symm (by simp) (R.isAlgebraicSpace_right j)
    (R.isAlgebraicSpace_right j') (R.isAffineHom_left a)
    (R.isAffineHom_right a)

end OverIntegers

/-! ### Stacks 09NS from absolute Noetherian approximation -/

section Main

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 09NS, from absolute Noetherian approximation over `Spec ℤ`.** Let `f : X ⟶ Y` be a
morphism of algebraic spaces over a scheme `S` with `X` quasi-compact and quasi-separated and `Y`
quasi-separated. Then `X = lim X_i` is the limit of a directed inverse system of algebraic spaces
`X_i` over `S` equipped with morphisms `X_i ⟶ Y` of finite presentation, compatible with the
transition morphisms, which are affine; the limit cone has vertex `X` and induces `f`.

The only input not proved here is `h07SU`, the content of Stacks 07SU over `Spec ℤ`: every
quasi-compact quasi-separated algebraic space over `Spec ℤ` is the limit of a directed system of
quasi-separated algebraic spaces of finite type over `Spec ℤ` with affine transition morphisms,
with no condition on the size of the index set.

The proof is the source's. Viewed over `Spec ℤ` along the lower-shriek extension (Stacks 03I5),
`X` stays quasi-compact and quasi-separated and `Y` quasi-separated, and the image of `X` lies in
a quasi-compact open subspace `V` of `Y`, whose inclusion is of finite presentation. Relative
approximation (Stacks 0GS3, from `h07SU` for `X` and for `V`, the approximations being first
replaced by the systems of scheme-theoretic images of their projections) writes `X ⟶ V` as the
limit of morphisms `X_i ⟶ V_i` of finite presentation; the base changes `X_i ×_{V_i} V` have
limit `X` (Stacks 002M), affine transition morphisms (Stacks 03KN, 03WI, 03WH), and finitely
presented morphisms to `V` (Stacks 03XR), hence to `Y` (Stacks 03XQ). Each of them maps to `Y`
and hence to the representable presheaf of `S`, so the equivalence of Stacks 04SG returns it to
an algebraic space over `S`; finite presentation and affineness are inherited from the
extension, and the equivalence preserves the limit.

The index set lives in `Type (u + 1)`: it is the set of triples of a stage of each of the two
approximations and a morphism between them, as in Stacks 0GS3. -/
theorem exists_isLimit_isFinitePresentation_isAffineHom_of_noetherianApproximation
    (h07SU : ∀ Z : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ Z → IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ Z →
        IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ Z →
          HasNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ Z)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXqc : IsQuasiCompactSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y) :
    ∃ (I : Type (u + 1)) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : Iᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
      (t : D ⟶ (Functor.const Iᵒᵖ).obj Y) (p : (Functor.const Iᵒᵖ).obj X ⟶ D)
      (_ : IsLimit (Cone.mk X p)),
      p ≫ t = (Functor.const Iᵒᵖ).map f ∧
        (∀ i, IsAlgebraicSpace B S hS (D.obj i)) ∧
        (∀ i, IsFinitePresentation B S hS (t.app i)) ∧
        (∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom B S hS (D.map a)) := by
  classical
  let g := integersMap B S hS hZ
  let Λ := OverShriek.relocalizePresheafFunctor g
  let E := smallerBasePresheafEquivalence B S (⊤_ Scheme.{u}) hS hZ g
  let ι := smallerBasePresheafForgetIso B S (⊤_ Scheme.{u}) hS hZ g
  have hΛX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (Λ.obj X) :=
    isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ g X hX
  have hΛY : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (Λ.obj Y) :=
    isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ g Y hY
  have hΛXqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ (Λ.obj X) :=
    isQuasiCompactSpace_relocalizePresheafFunctor_obj B S (⊤_ Scheme.{u}) hS hZ g X hXqc
  have hΛXqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (Λ.obj X) :=
    isAbsolutelyQuasiSeparated_viewOverIntegers B S hS hZ X hXqs
  have hΛYqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (Λ.obj Y) :=
    isAbsolutelyQuasiSeparated_viewOverIntegers B S hS hZ Y hYqs
  obtain ⟨V, hV, hVqc, fV, hfV⟩ := exists_isOpenSubspace_isQuasiCompactSpace_factor B
    (⊤_ Scheme.{u}) hZ hΛX hΛY hΛXqc (Λ.map f)
  have hVfp := isFinitePresentation_ι_of_isQuasiCompactSpace B (⊤_ Scheme.{u}) hZ hZ hΛY hΛYqs
    V hV hVqc
  have hVqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ V.toFunctor :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ hV.1 hΛYqs hVfp.2.2
  obtain ⟨R, ⟨hl⟩, ⟨hr⟩⟩ :=
    exists_relativeApproximation_isLimit_fst_snd_of_hasNoetherianApproximation fV hΛX hV.1
      (h07SU _ hΛX hΛXqc hΛXqs) (h07SU _ hV.1 hVqc hVqs)
  let : IsConnected R.Iᵒᵖ := IsCofiltered.isConnected _
  let P := pullbackSystem R.diagram fV R.π
  let c := pullbackSystemCone R.diagram fV R.π
  have hc : IsLimit c := isLimitPullbackSystemCone R.diagram fV R.π hl hr
  have hP (j : R.Iᵒᵖ) : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (P.obj j) :=
    isAlgebraicSpace_pullback B (⊤_ Scheme.{u}) hZ _ _ (R.isAlgebraicSpace_left j) hV.1
      (R.isAlgebraicSpace_right j)
  have hEY : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (E.functor.obj Y).left :=
    isAlgebraicSpace_of_iso B (⊤_ Scheme.{u}) hZ (ι.app Y).symm hΛY
  let q : V.toFunctor ⟶ (E.functor.obj Y).left := V.ι ≫ ι.inv.app Y
  have hqfp : IsFinitePresentation B (⊤_ Scheme.{u}) hZ q :=
    isFinitePresentation_of_arrowIso B (⊤_ Scheme.{u}) hZ V.ι q (𝟙 _) (ι.inv.app Y)
      (by simp [q]) hVfp
  have hsndfp (j : R.Iᵒᵖ) :
      IsFinitePresentation B (⊤_ Scheme.{u}) hZ (pullback.snd _ _ ≫ q : P.obj j ⟶ _) :=
    isFinitePresentation_comp B (⊤_ Scheme.{u}) hZ (hP j) hV.1 hEY _ q
      (IsFinitePresentation.of_isPullback B (⊤_ Scheme.{u}) hZ (hP j)
        (R.isAlgebraicSpace_left j) hV.1 (R.isAlgebraicSpace_right j)
        (IsPullback.of_hasPullback _ _) (R.isFinitePresentation_hom j)) hqfp
  let Zh : R.Iᵒᵖ ⥤ Over (yoneda.obj (Over.mk g)) :=
    P.toOver _ (fun j => pullback.snd _ _ ≫ q ≫ (E.functor.obj Y).hom) (fun a => by simp [P])
  let φ (j : R.Iᵒᵖ) : Zh.obj j ⟶ E.functor.obj Y :=
    Over.homMk (pullback.snd _ _ ≫ q) (Category.assoc _ _ _)
  have hιf : ι.hom.app X ≫ Λ.map f ≫ ι.inv.app Y = (E.functor.map f).left := by
    rw [← Category.assoc, ← ι.hom.naturality f]
    simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    rfl
  have hlift (j : R.Iᵒᵖ) :
      (ι.hom.app X ≫ pullbackSystemLift R.diagram fV R.π j) ≫ pullback.snd _ _ ≫ q =
        (E.functor.map f).left := by
    rw [Category.assoc, ← Category.assoc (pullbackSystemLift R.diagram fV R.π j),
      pullbackSystemLift_snd R.diagram fV R.π j, ← hιf, ← hfV]
    simp only [Category.assoc, q]
  have hσw (j : R.Iᵒᵖ) : (ι.hom.app X ≫ c.π.app j) ≫ (Zh.obj j).hom =
      (E.functor.obj X).hom := by
    change (ι.hom.app X ≫ pullbackSystemLift R.diagram fV R.π j) ≫ pullback.snd _ _ ≫ q ≫
      (E.functor.obj Y).hom = _
    simpa only [Category.assoc, Over.w] using hlift j =≫ (E.functor.obj Y).hom
  let c0 : Cone Zh :=
    { pt := E.functor.obj X
      π :=
        { app := fun j => Over.homMk (ι.hom.app X ≫ c.π.app j) (hσw j)
          naturality := fun j j' a => by
            apply Over.OverMorphism.ext
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
              Over.comp_left, Over.homMk_left]
            rw [← c.w a]
            rfl } }
  have hc0 : IsLimit c0 :=
    isLimitOfReflects (Over.forget _)
      (IsLimit.ofIsoLimit hc (Cones.ext (ι.app X).symm (fun j => by
        change c.π.app j = ι.inv.app X ≫ (ι.hom.app X ≫ c.π.app j)
        simp)))
  have hσφ (j : R.Iᵒᵖ) : c0.π.app j ≫ φ j = E.functor.map f := by
    apply Over.OverMorphism.ext
    exact hlift j
  let D : R.Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u := Zh ⋙ E.inverse
  let p : (Functor.const R.Iᵒᵖ).obj X ⟶ D :=
    { app := fun j => E.unitIso.hom.app X ≫ E.inverse.map (c0.π.app j)
      naturality := fun j j' a => by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, D,
          Functor.comp_map, Category.assoc, ← Functor.map_comp]
        rw [← c0.w a] }
  let t : D ⟶ (Functor.const R.Iᵒᵖ).obj Y :=
    { app := fun j => E.inverse.map (φ j) ≫ E.unitIso.inv.app Y
      naturality := fun j j' a => by
        have h : Zh.map a ≫ φ j' = φ j :=
          Over.OverMorphism.ext (pullbackSystem_map_snd_assoc R.diagram fV R.π a q)
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, D,
          Functor.comp_map, ← Category.assoc, ← Functor.map_comp, h] }
  have hp : IsLimit (Cone.mk X p) :=
    IsLimit.ofIsoLimit (isLimitOfPreserves E.inverse hc0)
      (Cones.ext (E.unitIso.app X).symm (fun j => by simp [p]))
  have hD (j : R.Iᵒᵖ) : IsAlgebraicSpace B S hS (D.obj j) :=
    isAlgebraicSpace_smallerBasePresheafEquivalence_inverse B S (⊤_ Scheme.{u}) hS hZ g (Zh.obj j)
      (hP j)
  refine ⟨R.I, inferInstance, inferInstance, inferInstance, D, t, p, hp, ?_, hD, ?_, ?_⟩
  · ext j : 2
    have h := E.unitIso.hom.naturality f
    dsimp at h
    simp only [NatTrans.comp_app, p, t, Functor.const_obj_obj, Functor.const_map_app,
      Category.assoc]
    rw [← Functor.map_comp_assoc, hσφ, ← Category.assoc, ← h]
    simp
  · intro j
    refine isFinitePresentation_of_relocalizeMap B S (⊤_ Scheme.{u}) hS hZ g (t.app j) ?_
    let e := (counitArrowIso B S hS hZ (φ j)).symm ≪≫ (unitInvArrowIso B S hS hZ (φ j)).symm ≪≫
      (relocalizeArrowIso B S hS hZ (t.app j)).symm
    exact isFinitePresentation_of_arrowIso B (⊤_ Scheme.{u}) hZ _ _ e.hom.left e.hom.right
      (Arrow.w e.hom) (hsndfp j)
  · intro j j' a
    refine isAffineHom_of_relocalizeMap_of_isAlgebraicSpace B S (⊤_ Scheme.{u}) hS hZ g (D.map a)
      (hD j) (hD j') ?_
    exact isAffineHom_of_iso_arrowMk
      ((counitArrowIso B S hS hZ (Zh.map a)).symm ≪≫
        (relocalizeArrowIso B S hS hZ (E.inverse.map (Zh.map a))).symm)
      (R.isAffineHom_pullbackSystem_map a)

end Main

end AlgebraicGeometry.Space

end
