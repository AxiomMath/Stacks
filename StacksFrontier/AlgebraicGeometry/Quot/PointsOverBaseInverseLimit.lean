module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineOverBase

/-!
# Inverse limits of the points of algebraic spaces affine over a base

Let `Y` be an algebraic space over a scheme `S` of a big fppf site and let `D` be a cofiltered
inverse system of algebraic spaces each carrying an affine morphism to `Y`.  The inverse limit
of `D` is again an algebraic space affine over `Y`, by Stacks 07SE, and this file reads that
statement on the test schemes over `Y`: the functor of points over `Y` of the limit is the
inverse limit of the functors of points over `Y` of the members.

The upshot is that `AlgebraicGeometry.Space.IsAffineAlgebraicSpaceOver`, the predicate on a
functor on the test schemes over `Y` of
`StacksFrontier/AlgebraicGeometry/Quot/RelativeHomRepresentable.lean`, is stable under cofiltered
inverse limits of functors.  This is the step
`\mathit{Hom}(\mathcal{F}, \mathcal{G}) = \lim \mathit{Hom}(\mathcal{F}_i, \mathcal{G})`
of the proof of Stacks 08K6, where the source cites Limits, Section 01YV and Limits of Spaces,
Section 07SE for exactly this: a cofiltered inverse limit of algebraic spaces affine over the
base is again one.

## Main definitions

* `AlgebraicGeometry.Space.spacePointsOverMap`: the map on points over `Y` induced by a
  morphism of algebraic spaces over `Y`.
* `AlgebraicGeometry.Space.systemProjection`: the structure morphism of a member of an
  inverse system of presheaves which is an algebraic space, read in
  `AlgebraicGeometry.AlgebraicSpaces`.
* `AlgebraicGeometry.Space.spacePointsSystem`: **the inverse system of the functors of points
  over `Y`** of the members of the system.
* `AlgebraicGeometry.Space.pointsSystemLimitSpace` and
  `AlgebraicGeometry.Space.limitStructureMorphism`: the inverse limit of the system, as an
  algebraic space over `Y`.
* `AlgebraicGeometry.Space.spacePointsLimitCone`: the cone on the system of functors of points
  whose vertex is the functor of points of the limit.

## Main results

* `AlgebraicGeometry.Space.isLimit_spacePointsLimitCone`: **the functor of points over `Y` of
  the inverse limit is the inverse limit of the functors of points over `Y`.**
* `AlgebraicGeometry.Space.isAffineHom_limitStructureMorphism`: the structure morphism of the
  limit is affine over `Y`, which is Stacks 07SE.
* `AlgebraicGeometry.Space.isAffineAlgebraicSpaceOver_of_isLimit`: **being an algebraic space
  affine over `Y` is stable under cofiltered inverse limits of functors on the test schemes
  over `Y`.**

## Implementation notes

**Why the members are given as a system of presheaves and not of algebraic spaces.**  The
hypotheses are `D : I ⥤ ((Sch/S)ᵒᵖ ⥤ Type u)` together with `τ : D ⟶ const Y`, `hD` saying that
each `D i` is an algebraic space, and `hτ` saying that each `τ i` is affine.  This is the shape
of the inputs in `StacksFrontier/AlgebraicGeometry/Spaces/Limits/AffineOverBase.lean`, where the
limit is formed as a presheaf and *then* shown to be an algebraic space; a system valued in
`AlgebraicGeometry.AlgebraicSpaces` would have to be pushed back into the presheaves to form
the limit, and the identification of the two constant functors at `Y` would then have to be
carried through every statement.  `AlgebraicGeometry.Space.systemProjection` packages a
member and its structure morphism in `AlgebraicGeometry.AlgebraicSpaces`, which is where
`spacePointsOver` wants them.

**The two cardinality hypotheses** are the ones carried by Stacks 07SF in this development, as
recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/AffineOverBase.lean`: they put the index category
below the cofinality of the site's size cutoff, which is what makes the limit exist inside the
site.  They are the set-theoretic condition the source's own footnote to the proof of
Stacks 08K6 omits to verify.

**Why the limit is read off at a chosen stage.**  The structure morphism of the limit is the
projection to a stage followed by the structure morphism of that stage, and
`AlgebraicGeometry.Space.limitπ_comp_app_eq'` says the result does not depend on the stage.
The choice of stage is therefore immaterial, and it is taken as an argument rather than
extracted from the cofilteredness of the index category so that a consumer which already has a
stage in hand may use it.

**The limit of the functors of points is computed pointwise**: the proof of
`isLimit_spacePointsLimitCone` goes through `evaluationJointlyReflectsLimits` and, at a test
scheme, the description of a limit in `Type u` as the sections of the diagram.  A section of
the system of points over `Y` is a compatible family of sections of the members lying over one
section of `Y`; the compatible family is a point of the limit by
`CategoryTheory.Limits.Types.isLimitEquivSections` applied to the evaluation of the limit cone,
and it lies over that section of `Y` because its component at the chosen stage does.

## References

* [Stacks Project, Tag 07SE](https://stacks.math.columbia.edu/tag/07SE)
* [Stacks Project, Tag 01YV](https://stacks.math.columbia.edu/tag/01YV)
* [Stacks Project, Tag 08K6](https://stacks.math.columbia.edu/tag/08K6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Y : AlgebraicSpaces B S hS}

/-! ### Functoriality of the points over the base -/

section Map

variable {H H' H'' : AlgebraicSpaces B S hS} {p : H ⟶ Y} {p' : H' ⟶ Y} {p'' : H'' ⟶ Y}

/-- Two sections of `H` lying over the section of `Y` that a test scheme is are equal as soon
as the underlying sections are. -/
theorem spacePointsOverObj_ext {T : SchemesOver Y} {x y : spacePointsOverObj p T}
    (h : x.1 = y.1) : x = y :=
  Subtype.ext h

/-- A morphism of algebraic spaces over `Y` carries a section of `H` lying over the section of
`Y` that a test scheme is to a section of `H'` lying over the same section. -/
theorem spacePointsOver_map_mem (k : H ⟶ H') (hk : k ≫ p' = p) (T : SchemesOver Y)
    (x : spacePointsOverObj p T) :
    p'.hom.app (Opposite.op T.left) (k.hom.app (Opposite.op T.left) x.1) = testPoint T := by
  have h : (k ≫ p').hom.app (Opposite.op T.left) x.1 = testPoint T := by
    rw [hk]; exact x.2
  simpa using h

/-- **The map on points over `Y` induced by a morphism of algebraic spaces over `Y`.**  A
morphism `k : H ⟶ H'` with `k ≫ p' = p` carries sections of `H` lying over the section of `Y`
that a test scheme is to sections of `H'` lying over the same section, naturally in the test
scheme. -/
def spacePointsOverMap (k : H ⟶ H') (hk : k ≫ p' = p) :
    spacePointsOver p ⟶ spacePointsOver p' where
  app T := ↾fun x ↦ ⟨k.hom.app (Opposite.op T.unop.left) x.1,
    spacePointsOver_map_mem k hk T.unop x⟩
  naturality T T' g := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦ Subtype.ext ?_
    exact NatTrans.naturality_apply k.hom g.unop.left.op x.1

/-- The map on points over `Y` induced by a morphism over `Y` depends only on the
morphism. -/
theorem spacePointsOverMap_congr {k k' : H ⟶ H'} (hk : k ≫ p' = p) (hk' : k' ≫ p' = p)
    (h : k = k') : spacePointsOverMap k hk = spacePointsOverMap k' hk' := by
  subst h; rfl

/-- The map on points over `Y` induced by an identity is the identity. -/
theorem spacePointsOverMap_id (hk : 𝟙 H ≫ p = p) :
    spacePointsOverMap (𝟙 H) hk = 𝟙 (spacePointsOver p) := by
  refine NatTrans.ext (funext fun T ↦ ConcreteCategory.hom_ext _ _ fun x ↦ Subtype.ext ?_)
  rfl

/-- The map on points over `Y` induced by a composite is the composite of the maps. -/
theorem spacePointsOverMap_comp (k : H ⟶ H') (k' : H' ⟶ H'') (hk : k ≫ p' = p)
    (hk' : k' ≫ p'' = p') (hkk : (k ≫ k') ≫ p'' = p) :
    spacePointsOverMap (k ≫ k') hkk =
      spacePointsOverMap k hk ≫ spacePointsOverMap k' hk' := by
  refine NatTrans.ext (funext fun T ↦ ConcreteCategory.hom_ext _ _ fun x ↦ Subtype.ext ?_)
  rfl

end Map

/-! ### The inverse system of the points over the base -/

section System

variable (B S hS)
variable {I : Type u} [Category.{u} I]
variable (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
variable (τ : D ⟶ (Functor.const I).obj Y.1) (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))

/-- The structure morphism of a member of the system, read as a morphism of algebraic
spaces.  A member itself is written out as the object `⟨D.obj i, hD i⟩` of
`AlgebraicGeometry.AlgebraicSpaces`, rather than through a wrapper of its own: the library has
no such wrapper, the only declaration named `stageAlgebraicSpace` being the field
`AlgebraicGeometry.Space.IntegralFiniteSystem.stageAlgebraicSpace` of
`StacksFrontier/AlgebraicGeometry/Spaces/AffineOfUniversallyClosedSurjection.lean:123`, which
records that each stage of a directed system is an algebraic space and packages nothing. -/
def systemProjection (i : I) : (⟨D.obj i, hD i⟩ : AlgebraicSpaces B S hS) ⟶ Y :=
  ObjectProperty.homMk (τ.app i)

/-- A transition morphism of the system, read as a morphism of algebraic spaces. -/
def systemTransition {i j : I} (φ : i ⟶ j) :
    (⟨D.obj i, hD i⟩ : AlgebraicSpaces B S hS) ⟶ (⟨D.obj j, hD j⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk (D.map φ)

/-- A transition morphism of the system is a morphism over `Y`. -/
theorem systemTransition_comp_projection {i j : I} (φ : i ⟶ j) :
    systemTransition B S hS D hD φ ≫ systemProjection B S hS D τ hD j =
      systemProjection B S hS D τ hD i := by
  refine ObjectProperty.hom_ext _ ?_
  change D.map φ ≫ τ.app j = τ.app i
  simp

/-- **The inverse system of the functors of points over `Y`** of the members of an inverse
system of algebraic spaces affine over `Y`: a transition morphism acts on sections by its own
action on sections of the members. -/
def spacePointsSystem : I ⥤ ((SchemesOver Y)ᵒᵖ ⥤ Type u) where
  obj i := spacePointsOver (systemProjection B S hS D τ hD i)
  map φ := spacePointsOverMap (systemTransition B S hS D hD φ)
    (systemTransition_comp_projection B S hS D τ hD φ)
  map_id i := by
    have hone : systemTransition B S hS D hD (𝟙 i) =
        𝟙 (⟨D.obj i, hD i⟩ : AlgebraicSpaces B S hS) :=
      ObjectProperty.hom_ext _ (by change D.map (𝟙 i) = 𝟙 (D.obj i); simp)
    have hid : 𝟙 (⟨D.obj i, hD i⟩ : AlgebraicSpaces B S hS) ≫
        systemProjection B S hS D τ hD i = systemProjection B S hS D τ hD i :=
      Category.id_comp _
    exact (spacePointsOverMap_congr
      (systemTransition_comp_projection B S hS D τ hD (𝟙 i)) hid hone).trans
      (spacePointsOverMap_id hid)
  map_comp {i j k} φ ψ := by
    have hcomp : systemTransition B S hS D hD (φ ≫ ψ) =
        systemTransition B S hS D hD φ ≫ systemTransition B S hS D hD ψ :=
      ObjectProperty.hom_ext _ (by change D.map (φ ≫ ψ) = D.map φ ≫ D.map ψ; simp)
    have hcc : (systemTransition B S hS D hD φ ≫ systemTransition B S hS D hD ψ) ≫
        systemProjection B S hS D τ hD k = systemProjection B S hS D τ hD i := by
      rw [Category.assoc, systemTransition_comp_projection, systemTransition_comp_projection]
    exact (spacePointsOverMap_congr
      (systemTransition_comp_projection B S hS D τ hD (φ ≫ ψ)) hcc hcomp).trans
      (spacePointsOverMap_comp _ _ (systemTransition_comp_projection B S hS D τ hD φ)
        (systemTransition_comp_projection B S hS D τ hD ψ) hcc)

/-- The value of the system of functors of points at a stage is the functor of points of that
stage. -/
theorem spacePointsSystem_obj (i : I) :
    (spacePointsSystem B S hS D τ hD).obj i =
      spacePointsOver (systemProjection B S hS D τ hD i) :=
  rfl

end System

/-! ### The limit of the system, and its points over the base -/

section Limit

variable (B S hS)
variable {I : Type u} [Category.{u} I] [IsPreconnected I]
variable (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
variable (τ : D ⟶ (Functor.const I).obj Y.1) (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))

/-- **The structure morphism of the limit does not depend on the stage at which it is read
off**, for any two stages of a connected system: the composite `lim D ⟶ D i ⟶ Y` is unchanged
along every morphism of the index category. -/
theorem limitπ_comp_app_eq' (i j : I) :
    limit.π D i ≫ τ.app i = limit.π D j ≫ τ.app j := by
  refine constant_of_preserves_morphisms (fun k : I => limit.π D k ≫ τ.app k) (fun k k' f => ?_)
    i j
  have hnat : D.map f ≫ τ.app k' = τ.app k := by simp
  rw [← hnat, ← Category.assoc, limit.w]

variable (hlim : IsAlgebraicSpace B S hS (limit D))

/-- **The limit of the system**, as an object of `AlgebraicGeometry.AlgebraicSpaces`, granted
that the limit presheaf is an algebraic space. -/
def pointsSystemLimitSpace : AlgebraicSpaces B S hS :=
  ⟨limit D, hlim⟩

/-- The projection of the limit to a member of the system, read as a morphism of algebraic
spaces. -/
def limitProjectionToStage (i : I) :
    pointsSystemLimitSpace B S hS D hlim ⟶ (⟨D.obj i, hD i⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk (limit.π D i)

/-- **The structure morphism of the limit to `Y`**: the projection to a stage followed by the
structure morphism of that stage. -/
def limitStructureMorphism (i₀ : I) : pointsSystemLimitSpace B S hS D hlim ⟶ Y :=
  ObjectProperty.homMk (limit.π D i₀ ≫ τ.app i₀)

/-- The projection of the limit to a member is a morphism over `Y`. -/
theorem limitProjectionToStage_comp_projection (i₀ i : I) :
    limitProjectionToStage B S hS D hD hlim i ≫ systemProjection B S hS D τ hD i =
      limitStructureMorphism B S hS D τ hlim i₀ := by
  refine ObjectProperty.hom_ext _ ?_
  change limit.π D i ≫ τ.app i = limit.π D i₀ ≫ τ.app i₀
  exact limitπ_comp_app_eq' B S hS D τ i i₀

/-- **The cone on the system of functors of points over `Y` whose vertex is the functor of
points over `Y` of the limit.**  Its leg at a stage is the map on points induced by the
projection of the limit to that stage. -/
def spacePointsLimitCone (i₀ : I) : Cone (spacePointsSystem B S hS D τ hD) where
  pt := spacePointsOver (limitStructureMorphism B S hS D τ hlim i₀)
  π :=
    { app i := spacePointsOverMap (limitProjectionToStage B S hS D hD hlim i)
        (limitProjectionToStage_comp_projection B S hS D τ hD hlim i₀ i)
      naturality := by
        intro i j φ
        have hstage : limitProjectionToStage B S hS D hD hlim i ≫
            systemTransition B S hS D hD φ = limitProjectionToStage B S hS D hD hlim j :=
          ObjectProperty.hom_ext _ (by change limit.π D i ≫ D.map φ = limit.π D j; simp)
        have hcc : (limitProjectionToStage B S hS D hD hlim i ≫
            systemTransition B S hS D hD φ) ≫ systemProjection B S hS D τ hD j =
            limitStructureMorphism B S hS D τ hlim i₀ := by
          rw [hstage]
          exact limitProjectionToStage_comp_projection B S hS D τ hD hlim i₀ j
        refine (Category.id_comp _).trans
          ((spacePointsOverMap_congr _ hcc hstage.symm).trans
            (spacePointsOverMap_comp _ _
              (limitProjectionToStage_comp_projection B S hS D τ hD hlim i₀ i)
              (systemTransition_comp_projection B S hS D τ hD φ) hcc)) }

/-- **The functor of points over `Y` of the limit is the limit of the functors of points over
`Y`.**

The claim is pointwise, by `CategoryTheory.Limits.evaluationJointlyReflectsLimits`, and at a
test scheme `T` it is the description of a limit in `Type u` as the sections of the diagram: a
compatible family of sections of the members of the system over the underlying scheme of `T` is
a section of the limit, and it lies over the section of `Y` that `T` is as soon as its component
at the chosen stage does. -/
def isLimit_spacePointsLimitCone (i₀ : I) :
    IsLimit (spacePointsLimitCone B S hS D τ hD hlim i₀) := by
  refine evaluationJointlyReflectsLimits _ fun T ↦ Nonempty.some
    ((Types.isLimit_iff _).mpr ?_)
  intro s hs
  have tW : IsLimit ((((evaluation ((BigFppfOver B S hS)ᵒᵖ) (Type u)).obj
      (Opposite.op T.unop.left))).mapCone (limit.cone D)) :=
    isLimitOfPreserves _ (limit.isLimit D)
  obtain ⟨x₀, hx₀, hx₀uniq⟩ := (Types.isLimit_iff _).mp ⟨tW⟩ (fun i ↦ (s i).1)
    fun φ ↦ congrArg Subtype.val (hs φ)
  have hx₀' : ∀ i, (limit.π D i).app (Opposite.op T.unop.left) x₀ = (s i).1 := fun i ↦ hx₀ i
  have hmem : (limitStructureMorphism B S hS D τ hlim i₀).hom.app
      (Opposite.op T.unop.left) x₀ = testPoint T.unop := by
    have h2 := (s i₀).2
    change (τ.app i₀).app (Opposite.op T.unop.left)
      ((limit.π D i₀).app (Opposite.op T.unop.left) x₀) = testPoint T.unop
    rw [hx₀' i₀]
    exact h2
  refine ⟨⟨x₀, hmem⟩, fun i ↦ spacePointsOverObj_ext (hx₀ i), fun x hx ↦ ?_⟩
  exact spacePointsOverObj_ext (hx₀uniq x.1 fun i ↦ congrArg Subtype.val (hx i))

end Limit

/-! ### Stability of the predicate under limits -/

section Predicate

variable (B S hS)
variable {I : Type u} [Category.{u} I] [IsPreconnected I]
variable (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
variable (τ : D ⟶ (Functor.const I).obj Y.1) (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))

/-- **Being an algebraic space affine over `Y` is stable under connected limits of functors on
the test schemes over `Y`, whenever the limit of the representing spaces is an algebraic space
affine over `Y`.**

Let `D` be a connected system of algebraic spaces over `Y` and let `R` be the vertex of a limit
cone on the universe lifts of their functors of points over `Y`.  If the limit of `D` is an
algebraic space whose structure morphism to `Y` is affine, then `R` is an algebraic space affine
over `Y`: the functor of points over `Y` of the limit is the limit of the functors of points
(`AlgebraicGeometry.Space.isLimit_spacePointsLimitCone`), and the universe lift preserves
limits. -/
theorem isAffineAlgebraicSpaceOver_of_isLimit (hlim : IsAlgebraicSpace B S hS (limit D))
    (i₀ : I) (haff : IsAffineHom B S hS (limit.π D i₀ ≫ τ.app i₀))
    {R : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1)}
    (c : Cone (spacePointsSystem B S hS D τ hD ⋙
      (Functor.whiskeringRight _ (Type u) (Type (u + 1))).obj uliftFunctor.{u + 1, u}))
    (hc : IsLimit c) (e : c.pt ≅ R) :
    IsAffineAlgebraicSpaceOver Y R := by
  refine ⟨pointsSystemLimitSpace B S hS D hlim, limitStructureMorphism B S hS D τ hlim i₀, haff,
    ⟨?_⟩⟩
  refine (IsLimit.conePointUniqueUpToIso
    (isLimitOfPreserves ((Functor.whiskeringRight _ (Type u) (Type (u + 1))).obj
      uliftFunctor.{u + 1, u})
      (isLimit_spacePointsLimitCone B S hS D τ hD hlim i₀)) hc).trans e

end Predicate

end AlgebraicGeometry.Space

end
