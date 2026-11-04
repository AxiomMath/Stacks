module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.AffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImmersionFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase

/-!
# Noetherian approximations with scheme-theoretically dominant projections

Let `X = lim X_j` be a Noetherian approximation of an algebraic space `X` over `S`. Replacing each
stage `X_j` by the scheme-theoretic image `X'_j` of the projection `X ⟶ X_j` gives again a
Noetherian approximation of `X`, now with projections `X ⟶ X'_j` whose scheme-theoretic images
are everything. The stages stay quasi-separated and of finite type over `Spec ℤ`, being closed
subspaces of the old ones, the transition morphisms stay affine (Stacks 08GB, part (2)), and `X`
is still their limit, the inclusions `X'_j ⟶ X_j` being monomorphisms.

Without a bound on the size of the index set, the limit of an inverse system of presheaves on a
big fppf site may be much smaller than the limit of the corresponding schemes, and the limit
criteria of Stacks 0CP4 then fail (an uncountable field is the colimit of its finitely generated
subrings, while the presheaf limit of their spectra is empty). Dominant projections are what
excludes this.

The construction works for the limit cone of any inverse system of algebraic spaces with affine
transition morphisms, and is set up in that generality first.

## Main results

* `AlgebraicGeometry.Space.coneImageCone` and `AlgebraicGeometry.Space.isLimitConeImageCone`:
  for a limit cone `c` of a system `F` of algebraic spaces, the system of scheme-theoretic images
  of the projections of `c`, and the cone with point `c.pt` over it, again a limit cone; its
  stages are closed subspaces (`isClosedSubspace_coneImageStage`), its transition morphisms are
  affine when those of `F` are (`isAffineHom_coneImageMap`), and its projections are
  scheme-theoretically dominant (`schemeTheoreticImageSubfunctor_coneImageCone_π`).
* `AlgebraicGeometry.Space.NoetherianApproximation.image`: the approximation by the
  scheme-theoretic images of the projections.
* `AlgebraicGeometry.Space.NoetherianApproximation.schemeTheoreticImageSubfunctor_image_π`: its
  projections are scheme-theoretically dominant.
* `AlgebraicGeometry.Space.exists_noetherianApproximation_dominant`: a space with a Noetherian
  approximation has one with scheme-theoretically dominant projections.

## References

* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 0CP2](https://stacks.math.columbia.edu/tag/0CP2)
* [Stacks Project, Tag 08GB](https://stacks.math.columbia.edu/tag/08GB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] NoetherianApproximation.preorder NoetherianApproximation.nonempty
  NoetherianApproximation.isDirected

section ConeImage

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {J : Type*} [Category J] {F : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hF : ∀ j, IsAlgebraicSpace B S hS (F.obj j)) (c : Cone F)

/-- The scheme-theoretic image of the projection of the cone point of `c` to the stage `j`. -/
abbrev coneImageStage (j : J) : Subfunctor (F.obj j) :=
  schemeTheoreticImageSubfunctor B S hS (c.π.app j)

/-- The square of a transition morphism and two projections of a cone. -/
lemma cone_π_comp_map {j j' : J} (g : j ⟶ j') :
    c.π.app j ≫ F.map g = 𝟙 c.pt ≫ c.π.app j' := by
  rw [Category.id_comp, c.w]

/-- The transition morphism between the scheme-theoretic images of two projections. -/
noncomputable def coneImageMap {j j' : J} (g : j ⟶ j') :
    (coneImageStage c j).toFunctor ⟶ (coneImageStage c j').toFunctor :=
  schemeTheoreticImageMap B S hS (hF j) (hF j') (cone_π_comp_map c g)

/-- The transition morphism between the images commutes with the inclusions into the stages. -/
@[reassoc (attr := simp)]
lemma coneImageMap_ι {j j' : J} (g : j ⟶ j') :
    coneImageMap hF c g ≫ (coneImageStage c j').ι = (coneImageStage c j).ι ≫ F.map g :=
  schemeTheoreticImageMap_ι B S hS _ _ _

/-- The inverse system of the scheme-theoretic images of the projections of a cone. -/
@[reducible] noncomputable def coneImageDiagram : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u where
  obj j := (coneImageStage c j).toFunctor
  map g := coneImageMap hF c g
  map_id j := (cancel_mono (coneImageStage c j).ι).1 (by simp)
  map_comp g g' := (cancel_mono (coneImageStage c _).ι).1 (by simp)

/-- The factorizations of the projections of a cone through their scheme-theoretic images. -/
noncomputable def coneImageπ : (Functor.const J).obj c.pt ⟶ coneImageDiagram hF c where
  app j := toSchemeTheoreticImage B S hS (c.π.app j)
  naturality j j' g := by
    refine (cancel_mono (coneImageStage c j').ι).1 ?_
    change (𝟙 c.pt ≫ toSchemeTheoreticImage B S hS (c.π.app j')) ≫ _ =
      (toSchemeTheoreticImage B S hS (c.π.app j) ≫ coneImageMap hF c g) ≫ _
    rw [Category.id_comp, toSchemeTheoreticImage_ι, Category.assoc, coneImageMap_ι,
      ← Category.assoc, toSchemeTheoreticImage_ι, cone_π_comp_map c g, Category.id_comp]

/-- The cone with the same point over the system of scheme-theoretic images. -/
@[reducible] noncomputable def coneImageCone : Cone (coneImageDiagram hF c) :=
  Cone.mk c.pt (coneImageπ hF c)

/-- The projections of `coneImageCone hF c`, followed by the inclusions into the stages, are the
projections of `c`. -/
@[reassoc (attr := simp)]
lemma coneImageCone_π_ι (j : J) :
    (coneImageCone hF c).π.app j ≫ (coneImageStage c j).ι = c.π.app j :=
  toSchemeTheoreticImage_ι B S hS (c.π.app j)

/-- A cone over the system of images, composed with the inclusions into the stages. -/
@[reducible] noncomputable def coneOfConeImageCone (s : Cone (coneImageDiagram hF c)) : Cone F :=
  Cone.mk s.pt
    { app j := s.π.app j ≫ (coneImageStage c j).ι
      naturality j j' g := by
        refine (Category.id_comp _).trans ?_
        rw [← s.w g, Category.assoc, Category.assoc]
        exact congrArg (s.π.app j ≫ ·) (coneImageMap_ι hF c g) }

variable {c} in
/-- A limit of a system is also the limit of the scheme-theoretic images of its projections. -/
noncomputable def isLimitConeImageCone (hc : IsLimit c) : IsLimit (coneImageCone hF c) where
  lift s := hc.lift (coneOfConeImageCone hF c s)
  fac s j := by
    refine (cancel_mono (coneImageStage c j).ι).1 ?_
    rw [Category.assoc, coneImageCone_π_ι]
    exact hc.fac _ j
  uniq s m hm := by
    refine hc.uniq (coneOfConeImageCone hF c s) m fun j => ?_
    change m ≫ c.π.app j = s.π.app j ≫ (coneImageStage c j).ι
    rw [← hm j, Category.assoc, coneImageCone_π_ι]

include hF in
/-- The stages of the image system are closed subspaces of the original stages. -/
theorem isClosedSubspace_coneImageStage (j : J) : IsClosedSubspace B S hS (coneImageStage c j) :=
  isClosedSubspace_schemeTheoreticImageSubfunctor B S hS _ (hF j)

/-- The transition morphisms of the image system are affine when those of the system are:
composed with the inclusion, a closed immersion and hence separated, they give an affine
morphism (Stacks 08GB, part (2)). -/
theorem isAffineHom_coneImageMap (hAff : ∀ {j j' : J} (g : j ⟶ j'), IsAffineHom B S hS (F.map g))
    {j j' : J} (g : j ⟶ j') : IsAffineHom B S hS (coneImageMap hF c g) := by
  refine isAffineHom_of_isAffineHom_comp_of_isSeparated B S hS _ (coneImageStage c j').ι ?_
    (isSeparated_of_isClosedImmersion B S hS _ (isClosedSubspace_coneImageStage hF c j').2)
  rw [coneImageMap_ι]
  exact isAffineHom_comp B S hS _ _
    (isAffineHom_of_isClosedImmersion B S hS _ (isClosedSubspace_coneImageStage hF c j).2)
    (hAff g)

/-- The projections of the image cone are scheme-theoretically dominant. -/
theorem schemeTheoreticImageSubfunctor_coneImageCone_π (j : J) :
    schemeTheoreticImageSubfunctor B S hS ((coneImageCone hF c).π.app j) = ⊤ :=
  schemeTheoreticImageSubfunctor_toSchemeTheoreticImage_eq_top B S hS (c.π.app j) (hF j)

include hF in
/-- The stages of the image system are quasi-separated when those of the system are, being
closed subspaces of them (Stacks 04ZH, part (2)). -/
theorem isAbsolutelyQuasiSeparated_coneImageStage {hZ : B.Contains (⊤_ Scheme.{u})} {j : J}
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ (F.obj j)) :
    IsAbsolutelyQuasiSeparated B S hS hZ (coneImageStage c j).toFunctor :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ
    (isClosedSubspace_coneImageStage hF c j).1 hqs
    (isQuasiSeparated_of_isClosedImmersion B S hS (isClosedSubspace_coneImageStage hF c j).2)

end ConeImage

namespace NoetherianApproximation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (A : NoetherianApproximation B S hS hZ X)

/-- The scheme-theoretic image of the projection of `X` to the stage `j`. -/
abbrev imageStage (j : A.Iᵒᵖ) : Subfunctor (A.diagram.obj j) :=
  coneImageStage (Cone.mk X A.π) j

/-- The stages of the image system are closed subspaces of the original stages. -/
theorem isClosedSubspace_imageStage (j : A.Iᵒᵖ) : IsClosedSubspace B S hS (A.imageStage j) :=
  isClosedSubspace_coneImageStage A.isAlgebraicSpace _ j

/-- The stages of the image system are quasi-separated, being closed subspaces of
quasi-separated algebraic spaces (Stacks 04ZH, part (2)). -/
theorem isAbsolutelyQuasiSeparated_imageStage (j : A.Iᵒᵖ) :
    IsAbsolutelyQuasiSeparated B S hS hZ (A.imageStage j).toFunctor :=
  isAbsolutelyQuasiSeparated_coneImageStage A.isAlgebraicSpace _ (A.isAbsolutelyQuasiSeparated j)

/-- The stages of the image system are of finite type over `Spec ℤ`: viewed over `Spec ℤ`, the
inclusion into the original stage stays a closed immersion, hence of finite type, and composes
with the structure morphism of that stage. -/
theorem isFiniteTypeOverIntegers_imageStage (j : A.Iᵒᵖ) :
    IsFiniteType B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B S hS hZ (A.imageStage j).toFunctor)) := by
  let g : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  have : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hcl : IsClosedImmersion B (⊤_ Scheme.{u}) hZ
      ((OverShriek.relocalizePresheafFunctor g).map (A.imageStage j).ι) :=
    OverShriek.presheaf_map_relocalize g (fun _ hk => hk) (A.isClosedSubspace_imageStage j).2
  have h := isFiniteType_comp B (⊤_ Scheme.{u}) hZ
    (isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ g _ (A.isClosedSubspace_imageStage j).1)
    (isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ g _ (A.isAlgebraicSpace j))
    (isAlgebraicSpace_terminal B (⊤_ Scheme.{u}) hZ) _ _
    (isFiniteType_of_isClosedImmersion B (⊤_ Scheme.{u}) hZ _ hcl) (A.isFiniteTypeOverIntegers j)
  rwa [terminal.comp_from] at h

/-- **The approximation by the scheme-theoretic images of the projections.** -/
noncomputable def image (_hX : IsAlgebraicSpace B S hS X) :
    NoetherianApproximation B S hS hZ X where
  I := A.I
  diagram := coneImageDiagram A.isAlgebraicSpace (Cone.mk X A.π)
  isAlgebraicSpace j := (A.isClosedSubspace_imageStage j).1
  isAffineHom_map g := isAffineHom_coneImageMap A.isAlgebraicSpace _ A.isAffineHom_map g
  isAbsolutelyQuasiSeparated j := A.isAbsolutelyQuasiSeparated_imageStage j
  isFiniteTypeOverIntegers j := A.isFiniteTypeOverIntegers_imageStage j
  π := coneImageπ A.isAlgebraicSpace (Cone.mk X A.π)
  isLimit := isLimitConeImageCone A.isAlgebraicSpace A.isLimit

/-- **The projections of the image approximation are scheme-theoretically dominant.** -/
theorem schemeTheoreticImageSubfunctor_image_π (hX : IsAlgebraicSpace B S hS X)
    (j : (A.image hX).Iᵒᵖ) :
    schemeTheoreticImageSubfunctor B S hS ((A.image hX).π.app j) = ⊤ :=
  schemeTheoreticImageSubfunctor_coneImageCone_π A.isAlgebraicSpace (Cone.mk X A.π) j

end NoetherianApproximation

/-- **A space with a Noetherian approximation has one whose projections are
scheme-theoretically dominant.** -/
theorem exists_noetherianApproximation_dominant {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (h : HasNoetherianApproximation B S hS hZ X) :
    ∃ A : NoetherianApproximation B S hS hZ X,
      ∀ j, schemeTheoreticImageSubfunctor B S hS (A.π.app j) = ⊤ :=
  let ⟨A⟩ := h
  ⟨A.image hX, A.schemeTheoreticImageSubfunctor_image_π hX⟩

end AlgebraicGeometry.Space

end
