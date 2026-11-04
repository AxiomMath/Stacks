module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackGlobalSmul
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Relative
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.CategoryTheory.Sites.Modules.GlobalSmulFunctoriality

/-!
# Scalars from the base on the modules of a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `θ : A →+* Γ(Y, 𝒪_Y)` a ring homomorphism,
for instance the scalars of an affine étale chart.  The inverse image `f⁻¹` of sheaves of sets
carries global sections of `𝒪_Y` to global sections of `f⁻¹𝒪_Y`
(`Stacks.Sheaves.ToposPullback.pullbackGlobalSectionHom`), and the structure map
`f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` carries those to global sections of `𝒪_X`.  This makes the categories of
`𝒪_Y`-modules, of `f⁻¹𝒪_Y`-modules and of `𝒪_X`-modules `A`-linear, and this file shows that

* the inverse image `f⁻¹` of modules,
* restriction of scalars along `f♯` (`AlgebraicGeometry.Space.scalarRestriction`),
* the pullback `f^*` of modules (Stacks 03LU), and
* the direct image `f_*` of modules

are `A`-linear for these structures.

## Main definitions

* `AlgebraicGeometry.Space.relativeScalars`: `Γ(Y, 𝒪_Y) →+* Γ(X, f⁻¹𝒪_Y)`.
* `AlgebraicGeometry.Space.sourceScalars`: `Γ(Y, 𝒪_Y) →+* Γ(X, 𝒪_X)`.

## Main results

* `AlgebraicGeometry.Space.scalarRestriction_map_globalSmul`,
  `AlgebraicGeometry.Space.modulePullback_map_globalSmul`,
  `AlgebraicGeometry.Space.modulePushforward_map_globalSmul_sourceScalars`: the compatibility of
  the three functors with multiplication by scalars from the base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped IsMulCommutative
open Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **Global sections of `𝒪_Y` pulled back to global sections of `f⁻¹𝒪_Y`.** -/
def relativeScalars :
    GlobalSectionRing
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) →+*
      GlobalSectionRing
        (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedSite B S hS f).O) :=
  Stacks.Sheaves.ToposPullback.pullbackGlobalSectionHom (SmallEtale.topology B S hS X.1)
    (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O)

/-- **Global sections of `𝒪_Y` pulled back to global sections of `𝒪_X`**, through `f⁻¹𝒪_Y` and
the structure map. -/
def sourceScalars :
    GlobalSectionRing
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) →+*
      GlobalSectionRing
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) :=
  (Stacks.SheafOfModules.globalSectionRingMap (inverseImageStructureMap B S hS f)).comp
    (relativeScalars B S hS f)

/-- The sections of `f⁻¹𝒪_Y` over an object of the small étale site of `X` form a commutative
ring. -/
instance (Z : (SmallEtale B S hS X.1)ᵒᵖ) :
    IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf
      (inverseImageRingedSite B S hS f).O).obj.obj Z) :=
  ⟨⟨fun a b => mul_comm (G := (inverseImageRingedSite B S hS f).O.obj.obj Z) a b⟩⟩

/-- The sections of the inverse-image ring sheaf `f⁻¹𝒪_Y` of the ringed topos morphism over an
object of the small étale site of `X` form a commutative ring. -/
instance (Z : (SmallEtale B S hS X.1)ᵒᵖ) :
    IsMulCommutative ((Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf
      (smallEtaleRingedToposHom B S hS f).toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O)).obj.obj Z) :=
  ⟨⟨fun a b => mul_comm (G := (inverseImageRingedSite B S hS f).O.obj.obj Z) a b⟩⟩

/-- **The inverse image of modules carries multiplication by `s` to multiplication by `f⁻¹ s`.** -/
theorem inverseImageModules_map_globalSmul
    (s : GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O))
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (Stacks.Sheaves.RingedToposModules.inverseImageModules
        (smallEtaleRingedToposHom B S hS f).toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O)).map
        (globalSmul _ s M) =
      globalSmul _ (relativeScalars B S hS f s)
        ((Stacks.Sheaves.RingedToposModules.inverseImageModules
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O)).obj M) :=
  Stacks.Sheaves.ToposPullback.pullbackModuleFunctor_map_globalSmul (SmallEtale.topology B S hS X.1)
    (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O) s M

/-- **Restriction of scalars along `f♯` carries multiplication by `f♯ s` to multiplication by
`s`.** -/
theorem scalarRestriction_map_globalSmul
    (s : GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf
      (inverseImageRingedSite B S hS f).O))
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (scalarRestriction B S hS f).map
        (globalSmul _ (Stacks.SheafOfModules.globalSectionRingMap
          (inverseImageStructureMap B S hS f) s) M) =
      globalSmul _ s ((scalarRestriction B S hS f).obj M) :=
  Stacks.SheafOfModules.restrictScalars_map_globalSmul _ s M

/-- **The pullback `f^*` of modules carries multiplication by `s` to multiplication by its
pullback to `𝒪_X`.** -/
theorem modulePullback_map_globalSmul
    (s : GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O))
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullback B S hS f).map (globalSmul _ s M) =
      globalSmul _ (sourceScalars B S hS f s) ((modulePullback B S hS f).obj M) := by
  let F := smallEtaleRingedToposModulesHom B S hS f
  have hext : ∀ N, (Stacks.Sheaves.RingedToposModules.extendScalarsFSharp F).map
      (globalSmul _ (relativeScalars B S hS f s) N) =
        globalSmul _ (sourceScalars B S hS f s)
          ((Stacks.Sheaves.RingedToposModules.extendScalarsFSharp F).obj N) :=
    fun N => Stacks.SheafOfModules.map_globalSmul_of_adjunction
      (Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction
        (SmallEtale.topology B S hS X.1)
        (Stacks.Sheaves.RingedToposModules.fSharpCommRing F) _ _) _ _
      (fun M => scalarRestriction_map_globalSmul B S hS f (relativeScalars B S hS f s) M) N
  show (Stacks.Sheaves.RingedToposModules.extendScalarsFSharp F).map
      ((Stacks.Sheaves.RingedToposModules.inverseImageModules
        (smallEtaleRingedToposHom B S hS f).toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O)).map
          (globalSmul _ s M)) = _
  exact (congrArg (Stacks.Sheaves.RingedToposModules.extendScalarsFSharp F).map
    (inverseImageModules_map_globalSmul B S hS f s M)).trans (hext _)

/-- **The direct image `f_*` carries multiplication by the pullback of `s` to multiplication by
`s`.** -/
theorem modulePushforward_map_globalSmul_sourceScalars
    (s : GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O))
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforward B S hS f).map (globalSmul _ (sourceScalars B S hS f s) M) =
      globalSmul _ s ((modulePushforward B S hS f).obj M) :=
  Stacks.SheafOfModules.map_globalSmul_of_adjunction_right (modulePullbackAdjunction B S hS f)
    (Stacks.SheafOfModules.globalSectionToEnd _ ⟨(sourceScalars B S hS f s).1,
      (sourceScalars B S hS f s).2⟩)
    (Stacks.SheafOfModules.globalSectionToEnd _ ⟨s.1, s.2⟩)
    (fun N => modulePullback_map_globalSmul B S hS f s N) M

variable {A : Type u} [CommRing A]
  (θ : A →+* GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS Y.1 Y.2).O))

/-- **Restriction of scalars along `f♯` is `A`-linear.** -/
theorem scalarRestriction_linear :
    letI := Stacks.SheafOfModules.linearOver
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
      ((sourceScalars B S hS f).comp θ)
    letI := Stacks.SheafOfModules.linearOver
      (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedSite B S hS f).O)
      ((relativeScalars B S hS f).comp θ)
    (scalarRestriction B S hS f).Linear A :=
  Stacks.SheafOfModules.linear_of_map_globalSmul _ _ (scalarRestriction B S hS f) fun _ M =>
    scalarRestriction_map_globalSmul B S hS f _ M

/-- **The direct image of modules is `A`-linear.** -/
theorem modulePushforward_linear :
    letI := Stacks.SheafOfModules.linearOver
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
      ((sourceScalars B S hS f).comp θ)
    letI := Stacks.SheafOfModules.linearOver
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) θ
    (modulePushforward B S hS f).Linear A :=
  Stacks.SheafOfModules.linear_of_map_globalSmul _ _ (modulePushforward B S hS f) fun _ M =>
    modulePushforward_map_globalSmul_sourceScalars B S hS f _ M

/-- The inverse image of `𝒪_Y`-modules to `f⁻¹𝒪_Y`-modules, with its target spelled as the
modules of `AlgebraicGeometry.Space.inverseImageRingedSite`. -/
abbrev relativeInverseImage :
    Modules.{u, u} B S hS Y.1 Y.2 ⥤
      RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f) :=
  Stacks.Sheaves.RingedToposModules.inverseImageModules
    (smallEtaleRingedToposHom B S hS f).toToposHom
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O)

/-- **The inverse image of modules is `A`-linear.** -/
theorem relativeInverseImage_linear :
    letI := Stacks.SheafOfModules.linearOver
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) θ
    letI := Stacks.SheafOfModules.linearOver
      (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedSite B S hS f).O)
      ((relativeScalars B S hS f).comp θ)
    (relativeInverseImage B S hS f).Linear A :=
  Stacks.SheafOfModules.linear_of_map_globalSmul _ _ _ fun _ M =>
    inverseImageModules_map_globalSmul B S hS f _ M

end AlgebraicGeometry.Space

end
