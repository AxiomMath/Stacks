module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.Retraction
public import StacksFrontier.Deformation.ToposThickening.Helpers.ExtDescentAlongThickening
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.MapBijectiveOne

/-!
# Modules over the thickened presentation, read on `X_T` through a retraction

Let `ξ = (T, 𝒢)` be an object of `Coh_{X/Y}` (Stacks 08KB), `h : T ⟶ T'` a first order thickening
of schemes over `Y` with a retraction `r : T' ⟶ T`, and `i : X_T ⟶ X_{T'}`, `ρ : X_{T'} ⟶ X_T` the
induced morphisms of small étale ringed topoi. The deformation theory of Stacks 08VW is developed
on `X_{T'}` with modules over `i_*𝒪_{X_T}`; restricting scalars to `𝒪_{X_{T'}}` and pushing forward
along `ρ` reads such a module on `X_T`. Since `i_*` is an equivalence and `ρ_* ∘ i_* = 𝟭`, this is
an equivalence too, quasi-inverse to `i_*`, so it induces bijections on `Ext¹`.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.thickenedRetraction`: the functor
  `Mod(i_*𝒪_{X_T}) ⥤ Mod(𝒪_{X_T})`, restriction of scalars followed by `ρ_*`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.isEquivalence_thickenedRetraction`: it is an
  equivalence.
* `AlgebraicGeometry.Space.CoherentSituation.bijective_thickenedRetraction_mapExt`: it induces
  bijections on `Ext¹`.
* `AlgebraicGeometry.Space.CoherentSituation.retractionExt_mapExtAddHom`: on `Ext¹` it is
  restriction of scalars followed by `ρ_*`.
* `CategoryTheory.Abelian.Ext.mapExactFunctor_one_comp`: on `Ext¹`, the map along a composite of
  exact functors is the composite of the maps (no injectives needed).

## References

* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
* [Stacks Project, Tag 08MM](https://stacks.math.columbia.edu/tag/08MM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Deformation.ToposThickening

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

universe e u

namespace CategoryTheory.Abelian.Ext

universe w w' w'' v₁ v₂ v₃ u₁ u₂ u₃

/-- **On `Ext¹`, the map along a composite of exact functors is the composite of the two maps.**
Every class in `Ext¹` is the class of a short exact sequence
(`CategoryTheory.Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum`), and each map
carries the class of a short exact sequence to the class of its image; unlike
`Stacks.Homology.ext_mapExactFunctor_comp_functor`, no injective objects are needed. -/
theorem mapExactFunctor_one_comp {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] {E : Type u₃} [Category.{v₃} E] [Abelian E]
    [HasExt.{w} C] [HasExt.{w'} D] [HasExt.{w''} E]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits (F ⋙ G)] [PreservesFiniteColimits (F ⋙ G)] {A B : C}
    (x : Ext.{w} A B 1) :
    ((x.mapExactFunctor F : Ext.{w'} (F.obj A) (F.obj B) 1).mapExactFunctor G :
        Ext.{w''} (G.obj (F.obj A)) (G.obj (F.obj B)) 1) =
      (x.mapExactFunctor (F ⋙ G) : Ext.{w''} ((F ⋙ G).obj A) ((F ⋙ G).obj B) 1) := by
  obtain ⟨X, i, p, w, hX, rfl⟩ := (extClass_surjective_and_eq_iff_iso_and_baerSum.{w} C A B).1 x
  rw [mapExactFunctor_extClass, mapExactFunctor_extClass, mapExactFunctor_extClass]

end CategoryTheory.Abelian.Ext

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  {T T' : SchemesOver D.Y} (h : T ⟶ T') (r : T' ⟶ T) (hr : h ≫ r = 𝟙 T)
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))

/-- **Modules over `i_*𝒪_{X_T}`, read on `X_T`**: restriction of scalars to `𝒪_{X_{T'}}` along
`i^♯`, followed by the direct image along the retraction `ρ = X_r`. -/
def thickenedRetraction :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T)).O)) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T)).O) :=
  structureRestrict (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h)) ⋙
    (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap r)).pushforwardModules

/-- `AlgebraicGeometry.Space.CoherentSituation.thickenedRetraction` unfolded. -/
theorem thickenedRetraction_eq :
    thickenedRetraction (D := D) h r =
      structureRestrict
          (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h)) ⋙
        (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap r)).pushforwardModules :=
  rfl

/-- Reading modules over `i_*𝒪_{X_T}` on `X_T` is additive. -/
instance additive_thickenedRetraction : (thickenedRetraction (D := D) h r).Additive :=
  inferInstanceAs (structureRestrict (smallEtaleRingedToposHom B S hS
    (D.relativeSquareSituation.relativeMap h)) ⋙
      (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap r)).pushforwardModules).Additive

/-- `i_*` followed by `thickenedRetraction` is the identity: it is `i_* ⋙ ρ_*` on modules, read
through the identification of the two direct images of modules along `i`. -/
def thickenedRetractionIso :
    pushforwardModuleFunctor
        (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h)).toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T)).O) ⋙
      thickenedRetraction h r ≅ 𝟭 _ :=
  retractionPushforwardModulesIso h r hr

include hr hh in
/-- **Reading modules over `i_*𝒪_{X_T}` on `X_T` is an equivalence**, quasi-inverse to `i_*`:
`i_*` is an equivalence
(`Deformation.ToposThickening.isEquivalence_pushforwardModuleFunctor_of_firstOrderThickening`)
and the composite is the identity. -/
theorem isEquivalence_thickenedRetraction : (thickenedRetraction h r).IsEquivalence := by
  have := isEquivalence_pushforwardModuleFunctor_of_firstOrderThickening.{u, u + 1, u, u + 1, u}
    (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
  have : (pushforwardModuleFunctor
        (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h)).toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T)).O) ⋙
      thickenedRetraction h r).IsEquivalence :=
    @Functor.isEquivalence_of_iso _ _ _ _ _ _ (thickenedRetractionIso h r hr).symm
      Functor.isEquivalence_refl
  exact Functor.isEquivalence_of_comp_left (pushforwardModuleFunctor
    (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h)).toToposHom
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T)).O)) _

include hr hh in
/-- Reading modules over `i_*𝒪_{X_T}` on `X_T` is left exact, being an equivalence. -/
theorem preservesFiniteLimits_thickenedRetraction :
    PreservesFiniteLimits (thickenedRetraction (D := D) h r) := by
  have := isEquivalence_thickenedRetraction h r hr hh
  have : PreservesLimitsOfSize.{0, 0} (thickenedRetraction (D := D) h r) :=
    (thickenedRetraction (D := D) h r).asEquivalence.symm.toAdjunction.rightAdjoint_preservesLimits
  exact PreservesLimitsOfSize0.preservesFiniteLimits _

include hr hh in
/-- Reading modules over `i_*𝒪_{X_T}` on `X_T` is right exact, being an equivalence. -/
theorem preservesFiniteColimits_thickenedRetraction :
    PreservesFiniteColimits (thickenedRetraction (D := D) h r) := by
  have := isEquivalence_thickenedRetraction h r hr hh
  infer_instance

section Ext

variable [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T)).O)))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T)).O))]

include hr hh in
/-- **A class of `𝒪_{X_{T'}}`-modules, read on `X_T`**: its image under the exact functor `ρ_*`. -/
def retractionExt {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O)} {n : ℕ}
    (x : Abelian.Ext.{e} M N n) :
    Abelian.Ext.{e}
      ((smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap r)).pushforwardModules.obj M)
      ((smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap r)).pushforwardModules.obj N) n :=
  letI := preservesFiniteLimits_retraction_pushforwardModules (D := D) r
  letI := preservesFiniteColimits_retraction_pushforwardModules h r hr hh
  x.mapExactFunctor
    (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap r)).pushforwardModules

omit [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T)).O)))] in
/-- `ρ_*` on `Ext` is additive. -/
theorem retractionExt_add {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O)} {n : ℕ}
    (x y : Abelian.Ext.{e} M N n) :
    retractionExt h r hr hh (x + y) = retractionExt h r hr hh x + retractionExt h r hr hh y := by
  have := preservesFiniteLimits_retraction_pushforwardModules (D := D) r
  have := preservesFiniteColimits_retraction_pushforwardModules h r hr hh
  exact Abelian.Ext.mapExactFunctor_add _ _ _ _ _ _

omit [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T)).O)))] in
/-- `ρ_*` on `Ext` commutes with composition of classes. -/
theorem retractionExt_comp {M N K : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O)}
    {a b c : ℕ} (x : Abelian.Ext.{e} M N a) (y : Abelian.Ext.{e} N K b) (hc : a + b = c) :
    retractionExt h r hr hh (x.comp y hc) =
      (retractionExt h r hr hh x).comp (retractionExt h r hr hh y) hc := by
  have := preservesFiniteLimits_retraction_pushforwardModules (D := D) r
  have := preservesFiniteColimits_retraction_pushforwardModules h r hr hh
  exact Abelian.Ext.mapExactFunctor_comp _ _ _ _

omit [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T)).O)))] in
/-- `ρ_*` on `Ext` carries a degree-zero class to the class of the image of the map. -/
theorem retractionExt_mk₀ {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O)}
    (φ : M ⟶ N) :
    retractionExt h r hr hh (Abelian.Ext.mk₀.{e} φ) =
      Abelian.Ext.mk₀
        ((smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap r)).pushforwardModules.map φ) := by
  have := preservesFiniteLimits_retraction_pushforwardModules (D := D) r
  have := preservesFiniteColimits_retraction_pushforwardModules h r hr hh
  exact Abelian.Ext.mapExactFunctor_mk₀ _ _

include hr hh in
/-- **Modules over `i_*𝒪_{X_T}`: a class read on `X_T`**, its image under the exact equivalence
`AlgebraicGeometry.Space.CoherentSituation.thickenedRetraction`. -/
def thickenedRetractionExt {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T)).O))} {n : ℕ}
    (x : Abelian.Ext.{e} M N n) :
    Abelian.Ext.{e} ((thickenedRetraction h r).obj M) ((thickenedRetraction h r).obj N) n :=
  letI := preservesFiniteLimits_thickenedRetraction h r hr hh
  letI := preservesFiniteColimits_thickenedRetraction h r hr hh
  x.mapExactFunctor (thickenedRetraction h r)

/-- **On `Ext¹`, reading on `X_T` is restriction of scalars followed by `ρ_*`**
(`CategoryTheory.Abelian.Ext.mapExactFunctor_one_comp`). -/
theorem retractionExt_mapExtAddHom {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T)).O))}
    (x : Abelian.Ext.{e} M N 1) :
    retractionExt h r hr hh
        ((structureRestrict (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h))).mapExtAddHom.{e, e} M N 1 x) =
      thickenedRetractionExt h r hr hh x := by
  have := preservesFiniteLimits_retraction_pushforwardModules (D := D) r
  have := preservesFiniteColimits_retraction_pushforwardModules h r hr hh
  have := preservesFiniteLimits_thickenedRetraction h r hr hh
  have := preservesFiniteColimits_thickenedRetraction h r hr hh
  exact Abelian.Ext.mapExactFunctor_one_comp
    (structureRestrict (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h)))
    (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap r)).pushforwardModules x

omit [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O))] in
include hr hh in
/-- **Reading on `X_T` is bijective on `Ext¹`**: the functor is an exact equivalence
(`CategoryTheory.Functor.mapExtAddHom_one_bijective`, no injectives needed). -/
theorem bijective_thickenedRetractionExt
    (M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T)).O))) :
    Function.Bijective (fun x : Abelian.Ext.{e} M N 1 => thickenedRetractionExt h r hr hh x) := by
  have := isEquivalence_thickenedRetraction h r hr hh
  have := preservesFiniteLimits_thickenedRetraction h r hr hh
  have := preservesFiniteColimits_thickenedRetraction h r hr hh
  have : (thickenedRetraction (D := D) h r).Full := Functor.IsEquivalence.full
  have : (thickenedRetraction (D := D) h r).Faithful := Functor.IsEquivalence.faithful
  exact Functor.mapExtAddHom_one_bijective.{e, e} (thickenedRetraction h r) N M
    (fun E _ _ _ _ => ⟨_, ⟨(thickenedRetraction h r).objObjPreimageIso E⟩⟩)

end Ext

end AlgebraicGeometry.Space.CoherentSituation

end
