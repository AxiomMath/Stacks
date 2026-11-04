module

public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardDerivation
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceRingSurjectivity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleAdjointPullPush

/-!
# The transpose of a derivation along the inverse image of sheaves of sets

Let `f : X' ⟶ X` be a morphism of algebraic spaces over a scheme `S`, let `b : X ⟶ Bb` be a
morphism to a base, let `M` be an `𝒪_{X'}`-module and let

```
  D : 𝒪_X ⟶ f_*M
```

be a `Bb`-derivation of `𝒪_X` with values in the direct image of `M`.  Reading `D` as a
morphism `δ : 𝒪_X ⟶ f_*M` of the underlying sheaves of *sets*
(`AlgebraicGeometry.Space.derivationHom`) and transposing it along `f^{-1} ⊣ f_*` gives a
morphism

```
  f^{-1}𝒪_X ⟶ M
```

of sheaves of sets on the small étale site of `X'`.  Its component over an étale chart `W` of
`X'` is a function `(f^{-1}𝒪_X)(W) → M(W)`.  It is additive, and it satisfies the Leibniz rule
for the `𝒪_{X'}`-action read through the inverse-image form `f^♯ : f^{-1}𝒪_X ⟶ 𝒪_{X'}` of the
structure map.

## Main definitions

* `AlgebraicGeometry.Space.inverseImageSections`: the inverse image followed by sections over an
  étale chart of `X'`, the inverse-image counterpart of
  `AlgebraicGeometry.Space.smallEtaleDirectImageSections`.
* `AlgebraicGeometry.Space.inverseImageDerivationHom`: **the transpose** of a derivation along
  `f^{-1} ⊣ f_*`, on underlying sheaves of sets.
* `AlgebraicGeometry.Space.inverseImageDerivationFun`: that transpose on sections over a chart,
  with values in the sections of `M`.

## Main results

* `AlgebraicGeometry.Space.homEquiv_inverseImageDerivationHom`: the image of the transpose under
  the hom-set bijection of `f^{-1} ⊣ f_*` is the derivation it was built from.
* `AlgebraicGeometry.Space.inverseImageDerivationFun_add`: **the transpose is additive.**
* `AlgebraicGeometry.Space.inverseImageDerivationFun_mul`: **the Leibniz rule for the
  transpose**, with the scalar acting through `f^♯ : f^{-1}𝒪_X ⟶ 𝒪_{X'}`.
* `AlgebraicGeometry.Space.inverseImageDerivationFun_map`: compatibility with étale
  restriction, which is the naturality of the transpose.
* `AlgebraicGeometry.Space.inverseImageCounitFun_moduleAddObj`,
  `inverseImageCounitFun_moduleSMulObj` and `inverseImageCounitFun_moduleZeroObj`: the counit is
  additive and semilinear on sections, and sends the transported zero to zero.
* `AlgebraicGeometry.Space.inverseImageDerivationFun_map_structureSharpInverseImageSet_eq_zero`:
  **the transpose kills the sections read from the base**, that is the image of
  `f^{-1}(b^♯)`.

## References

* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA), the conormal sequence.
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2), the inverse image of a
  sheaf of modules.
* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1), the direct image over
  the direct-image sheaf of rings.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the two forms of the
  structure map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf CategoryTheory.Functor
open Stacks.Sites Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X X' Bb : AlgebraicSpaces B S hS} (b : X ⟶ Bb) (f : X' ⟶ X)
  (M : Modules.{u, u} B S hS X'.1 X'.2)
  (D : ((modulePushforward B S hS f).obj M).val.Derivation'
    (structureSharpInverseImage B S hS b).hom)

/-- Sections over an étale chart `W` of `X'` of the inverse image along `f : X' ⟶ X`, as a
functor on sheaves of sets on the small étale site of `X`. -/
noncomputable abbrev inverseImageSections (W : (SmallEtale B S hS X'.1)ᵒᵖ) :
    Sheaf (SmallEtale.topology B S hS X.1) (Type u) ⥤ Type u :=
  (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage ⋙
    sectionsFunctor (SmallEtale.topology B S hS X'.1) W

/-- **The transpose of a derivation of `𝒪_X` with values in `f_*M` along `f^{-1} ⊣ f_*`**, as a
morphism `f^{-1}𝒪_X ⟶ M` of the underlying sheaves of sets on the small étale site of `X'`. -/
noncomputable def inverseImageDerivationHom :
    (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.obj
        (Sheaf.ringSheaf.{u, u, u + 1} (structureRingSheaf B S hS X)) ⟶
      Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X') M :=
  (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.map
      (derivationHom B S hS b ((modulePushforward B S hS f).obj M) D) ≫
    (smallEtaleRingedToposHom B S hS f).toToposHom.adj.counit.app
      (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X') M)

/-- The image of the transpose under the hom-set bijection of `f^{-1} ⊣ f_*` is the morphism of
sheaves of sets belonging to `D`. -/
theorem homEquiv_inverseImageDerivationHom :
    (smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv
        (Sheaf.ringSheaf.{u, u, u + 1} (structureRingSheaf B S hS X))
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X') M)
        (inverseImageDerivationHom B S hS b f M D) =
      derivationHom B S hS b ((modulePushforward B S hS f).obj M) D :=
  ((smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv_apply_eq _ _).2 rfl

/-- The transpose on sections of `f^{-1}𝒪_X` over an étale chart, as a function with values in
the sections of `M`. -/
noncomputable def inverseImageDerivationFun (W : (SmallEtale B S hS X'.1)ᵒᵖ)
    (a : (structureRingSheafInverseImage B S hS f).obj.obj W) : M.val.obj W :=
  (inverseImageDerivationHom B S hS b f M D).hom.app W a

/-- The counit of `f^{-1} ⊣ f_*` at the sheaf of sets of `M`, on sections over an étale chart of
`X'`, with values in the sections of `M`. -/
noncomputable def inverseImageCounitFun (W : (SmallEtale B S hS X'.1)ᵒᵖ)
    (z : (inverseImageSections B S hS f W).obj
      (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X)
        ((modulePushforward B S hS f).obj M))) : M.val.obj W :=
  (counitSections (smallEtaleRingedToposHom B S hS f).toToposHom W).app
    (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X') M) z

/-- The transpose on sections is the inverse image of the derivation followed by the counit. -/
theorem inverseImageDerivationFun_eq (W : (SmallEtale B S hS X'.1)ᵒᵖ)
    (a : (structureRingSheafInverseImage B S hS f).obj.obj W) :
    inverseImageDerivationFun B S hS b f M D W a =
      inverseImageCounitFun B S hS f M W
        ((inverseImageSections B S hS f W).map
          (derivationHom B S hS b ((modulePushforward B S hS f).obj M) D) a) :=
  rfl

/-- The addition transported to the sections of `f^{-1}𝒪_X` over an étale chart is the ring
addition of those sections. -/
theorem ringAddObj_inverseImageSections (W : (SmallEtale B S hS X'.1)ᵒᵖ)
    (x y : (structureRingSheafInverseImage B S hS f).obj.obj W) :
    ringAddObj (structureRingSheaf B S hS X) (inverseImageSections B S hS f W) x y = x + y :=
  (ringAddHom_pullback_apply (SmallEtale.topology B S hS X'.1)
      (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage
      (structureRingSheaf B S hS X) W x y).symm.trans
    (sectionsFunctor_map_ringAddHom (structureRingSheafInverseImage B S hS f) W x y)

/-- The multiplication transported to the sections of `f^{-1}𝒪_X` over an étale chart is the
ring multiplication of those sections. -/
theorem ringMulObj_inverseImageSections (W : (SmallEtale B S hS X'.1)ᵒᵖ)
    (x y : (structureRingSheafInverseImage B S hS f).obj.obj W) :
    ringMulObj (structureRingSheaf B S hS X) (inverseImageSections B S hS f W) x y = x * y :=
  (ringMulHom_pullback_apply (SmallEtale.topology B S hS X'.1)
      (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage
      (structureRingSheaf B S hS X) W x y).symm.trans
    (sectionsFunctor_map_ringMulHom (structureRingSheafInverseImage B S hS f) W x y)

/-- **The counit is additive on sections**, for the addition transported to the sections of the
inverse image of the sheaf of sets of `f_*M`. -/
theorem inverseImageCounitFun_moduleAddObj (W : (SmallEtale B S hS X'.1)ᵒᵖ)
    (m n : (inverseImageSections B S hS f W).obj
      (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X)
        ((modulePushforward B S hS f).obj M))) :
    inverseImageCounitFun B S hS f M W
        (moduleAddObj (structureRingSheaf B S hS X) ((modulePushforward B S hS f).obj M)
          (inverseImageSections B S hS f W) m n) =
      inverseImageCounitFun B S hS f M W m + inverseImageCounitFun B S hS f M W n :=
  Eq.trans
    (congrArg ((counitSections (smallEtaleRingedToposHom B S hS f).toToposHom W).app
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X') M))
      (moduleAddObj_comp (SmallEtale.topology B S hS X.1)
        (smallEtaleDirectImage B S hS f) (structureRingSheaf B S hS X') M
        (inverseImageSections B S hS f W) m n))
    ((moduleAddObj_naturality (structureRingSheaf B S hS X') M
        (counitSections (smallEtaleRingedToposHom B S hS f).toToposHom W) m n).trans
      (sectionsFunctor_map_moduleAddHom (structureRingSheaf B S hS X') M W _ _))

/-- **The transpose of a derivation is additive on sections.** -/
theorem inverseImageDerivationFun_add (W : (SmallEtale B S hS X'.1)ᵒᵖ)
    (x y : (structureRingSheafInverseImage B S hS f).obj.obj W) :
    inverseImageDerivationFun B S hS b f M D W (x + y) =
      inverseImageDerivationFun B S hS b f M D W x +
        inverseImageDerivationFun B S hS b f M D W y := by
  simp only [inverseImageDerivationFun_eq]
  rw [← ringAddObj_inverseImageSections B S hS f W x y, map_ringAddObj_derivationHom
    (structureRingSheaf B S hS X) ((modulePushforward B S hS f).obj M)
    (inverseImageSections B S hS f W)
    (derivationHom B S hS b ((modulePushforward B S hS f).obj M) D)
    (ringAddHom_comp_derivationHom_eq B S hS b ((modulePushforward B S hS f).obj M) D) x y]
  exact inverseImageCounitFun_moduleAddObj B S hS f M W _ _

/-- **The counit at the structure sheaf carries the direct-image form of the structure map to
the inverse-image form.** -/
theorem counitSections_structureSharpSet (W : (SmallEtale B S hS X'.1)ᵒᵖ)
    (r : (structureRingSheafInverseImage B S hS f).obj.obj W) :
    (counitSections (smallEtaleRingedToposHom B S hS f).toToposHom W).app
        (Sheaf.ringSheaf.{u, u, u + 1} (structureRingSheaf B S hS X'))
        ((inverseImageSections B S hS f W).map (structureSharpSet B S hS f) r) =
      (structureSharpRingInverseImage B S hS f).hom.app W r := by
  have h : structureSharpInverseImageSet B S hS f =
      (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.map
          (structureSharpSet B S hS f) ≫
        (smallEtaleRingedToposHom B S hS f).toToposHom.adj.counit.app
          (structureSetSheaf B S hS X') :=
    (((smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv_apply_eq _ _).1
      (homEquiv_structureSharpInverseImageSet B S hS f)).trans
      (Adjunction.homEquiv_counit _ _ _ _)
  refine Eq.trans ?_ (structureSharpRingInverseImage_app B S hS f W r).symm
  refine Eq.trans ?_ (congrArg
    (fun m ↦ (sectionsFunctor (SmallEtale.topology B S hS X'.1) W).map m r) h.symm)
  exact ((sectionsFunctor (SmallEtale.topology B S hS X'.1) W).map_comp_apply
    ((smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.map
      (structureSharpSet B S hS f))
    ((smallEtaleRingedToposHom B S hS f).toToposHom.adj.counit.app
      (structureSetSheaf B S hS X')) r).symm

/-- **The sections of `M` over an étale chart of `X'` are a module over the sections there of
the structure sheaf of rings.** -/
local instance sectionsModule (W : (SmallEtale B S hS X'.1)ᵒᵖ) :
    Module (ToType ((structureRingSheaf B S hS X').obj.obj W)) (ToType (M.val.obj W)) :=
  ModuleCat.isModule _

/-- **The counit is semilinear on sections**: a scalar from `f^{-1}𝒪_X` acts on the value
through the inverse-image form `f^♯ : f^{-1}𝒪_X ⟶ 𝒪_{X'}` of the structure map. -/
theorem inverseImageCounitFun_moduleSMulObj (W : (SmallEtale B S hS X'.1)ᵒᵖ)
    (r : (structureRingSheafInverseImage B S hS f).obj.obj W)
    (m : (inverseImageSections B S hS f W).obj
      (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X)
        ((modulePushforward B S hS f).obj M))) :
    inverseImageCounitFun B S hS f M W
        (moduleSMulObj (structureRingSheaf B S hS X) ((modulePushforward B S hS f).obj M)
          (inverseImageSections B S hS f W) r m) =
      ((structureSharpRingInverseImage B S hS f).hom.app W r :
          (structureRingSheaf B S hS X').obj.obj W) •
        inverseImageCounitFun B S hS f M W m := by
  refine Eq.trans (congrArg (inverseImageCounitFun B S hS f M W)
    (Stacks.Sheaves.RingedToposModules.moduleSMulObj_restrictScalars
      (structureSharp B S hS f) ((moduleDirectImage B S hS f).obj M)
      (inverseImageSections B S hS f W) r m)) ?_
  refine Eq.trans (congrArg (inverseImageCounitFun B S hS f M W)
    (moduleSMulObj_comp (SmallEtale.topology B S hS X.1)
      (smallEtaleDirectImage B S hS f) (structureRingSheaf B S hS X') M
      (inverseImageSections B S hS f W)
      ((inverseImageSections B S hS f W).map (structureSharpSet B S hS f) r) m)) ?_
  refine Eq.trans (moduleSMulObj_naturality (structureRingSheaf B S hS X') M
    (counitSections (smallEtaleRingedToposHom B S hS f).toToposHom W) _ m) ?_
  refine Eq.trans (sectionsFunctor_map_moduleSMulHom
    (structureRingSheaf B S hS X') M W _ _) ?_
  exact congrArg (fun z : (structureRingSheaf B S hS X').obj.obj W ↦
      z • inverseImageCounitFun B S hS f M W m)
    (counitSections_structureSharpSet B S hS f W r)

/-- **The Leibniz rule for the transpose of a derivation**, for the `𝒪_{X'}`-action on `M` read
through the inverse-image form `f^♯ : f^{-1}𝒪_X ⟶ 𝒪_{X'}` of the structure map. -/
theorem inverseImageDerivationFun_mul (W : (SmallEtale B S hS X'.1)ᵒᵖ)
    (x y : (structureRingSheafInverseImage B S hS f).obj.obj W) :
    inverseImageDerivationFun B S hS b f M D W (x * y) =
      (((structureSharpRingInverseImage B S hS f).hom.app W x :
            (structureRingSheaf B S hS X').obj.obj W) •
          inverseImageDerivationFun B S hS b f M D W y : M.val.obj W) +
        (((structureSharpRingInverseImage B S hS f).hom.app W y :
            (structureRingSheaf B S hS X').obj.obj W) •
          inverseImageDerivationFun B S hS b f M D W x : M.val.obj W) := by
  simp only [inverseImageDerivationFun_eq]
  rw [← ringMulObj_inverseImageSections B S hS f W x y, map_ringMulObj_derivationHom
    (structureRingSheaf B S hS X) ((modulePushforward B S hS f).obj M)
    (inverseImageSections B S hS f W)
    (derivationHom B S hS b ((modulePushforward B S hS f).obj M) D)
    (ringMulHom_comp_derivationHom_eq B S hS b ((modulePushforward B S hS f).obj M) D) x y,
    inverseImageCounitFun_moduleAddObj, inverseImageCounitFun_moduleSMulObj,
    inverseImageCounitFun_moduleSMulObj]

/-- **The counit sends the transported zero section to zero.** -/
theorem inverseImageCounitFun_moduleZeroObj (W : (SmallEtale B S hS X'.1)ᵒᵖ) :
    inverseImageCounitFun B S hS f M W
        (moduleZeroObj (structureRingSheaf B S hS X)
          ((modulePushforward B S hS f).obj M)
          (inverseImageSections B S hS f W)) = 0 :=
  Eq.trans
    (congrArg ((counitSections (smallEtaleRingedToposHom B S hS f).toToposHom W).app
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X') M))
      (moduleZeroObj_comp (SmallEtale.topology B S hS X.1)
        (smallEtaleDirectImage B S hS f) (structureRingSheaf B S hS X') M
        (inverseImageSections B S hS f W)))
    ((moduleZeroObj_naturality (structureRingSheaf B S hS X') M
        (counitSections (smallEtaleRingedToposHom B S hS f).toToposHom W)).trans
      (sectionsFunctor_map_moduleZeroHom (structureRingSheaf B S hS X') M W _))

/-- **The transpose of a derivation kills the sections read from the base.**  A section of
`f^{-1}𝒪_X` in the image of `f^{-1}(b^♯)` — the inverse image along `f` of the inverse-image
form of the structure map of `b : X ⟶ Bb` — is killed by the transpose. -/
theorem inverseImageDerivationFun_map_structureSharpInverseImageSet_eq_zero
    (W : (SmallEtale B S hS X'.1)ᵒᵖ)
    (z : (inverseImageSections B S hS f W).obj
      ((smallEtaleRingedToposHom B S hS b).toToposHom.inverseImage.obj
        (structureSetSheaf B S hS Bb))) :
    inverseImageDerivationFun B S hS b f M D W
        ((inverseImageSections B S hS f W).map
          (structureSharpInverseImageSet B S hS b) z) = 0 := by
  refine (inverseImageDerivationFun_eq B S hS b f M D W _).trans ?_
  rw [← (inverseImageSections B S hS f W).map_comp_apply,
    structureSharpInverseImageSet_comp_derivationHom,
    (inverseImageSections B S hS f W).map_comp_apply]
  exact (congrArg (inverseImageCounitFun B S hS f M W)
    (map_zeroDerivationHom (structureRingSheaf B S hS X)
      ((modulePushforward B S hS f).obj M) (inverseImageSections B S hS f W) _)).trans
    (inverseImageCounitFun_moduleZeroObj B S hS f M W)

/-- **The transpose of a derivation commutes with étale restriction**: the naturality of the
transpose, read on sections. -/
theorem inverseImageDerivationFun_map {W V : (SmallEtale B S hS X'.1)ᵒᵖ} (g : W ⟶ V)
    (a : (structureRingSheafInverseImage B S hS f).obj.obj W) :
    inverseImageDerivationFun B S hS b f M D V
        ((structureRingSheafInverseImage B S hS f).obj.map g a) =
      M.val.map g (inverseImageDerivationFun B S hS b f M D W a) :=
  ConcreteCategory.congr_hom
    ((inverseImageDerivationHom B S hS b f M D).hom.naturality g) a

end AlgebraicGeometry.Space

end
