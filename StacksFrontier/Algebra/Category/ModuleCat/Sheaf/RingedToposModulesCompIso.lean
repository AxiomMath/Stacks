module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget

/-!
# Composing the direct and inverse images of sheaves of modules

Let `φ : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and `ψ : (Sh(D), O_D) ⟶ (Sh(E), O_E)` be morphisms of
ringed topoi in the four-field sense of
`Stacks.Sheaves.RingedToposModules.RingedToposHom`, and let `χ : (Sh(C), O_C) ⟶ (Sh(E), O_E)`
be a third one playing the role of their composite.  In a concrete situation — a composite of
morphisms of algebraic spaces, say — the direct image of `χ` is *not* the composite of the
direct images on the nose: the two are joined by a comparison isomorphism `τ` of the
underlying geometric direct images, and the structure map of `χ` is the composite structure
map read through `τ`.

This file turns such a `τ` into the corresponding comparison on sheaves of *modules*,

`ψ_*(φ_*M) ≅ χ_*M`,  `χ^*G ≅ ψ^*(φ^*G)`,

the second by uniqueness of left adjoints.  The comparison is `τ` itself on the underlying
sheaves of sets. This covers a composite of morphisms of ringed topoi in the sense of
Stacks 01D3, where `τ` is the identity, and the small étale ringed topoi of algebraic spaces,
where it is not.

## Main definitions

* `Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso`: the comparison
  `φ_* ⋙ ψ_* ≅ χ_*` of direct images of sheaves of modules attached to `τ`.
* `Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso`: its adjoint mate, the comparison
  `χ^* ≅ ψ^* ⋙ φ^*` of pullbacks.
* `Stacks.Sheaves.ToposPullback.pullbackModuleCompIso`: the comparison of an iterated inverse
  image of sheaves of modules along finite-product-preserving functors of sheaves of sets with
  the inverse image along the composite, the scalars being read through
  `Stacks.Sheaves.ToposPullback.pullbackRingSheafCompIso`.

## Main results

* `Stacks.Sheaves.RingedToposModules.moduleAddObj_pushforwardModules` and
  `Stacks.Sheaves.RingedToposModules.pushforwardModules_add`: addition on a direct image of a
  sheaf of modules is the addition of the original module, transported along the geometric
  direct image.
* `Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_pushforwardModulesCompIso_hom_app`:
  the comparison *is* `τ` on underlying sheaves of sets.
* `AlgebraicGeometry.RingedToposHom.ringFsharp_forget`: the structure map of the four-field
  reading `AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom` of a morphism of ringed
  topoi is, on underlying sheaves of sets, the structure map of the morphism itself.
* `Stacks.Sheaves.ToposPullback.moduleAddObj_pullbackModuleObj`: the addition of an inverse
  image of a sheaf of modules, read through a further functor to types, is the addition of the
  original module read through the composite; the additive counterpart of
  `Stacks.Sheaves.ToposPullback.moduleSMulObj_pullbackModuleObj`.

## Implementation notes

The hypothesis `hτ` is stated on underlying sheaves of *sets* rather than on sheaves of rings:
that is the form in which `pushforwardModules_smul` carries the scalar along `f♯`, and a `τ`
need not be a comparison of sheaves of rings at all.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.RingedToposHom

universe v u w v' u' w'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

/-- The direct-image form of the structure map of the four-field reading
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom` of a morphism of ringed topoi is,
on underlying sheaves of sets, the underlying map of `f♯` itself. -/
theorem ringFsharp_forget (f : RingedToposHom X Y) :
    (sheafCompose Y.J (forget RingCat.{w'})).map f.ringFsharp = Y.forgetRing.map f.fSharp :=
  (ringSheafMap_ringFsharp f).trans
    ((congrArg (fun m ↦ (f.toToposHom.adj.homEquiv _ _) m)
      (fSharpInverseImage_forget_homEquiv f)).trans (Equiv.apply_symm_apply _ _))

end AlgebraicGeometry.RingedToposHom

namespace Stacks.Sheaves.RingedToposModules

universe t w w' w'' v u v' u' v'' u''

section Pushforward

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : RingedToposHom X Y)

/-- The direct-image form `f♯ : O_D ⟶ f_*O_C` of the structure map of a morphism of ringed
topoi, on underlying sheaves of sets.

This is `(sheafCompose _ (forget RingCat)).map f.fSharp`, with the codomain written as the
geometric direct image `f_*` of the underlying sheaf of sets of `O_C` rather than as the
underlying sheaf of sets of the direct image of `O_C`: only in this spelling can the structure
maps of a composite be composed. -/
noncomputable def fSharpSet :
    Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
      f.toToposHom.pushforward.obj (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (sheafCompose Y.J (forget RingCat.{w'})).map f.fSharp

variable (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- The addition on the direct image of a sheaf of modules along a morphism of ringed topoi,
transported to the image of a finite-product-preserving functor `P` to types, is the addition on
the original module transported along `f_* ⋙ P` (Stacks 03D6, part (1)). -/
lemma moduleAddObj_pushforwardModules (P : Sheaf Y.J (Type w') ⥤ Type t)
    [PreservesFiniteProducts P]
    (x y : P.obj (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      ((pushforwardModules f).obj M))) :
    Sheaf.moduleAddObj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ((pushforwardModules f).obj M) P
        x y =
      Sheaf.moduleAddObj (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M
        (f.toToposHom.pushforward ⋙ P) x y :=
  Stacks.Sheaves.ToposPushforward.moduleAddObj_comp Y.J f.toToposHom.pushforward
    (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj M) P x y

/-- `Stacks.Sheaves.RingedToposModules.moduleSMulObj_pushforwardModules` with the structure map
written as `Stacks.Sheaves.RingedToposModules.fSharpSet`. -/
lemma moduleSMulObj_pushforwardModules_fSharpSet (P : Sheaf Y.J (Type w') ⥤ Type t)
    [PreservesFiniteProducts P]
    (r : P.obj (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (m : P.obj (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      ((pushforwardModules f).obj M))) :
    Sheaf.moduleSMulObj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ((pushforwardModules f).obj M)
        P r m =
      Sheaf.moduleSMulObj (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M
        (f.toToposHom.pushforward ⋙ P) (P.map (fSharpSet f) r) m :=
  moduleSMulObj_pushforwardModules f M P r m

/-- The addition on the sections of a direct image of a sheaf of modules is the addition of
the original module, transported along the geometric direct image. -/
lemma pushforwardModules_add (V : Y.Cᵒᵖ)
    (x y : (Sheaf.sectionsFunctor Y.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj M))) :
    x + y =
      Sheaf.moduleAddObj (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M
        (f.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor Y.J V) x y :=
  (Sheaf.sectionsFunctor_map_moduleAddHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      ((pushforwardModules f).obj M) V x y).symm.trans
    (moduleAddObj_pushforwardModules f M (Sheaf.sectionsFunctor Y.J V) x y)

/-- `Stacks.Sheaves.RingedToposModules.pushforwardModules_smul` with the structure map written
as `Stacks.Sheaves.RingedToposModules.fSharpSet`. -/
lemma pushforwardModules_smul_fSharpSet (V : Y.Cᵒᵖ)
    (r : (Sheaf.sectionsFunctor Y.J V).obj
      (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (x : (Sheaf.sectionsFunctor Y.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj M))) :
    r • x =
      Sheaf.moduleSMulObj (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M
        (f.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor Y.J V)
        ((Sheaf.sectionsFunctor Y.J V).map (fSharpSet f) r) x :=
  pushforwardModules_smul f M V r x

end Pushforward

section Composition

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
    {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  (φ : RingedToposHom X Y) (ψ : RingedToposHom Y Z) (χ : RingedToposHom X Z)

/-- The structure map of a composite of two morphisms of ringed topoi, on underlying sheaves of
sets: `ψ♯` followed by the direct image under `ψ` of `φ♯`. -/
noncomputable def fSharpSetComp :
    Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) ⟶
      (φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward).obj
        (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  fSharpSet ψ ≫ ψ.toToposHom.pushforward.map (fSharpSet φ)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})] in
/-- `Stacks.Sheaves.RingedToposModules.fSharpSetComp` unfolded. -/
theorem fSharpSetComp_eq :
    fSharpSetComp φ ψ = fSharpSet ψ ≫ ψ.toToposHom.pushforward.map (fSharpSet φ) :=
  rfl

variable (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- The addition on the sections of a twice-pushed-forward sheaf of modules is the addition of
the original module, transported along the two geometric direct images in succession. -/
lemma pushforwardModules_comp_add (V : Z.Cᵒᵖ)
    (x y : (Sheaf.sectionsFunctor Z.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
      ((pushforwardModules ψ).obj ((pushforwardModules φ).obj M)))) :
    x + y =
      Sheaf.moduleAddObj (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M
        ((φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward) ⋙
          Sheaf.sectionsFunctor Z.J V) x y :=
  (pushforwardModules_add ψ ((pushforwardModules φ).obj M) V x y).trans
    (moduleAddObj_pushforwardModules φ M
      (ψ.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor Z.J V) x y)

/-- The scalar action on the sections of a twice-pushed-forward sheaf of modules is the action
on the original module transported along the two geometric direct images in succession, with
the scalar carried along the composite structure map. -/
lemma pushforwardModules_comp_smul (V : Z.Cᵒᵖ)
    (r : (Sheaf.sectionsFunctor Z.J V).obj
      (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
    (x : (Sheaf.sectionsFunctor Z.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
      ((pushforwardModules ψ).obj ((pushforwardModules φ).obj M)))) :
    r • x =
      Sheaf.moduleSMulObj (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M
        ((φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward) ⋙
          Sheaf.sectionsFunctor Z.J V)
        ((Sheaf.sectionsFunctor Z.J V).map (fSharpSetComp φ ψ) r) x := by
  refine Eq.trans
    (pushforwardModules_smul_fSharpSet ψ ((pushforwardModules φ).obj M) V r x) ?_
  refine Eq.trans (moduleSMulObj_pushforwardModules_fSharpSet φ M
    (ψ.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor Z.J V) _ x) ?_
  exact congrArg (fun z ↦ Sheaf.moduleSMulObj (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M
      ((φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward) ⋙
        Sheaf.sectionsFunctor Z.J V) z x)
    ((Sheaf.sectionsFunctor Z.J V).map_comp_apply (fSharpSet ψ)
      (ψ.toToposHom.pushforward.map (fSharpSet φ)) r).symm

/-- A comparison `σ` of the geometric direct images, read as a morphism of the underlying
sheaves of sets of a twice-pushed-forward sheaf of modules and of the direct image along `χ`:
the component of `σ` at the underlying sheaf of sets of `M`. -/
noncomputable def pushforwardComparisonSheafHom
    (σ : φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward ⟶ χ.toToposHom.pushforward) :
    Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
        ((pushforwardModules ψ).obj ((pushforwardModules φ).obj M)) ⟶
      Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
        ((pushforwardModules χ).obj M) :=
  σ.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)

/-- `Stacks.Sheaves.RingedToposModules.pushforwardComparisonSheafHom` for a comparison in the
other direction. -/
noncomputable def pushforwardComparisonSheafHomSymm
    (σ : χ.toToposHom.pushforward ⟶ φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward) :
    Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) ((pushforwardModules χ).obj M) ⟶
      Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
        ((pushforwardModules ψ).obj ((pushforwardModules φ).obj M)) :=
  σ.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)

/-- A comparison of the geometric direct images is additive on sections, with no compatibility
with the structure maps assumed. -/
lemma sectionsFunctor_map_pushforwardComparison_add (V : Z.Cᵒᵖ)
    (σ : φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward ⟶ χ.toToposHom.pushforward)
    (x y : (Sheaf.sectionsFunctor Z.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
      ((pushforwardModules ψ).obj ((pushforwardModules φ).obj M)))) :
    (Sheaf.sectionsFunctor Z.J V).map
        (pushforwardComparisonSheafHom φ ψ χ M σ) (x + y) =
      (Sheaf.sectionsFunctor Z.J V).map
          (pushforwardComparisonSheafHom φ ψ χ M σ) x +
        (Sheaf.sectionsFunctor Z.J V).map
          (pushforwardComparisonSheafHom φ ψ χ M σ) y := by
  refine (congrArg ((Sheaf.sectionsFunctor Z.J V).map (pushforwardComparisonSheafHom φ ψ χ M σ))
    (pushforwardModules_comp_add φ ψ M V x y)).trans
    ((Sheaf.moduleAddObj_naturality (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M
      (Functor.whiskerRight σ (Sheaf.sectionsFunctor Z.J V)) x y).trans ?_)
  exact (pushforwardModules_add χ M V _ _).symm

/-- A comparison of the geometric direct images which carries the composite structure map to
the structure map of `χ` is linear on sections. -/
lemma sectionsFunctor_map_pushforwardComparison_smul (V : Z.Cᵒᵖ)
    (σ : φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward ⟶ χ.toToposHom.pushforward)
    (hσ : fSharpSetComp φ ψ ≫ σ.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) =
      fSharpSet χ)
    (r : (Sheaf.sectionsFunctor Z.J V).obj
      (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
    (x : (Sheaf.sectionsFunctor Z.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
      ((pushforwardModules ψ).obj ((pushforwardModules φ).obj M)))) :
    (Sheaf.sectionsFunctor Z.J V).map
        (pushforwardComparisonSheafHom φ ψ χ M σ) (r • x) =
      r • (Sheaf.sectionsFunctor Z.J V).map
        (pushforwardComparisonSheafHom φ ψ χ M σ) x := by
  refine (congrArg ((Sheaf.sectionsFunctor Z.J V).map (pushforwardComparisonSheafHom φ ψ χ M σ))
    (pushforwardModules_comp_smul φ ψ M V r x)).trans
    ((Sheaf.moduleSMulObj_naturality (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M
      (Functor.whiskerRight σ (Sheaf.sectionsFunctor Z.J V)) _ x).trans ?_)
  refine Eq.trans (congrArg (fun z ↦ Sheaf.moduleSMulObj _ M _ z _)
    (((Sheaf.sectionsFunctor Z.J V).map_comp_apply _ _ r).symm.trans
      (congrArg (fun m ↦ (Sheaf.sectionsFunctor Z.J V).map m r) hσ))) ?_
  exact (pushforwardModules_smul_fSharpSet χ M V r _).symm

/-- A comparison of the geometric direct images in the other direction is additive on
sections. -/
lemma sectionsFunctor_map_pushforwardComparisonSymm_add (V : Z.Cᵒᵖ)
    (σ : χ.toToposHom.pushforward ⟶ φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward)
    (x y : (Sheaf.sectionsFunctor Z.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
      ((pushforwardModules χ).obj M))) :
    (Sheaf.sectionsFunctor Z.J V).map
        (pushforwardComparisonSheafHomSymm φ ψ χ M σ) (x + y) =
      (Sheaf.sectionsFunctor Z.J V).map
          (pushforwardComparisonSheafHomSymm φ ψ χ M σ) x +
        (Sheaf.sectionsFunctor Z.J V).map
          (pushforwardComparisonSheafHomSymm φ ψ χ M σ) y := by
  refine (congrArg ((Sheaf.sectionsFunctor Z.J V).map (pushforwardComparisonSheafHomSymm φ ψ χ M σ))
    (pushforwardModules_add χ M V x y)).trans
    ((Sheaf.moduleAddObj_naturality (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M
      (Functor.whiskerRight σ (Sheaf.sectionsFunctor Z.J V)) x y).trans ?_)
  exact (pushforwardModules_comp_add φ ψ M V _ _).symm

/-- A comparison of the geometric direct images in the other direction which carries the
structure map of `χ` to the composite structure map is linear on sections. -/
lemma sectionsFunctor_map_pushforwardComparisonSymm_smul (V : Z.Cᵒᵖ)
    (σ : χ.toToposHom.pushforward ⟶ φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward)
    (hσ : fSharpSet χ ≫ σ.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) =
      fSharpSetComp φ ψ)
    (r : (Sheaf.sectionsFunctor Z.J V).obj
      (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
    (x : (Sheaf.sectionsFunctor Z.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
      ((pushforwardModules χ).obj M))) :
    (Sheaf.sectionsFunctor Z.J V).map
        (pushforwardComparisonSheafHomSymm φ ψ χ M σ) (r • x) =
      r • (Sheaf.sectionsFunctor Z.J V).map
        (pushforwardComparisonSheafHomSymm φ ψ χ M σ) x := by
  refine (congrArg ((Sheaf.sectionsFunctor Z.J V).map (pushforwardComparisonSheafHomSymm φ ψ χ M σ))
    (pushforwardModules_smul_fSharpSet χ M V r x)).trans
    ((Sheaf.moduleSMulObj_naturality (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M
      (Functor.whiskerRight σ (Sheaf.sectionsFunctor Z.J V)) _ x).trans ?_)
  refine Eq.trans (congrArg (fun z ↦ Sheaf.moduleSMulObj _ M _ z _)
    (((Sheaf.sectionsFunctor Z.J V).map_comp_apply _ _ r).symm.trans
      (congrArg (fun m ↦ (Sheaf.sectionsFunctor Z.J V).map m r) hσ))) ?_
  exact (pushforwardModules_comp_smul φ ψ M V r _).symm

section Iso

variable (τ : φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward ≅ χ.toToposHom.pushforward)
  (hτ : fSharpSetComp φ ψ ≫
    τ.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = fSharpSet χ)

/-- The comparison `ψ_*(φ_*M) ⟶ χ_*M` of sheaves of modules attached to a comparison `τ` of
the geometric direct images carrying the composite structure map to the structure map of
`χ`. -/
noncomputable def pushforwardModulesCompHom :
    (pushforwardModules ψ).obj ((pushforwardModules φ).obj M) ⟶
      (pushforwardModules χ).obj M :=
  ofSheafHom (pushforwardComparisonSheafHom φ ψ χ M τ.hom)
    (fun V ↦ sectionsFunctor_map_pushforwardComparison_add φ ψ χ M V τ.hom)
    (fun V ↦ sectionsFunctor_map_pushforwardComparison_smul φ ψ χ M V τ.hom hτ)

/-- The inverse comparison `χ_*M ⟶ ψ_*(φ_*M)`, attached to `τ.inv`. -/
noncomputable def pushforwardModulesCompInv :
    (pushforwardModules χ).obj M ⟶
      (pushforwardModules ψ).obj ((pushforwardModules φ).obj M) :=
  ofSheafHom (pushforwardComparisonSheafHomSymm φ ψ χ M τ.inv)
    (fun V ↦ sectionsFunctor_map_pushforwardComparisonSymm_add φ ψ χ M V τ.inv)
    (fun V ↦ sectionsFunctor_map_pushforwardComparisonSymm_smul φ ψ χ M V τ.inv (by
      rw [← hτ, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]))

/-- The comparison of sheaves of modules is `τ` on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_pushforwardModulesCompHom :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
        (pushforwardModulesCompHom φ ψ χ M τ hτ) =
      τ.hom.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M) :=
  rfl

/-- The inverse comparison of sheaves of modules is `τ.inv` on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_pushforwardModulesCompInv :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
        (pushforwardModulesCompInv φ ψ χ M τ hτ) =
      τ.inv.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M) :=
  rfl

/-- The comparison `ψ_*(φ_*M) ≅ χ_*M` of sheaves of modules attached to `τ`, for a single
module `M`. -/
noncomputable def pushforwardModulesCompIsoApp :
    (pushforwardModules ψ).obj ((pushforwardModules φ).obj M) ≅
      (pushforwardModules χ).obj M where
  hom := pushforwardModulesCompHom φ ψ χ M τ hτ
  inv := pushforwardModulesCompInv φ ψ χ M τ hτ
  hom_inv_id := hom_ext_moduleSheafFunctor (by
    rw [CategoryTheory.Functor.map_comp, moduleSheafFunctor_map_pushforwardModulesCompHom,
      moduleSheafFunctor_map_pushforwardModulesCompInv, CategoryTheory.Functor.map_id]
    exact τ.hom_inv_id_app _)
  inv_hom_id := hom_ext_moduleSheafFunctor (by
    rw [CategoryTheory.Functor.map_comp, moduleSheafFunctor_map_pushforwardModulesCompInv,
      moduleSheafFunctor_map_pushforwardModulesCompHom, CategoryTheory.Functor.map_id]
    exact τ.inv_hom_id_app _)

/-- The component of the comparison is `τ` on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_pushforwardModulesCompIsoApp_hom :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
        (pushforwardModulesCompIsoApp φ ψ χ M τ hτ).hom =
      τ.hom.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M) :=
  rfl

variable {M}

/-- The comparison `φ_* ⋙ ψ_* ≅ χ_*` of direct images of sheaves of modules attached to a
comparison `τ` of the geometric direct images carrying the composite structure map to the
structure map of `χ`. -/
noncomputable def pushforwardModulesCompIso :
    pushforwardModules φ ⋙ pushforwardModules ψ ≅ pushforwardModules χ :=
  NatIso.ofComponents (fun M ↦ pushforwardModulesCompIsoApp φ ψ χ M τ hτ)
    (fun {M N} α ↦ hom_ext_moduleSheafFunctor (by
      have hsrc : (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
            ((pushforwardModules φ ⋙ pushforwardModules ψ).map α) =
          ψ.toToposHom.pushforward.map (φ.toToposHom.pushforward.map
            ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map α)) :=
        (moduleSheafFunctor_map_pushforwardModules_map ψ
            ((pushforwardModules φ).map α)).trans
          (congrArg ψ.toToposHom.pushforward.map
            (moduleSheafFunctor_map_pushforwardModules_map φ α))
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, hsrc,
        moduleSheafFunctor_map_pushforwardModulesCompIsoApp_hom,
        moduleSheafFunctor_map_pushforwardModulesCompIsoApp_hom,
        moduleSheafFunctor_map_pushforwardModules_map χ α]
      exact τ.hom.naturality
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map α)))

/-- The comparison of direct images of sheaves of modules *is* `τ` on the underlying sheaves of
sets. -/
theorem moduleSheafFunctor_map_pushforwardModulesCompIso_hom_app
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
        ((pushforwardModulesCompIso φ ψ χ τ hτ).hom.app M) =
      τ.hom.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M) :=
  rfl

variable [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]

/-- The comparison `χ^* ≅ ψ^* ⋙ φ^*` of pullbacks of sheaves of modules, the adjoint mate of
`Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso`. -/
noncomputable def pullbackModulesCompIso :
    χ.pullbackModules ≅ ψ.pullbackModules ⋙ φ.pullbackModules :=
  ((pullbackAdjPushforwardModules χ).ofNatIsoRight
      (pushforwardModulesCompIso φ ψ χ τ hτ).symm).leftAdjointUniq
    ((pullbackAdjPushforwardModules ψ).comp (pullbackAdjPushforwardModules φ))

/-- The transpose of the comparison of pullbacks under the two adjunctions is the unit of the
composite adjunction. -/
theorem unit_pullbackModulesCompIso_hom_app
    (G : SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :
    ((pullbackAdjPushforwardModules χ).ofNatIsoRight
          (pushforwardModulesCompIso φ ψ χ τ hτ).symm).unit.app G ≫
        (pushforwardModules φ ⋙ pushforwardModules ψ).map
          ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app G) =
      ((pullbackAdjPushforwardModules ψ).comp
        (pullbackAdjPushforwardModules φ)).unit.app G :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ G

end Iso

end Composition

end Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.ToposPullback

open Stacks.Sheaves.RingedToposModules

universe t ww ww' ww'' vv uu vv' uu' vv'' uu''

section Aux

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  (O : Sheaf K RingCat.{ww'}) (G : SheafOfModules.{ww'} O)

variable [J.HasSheafCompose (forget RingCat.{ww})]

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- The addition of an inverse image of a sheaf of modules, read through a further
finite-product-preserving functor `P` to types, is the addition of the original module read
through `Φ ⋙ P`. -/
lemma moduleAddObj_pullbackModuleObj (P : Sheaf J (Type ww) ⥤ Type t)
    [PreservesFiniteProducts P]
    (x y : P.obj (Φ.obj (Sheaf.moduleSheaf O G))) :
    Sheaf.moduleAddObj (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G) P x y =
      Sheaf.moduleAddObj O G (Φ ⋙ P) x y := by
  have : PreservesFiniteProducts (Φ ⋙ P) := inferInstance
  show P.map _ (Functor.prodObjMk x y) =
    (Φ ⋙ P).map (Sheaf.moduleAddHom O G) (Functor.prodObjMk (P := Φ ⋙ P) x y)
  refine Eq.symm (Eq.trans (congrArg
    (fun n ↦ P.map n (Functor.prodObjMk (P := Φ ⋙ P) x y)) (moduleAdd_map_aux' J Φ O G)) ?_)
  refine Eq.trans (P.map_comp_apply _ _ _) ?_
  congr 1
  rw [Functor.map_prodComparison_apply, Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk]

end Aux

section Comp

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {E : Type uu''} [Category.{vv''} E]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) {L : GrothendieckTopology E}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [L.HasSheafCompose (forget RingCat.{ww''})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  [L.HasSheafCompose (forget AddCommGrpCat.{ww''})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  (Ψ : Sheaf L (Type ww'') ⥤ Sheaf K (Type ww')) [PreservesFiniteProducts Ψ]
  (R : Sheaf L RingCat.{ww''})

section Module

variable (G : SheafOfModules.{ww''} R)

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- The addition maps of the iterated inverse image of a sheaf of modules and of the inverse
image along the composite agree. -/
lemma moduleAddHom_pullbackModuleObj_comp :
    Sheaf.moduleAddHom (pullbackRingSheaf J Φ (pullbackRingSheaf K Ψ R))
        (pullbackModuleObj J Φ (pullbackRingSheaf K Ψ R) (pullbackModuleObj K Ψ R G)) =
      Sheaf.moduleAddHom (pullbackRingSheaf J (Ψ ⋙ Φ) R)
        (pullbackModuleObj J (Ψ ⋙ Φ) R G) := by
  refine Sheaf.hom_ext_sections fun W p ↦ ?_
  rw [← Functor.prodObjMk_map_fst_map_snd (P := Sheaf.sectionsFunctor J W) p]
  exact ((moduleAddObj_pullbackModuleObj J Φ (pullbackRingSheaf K Ψ R)
        (pullbackModuleObj K Ψ R G) (Sheaf.sectionsFunctor J W) _ _).trans
      (moduleAddObj_pullbackModuleObj K Ψ R G (Φ ⋙ Sheaf.sectionsFunctor J W) _ _)).trans
    (moduleAddObj_pullbackModuleObj J (Ψ ⋙ Φ) R G (Sheaf.sectionsFunctor J W) _ _).symm

/-- The scalar actions of the iterated inverse image of a sheaf of modules and of the inverse
image along the composite agree, with no transport along the comparison of the inverse images
of the sheaf of rings. -/
lemma moduleSMulHom_pullbackModuleObj_comp :
    Sheaf.moduleSMulHom (pullbackRingSheaf J Φ (pullbackRingSheaf K Ψ R))
        (pullbackModuleObj J Φ (pullbackRingSheaf K Ψ R) (pullbackModuleObj K Ψ R G)) =
      Sheaf.moduleSMulHom (pullbackRingSheaf J (Ψ ⋙ Φ) R)
        (pullbackModuleObj J (Ψ ⋙ Φ) R G) := by
  refine Sheaf.hom_ext_sections fun W p ↦ ?_
  rw [← Functor.prodObjMk_map_fst_map_snd (P := Sheaf.sectionsFunctor J W) p]
  exact ((moduleSMulObj_pullbackModuleObj J Φ (pullbackRingSheaf K Ψ R)
        (pullbackModuleObj K Ψ R G) (Sheaf.sectionsFunctor J W) _ _).trans
      (moduleSMulObj_pullbackModuleObj K Ψ R G (Φ ⋙ Sheaf.sectionsFunctor J W) _ _)).trans
    (moduleSMulObj_pullbackModuleObj J (Ψ ⋙ Φ) R G (Sheaf.sectionsFunctor J W) _ _).symm

/-- The comparison of the iterated inverse image of a sheaf of modules with the inverse image
along the composite: the identity on underlying sheaves of sets, read as a morphism of sheaves
of modules over the iterated inverse image of the sheaf of rings. -/
noncomputable def pullbackModuleCompHom :
    pullbackModuleObj J Φ (pullbackRingSheaf K Ψ R) (pullbackModuleObj K Ψ R G) ⟶
      (SheafOfModules.restrictScalars (pullbackRingSheafCompIso J K Φ Ψ R).hom).obj
        (pullbackModuleObj J (Ψ ⋙ Φ) R G) :=
  homEquivSubtype.symm ⟨𝟙 (Φ.obj (Ψ.obj (Sheaf.moduleSheaf R G))),
    ((Category.comp_id (Sheaf.moduleAddHom (pullbackRingSheaf J Φ (pullbackRingSheaf K Ψ R))
            (pullbackModuleObj J Φ (pullbackRingSheaf K Ψ R)
              (pullbackModuleObj K Ψ R G)))).trans
        (moduleAddHom_pullbackModuleObj_comp J K Φ Ψ R G)).trans
      ((Category.id_comp (Sheaf.moduleAddHom
            (pullbackRingSheaf J Φ (pullbackRingSheaf K Ψ R))
            ((SheafOfModules.restrictScalars
              (pullbackRingSheafCompIso J K Φ Ψ R).hom).obj
                (pullbackModuleObj J (Ψ ⋙ Φ) R G)))).symm.trans
        (congrArg (fun m ↦ m ≫ Sheaf.moduleAddHom
            (pullbackRingSheaf J Φ (pullbackRingSheaf K Ψ R))
            ((SheafOfModules.restrictScalars
              (pullbackRingSheafCompIso J K Φ Ψ R).hom).obj
                (pullbackModuleObj J (Ψ ⋙ Φ) R G)))
          (Limits.prod.map_id_id (X := Φ.obj (Ψ.obj (Sheaf.moduleSheaf R G)))
            (Y := Φ.obj (Ψ.obj (Sheaf.moduleSheaf R G)))).symm)),
    ((Category.comp_id (Sheaf.moduleSMulHom (pullbackRingSheaf J Φ (pullbackRingSheaf K Ψ R))
            (pullbackModuleObj J Φ (pullbackRingSheaf K Ψ R)
              (pullbackModuleObj K Ψ R G)))).trans
        (moduleSMulHom_pullbackModuleObj_comp J K Φ Ψ R G)).trans
      ((Category.id_comp (Sheaf.moduleSMulHom
            (pullbackRingSheaf J Φ (pullbackRingSheaf K Ψ R))
            ((SheafOfModules.restrictScalars
              (pullbackRingSheafCompIso J K Φ Ψ R).hom).obj
                (pullbackModuleObj J (Ψ ⋙ Φ) R G)))).symm.trans
        (congrArg (fun m ↦ m ≫ Sheaf.moduleSMulHom
            (pullbackRingSheaf J Φ (pullbackRingSheaf K Ψ R))
            ((SheafOfModules.restrictScalars
              (pullbackRingSheafCompIso J K Φ Ψ R).hom).obj
                (pullbackModuleObj J (Ψ ⋙ Φ) R G)))
          (Limits.prod.map_id_id
            (X := Sheaf.ringSheaf (pullbackRingSheaf J Φ (pullbackRingSheaf K Ψ R)))
            (Y := Φ.obj (Ψ.obj (Sheaf.moduleSheaf R G)))).symm))⟩

/-- The comparison of iterated inverse images of a sheaf of modules is the identity on
underlying sheaves of sets. -/
@[simp]
lemma moduleSheafFunctor_map_pullbackModuleCompHom :
    (Sheaf.moduleSheafFunctor (pullbackRingSheaf J Φ (pullbackRingSheaf K Ψ R))).map
        (pullbackModuleCompHom J K Φ Ψ R G) =
      𝟙 (Φ.obj (Ψ.obj (Sheaf.moduleSheaf R G))) := rfl

/-- The comparison of iterated inverse images of a sheaf of modules is an isomorphism. -/
theorem isIso_pullbackModuleCompHom : IsIso (pullbackModuleCompHom J K Φ Ψ R G) := by
  have h : IsIso ((Sheaf.moduleSheafFunctor
      (pullbackRingSheaf J Φ (pullbackRingSheaf K Ψ R))).map
      (pullbackModuleCompHom J K Φ Ψ R G)) := by
    rw [moduleSheafFunctor_map_pullbackModuleCompHom]
    exact IsIso.id _
  exact isIso_of_reflects_iso (pullbackModuleCompHom J K Φ Ψ R G)
    (Sheaf.moduleSheafFunctor (pullbackRingSheaf J Φ (pullbackRingSheaf K Ψ R)))

/-- The comparison of the iterated inverse image of a sheaf of modules with the inverse image
along the composite, as an isomorphism. -/
noncomputable def pullbackModuleCompObjIso :
    pullbackModuleObj J Φ (pullbackRingSheaf K Ψ R) (pullbackModuleObj K Ψ R G) ≅
      (SheafOfModules.restrictScalars (pullbackRingSheafCompIso J K Φ Ψ R).hom).obj
        (pullbackModuleObj J (Ψ ⋙ Φ) R G) := by
  have := isIso_pullbackModuleCompHom J K Φ Ψ R G
  exact asIso (pullbackModuleCompHom J K Φ Ψ R G)

/-- The comparison isomorphism of iterated inverse images of a sheaf of modules is the identity
on underlying sheaves of sets. -/
@[simp]
lemma moduleSheafFunctor_map_pullbackModuleCompObjIso_hom :
    (Sheaf.moduleSheafFunctor (pullbackRingSheaf J Φ (pullbackRingSheaf K Ψ R))).map
        (pullbackModuleCompObjIso J K Φ Ψ R G).hom =
      𝟙 (Φ.obj (Ψ.obj (Sheaf.moduleSheaf R G))) :=
  moduleSheafFunctor_map_pullbackModuleCompHom J K Φ Ψ R G

end Module

/-- **Iterated inverse images of sheaves of modules.**  Transporting a sheaf of modules along
`Ψ` and then along `Φ` is transporting it along `Ψ ⋙ Φ`, the scalars being read through the
comparison `Stacks.Sheaves.ToposPullback.pullbackRingSheafCompIso` of the transported sheaves of
rings. -/
noncomputable def pullbackModuleCompIso :
    pullbackModuleFunctor K Ψ R ⋙ pullbackModuleFunctor J Φ (pullbackRingSheaf K Ψ R) ≅
      pullbackModuleFunctor J (Ψ ⋙ Φ) R ⋙
        SheafOfModules.restrictScalars (pullbackRingSheafCompIso J K Φ Ψ R).hom :=
  NatIso.ofComponents (fun G ↦ pullbackModuleCompObjIso J K Φ Ψ R G)
    (fun {_G _G'} _φ ↦ hom_ext_moduleSheafFunctor
      ((((Sheaf.moduleSheafFunctor (pullbackRingSheaf J Φ (pullbackRingSheaf K Ψ R))).map_comp
            _ _).trans (Category.comp_id _)).trans
        ((Category.id_comp _).trans
          (((Sheaf.moduleSheafFunctor
            (pullbackRingSheaf J Φ (pullbackRingSheaf K Ψ R))).map_comp _ _).symm))))

end Comp

end Stacks.Sheaves.ToposPullback

end
