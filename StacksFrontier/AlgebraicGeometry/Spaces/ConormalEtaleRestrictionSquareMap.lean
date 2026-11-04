module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSquarePieceMapCompositionLaw
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitStructureSheaf

/-!
# The étale-restriction comparison is the canonical map of its cartesian square

Let `i : Z ⟶ X` be a morphism of algebraic spaces over a scheme `S`, let `φ : U ⟶ X` be étale and
let

```
Z_U --p--> Z
|i_U       |i
U  --φ-->  X
```

be the cartesian square it induces.  [Stacks Project, Tag 09RR] identifies the inverse image
along `p` of the conormal algebra of `i` with the conormal algebra of `i_U`, degree by degree, as
`AlgebraicGeometry.Space.conormalAlgebraEtaleRestrictionPieceIso`, and [Stacks Project, Tag 04CO]
is its degree-one case for the conormal module.  The square is also a commutative square of the
kind [Stacks Project, Tag 04CP] attaches a canonical map to.  This file proves that **the two
agree**: 09RR's comparison is the canonical map of the square.

That is what makes a change of ambient space an instance of the canonical map, so that the
composition law `AlgebraicGeometry.Space.conormalMapOfImmersions_comp` applies to it — which is
how the reduction of part (2) of [Stacks Project, Tag 04G2] to a pair of ambient open subspaces
is carried.

## Main results

* `AlgebraicGeometry.Space.modulePullbackSquareCompIso_eq`: the square comparison used by 09RR is
  `AlgebraicGeometry.Space.squarePullbackCompIso` of the same square.
* `Stacks.SheafOfModules.Submodule.eqToHom_comp_ι` and
  `AlgebraicGeometry.Space.etaleModulePullback_idealSheafZPow_eqToHom_comp_ι`: the equality of the
  étale restriction of a power of a sheaf of ideals with the power of the restricted sheaf of
  ideals is compatible with the two inclusions into the structure sheaves.
* `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_hom_app_kernelIdealSheafZPow`:
  Equation 03LW at a power of the kernel ideal sheaf, transported, is
  `AlgebraicGeometry.Space.kernelIdealSquareMap` of the square.
* `AlgebraicGeometry.Space.conormalAlgebraEtaleRestrictionPieceIso_hom_eq`: **09RR's comparison
  is `AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap` of the square**, which is the
  canonical map of [Stacks Project, Tag 04CP] in degree `n`.

## Implementation notes

**The unfolding of 09RR's comparison is made at the level of isomorphisms, not of forward
maps**, by `AlgebraicGeometry.Space.conormalAlgebraEtaleRestrictionPieceIso_eq`, with the
passage to forward maps carried out generically by
`Stacks.CategoryTheory.trans_mapIso_trans_mapIso_hom`.  With the unfolding stated
directly between the forward maps the elaborator accepts it and the **kernel** then runs out of
budget — 2.9 minutes to a deterministic timeout — while the isomorphism-level identity is
`Eq.refl` and the whole file checks in under seven seconds.  Projecting `hom` out of the
composite is what drives the conversion check into the construction of the inverse image of
modules.

## References

* [Stacks Project, Tag 09RR](https://stacks.math.columbia.edu/tag/09RR)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U X Z ZU : AlgebraicSpaces B S hS}

/-- **The square comparison of [Stacks Project, Tag 09RR] is
`AlgebraicGeometry.Space.squarePullbackCompIso` of the same square.**  The two definitions have
the same body: `AlgebraicGeometry.Space.modulePullbackSquareCompIso` was written for a cartesian
square with an étale transverse edge and `AlgebraicGeometry.Space.squarePullbackCompIso` for an
arbitrary commutative square, and neither uses anything but the composition comparison of
[Stacks Project, Tag 03LU] and the commutativity. -/
theorem modulePullbackSquareCompIso_eq (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X) (φ : U ⟶ X)
    (hsq : iU ≫ φ = p ≫ i) :
    modulePullbackSquareCompIso B S hS p iU i φ hsq =
      squarePullbackCompIso B S hS iU i p φ hsq :=
  rfl

end AlgebraicGeometry.Space

namespace Stacks.CategoryTheory

universe v₁ u₁ v₂ u₂

/-- **The forward map of a composite of two images of isomorphisms under one functor**: the
functor's image of the composite of the two forward maps.

Stated with the functor, the three objects and the three isomorphisms as variables, so that the
two applications of `CategoryTheory.Functor.map_comp` and the two projections out of
`CategoryTheory.Iso.trans` are carried out once, where they cost nothing. -/
theorem trans_mapIso_trans_mapIso_hom {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] (F : C ⥤ D) {A : D} {Y Y' Y'' : C} (e : A ≅ F.obj Y) (α : Y ≅ Y')
    (β : Y' ≅ Y'') :
    (e ≪≫ F.mapIso α ≪≫ F.mapIso β).hom = e.hom ≫ F.map (α.hom ≫ β.hom) :=
  congrArg (fun m ↦ e.hom ≫ m) (F.map_comp α.hom β.hom).symm

end Stacks.CategoryTheory

namespace Stacks.SheafOfModules.Submodule

universe w v' u'

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  {R : Sheaf J RingCat.{w}} {M : SheafOfModules.{w} R}

omit [J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})] in
/-- **Transport along an equality of sheaf submodules is compatible with the two inclusions.**
For equal submodules `A = A'` of `M`, the transport of the first onto the second, followed by the
inclusion of the second, is the inclusion of the first.

The equality of the two sheaves of modules is taken as a separate hypothesis rather than as
`congrArg`: in the application the equality at hand has a different proof term, and by proof
irrelevance `CategoryTheory.eqToHom` does not depend on which. -/
theorem eqToHom_comp_ι {A A' : M.Submodule} (hA : A = A')
    (hobj : A.toSheafOfModules = A'.toSheafOfModules) :
    CategoryTheory.eqToHom hobj ≫ A'.ι = A.ι := by
  subst hA
  rw [CategoryTheory.eqToHom_refl]
  exact Category.id_comp _

end Stacks.SheafOfModules.Submodule

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U X Z ZU : AlgebraicSpaces B S hS}

/-- The inclusion of the étale restriction of the `n`-th power of a sheaf of ideals into `𝒪_U` is
the étale restriction of the inclusion into `𝒪_X`: étale restriction is restriction of sections
along `AlgebraicGeometry.Space.smallEtalePostcomp`, and it leaves an inclusion of submodules an
inclusion of submodules. -/
theorem etaleRestrictionIdealSheafZPowSheaf_ι (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (𝓘 : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (𝓙 : (SheafOfModules.unit (structureRingSheaf B S hS U)).Submodule)
    (h : ∀ W : SmallEtale B S hS U.1,
      SheafOfModules.idealAt 𝓙 (Opposite.op W) =
        SheafOfModules.idealAt 𝓘 (Opposite.op ((smallEtalePostcomp B S hS φ hφ).obj W)))
    (n : ℤ) :
    (etaleRestrictionIdealSheafZPowSheaf B S hS φ hφ 𝓘 𝓙 h n).ι =
      (etaleModulePullback.{u, u} B S hS φ hφ).map
        (SheafOfModules.idealSheafZPow 𝓘 n).ι :=
  rfl

/-- **The equality of the two powers of the sheaves of ideals is compatible with the inclusions
into the structure sheaves.**  The transport of
`AlgebraicGeometry.Space.etaleModulePullback_idealSheafZPow_eq`, followed by the inclusion of
`𝓙ⁿ` into `𝒪_U`, is the étale restriction of the inclusion of `𝓘ⁿ` into `𝒪_X`.

The equality of modules comes from the equality of *submodules*
`AlgebraicGeometry.Space.etaleRestrictionIdealSheafZPowSheaf_eq`, and the transport along an
equality of submodules carries the inclusion of the larger onto the inclusion of the smaller by
`Stacks.SheafOfModules.Submodule.eqToHom_comp_ι`. -/
theorem etaleModulePullback_idealSheafZPow_eqToHom_comp_ι (φ : U ⟶ X)
    (hφ : IsEtale B S hS φ.hom)
    (𝓘 : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (𝓙 : (SheafOfModules.unit (structureRingSheaf B S hS U)).Submodule)
    (h : ∀ W : SmallEtale B S hS U.1,
      SheafOfModules.idealAt 𝓙 (Opposite.op W) =
        SheafOfModules.idealAt 𝓘 (Opposite.op ((smallEtalePostcomp B S hS φ hφ).obj W)))
    (n : ℤ) :
    eqToHom (etaleModulePullback_idealSheafZPow_eq B S hS φ hφ 𝓘 𝓙 h n) ≫
        (SheafOfModules.idealSheafZPow 𝓙 n).ι =
      (etaleModulePullback.{u, u} B S hS φ hφ).map
        (SheafOfModules.idealSheafZPow 𝓘 n).ι :=
  (Stacks.SheafOfModules.Submodule.eqToHom_comp_ι
      (etaleRestrictionIdealSheafZPowSheaf_eq B S hS φ hφ 𝓘 𝓙 h n)
      (etaleModulePullback_idealSheafZPow_eq B S hS φ hφ 𝓘 𝓙 h n)).trans
    (etaleRestrictionIdealSheafZPowSheaf_ι B S hS φ hφ 𝓘 𝓙 h n)

/-- **Equation 03LW at a power of the kernel ideal sheaf, transported onto the power of the
kernel ideal sheaf of the base change, is the canonical map of the square.**

Both sides are morphisms into the `n`-th power of `Ker(i_U^♯)`, whose inclusion into `𝒪_U` is a
monomorphism, so it is enough to compare them after that inclusion.  There the left-hand side
becomes, by
`AlgebraicGeometry.Space.etaleModulePullback_idealSheafZPow_eqToHom_comp_ι` and the naturality of
Equation 03LW, the inverse image along `φ` of the inclusion followed by Equation 03LW at the
structure sheaf, which is `AlgebraicGeometry.Space.structureModulePullbackMap` by
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_hom_app_unit_eq`; and that is what
`AlgebraicGeometry.Space.kernelIdealSquareMap_comp_ι` says the right-hand side becomes. -/
theorem modulePullbackIsoEtaleModulePullback_hom_app_kernelIdealSheafZPow (p : ZU ⟶ Z)
    (iU : ZU ⟶ U) (i : Z ⟶ X) (φ : U ⟶ X) (sq : IsPullback p iU i φ)
    (hφ : IsEtale B S hS φ.hom) (n : ℤ) :
    (modulePullbackIsoEtaleModulePullback B S hS φ hφ).hom.app
          (kernelIdealSheafZPow B S hS i n).toSheafOfModules ≫
        eqToHom (etaleModulePullback_kernelIdealSheafZPow_eq B S hS p iU i φ sq hφ n) =
      kernelIdealSquareMap B S hS iU i p φ sq.w.symm n := by
  refine (cancel_mono (kernelIdealSheafZPow B S hS iU n).ι).1 ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun m ↦
      (modulePullbackIsoEtaleModulePullback B S hS φ hφ).hom.app
        (kernelIdealSheafZPow B S hS i n).toSheafOfModules ≫ m)
    (etaleModulePullback_idealSheafZPow_eqToHom_comp_ι B S hS φ hφ
      (kernelIdealSheaf B S hS i) (kernelIdealSheaf B S hS iU)
      (fun W ↦ kernelIdealSheaf_baseChange_obj B S hS p iU i φ sq hφ W) n)) ?_
  refine Eq.trans ((modulePullbackIsoEtaleModulePullback B S hS φ hφ).hom.naturality
    (kernelIdealSheafZPow B S hS i n).ι).symm ?_
  refine Eq.trans ?_ (kernelIdealSquareMap_comp_ι B S hS iU i p φ sq.w.symm n).symm
  exact congrArg (fun m ↦ (modulePullback B S hS φ).map
      (kernelIdealSheafZPow B S hS i n).ι ≫ m)
    (modulePullbackIsoEtaleModulePullback_hom_app_unit_eq B S hS φ hφ)

/-- **The comparison of [Stacks Project, Tag 09RR] in degree `n`, unfolded as an isomorphism**:
the square comparison, then the inverse image along `i_U` of Equation 03LW, then the inverse image
along `i_U` of the transport along the equality of the two powers of the kernel ideal sheaves.

This is the definition, stated at the level of isomorphisms rather than of their forward maps.
The forward-map form does not fit the kernel's budget: projecting `hom` out of the composite
drives the conversion check into the construction of the inverse image of modules, whereas the
isomorphism-level identity is `Eq.refl`. -/
theorem conormalAlgebraEtaleRestrictionPieceIso_eq (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X)
    (φ : U ⟶ X) (sq : IsPullback p iU i φ) (hφ : IsEtale B S hS φ.hom) (n : ℤ) :
    conormalAlgebraEtaleRestrictionPieceIso B S hS p iU i φ sq hφ n =
      (squarePullbackCompIso B S hS iU i p φ sq.w.symm).app
          (kernelIdealSheafZPow B S hS i n).toSheafOfModules ≪≫
        (modulePullback B S hS iU).mapIso
            ((modulePullbackIsoEtaleModulePullback B S hS φ hφ).app
              (kernelIdealSheafZPow B S hS i n).toSheafOfModules) ≪≫
          (modulePullback B S hS iU).mapIso
            (eqToIso (etaleModulePullback_kernelIdealSheafZPow_eq B S hS p iU i φ sq hφ n)) :=
  rfl

/-- The comparison of [Stacks Project, Tag 09RR] in degree `n`, written as the square comparison
followed by the inverse image along `i_U` of a single morphism. -/
theorem conormalAlgebraEtaleRestrictionPieceIso_hom (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X)
    (φ : U ⟶ X) (sq : IsPullback p iU i φ) (hφ : IsEtale B S hS φ.hom) (n : ℤ) :
    (conormalAlgebraEtaleRestrictionPieceIso B S hS p iU i φ sq hφ n).hom =
      (squarePullbackCompIso B S hS iU i p φ sq.w.symm).hom.app
          (kernelIdealSheafZPow B S hS i n).toSheafOfModules ≫
        (modulePullback B S hS iU).map
          ((modulePullbackIsoEtaleModulePullback B S hS φ hφ).hom.app
              (kernelIdealSheafZPow B S hS i n).toSheafOfModules ≫
            eqToHom (etaleModulePullback_kernelIdealSheafZPow_eq B S hS p iU i φ sq hφ n)) :=
  (congrArg Iso.hom
        (conormalAlgebraEtaleRestrictionPieceIso_eq B S hS p iU i φ sq hφ n)).trans
    (Stacks.CategoryTheory.trans_mapIso_trans_mapIso_hom (modulePullback B S hS iU)
      ((squarePullbackCompIso B S hS iU i p φ sq.w.symm).app
        (kernelIdealSheafZPow B S hS i n).toSheafOfModules)
      ((modulePullbackIsoEtaleModulePullback B S hS φ hφ).app
        (kernelIdealSheafZPow B S hS i n).toSheafOfModules)
      (eqToIso (etaleModulePullback_kernelIdealSheafZPow_eq B S hS p iU i φ sq hφ n)))

/-- **Stacks 09RR's comparison is the canonical map of [Stacks Project, Tag 04CP] of its
cartesian square.**  For `i : Z ⟶ X`, an étale `φ : U ⟶ X` and the cartesian square it induces,
the degree-`n` comparison `p^*(𝒞_{Z/X,*})_n ≅ (𝒞_{Z_U/U,*})_n` of
`AlgebraicGeometry.Space.conormalAlgebraEtaleRestrictionPieceIso` is
`AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap` of the square.

Both factor as the square comparison followed by the inverse image along `i_U` of a map of the
`n`-th powers of the kernel ideal sheaves on the ambient spaces — the square comparisons agreeing
by `AlgebraicGeometry.Space.modulePullbackSquareCompIso_eq` and the two maps of ideal sheaves by
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_hom_app_kernelIdealSheafZPow`.

This is what makes a change of ambient space an instance of the canonical map, so that the
composition law `AlgebraicGeometry.Space.conormalMapOfImmersions_comp` applies to it. -/
theorem conormalAlgebraEtaleRestrictionPieceIso_hom_eq (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X)
    (φ : U ⟶ X) (sq : IsPullback p iU i φ) (hφ : IsEtale B S hS φ.hom) (n : ℤ) :
    (conormalAlgebraEtaleRestrictionPieceIso B S hS p iU i φ sq hφ n).hom =
      conormalAlgebraSquarePieceMap B S hS iU i p φ sq.w.symm n :=
  ((conormalAlgebraEtaleRestrictionPieceIso_hom B S hS p iU i φ sq hφ n).trans
      (congrArg (fun m ↦ (squarePullbackCompIso B S hS iU i p φ sq.w.symm).hom.app
            (kernelIdealSheafZPow B S hS i n).toSheafOfModules ≫
          (modulePullback B S hS iU).map m)
        (modulePullbackIsoEtaleModulePullback_hom_app_kernelIdealSheafZPow B S hS p iU i φ sq
          hφ n))).trans
    (conormalAlgebraSquarePieceMap_eq_comp B S hS iU i p φ sq.w.symm n).symm

end AlgebraicGeometry.Space

end
