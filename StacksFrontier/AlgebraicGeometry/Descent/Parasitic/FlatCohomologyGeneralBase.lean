module

public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FlatCohomologyBaseChangeFactor
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FlatCohomologySmallSiteComparison
public import StacksCore.Tactic.StacksAttribute

/-!
# The conclusion of [Stacks, Tag 0756] over a general flat object, at `τ = Zariski`

Let `B` be a big fppf site, `S` a scheme below its cutoff and `𝒢` a sheaf of `𝒪`-modules on
`(Sch/S)_fppf` satisfying the two hypotheses of [Stacks, Tag 0756] at `τ = Zar`:

1. `𝒢|_{S_Zar}` is quasi-coherent;
2. for every object of `(Sch/S)_fppf` flat and locally of finite presentation over `S`, with
   structure morphism `g : X ⟶ S`, the canonical map
   `g^*_{Zar, small}(𝒢|_{S_Zar}) ⟶ 𝒢|_{X_Zar}` of
   `AlgebraicGeometry.BigFppfOver.zariskiClause2Map` is an isomorphism.

`StacksFrontier/AlgebraicGeometry/Descent/Parasitic/FlatCohomologySmallSiteComparison.lean` proves
the tag's conclusion

```
H^p(U, 𝒢)  ≅  H^p(U, 𝒢|_{U_Zar})      for every p
```

in the single instance `U = S`.  This file proves it for **every** `U` flat and locally of
finite presentation over `S`, and that is the whole clause at `τ = Zar`.

## The reduction, and the one thing it needed

Write `X` for the scheme of `U` and `𝒢_U = 𝒢|_{(Sch/X)_fppf}` for
`(objRestrict B S hS U).obj 𝒢`.  Cohomology over `U` is global cohomology of `𝒢_U` on
`(Sch/X)_fppf` — the localization of `(Sch/S)_fppf` at `U` is the big fppf site of `X` by
[Stacks, Tag 06WI], `AlgebraicGeometry.BigFppfOver.objEquiv` — so the conclusion at `U`
is `AlgebraicGeometry.BigFppfOver.zariskiSmallSiteCohomologyAddEquiv` applied **at the base `X`**
to `𝒢_U`.  Its two hypotheses there are clauses (1) and (2) for `𝒢_U` over `X`.

Clause (1) over `X` was already available:
`AlgebraicGeometry.BigFppfOver.isQuasicoherent_objZariskiRestrict` derives it from clause (2) at
`U` itself.  Clause (2) over `X` is what was missing, and it is a statement about **counits**:
unwinding `AlgebraicGeometry.BigFppfOver.zariskiClause2Map` at the base `X`, it asks that the
counit of `AlgebraicGeometry.BigFppfOver.associatedModuleAdjunction` at `X`, applied to `𝒢_U`,
be an isomorphism on `Y_Zar` for every `Y` flat and locally of finite presentation over `X`.

[Stacks, Tag 03DV] functorial in the object,
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso`, is a natural isomorphism

```
α : g^*(-)^a  ≅  ((-)^a)|_{(Sch/X)_fppf}
```

between the two **left** adjoints and says nothing about counits.  What relates the two counits
is its **mate square**, `AlgebraicGeometry.BigFppfOver.mateSquare_objRestrictCounit` below:

```
      α_{𝒢|_{S_Zar}}                      (g^*(𝒢|_{S_Zar}))^a ──(ε_X)_{𝒢_U}──▶ 𝒢_U
(𝒢|_{S_Zar})^a|_{(Sch/X)} ◀────────  with                ▲
                                                 ((-)^a of clause (2)'s map)
```

that is

```
α_{𝒢|_{S_Zar}} ≫ (ε_S)_𝒢|_{(Sch/X)_fppf}  =  (zariskiClause2Map)^a ≫ (ε_X)_{𝒢_U}.
```

It needs no new mathematics once the right thing is said: `zariskiClause2Map` is, by its own
definition, the adjoint **transpose** under `associatedModuleAdjunction` at `X` of the left-hand
side, so the square is `Equiv.symm_apply_apply` for that transpose — the triangle identity and
nothing else.  This is the sense in which [Stacks, Tag 03DV] is compatible with the two
associated-module adjunctions.

With the square, clause (2) at `U` makes `(zariskiClause2Map)^a` invertible, so the counit at
`X` is `α` followed by the restricted counit at `S`, up to an isomorphism on the source; and
restricting further to `Y_Zar` turns the right-hand side into clause (2)'s hypothesis at the
**composite** object `Y → X → S`, which is flat and locally of finite presentation over `S`
because both factors are.  The passage from `𝒢|_{Y over X}` to `𝒢|_{Y over S}` is
`AlgebraicGeometry.BigFppfOver.objRestrictComp`.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.objRestrictCounit`: the counit `φ : (𝒢|_{S_Zar})^a ⟶ 𝒢` of
  `AlgebraicGeometry.BigFppfOver.associatedModuleAdjunction` restricted to `(Sch/X)_fppf`, with
  its source spelled as the value of `(-)^a ⋙ (-)|_{(Sch/X)_fppf}` so that it composes with the
  natural isomorphism of [Stacks, Tag 03DV].
* `AlgebraicGeometry.BigFppfOver.objComp`: the composite object `Y → X → S` of `(Sch/S)_fppf`
  attached to an object `Y` of `(Sch/X)_fppf`.

## Main results

* `AlgebraicGeometry.BigFppfOver.mateSquare_objRestrictCounit`: **the mate square for
  `associatedModule ⊣ restrictModule` along the restriction to the big fppf site of an object**
  — the compatibility of [Stacks, Tag 03DV] with the two counits.
* `AlgebraicGeometry.BigFppfOver.isIso_zariskiClause2Map_objRestrict`: **clause (2) of
  [Stacks, Tag 0756] holds at the base `X` for `𝒢_U`** whenever it holds at `S` for `𝒢` and `U`
  is flat and locally of finite presentation over `S`.
* `AlgebraicGeometry.BigFppfOver.flatSmallSiteCohomologyAddEquiv`: **the conclusion of
  [Stacks, Tag 0756] at `τ = Zar`, for every `U` flat and locally of finite presentation over
  `S`**, from clauses (1) and (2) and nothing else.
* `AlgebraicGeometry.BigFppfOver.flatSmallZariskiSiteCohomologyAddEquiv`: the same with the
  right-hand side read on the small Zariski site of [Stacks, Tag 020T] (2).

## Implementation notes

The étale half of the tag is
`AlgebraicGeometry.BigFppfOver.flatSmallEtaleSiteCohomologyAddEquiv`
(`StacksFrontier/AlgebraicGeometry/Descent/Parasitic/FlatCohomologyEtaleConclusion.lean`), which
reduces to the statement here; nothing in this file is about the étale topology.

Clause (2) enters as `AlgebraicGeometry.BigFppfOver.zariskiClause2Map`, which needs no hypothesis
on `𝒢` to be defined and is the base-change map of the square of ringed sites: it is the adjoint
transpose of the restriction map `𝒢|_{S_Zar} ⟶ g_*(𝒢|_{X_Zar})` by
`AlgebraicGeometry.BigFppfOver.zariskiClause2Map_eq_homEquiv_symm`.

## References

* [Stacks Project, Tag 0756](https://stacks.math.columbia.edu/tag/0756)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 020T](https://stacks.math.columbia.edu/tag/020T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.MateSquare

/-- **An isomorphism on the source does not change whether a functor inverts a morphism.**  If
`p` is an isomorphism and `p ≫ g = f`, then `F.map g` is an isomorphism as soon as `F.map f` is:
`F.map g` is `inv (F.map p) ≫ F.map f`.

This is the shape in which a mate square is used: the square expresses `p ≫ g = f` with `p` the
image of an invertible comparison map, `g` the counit one wants to control and `f` the counit one
controls. -/
public theorem isIso_map_of_comp_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A A' X : C} (p : A ⟶ A') {f : A ⟶ X} {g : A' ⟶ X}
    (hp : IsIso p) (hg : p ≫ g = f) (h : IsIso (F.map f)) :
    IsIso (F.map g) := by
  have := hp
  have := h
  have hgg : F.map g = inv (F.map p) ≫ F.map f := by
    rw [← hg, F.map_comp, IsIso.inv_hom_id_assoc]
  rw [hgg]
  infer_instance

end Stacks.MateSquare

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (T : BigFppfOver B S hS) (G : SheafOfModules.{u} (structureSheaf B S hS))

/-! ### The mate square -/

/-- **The comparison map `φ : (𝒢|_{S_Zar})^a ⟶ 𝒢` restricted to the big fppf site of the scheme
of `T`.**  This is `(objRestrict B S hS T).map (zariskiComparisonMap B S hS G)`; the only reason
it is given a name is its *stated* source, which is the value at `𝒢|_{S_Zar}` of the composite
`(-)^a ⋙ (-)|_{(Sch/X)_fppf}`.  That is the target of
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso`, so the two compose on the
nose rather than through an unfolding of
`AlgebraicGeometry.BigFppfOver.zariskiComparisonModule`. -/
public def objRestrictCounit :
    (associatedModule B S hS ⋙ objRestrict B S hS T).obj ((restrictModule B S hS).obj G) ⟶
      (objRestrict B S hS T).obj G :=
  (objRestrict B S hS T).map (zariskiComparisonMap B S hS G)

/-- **The mate square for `associatedModule ⊣ restrictModule` along the restriction to the big
fppf site of an object.**  For `g : X ⟶ S` the structure morphism of an object `T` of
`(Sch/S)_fppf` and `𝒢` a sheaf of `𝒪`-modules on `(Sch/S)_fppf` with `𝒢|_{S_Zar}` quasi-coherent,

```
α_{𝒢|_{S_Zar}} ≫ φ|_{(Sch/X)_fppf}  =  (zariskiClause2Map)^a ≫ φ_X
```

where `α` is [Stacks, Tag 03DV] functorial in the object,
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso`; `φ` and `φ_X` are the counits
of `AlgebraicGeometry.BigFppfOver.associatedModuleAdjunction` at `S` and at `X`, i.e. the
comparison maps of [Stacks, Tag 0756] there; and `(-)^a` on the right is the associated-module
functor of the big fppf site of `X`.

[Stacks, Tag 03DV] compares the two **left** adjoints and by itself says nothing about counits.
This square is what makes it a statement about them, and it is free: by definition
`AlgebraicGeometry.BigFppfOver.zariskiClause2Map` is the adjoint transpose, under the
associated-module adjunction at `X`, of the left-hand side — its first factor
`AlgebraicGeometry.BigFppfOver.zariskiComparisonRestrictIso` is the unit at `g^*(𝒢|_{S_Zar})`
followed by the restriction of `α`, and its second is the restriction of `φ`.  So the square is
the inverse pair `Equiv.symm_apply_apply` of that transpose, which is the triangle identity. -/
public theorem mateSquare_objRestrictCounit :
    ((associatedModuleObjRestrictNatIso B S hS T).app
          ((restrictModule B S hS).obj G)).hom ≫ objRestrictCounit B S hS T G =
      (associatedModule B (objScheme B S hS T) (contains_objScheme B S hS T)).map
          (zariskiClause2Map B S hS T G) ≫
        zariskiComparisonMap B (objScheme B S hS T) (contains_objScheme B S hS T)
          ((objRestrict B S hS T).obj G) := by
  have hc2 : zariskiClause2Map B S hS T G =
      (associatedModuleAdjunction B (objScheme B S hS T)
            (contains_objScheme B S hS T)).homEquiv _ _
        (((associatedModuleObjRestrictNatIso B S hS T).app
              ((restrictModule B S hS).obj G)).hom ≫ objRestrictCounit B S hS T G) := by
    rw [Adjunction.homEquiv_unit, Functor.map_comp]
    simp only [zariskiClause2Map, objRestrictCounit, Category.assoc]
    rfl
  rw [hc2, zariskiComparisonMap_eq B (objScheme B S hS T) (contains_objScheme B S hS T)
    ((objRestrict B S hS T).obj G), ← Adjunction.homEquiv_counit, Equiv.symm_apply_apply]

/-! ### The composite object `Y → X → S` -/

section Comp

variable {B S hS T}

/-- **The composite object.**  An object `Y` of the big fppf category over the scheme `X` of an
object `T` of the big fppf category over `S`, read as an object of the latter by composing its
structure morphism with that of `T`. -/
public def objComp
    (Y : BigFppfOver B (objScheme B S hS T) (contains_objScheme B S hS T)) :
    BigFppfOver B S hS :=
  Over.mk (Y.hom ≫ T.hom)

/-- The composite object lies over `T`, by its own structure morphism. -/
public def objCompHom
    (Y : BigFppfOver B (objScheme B S hS T) (contains_objScheme B S hS T)) :
    objComp Y ⟶ T :=
  Over.homMk Y.hom

/-- `Y` is recovered from `AlgebraicGeometry.BigFppfOver.objCompHom`, which is what lets
`AlgebraicGeometry.BigFppfOver.objRestrictComp` be read at `Y`. -/
public theorem objComp_mk
    (Y : BigFppfOver B (objScheme B S hS T) (contains_objScheme B S hS T)) :
    Over.mk (objCompHom Y).left = Y := rfl

/-- A morphism property stable under composition holds for the composite object if it holds for
`T` and for `Y`. -/
private theorem property_objComp (W : MorphismProperty Scheme.{u}) [W.IsStableUnderComposition]
    (Y : BigFppfOver B (objScheme B S hS T) (contains_objScheme B S hS T))
    (h1 : W ((Over.post B.inclusion).obj T).hom)
    (h2 : W ((Over.post B.inclusion).obj Y).hom) :
    W ((Over.post B.inclusion).obj (objComp Y)).hom := by
  have heq : ((Over.post B.inclusion).obj (objComp (T := T) Y)).hom
      = ((Over.post B.inclusion).obj Y).hom ≫ ((Over.post B.inclusion).obj T).hom :=
    B.inclusion.map_comp _ _
  rw [heq]
  exact MorphismProperty.comp_mem W _ _ h2 h1

/-- **The composite object is flat over `S`** when `Y` is flat over `X` and `T` is flat over
`S`: its structure morphism is the composite of the two, and flatness is stable under
composition. -/
@[ega "IV 2.1.6" "special case"]
public theorem flat_objComp
    (Y : BigFppfOver B (objScheme B S hS T) (contains_objScheme B S hS T))
    (h1 : Flat ((Over.post B.inclusion).obj T).hom)
    (h2 : Flat ((Over.post B.inclusion).obj Y).hom) :
    Flat ((Over.post B.inclusion).obj (objComp Y)).hom :=
  property_objComp (@Flat) Y h1 h2

/-- **The composite object is locally of finite presentation over `S`** when `Y` is over `X` and
`T` is over `S`: its structure morphism is the composite of the two, and the property is stable
under composition. -/
@[ega "IV 1.4.3" "(ii), special case"]
public theorem locallyOfFinitePresentation_objComp
    (Y : BigFppfOver B (objScheme B S hS T) (contains_objScheme B S hS T))
    (h1 : LocallyOfFinitePresentation ((Over.post B.inclusion).obj T).hom)
    (h2 : LocallyOfFinitePresentation ((Over.post B.inclusion).obj Y).hom) :
    LocallyOfFinitePresentation ((Over.post B.inclusion).obj (objComp Y)).hom :=
  property_objComp (@LocallyOfFinitePresentation) Y h1 h2

/-- Restriction to the big fppf site of the composite object, with its target read at the scheme
of `Y` rather than at the scheme of `AlgebraicGeometry.BigFppfOver.objComp`.  The two schemes are
the same; naming the functor once at the spelling its consumers use keeps the two out of each
other's way. -/
public def objRestrictOfComp
    (Y : BigFppfOver B (objScheme B S hS T) (contains_objScheme B S hS T)) :
    SheafOfModules.{u} (structureSheaf B S hS) ⥤
      SheafOfModules.{u} (structureSheaf B
        (objScheme B (objScheme B S hS T) (contains_objScheme B S hS T) Y)
        (contains_objScheme B (objScheme B S hS T) (contains_objScheme B S hS T) Y)) :=
  objRestrict B S hS (objComp Y)

/-- **Restricting to `(Sch/X)_fppf` and then to the big fppf site of `Y` over `X` is restricting
to the big fppf site of the composite object.**  This is
`AlgebraicGeometry.BigFppfOver.objRestrictComp` at
`AlgebraicGeometry.BigFppfOver.objCompHom`, read through
`AlgebraicGeometry.BigFppfOver.objComp_mk`. -/
public def objRestrictCompObj
    (Y : BigFppfOver B (objScheme B S hS T) (contains_objScheme B S hS T)) :
    objRestrict B S hS T ⋙
        objRestrict B (objScheme B S hS T) (contains_objScheme B S hS T) Y ≅
      objRestrictOfComp Y :=
  objRestrictComp B S hS (objCompHom Y)

/-- **A morphism inverted on the small Zariski site of the composite object is inverted on the
small Zariski site of `Y` over `X`**, and conversely: the two restrictions are isomorphic
functors by `AlgebraicGeometry.BigFppfOver.objRestrictCompObj`. -/
public theorem isIso_map_objRestrict_comp
    (Y : BigFppfOver B (objScheme B S hS T) (contains_objScheme B S hS T))
    {M N : SheafOfModules.{u} (structureSheaf B S hS)} (φ : M ⟶ N)
    (h : IsIso ((restrictModule B (objScheme B (objScheme B S hS T)
            (contains_objScheme B S hS T) Y)
          (contains_objScheme B (objScheme B S hS T) (contains_objScheme B S hS T) Y)).map
        ((objRestrictOfComp Y).map φ))) :
    IsIso ((restrictModule B (objScheme B (objScheme B S hS T)
          (contains_objScheme B S hS T) Y)
        (contains_objScheme B (objScheme B S hS T) (contains_objScheme B S hS T) Y)).map
      ((objRestrict B (objScheme B S hS T) (contains_objScheme B S hS T) Y).map
        ((objRestrict B S hS T).map φ))) :=
  (NatIso.isIso_map_iff (Functor.isoWhiskerRight (objRestrictCompObj Y)
    (restrictModule B (objScheme B (objScheme B S hS T) (contains_objScheme B S hS T) Y)
      (contains_objScheme B (objScheme B S hS T) (contains_objScheme B S hS T) Y))) φ).mpr h

/-- **The comparison map at the base `X` is an isomorphism on the small Zariski site of `Y`.**
Let `𝒢` be a sheaf of `𝒪`-modules on `(Sch/S)_fppf` with `𝒢|_{S_Zar}` quasi-coherent, let `T` be
an object of `(Sch/S)_fppf` with scheme `X`, and let `Y` be an object of `(Sch/X)_fppf`.  If the
canonical map of clause (2) of [Stacks, Tag 0756] is an isomorphism at `T` and at the composite
object `Y → X → S`, then the counit of the associated-module adjunction **at the base `X`**,
applied to `𝒢|_{(Sch/X)_fppf}`, is an isomorphism on the small Zariski site of the scheme of `Y`.

This is `AlgebraicGeometry.BigFppfOver.mateSquare_objRestrictCounit` used in the only way a mate
square can be used.  Clause (2) at `T` makes the left factor of the right-hand side of the square
invertible, so the counit at `X` is the two isomorphisms `α` and `(-)^a` of clause (2)'s map
followed by the restriction of the counit at `S`; and the restriction of the counit at `S` to the
small Zariski site of `Y` over `X` is its restriction to the small Zariski site of the composite
object, by `AlgebraicGeometry.BigFppfOver.isIso_map_objRestrict_comp`, which clause (2) at the
composite object inverts through
`AlgebraicGeometry.BigFppfOver.isIso_objZariskiRestrict_map_zariskiComparisonMap`. -/
public theorem isIso_objZariskiRestrict_map_counit_objRestrict
    (hqc : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G))
    (Y : BigFppfOver B (objScheme B S hS T) (contains_objScheme B S hS T))
    (h2T : IsIso (zariskiClause2Map B S hS T G))
    (h2Z : IsIso (zariskiClause2Map B S hS (objComp Y) G)) :
    IsIso ((restrictModule B (objScheme B (objScheme B S hS T)
          (contains_objScheme B S hS T) Y)
        (contains_objScheme B (objScheme B S hS T) (contains_objScheme B S hS T) Y)).map
      ((objRestrict B (objScheme B S hS T) (contains_objScheme B S hS T) Y).map
        (zariskiComparisonMap B (objScheme B S hS T) (contains_objScheme B S hS T)
          ((objRestrict B S hS T).obj G)))) := by
  have := h2T
  have hB : IsIso ((objRestrict B (objScheme B S hS T) (contains_objScheme B S hS T) Y ⋙
      restrictModule B (objScheme B (objScheme B S hS T) (contains_objScheme B S hS T) Y)
        (contains_objScheme B (objScheme B S hS T) (contains_objScheme B S hS T) Y)).map
      (objRestrictCounit B S hS T G)) :=
    isIso_map_objRestrict_comp Y (zariskiComparisonMap B S hS G)
      (isIso_objZariskiRestrict_map_zariskiComparisonMap B S hS (objComp Y) G hqc h2Z)
  have hA : IsIso ((objRestrict B (objScheme B S hS T) (contains_objScheme B S hS T) Y ⋙
      restrictModule B (objScheme B (objScheme B S hS T) (contains_objScheme B S hS T) Y)
        (contains_objScheme B (objScheme B S hS T) (contains_objScheme B S hS T) Y)).map
      (((associatedModuleObjRestrictNatIso B S hS T).app
          ((restrictModule B S hS).obj G)).hom ≫ objRestrictCounit B S hS T G)) := by
    rw [Functor.map_comp]
    infer_instance
  exact Stacks.MateSquare.isIso_map_of_comp_eq
    (objRestrict B (objScheme B S hS T) (contains_objScheme B S hS T) Y ⋙
      restrictModule B (objScheme B (objScheme B S hS T) (contains_objScheme B S hS T) Y)
        (contains_objScheme B (objScheme B S hS T) (contains_objScheme B S hS T) Y))
    ((associatedModule B (objScheme B S hS T) (contains_objScheme B S hS T)).map
      (zariskiClause2Map B S hS T G))
    inferInstance (mateSquare_objRestrictCounit B S hS T G).symm hA

end Comp

/-! ### The conclusion of [Stacks, Tag 0756] at `τ = Zariski` -/

section Conclusion

-- The localized big fppf site is essentially small and the Zariski site of a scheme has enough
-- injectives; without these four the `CategoryTheory.Sheaf.H` groups below are not defined.
attribute [local instance] Stacks.Topology.hasExt_sheafOpens
  Stacks.Topology.enoughInjectives_sheafOpens
  Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite
  Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite

variable (U : BigFppfOver B S hS)
  (hqc : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
    ((restrictModule B S hS).obj G))
  (hcl2 : ∀ Z : BigFppfOver B S hS, Flat ((Over.post B.inclusion).obj Z).hom →
    LocallyOfFinitePresentation ((Over.post B.inclusion).obj Z).hom →
    IsIso (zariskiClause2Map B S hS Z G))
  (hU₁ : Flat ((Over.post B.inclusion).obj U).hom)
  (hU₂ : LocallyOfFinitePresentation ((Over.post B.inclusion).obj U).hom)

include hqc hcl2 hU₁ hU₂ in
/-- **Clause (2) of [Stacks, Tag 0756] at `τ = Zar` passes to the base `X`.**  If `𝒢|_{S_Zar}` is
quasi-coherent and clause (2) holds for `𝒢` at every object of `(Sch/S)_fppf` flat and locally of
finite presentation over `S`, then for `U` such an object with scheme `X` the restriction
`𝒢_U = 𝒢|_{(Sch/X)_fppf}` satisfies clause (2) over `X`: the canonical map

```
h^*(𝒢_U|_{X_Zar}) ⟶ 𝒢_U|_{W_Zar}
```

is an isomorphism for every object `Y` of `(Sch/X)_fppf` with scheme `W` and structure morphism
`h : W ⟶ X` flat and locally of finite presentation.

The quasi-coherence hypothesis the map needs at `X` — clause (1) over `X` — is
`AlgebraicGeometry.BigFppfOver.isQuasicoherent_objZariskiRestrict` from clause (2) at `U`.  The
first factor of `AlgebraicGeometry.BigFppfOver.zariskiClause2Map` is an isomorphism by
construction and the second is
`AlgebraicGeometry.BigFppfOver.isIso_objZariskiRestrict_map_counit_objRestrict`, which is where
the mate square is used; its two inputs are clause (2) at `U` and clause (2) at the composite
object `Y → X → S`, flat and locally of finite presentation over `S` by
`AlgebraicGeometry.BigFppfOver.flat_objComp` and
`AlgebraicGeometry.BigFppfOver.locallyOfFinitePresentation_objComp`. -/
public theorem isIso_zariskiClause2Map_objRestrict
    (Y : BigFppfOver B (objScheme B S hS U) (contains_objScheme B S hS U))
    (hY₁ : Flat ((Over.post B.inclusion).obj Y).hom)
    (hY₂ : LocallyOfFinitePresentation ((Over.post B.inclusion).obj Y).hom) :
    IsIso (zariskiClause2Map B (objScheme B S hS U) (contains_objScheme B S hS U) Y
      ((objRestrict B S hS U).obj G)) := by
  have := isIso_objZariskiRestrict_map_counit_objRestrict (T := U) G hqc Y
    (hcl2 U hU₁ hU₂)
    (hcl2 (objComp Y) (flat_objComp Y hU₁ hY₁) (locallyOfFinitePresentation_objComp Y hU₂ hY₂))
  rw [zariskiClause2Map_eq B (objScheme B S hS U) (contains_objScheme B S hS U) Y
    ((objRestrict B S hS U).obj G) (isQuasicoherent_objZariskiRestrict B S hS U G hqc
      (hcl2 U hU₁ hU₂))]
  infer_instance

/-- **The conclusion of [Stacks, Tag 0756] at `τ = Zar`.**  Let `B` be a big fppf site, `S` a
scheme below its cutoff and `𝒢` a sheaf of `𝒪`-modules on `(Sch/S)_fppf` such that

1. `𝒢|_{S_Zar}` is quasi-coherent, and
2. for every object of `(Sch/S)_fppf` flat and locally of finite presentation over `S`, with
   structure morphism `g : X ⟶ S`, the canonical map `g^*(𝒢|_{S_Zar}) ⟶ 𝒢|_{X_Zar}`,
   `AlgebraicGeometry.BigFppfOver.zariskiClause2Map`, is an isomorphism; this is the adjoint
   transpose of the restriction map `𝒢|_{S_Zar} ⟶ g_*(𝒢|_{X_Zar})` by
   `AlgebraicGeometry.BigFppfOver.zariskiClause2Map_eq_homEquiv_symm`, and it is an isomorphism
   exactly when the transpose of restriction along `g^{-1}V ⟶ V` is, by
   `AlgebraicGeometry.BigFppfOver.isIso_zariskiClause2Map_iff`.

Then for **every** object `U` of `(Sch/S)_fppf` flat and locally of finite presentation over `S`,
with scheme `X`, and every `p`,

```
H^p(U, 𝒢)  ≅  H^p(U, 𝒢|_{U_Zar}).
```

The left-hand side is global cohomology of `𝒢|_{(Sch/X)_fppf}` on the big fppf site of `X`, the
localization of `(Sch/S)_fppf` at `U` by [Stacks, Tag 06WI]; the right-hand side is the cohomology
of the site of opens of `X` with values in the restriction of `𝒢` along the inclusion of the small
Zariski site of `X`.  See `AlgebraicGeometry.BigFppfOver.flatSmallZariskiSiteCohomologyAddEquiv`
for the same statement with that side read on the site `AlgebraicGeometry.SmallZariski` of
[Stacks, Tag 020T] (2).

This is `AlgebraicGeometry.BigFppfOver.zariskiSmallSiteCohomologyAddEquiv` — the conclusion at
the base of a big site — applied at the base `X` to `𝒢|_{(Sch/X)_fppf}`.  Its two hypotheses
there are clause (1) over `X`, which is
`AlgebraicGeometry.BigFppfOver.isQuasicoherent_objZariskiRestrict`, and clause (2) over `X`,
which is `AlgebraicGeometry.BigFppfOver.isIso_zariskiClause2Map_objRestrict` and rests on the
mate square `AlgebraicGeometry.BigFppfOver.mateSquare_objRestrictCounit`.

The attribute records the topology: this is the tag at `τ = Zariski`, and nothing here claims the
étale half; that is
`AlgebraicGeometry.BigFppfOver.flatSmallEtaleSiteCohomologyAddEquiv`, in
`StacksFrontier/AlgebraicGeometry/Descent/Parasitic/FlatCohomologyEtaleConclusion.lean`. -/
@[stacks 0756 "Zariski topology"]
public def flatSmallSiteCohomologyAddEquiv (p : ℕ) :
    Sheaf.H.{u} ((SheafOfModules.toSheaf (structureSheaf B (objScheme B S hS U)
        (contains_objScheme B S hS U))).obj ((objRestrict B S hS U).obj G)) p ≃+
      Sheaf.H.{u} ((SheafOfModules.toSheaf (objScheme B S hS U).ringCatSheaf).obj
        ((restrictModule B (objScheme B S hS U) (contains_objScheme B S hS U)).obj
          ((objRestrict B S hS U).obj G))) p :=
  zariskiSmallSiteCohomologyAddEquiv B (objScheme B S hS U) (contains_objScheme B S hS U)
    ((objRestrict B S hS U).obj G)
    (isQuasicoherent_objZariskiRestrict B S hS U G hqc (hcl2 U hU₁ hU₂))
    (fun Y hY₁ hY₂ => isIso_zariskiClause2Map_objRestrict B S hS G U hqc hcl2 hU₁ hU₂ Y hY₁ hY₂)
    p

/-- **The conclusion of [Stacks, Tag 0756] at `τ = Zar`, with the right-hand side on the small
Zariski site.**  Under the hypotheses of
`AlgebraicGeometry.BigFppfOver.flatSmallSiteCohomologyAddEquiv`, for every object `U` of
`(Sch/S)_fppf` flat and locally of finite presentation over `S`, with scheme `X`, and every `p`,

```
H^p(U, 𝒢)  ≅  H^p(X_Zar, (𝒢|_{X_Zar})^a),
```

the right-hand side being the cohomology of the small Zariski site of [Stacks, Tag 020T] (2)
with values in the associated sheaf of [Stacks, Tag 03DU] (4) at `τ = Zariski`.  This is the
previous statement composed with the small Zariski link of [Stacks, Tag 03DW] clause (2),
`AlgebraicGeometry.smallZariskiQuasiCoherentSiteCohomologyAddEquiv`.

The big Zariski site `BZ` carrying `X_Zar` is unrelated to the big fppf site `B`: the restriction
`𝒢|_{X_Zar}` is produced as an `𝒪_X`-module and only then read on `X_Zar`.

The attribute records the topology: this is the tag at `τ = Zariski`. -/
@[stacks 0756 "Zariski topology, with the small site read as in 020T (2)"]
public def flatSmallZariskiSiteCohomologyAddEquiv (BZ : BigZariskiSite.{u})
    (hXZ : BZ.Contains (objScheme B S hS U)) (p : ℕ) :
    Sheaf.H.{u} ((SheafOfModules.toSheaf (structureSheaf B (objScheme B S hS U)
        (contains_objScheme B S hS U))).obj ((objRestrict B S hS U).obj G)) p ≃+
      Sheaf.H.{u} (@smallZariskiAssociatedSheaf BZ (objScheme B S hS U) hXZ
        ((restrictModule B (objScheme B S hS U) (contains_objScheme B S hS U)).obj
          ((objRestrict B S hS U).obj G))
        (isQuasicoherent_objZariskiRestrict B S hS U G hqc (hcl2 U hU₁ hU₂))) p :=
  haveI : SheafOfModules.IsQuasicoherent (R := (objScheme B S hS U).ringCatSheaf)
      ((restrictModule B (objScheme B S hS U) (contains_objScheme B S hS U)).obj
        ((objRestrict B S hS U).obj G)) :=
    isQuasicoherent_objZariskiRestrict B S hS U G hqc (hcl2 U hU₁ hU₂)
  (flatSmallSiteCohomologyAddEquiv B S hS G U hqc hcl2 hU₁ hU₂ p).trans
    (smallZariskiQuasiCoherentSiteCohomologyAddEquiv BZ (objScheme B S hS U) hXZ
      ((restrictModule B (objScheme B S hS U) (contains_objScheme B S hS U)).obj
        ((objRestrict B S hS U).obj G)) p)

end Conclusion

end AlgebraicGeometry.BigFppfOver

end
