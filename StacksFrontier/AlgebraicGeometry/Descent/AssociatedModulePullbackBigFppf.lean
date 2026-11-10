module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ObjectRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.BigFppfRingedMorphism
public import StacksCore.Tactic.StacksAttribute

/-!
# The associated module commutes with pullback along a morphism of big fppf sites

`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullback` states Stacks 03FH (2),
`(f^*𝓕)^a ≅ f_{sites}^*𝓕^a`, over a morphism of ringed sites `f_big` taken as hypothesis data.
This file supplies that data for the morphism of ringed sites of Stacks 070R between the big
fppf sites of two schemes, and discharges the two provisos, so that the conclusion holds with no
hypothesis beyond `B.Contains X` and `B.Contains Y`.

The square of ringed sites is

```
    Opens Y  --- f⁻¹ --->  Opens X
       |                      |
    opensToBig            opensToBig
       |                      |
       v                      v
   (Sch/Y)_fppf -- X ×_Y - -> (Sch/X)_fppf
```

whose horizontal isomorphism is the geometric content: the base change `X ×_Y V` of an open `V`
of `Y` is the preimage `f⁻¹(V)`.  Both the isomorphism and its naturality are formal here, for
the reason they are formal in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ObjectRestriction`: a morphism into an
open of `X` is unique (`AlgebraicGeometry.BigFppfOver.subsingleton_hom_opensObj`) and exists as
soon as the structure morphism has range inside that open
(`AlgebraicGeometry.BigFppfOver.homOfRangeLe`), while a morphism into the base change of an open
of `Y` is unique because base change is right adjoint to postcomposition
(`AlgebraicGeometry.BigFppfOver.subsingleton_hom_baseChangeOpensObj`).  So neither composite nor
identity has to be computed: every equation between two morphisms with one of those two targets
is `Subsingleton.elim`.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.opensBaseChangeIso`: the natural isomorphism
  `f⁻¹(V) ≅ X ×_Y V` of functors from the small Zariski site of `Y` into the big fppf category
  over `X`.
* `AlgebraicGeometry.BigFppfOver.associatedModuleBigPullbackIso` and
  `AlgebraicGeometry.BigFppfOver.associatedModuleBigObjPullbackIso`: **Stacks 03FH (2)** for
  `f_big`, as functors and at one module.

## Main results

* `AlgebraicGeometry.BigFppfOver.subsingleton_hom_baseChangeOpensObj`: a morphism into the base
  change of an open of `Y` is unique.
* `AlgebraicGeometry.BigFppfOver.comparisonComp_opensBaseChangeIso`: the two routes round the
  square carry the same comparison of structure sheaves, the second proviso of
  `SheafOfModules.pullbackSquareIso`.

## Implementation notes

The pullback of sheaves of modules along `f_big` exists because the big fppf category over `Y`
is essentially small, by
`SheafOfModules.pushforward_isRightAdjoint_of_essentiallySmall` (Stacks 03D6 (2)).  The
implementation note of
`StacksFrontier.AlgebraicGeometry.Descent.BigFppfRingedMorphism` records that only the *small*-site
instance was available when that file was written; the essentially small one is what removes the
restriction.

## References

* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) {X Y : Scheme.{u}} (hX : B.Contains X) (hY : B.Contains Y)
  (f : X ⟶ Y)

/-! ### The base change of an open of `Y` is its preimage -/

/-- **A morphism into the base change of an open of `Y` is unique.**  Base change is right
adjoint to postcomposition along `f`, and a morphism into an open of `Y` is unique by
`AlgebraicGeometry.BigFppfOver.subsingleton_hom_opensObj`. -/
public theorem subsingleton_hom_baseChangeOpensObj (Z : BigFppfOver B X hX) (V : Y.Opens) :
    Subsingleton (Z ⟶ (baseChange B hX hY f).obj (opensObj B Y hY V)) :=
  have := subsingleton_hom_opensObj B Y hY ((Over.map (siteHom B hX hY f)).obj Z) V
  Equiv.subsingleton
    ((Over.mapPullbackAdj (siteHom B hX hY f)).homEquiv Z (opensObj B Y hY V)).symm

/-- A morphism into the base change of the big-site object `(opensToBig B Y hY).obj V` of an
open `V` of `Y` is unique: instance form of
`AlgebraicGeometry.BigFppfOver.subsingleton_hom_baseChangeOpensObj`. -/
public instance subsingleton_hom_baseChangeOpensToBig (Z : BigFppfOver B X hX) (V : Y.Opens) :
    Subsingleton (Z ⟶ (baseChange B hX hY f).obj ((opensToBig B Y hY).obj V)) :=
  subsingleton_hom_baseChangeOpensObj B hX hY f Z V

/-- The restriction `f ∣_ V : f⁻¹(V) ⟶ V` of `f` to an open of `Y`, as a morphism of the big
fppf site's chosen category of schemes. -/
@[implicit_reducible]
public noncomputable def restrictHom (V : Y.Opens) :
    B.obj (contains_opens B hX (f ⁻¹ᵁ V)) ⟶ B.obj (contains_opens B hY V) :=
  ObjectProperty.homMk (f ∣_ V)

/-- The restriction of `f` to an open of `Y` is a morphism over `Y` out of the preimage. -/
public theorem restrictHom_comp (V : Y.Opens) :
    restrictHom B hX hY f V ≫ (opensObj B Y hY V).hom
      = (opensObj B X hX (f ⁻¹ᵁ V)).hom ≫ siteHom B hX hY f :=
  ObjectProperty.hom_ext _ (morphismRestrict_ι f V)

/-- **The preimage of an open of `Y` maps to its base change.**  Over `X`, the preimage
`f⁻¹(V)` carries the two morphisms `f ∣_ V` and the open immersion, which agree over `Y`, hence
a morphism to the fibre product `X ×_Y V`. -/
public noncomputable def opensBaseChangeHom (V : Y.Opens) :
    (opensToBig B X hX).obj ((Opens.map f.base).obj V) ⟶
      (baseChange B hX hY f).obj ((opensToBig B Y hY).obj V) :=
  Over.homMk
    (pullback.lift (restrictHom B hX hY f V) (opensObj B X hX (f ⁻¹ᵁ V)).hom
      (restrictHom_comp B hX hY f V))
    (pullback.lift_snd _ _ _)

/-- The morphism `opensBaseChangeHom` followed by the first projection of the fibre product
`V ×_Y X` is the restriction `f ∣_ V`. -/
public theorem opensBaseChangeHom_left_comp_fst (V : Y.Opens) :
    (opensBaseChangeHom B hX hY f V).left
        ≫ pullback.fst (opensObj B Y hY V).hom (siteHom B hX hY f)
      = restrictHom B hX hY f V :=
  pullback.lift_fst _ _ _

/-- The base change `X ×_Y V` of an open of `Y` lies over the preimage `f⁻¹(V)`: a point of it
is carried by `f` to the image of its first projection, which lies in `V`. -/
public theorem range_baseChangeOpensObj_le (V : Y.Opens) :
    Set.range ⇑(((baseChange B hX hY f).obj (opensObj B Y hY V)).hom.hom)
      ⊆ ((f ⁻¹ᵁ V : X.Opens) : Set X) := by
  have hc : (pullback.fst (opensObj B Y hY V).hom (siteHom B hX hY f)).hom ≫ V.ι
      = (pullback.snd (opensObj B Y hY V).hom (siteHom B hX hY f)).hom ≫ f := by
    have h := congrArg (fun k : pullback (opensObj B Y hY V).hom (siteHom B hX hY f) ⟶ B.obj hY
      => k.hom) (pullback.condition (f := (opensObj B Y hY V).hom) (g := siteHom B hX hY f))
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom] at h
    exact h
  rintro x ⟨z, rfl⟩
  have hz : V.ι.base ((pullback.fst (opensObj B Y hY V).hom (siteHom B hX hY f)).hom.base z)
      = f.base ((pullback.snd (opensObj B Y hY V).hom (siteHom B hX hY f)).hom.base z) :=
    congrArg
      (fun k : (pullback (opensObj B Y hY V).hom (siteHom B hX hY f)).obj ⟶ Y => k.base z) hc
  have hmem : V.ι.base ((pullback.fst (opensObj B Y hY V).hom (siteHom B hX hY f)).hom.base z)
      ∈ (V : Set Y) := by
    rw [← Scheme.Opens.range_ι V]
    exact Set.mem_range_self _
  change f.base ((pullback.snd (opensObj B Y hY V).hom (siteHom B hX hY f)).hom.base z)
    ∈ (V : Set Y)
  exact hz ▸ hmem

/-- **The base change of an open of `Y` maps to its preimage.** -/
public noncomputable def opensBaseChangeInv (V : Y.Opens) :
    (baseChange B hX hY f).obj ((opensToBig B Y hY).obj V) ⟶
      (opensToBig B X hX).obj ((Opens.map f.base).obj V) :=
  homOfRangeLe B X hX (f ⁻¹ᵁ V) (range_baseChangeOpensObj_le B hX hY f V)

/-- **The geometric content of the square of ringed sites.**  The base change `X ×_Y V` of an
open `V` of `Y` is the preimage `f⁻¹(V)`, naturally in `V`.

Nothing is computed: the two morphisms are the ones the two universal properties supply, and
every equation needed — the two naturality squares and the two triangles — is between morphisms
whose target is either an open of `X` or the base change of an open of `Y`, and there is at most
one of each. -/
public noncomputable def opensBaseChangeIso :
    Opens.map f.base ⋙ opensToBig B X hX ≅ opensToBig B Y hY ⋙ baseChange B hX hY f where
  hom :=
    { app := opensBaseChangeHom B hX hY f
      naturality := fun _ W _ =>
        @Subsingleton.elim _ (subsingleton_hom_baseChangeOpensObj B hX hY f _ W) _ _ }
  inv :=
    { app := opensBaseChangeInv B hX hY f
      naturality := fun _ W _ =>
        @Subsingleton.elim _ (subsingleton_hom_opensObj B X hX _ (f ⁻¹ᵁ W)) _ _ }
  hom_inv_id :=
    NatTrans.ext (funext fun V =>
      @Subsingleton.elim _ (subsingleton_hom_opensObj B X hX _ (f ⁻¹ᵁ V)) _ _)
  inv_hom_id :=
    NatTrans.ext (funext fun V =>
      @Subsingleton.elim _ (subsingleton_hom_baseChangeOpensObj B hX hY f _ V) _ _)

/-! ### The comparison of structure sheaves -/

/-- The small Zariski site of `Y` into the big fppf site of `X` through the preimage is
continuous: a composite of two continuous functors. -/
public instance isContinuous_opensMap_comp_opensToBig :
    (Opens.map f.base ⋙ opensToBig B X hX).IsContinuous
      (Opens.grothendieckTopology ↥Y) (topology B X hX) :=
  Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology ↥X) _

/-- The small Zariski site of `Y` into the big fppf site of `X` through base change is
continuous: a composite of two continuous functors. -/
public instance isContinuous_opensToBig_comp_baseChange :
    (opensToBig B Y hY ⋙ baseChange B hX hY f).IsContinuous
      (Opens.grothendieckTopology ↥Y) (topology B X hX) :=
  Functor.isContinuous_comp _ _ _ (topology B Y hY) _

/-- **The two routes round the square of ringed sites carry the same comparison of structure
sheaves.**  Both composites restrict a section of `𝒪_Y` over `V` to the open `f⁻¹(V)` of `X`:
going round the big sites one pulls back along the projection `X ×_Y V ⟶ V` and then along the
comparison `f⁻¹(V) ⟶ X ×_Y V`, whose composite is `f ∣_ V`; going round the small sites one
applies `f^♯` and then identifies global functions.  The two agree by
`AlgebraicGeometry.Scheme.Opens.topIso_inv_appTop_of_comp`.

This is the second proviso of `SheafOfModules.pullbackSquareIso`. -/
public theorem comparisonComp_opensBaseChangeIso :
    SheafOfModules.comparisonComp (structureMap B Y hY) (structureComparison B hX hY f) ≫
        (Functor.sheafPushforwardContinuousNatTrans (opensBaseChangeIso B hX hY f).hom
          RingCat.{u} (Opens.grothendieckTopology ↥Y) (topology B X hX)).app
          (structureSheaf B X hX) =
      SheafOfModules.comparisonComp f.toRingCatSheafHom (structureMap B X hX) := by
  ext : 2
  funext V
  change (structureMap B Y hY).hom.app V ≫
      (Scheme.Γ ⋙ forget₂ CommRingCat RingCat.{u}).map
          (B.inclusion.map
            (pullback.fst (opensObj B Y hY V.unop).hom (siteHom B hX hY f))).op ≫
        (structureSheaf B X hX).obj.map
          ((opensBaseChangeHom B hX hY f V.unop)).op =
    (f.toRingCatSheafHom).hom.app V ≫
      (structureMap B X hX).hom.app (op ((Opens.map f.base).obj V.unop))
  have hcomb : (Scheme.Γ ⋙ forget₂ CommRingCat RingCat.{u}).map
          (B.inclusion.map
            (pullback.fst (opensObj B Y hY V.unop).hom (siteHom B hX hY f))).op ≫
        (structureSheaf B X hX).obj.map ((opensBaseChangeHom B hX hY f V.unop)).op
      = (Scheme.Γ ⋙ forget₂ CommRingCat RingCat.{u}).map
          (B.inclusion.map (restrictHom B hX hY f V.unop)).op :=
    ((Scheme.Γ ⋙ forget₂ CommRingCat RingCat.{u}).map_comp _ _).symm.trans
      (congrArg
        (fun k : B.obj (contains_opens B hX (f ⁻¹ᵁ V.unop)) ⟶ B.obj (contains_opens B hY V.unop)
          => (Scheme.Γ ⋙ forget₂ CommRingCat RingCat.{u}).map (B.inclusion.map k).op)
        (opensBaseChangeHom_left_comp_fst B hX hY f V.unop))
  refine Eq.trans (congrArg (fun k => (structureMap B Y hY).hom.app V ≫ k) hcomb) ?_
  have key := Scheme.Opens.topIso_inv_appTop_of_comp f V.unop (f ∣_ V.unop)
    (morphismRestrict_ι f V.unop)
  change (forget₂ CommRingCat RingCat.{u}).map (Scheme.Opens.topIso (X := Y) V.unop).inv ≫
      (forget₂ CommRingCat RingCat.{u}).map (f ∣_ V.unop).appTop =
    (forget₂ CommRingCat RingCat.{u}).map (f.app V.unop) ≫
      (forget₂ CommRingCat RingCat.{u}).map
        (Scheme.Opens.topIso (X := X) ((Opens.map f.base).obj V.unop)).inv
  exact ((forget₂ CommRingCat RingCat.{u}).map_comp _ _).symm.trans
    ((congrArg (forget₂ CommRingCat RingCat.{u}).map key).trans
      ((forget₂ CommRingCat RingCat.{u}).map_comp _ _))

/-! ### Stacks 03FH (2) -/

/-- **Stacks 03FH, part (2), for the morphism of big fppf sites
`f_big : ((Sch/X)_fppf, 𝒪_X) ⟶ ((Sch/Y)_fppf, 𝒪_Y)` of Stacks 070R.**  The associated module of
a pullback is the pullback of the associated module, `(f^*𝓕)^a ≅ f_{big}^*(𝓕^a)`.

No hypothesis: the morphism of ringed sites is
`AlgebraicGeometry.BigFppfOver.baseChange` together with
`AlgebraicGeometry.BigFppfOver.structureComparison`, both available, and the two provisos of
`SheafOfModules.pullbackSquareIso` are
`AlgebraicGeometry.BigFppfOver.opensBaseChangeIso` and
`AlgebraicGeometry.BigFppfOver.comparisonComp_opensBaseChangeIso`.

Only the fppf `f_big` is claimed here.  Stacks 03FH (2) ranges over every morphism of ringed
sites `f_{sites}` of Remark 070R; the other morphisms that remark enumerates are claimed
elsewhere — `f_big` at the other four topologies by
`AlgebraicGeometry.BigFppfOver.associatedModuleBasePullbackIso`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModulePullbackBigSites.lean`, which is this
construction read at a variable topology), the small étale `f_small` by
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso` and the small Zariski `f_small` by
`AlgebraicGeometry.SmallZariski.lcAssociatedModulePullbackIso` (
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallZariskiPushforwardSquare.lean:458`).
(The last was formerly cited as
`AlgebraicGeometry.SmallZariski.associatedModulePullbackIso`, which states the commutation over
the *identity reading* of `𝓕 ↦ 𝓕^a` and is a tautology about `𝟭`; it is untagged, and naming it
here made this enumeration a false completeness claim.) -/
@[stacks 03FH "part (2), for the morphism of big fppf sites f_big of Stacks 070R"]
public noncomputable def associatedModuleBigPullbackIso :
    Scheme.Modules.pullback f ⋙ associatedModule B X hX ≅
      associatedModule B Y hY ⋙
        SheafOfModules.pullback.{u} (structureComparison B hX hY f) :=
  associatedModulePullbackIsoOfSquare B hX hY f (baseChange B hX hY f)
    (structureComparison B hX hY f) (opensBaseChangeIso B hX hY f)
    (comparisonComp_opensBaseChangeIso B hX hY f)

/-- **Stacks 03FH, part (2), at one module**: `(f^*𝓕)^a ≅ f_{big}^*(𝓕^a)`. -/
@[stacks 03FH "part (2) at one module, for the morphism of big fppf sites f_big"]
public noncomputable def associatedModuleBigObjPullbackIso (𝓕 : Y.Modules) :
    (associatedModule B X hX).obj ((Scheme.Modules.pullback f).obj 𝓕) ≅
      (SheafOfModules.pullback.{u} (structureComparison B hX hY f)).obj
        ((associatedModule B Y hY).obj 𝓕) :=
  (associatedModuleBigPullbackIso B hX hY f).app 𝓕

end AlgebraicGeometry.BigFppfOver

end
