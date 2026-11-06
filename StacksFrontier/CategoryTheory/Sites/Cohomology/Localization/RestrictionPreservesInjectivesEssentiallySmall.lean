module

public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroExactness
import Mathlib.CategoryTheory.Sites.Equivalence
import StacksCore.Tactic.EgaSgaAttribute

/-! # Restriction to a localized site preserves injectives, over a site with large objects

Let `(C, J)` be a site whose objects form a type in an arbitrary universe `c` while its
morphisms, its sheaf of rings `R` and its modules all live in one universe `u`, and let `U` be
an object of `C`. Restriction along `Over.forget U` sends a sheaf of `R`-modules to a sheaf of
`R_U`-modules on the localized site `C/U`; it is `SheafOfModules.overFunctor R U`, written
`j_U^{-1}` in Stacks 03DH, and its left adjoint is extension by zero `j_{U!}`. The sections of
the presheaf whose sheafification is `j_{U!} G` over an object `V` are the direct sum of the
`G(φ)` over all `φ : V ⟶ U` (Stacks 03DI), so a monomorphism of sheaves of `R_U`-modules
induces a coproduct of monomorphisms of modules, which is again a monomorphism by
Grothendieck's axiom AB4 for `ModuleCat`. Hence `j_{U!}` preserves monomorphisms and its right
adjoint preserves injective objects (Stacks 015Z), which is part (1) of Stacks 03F3.

## Main results

* `Stacks.Cohomology.Localization.preservesInjectiveObjects_overFunctor_of_essentiallySmall`:
  restriction to the localized site preserves injective objects.
* `Stacks.Cohomology.Localization.injective_over_of_essentiallySmall`: the same statement for
  one injective module, `I|_U` is injective.
* `Stacks.Sites.ExtensionByZero.OfEssentiallySmall.extensionByZero_preservesMonomorphisms`:
  extension by zero preserves monomorphisms.
* `Stacks.Sites.ExtensionByZero.OfEssentiallySmall.extensionByZeroPresheafSectionIso`: the
  direct-sum formula for the presheaf computing `j_{U!}`.

## Implementation notes

This restates the development of `Stacks.Sites.ExtensionByZero` and
`Stacks.Cohomology.Localization` with the universe of the objects of the site freed from the
universe of its morphisms, everything else staying in the single universe `u`. The reason is
that the small étale ringed site of an algebraic space has its objects one universe above its
morphisms: it is a `AlgebraicGeometry.RingedSite.{u + 1, u, u}`, so the single-universe
statements cannot be instantiated at it. Taking the object universe to be `u + 1` recovers
exactly that configuration.

The presheaf-level construction of the direct sum is not restated: the declarations of
`Stacks.Sites.ExtensionByZero` from `presheafSummands` to `directSumPresheafIso` already carry
the objects of `C` in a universe of their own, and the adjointness hypothesis the last few of
them ask for is exactly the instance provided here. They are therefore reused verbatim, and
what this file adds at the presheaf level is only that instance.

That instance, `OfEssentiallySmall.presheafRestrictionIsRightAdjoint`, asserts that restriction
of presheaves of modules along `Over.forget U` is a right adjoint. Mathlib discharges that from
smallness of `Over U`, which fails as soon as the objects of `C` are large; here it comes from
`PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall`, which asks only that the
source site be essentially `u`-small, and `Over U` is essentially `u`-small because `C` is and
`C` is locally `u`-small.

Apart from that, the only change from the single-universe development is bookkeeping in
`OfEssentiallySmall.extensionByZero_preservesMonomorphisms`: left exactness of sheafification
of presheaves of modules is stated by Mathlib under `HasSheafify`, which over a small site is
an instance but over a site with large objects has to be produced from essential smallness by
`CategoryTheory.hasSheafifyEssentiallySmallSite`. No new hypothesis is needed for it. Every
remaining proof is the single-universe one verbatim: the direct sum realizing AB4 is indexed by
the hom-set `V ⟶ U`, which lies in `Type u` whatever the universe of the objects, so
`Stacks.Sites.ExtensionByZero.mono_sigmaMap` applies as it stands and is reused rather than
restated.

## References

* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites.ExtensionByZero.OfEssentiallySmall

universe u c

variable {C : Type c} [Category.{u} C] [EssentiallySmall.{u} C]
  (J : GrothendieckTopology C) (R : Sheaf J RingCat.{u}) (U : C)

/-- Every slice of an essentially `u`-small category whose morphisms lie in `Type u` is again
essentially `u`-small. -/
lemma essentiallySmall_over : EssentiallySmall.{u} (Over U) :=
  CostructuredArrow.essentiallySmall (S := 𝟭 C) (T := U)

/-- The family of modules indexed by the maps from `V` to `U`. -/
abbrev extensionByZeroSummands (G : SheafOfModules.{u} (R.over U)) (V : C) :
    (V ⟶ U) → ModuleCat (R.obj.obj (op V)) :=
  fun φ => G.val.obj (op (Over.mk φ))

variable (S : Cᵒᵖ ⥤ RingCat.{u})

/-- Restriction of presheaves of modules along `Over.forget U` has a left adjoint, because
`Over U` is essentially small in the universe of the rings and the module sections. -/
instance presheafRestrictionIsRightAdjoint :
    (PresheafOfModules.pushforward.{u} (F := Over.forget U)
      (𝟙 ((Over.forget U).op ⋙ S))).IsRightAdjoint :=
  have := essentiallySmall_over U
  PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall.{u} _

/-- The previous instance restated with the morphism of presheaves of rings spelled as the
identity of `R.over U`, which is the form the declarations about a sheaf of rings ask for and
which the instance discrimination tree does not match against the generic spelling. -/
instance presheafRestrictionSheafIsRightAdjoint :
    (PresheafOfModules.pushforward.{u} (F := Over.forget U) (R := R.obj)
      (S := (R.over U).obj)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).IsRightAdjoint :=
  presheafRestrictionIsRightAdjoint U R.obj

/-- The presheaf whose sheafification is extension by zero has over `V` the direct sum of
the sections over all maps from `V` to `U`. -/
noncomputable def extensionByZeroPresheafSectionIso
    (G : SheafOfModules.{u} (R.over U)) (V : C) :
    ((PresheafOfModules.pullback.{u} (F := Over.forget U) (R := R.obj)
      (S := (R.over U).obj)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).obj G.val).obj (op V) ≅
      (∐ extensionByZeroSummands J R U G V) := by
  let comparison : (∐ extensionByZeroSummands J R U G V) ⟶
      ((PresheafOfModules.pullback.{u} (F := Over.forget U) (R := R.obj)
        (S := (R.over U).obj) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).obj
          G.val).obj (op V) :=
    Sigma.desc fun φ =>
      (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
        (F := Over.forget U) (R := R.obj) (S := (R.over U).obj)
        (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).unit.app G.val).app
          (op (Over.mk φ)))
  have : IsIso comparison := by
    change IsIso (((PresheafOfModules.evaluation R.obj (op V)).mapIso
      (directSumPresheafIso U R.obj G.val)).hom)
    infer_instance
  exact (asIso comparison).symm

/-- The direct-sum comparison is the canonical one: on the summand indexed by
`φ : V ⟶ U`, its inverse is the unit of the presheaf adjunction at `φ`.

It is stated with `HEq` because the two sides live in `ModuleCat` over rings that are equal but
not syntactically identical. -/
theorem extensionByZeroPresheafSectionIso_inv_ι
    (G : SheafOfModules.{u} (R.over U)) (V : C) (φ : V ⟶ U) :
    HEq (Limits.Sigma.ι (extensionByZeroSummands J R U G V) φ ≫
      (extensionByZeroPresheafSectionIso J R U G V).inv)
    (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
      (F := Over.forget U) (R := R.obj) (S := (R.over U).obj)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).unit.app G.val).app
        (op (Over.mk φ))) :=
  heq_of_eq (Sigma.ι_desc _ φ)

variable [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restriction of sheaves of modules along `Over.forget U` has a left adjoint, namely
extension by zero. -/
instance sheafRestrictionIsRightAdjoint :
    (SheafOfModules.pushforward.{u} (F := Over.forget U)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).IsRightAdjoint :=
  have := presheafRestrictionSheafIsRightAdjoint J R U
  (SheafOfModules.PullbackConstruction.adjunction.{u}
    (F := Over.forget U) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).isRightAdjoint

/-- The map of direct sums induced on the sections over `V` of the extension-by-zero presheaf by
a map `f : G ⟶ H` of sheaves of `R_U`-modules: on the summand indexed by `φ : V ⟶ U` it is the
component of `f` at `φ`. -/
noncomputable def extensionByZeroSummandsMap {G H : SheafOfModules.{u} (R.over U)}
    (f : G ⟶ H) (V : C) :
    (∐ extensionByZeroSummands J R U G V) ⟶ (∐ extensionByZeroSummands J R U H V) :=
  Limits.Sigma.map
    (g := extensionByZeroSummands J R U G V)
    (f := extensionByZeroSummands J R U H V)
    (fun φ => (f.val.app (op (Over.mk φ)) :
      extensionByZeroSummands J R U G V φ ⟶ extensionByZeroSummands J R U H V φ))

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `extensionByZeroSummandsMap` is a monomorphism as soon as `f` is: each summand component is
a monomorphism of modules, the index type `V ⟶ U` lies in the universe of the modules, and
`ModuleCat` satisfies AB4 there. -/
lemma extensionByZeroSummandsMap_mono {G H : SheafOfModules.{u} (R.over U)}
    (f : G ⟶ H) (V : C) [Mono f] :
    Mono (extensionByZeroSummandsMap J R U f V) := by
  have hval : Mono f.val := by
    change Mono ((SheafOfModules.forget (R.over U)).map f)
    infer_instance
  exact Stacks.Sites.ExtensionByZero.mono_sigmaMap _ fun φ =>
    (ModuleCat.mono_iff_injective _).2 (PresheafOfModules.injective_of_mono f.val (op (Over.mk φ)))

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The direct-sum formula of Stacks 03DI is natural in the sheaf of modules: the map induced by
`f : G ⟶ H` on the sections of the extension-by-zero presheaf over `V` is
`extensionByZeroSummandsMap`. -/
lemma extensionByZeroSectionMap_naturality
    {G H : SheafOfModules.{u} (R.over U)} (f : G ⟶ H) (V : C) :
    ((PresheafOfModules.pullback.{u} (F := Over.forget U)
        (R := R.obj) (S := (R.over U).obj)
        (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).map f.val).app (op V) ≫
      (extensionByZeroPresheafSectionIso J R U H V).hom =
      (extensionByZeroPresheafSectionIso J R U G V).hom ≫
      extensionByZeroSummandsMap J R U f V := by
  let eG := extensionByZeroPresheafSectionIso J R U G V
  let eH := extensionByZeroPresheafSectionIso J R U H V
  let P : PresheafOfModules (R.over U).obj ⥤ PresheafOfModules R.obj :=
    PresheafOfModules.pullback.{u} (F := Over.forget U)
      (R := R.obj) (S := (R.over U).obj)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom
  let adj : P ⊣ PresheafOfModules.pushforward.{u} (F := Over.forget U)
      (R := R.obj) (S := (R.over U).obj)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom :=
    PresheafOfModules.pullbackPushforwardAdjunction.{u}
      (F := Over.forget U) (R := R.obj) (S := (R.over U).obj)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom
  apply (Iso.inv_comp_eq eG).1
  refine Sigma.hom_ext _ _ fun φ => ?_
  have hG' := eq_of_heq (extensionByZeroPresheafSectionIso_inv_ι J R U G V φ)
  have hH' := eq_of_heq (extensionByZeroPresheafSectionIso_inv_ι J R U H V φ)
  have hnat' :
      ((adj.unit.app G.val).app (op (Over.mk φ))) ≫ (P.map f.val).app (op V) =
        f.val.app (op (Over.mk φ)) ≫ ((adj.unit.app H.val).app (op (Over.mk φ))) :=
    (congrArg (fun g => g.app (op (Over.mk φ))) (adj.unit.naturality f.val)).symm
  have hUnit : ((adj.unit.app H.val).app (op (Over.mk φ))) ≫ eH.hom =
      Sigma.ι (extensionByZeroSummands J R U H V) φ :=
    ((Iso.comp_inv_eq eH).1 hH').symm
  have hι : (f.val.app (op (Over.mk φ)) :
        extensionByZeroSummands J R U G V φ ⟶ extensionByZeroSummands J R U H V φ) ≫
      Sigma.ι (extensionByZeroSummands J R U H V) φ =
      Sigma.ι (extensionByZeroSummands J R U G V) φ ≫
        extensionByZeroSummandsMap J R U f V :=
    (Limits.Sigma.ι_map (g := extensionByZeroSummands J R U G V)
      (f := extensionByZeroSummands J R U H V)
      (fun ψ => (f.val.app (op (Over.mk ψ)) :
        extensionByZeroSummands J R U G V ψ ⟶ extensionByZeroSummands J R U H V ψ)) φ).symm
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun x => x ≫ ((P.map f.val).app (op V) ≫ eH.hom)) hG').trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun x => x ≫ eH.hom) hnat').trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun x => f.val.app (op (Over.mk φ)) ≫ x) hUnit).trans hι)))))

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The presheaf whose sheafification is extension by zero depends on the sheaf of modules
through a functor preserving monomorphisms. -/
lemma extensionByZeroPresheaf_map_mono {G H : SheafOfModules.{u} (R.over U)}
    (f : G ⟶ H) [Mono f] :
    Mono ((PresheafOfModules.pullback.{u} (F := Over.forget U)
      (R := R.obj) (S := (R.over U).obj)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).map f.val) := by
  apply PresheafOfModules.mono_of_injective
  rintro ⟨V⟩
  rw [← ModuleCat.mono_iff_injective,
    (Iso.eq_comp_inv _).2 (extensionByZeroSectionMap_naturality J R U f V)]
  have := extensionByZeroSummandsMap_mono J R U f V
  infer_instance

/-- Extension by zero preserves monomorphisms. -/
lemma extensionByZero_preservesMonomorphisms :
    Functor.PreservesMonomorphisms (SheafOfModules.pullback.{u}
      (F := Over.forget U) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))) := by
  have := presheafRestrictionSheafIsRightAdjoint J R U
  have : HasSheafify J AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{u} J AddCommGrpCat.{u}
  refine ⟨fun {G H} f _ => ?_⟩
  have := extensionByZeroPresheaf_map_mono J R U f
  let e := SheafOfModules.pullbackIso (𝟙 (R.over U))
  have hcomp : Mono ((SheafOfModules.forget (R.over U) ⋙
      PresheafOfModules.pullback.{u} (F := Over.forget U)
        (R := R.obj) (S := (R.over U).obj)
        (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom ⋙
      PresheafOfModules.sheafification (𝟙 R.obj)).map f) := by
    change Mono ((PresheafOfModules.sheafification (𝟙 R.obj)).map
      ((PresheafOfModules.pullback.{u} (F := Over.forget U)
        (R := R.obj) (S := (R.over U).obj)
        (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).map f.val))
    infer_instance
  rw [← NatIso.naturality_2 e f]
  infer_instance

end Stacks.Sites.ExtensionByZero.OfEssentiallySmall

namespace Stacks.Cohomology.Localization

universe u c

variable {C : Type c} [Category.{u} C] [EssentiallySmall.{u} C]
  (J : GrothendieckTopology C) (R : Sheaf J RingCat.{u}) (U : C)
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restriction of sheaves of modules to the site localized at an object preserves injective
objects, over a site whose objects need not lie in the universe of its morphisms: its left
adjoint, extension by zero, preserves monomorphisms. -/
@[sga "4 V 2.2" "special case", sga "4 V 4.11" "1), special case"]
theorem preservesInjectiveObjects_overFunctor_of_essentiallySmall :
    (SheafOfModules.overFunctor.{u} R U).PreservesInjectiveObjects :=
  have := Stacks.Sites.ExtensionByZero.OfEssentiallySmall.extensionByZero_preservesMonomorphisms
    J R U
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (SheafOfModules.pullbackPushforwardAdjunction
      (F := Over.forget U) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)))

/-- For one module: the restriction `I|_U` of an injective sheaf of `R`-modules is an injective
sheaf of `R_U`-modules, over a site whose objects need not lie in the universe of its
morphisms. -/
@[sga "4 V 4.11" "1), special case"]
theorem injective_over_of_essentiallySmall (I : SheafOfModules.{u} R) [Injective I] :
    Injective (I.over U) :=
  have := preservesInjectiveObjects_overFunctor_of_essentiallySmall J R U
  Functor.injective_obj (SheafOfModules.overFunctor.{u} R U) I

end Stacks.Cohomology.Localization

end
