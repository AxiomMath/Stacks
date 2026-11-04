module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionKInjectiveEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-!
# Exactness of extension by zero over a site with large objects

Let `(C, J)` be a site whose objects form a type in an arbitrary universe `c` while its
morphisms, its sheaf of rings `R` and its modules all live in one universe `u`, let `C` be
essentially `u`-small, and let `U` be an object of `C`. This file carries the two exactness
properties of extension by zero `j_{U!}` over to that configuration: that `j_{U!}` is exact
(Stacks 03DJ) and that it *reflects* exactness as well (Stacks 0E8G).

The single-universe versions of both statements concern a site whose objects, morphisms and
ring sections lie in one universe. The small étale ringed site of an algebraic space is an
`AlgebraicGeometry.RingedSite.{u + 1, u, u}` — its objects sit one universe above its
morphisms — so those statements cannot be instantiated at it; taking the object universe to be
`u + 1` here recovers exactly that configuration.

Exactness of `j_{U!}` in this setting is
`Stacks.Sites.ExtensionByZero.OfEssentiallySmall.extensionByZero_exact`.

## Main results

* `Stacks.Sites.ExtensionByZero.OfEssentiallySmall.unit_mono`: the unit of `j_{U!} ⊣ j_U^*` is
  a monomorphism.
* `Stacks.Sites.ExtensionByZero.OfEssentiallySmall.extensionByZero_exact_iff`: `j_{U!}`
  reflects exactness, Stacks 0E8G at this shape.
* `Stacks.Sites.ExtensionByZero.OfEssentiallySmall.isZero_of_isZero_extensionByZero`: `j_{U!}`
  reflects zero objects, which is the form in which the reflection is used to read a vanishing
  statement on the slice site off one on `C`.
* `Stacks.Sites.ExtensionByZero.OfEssentiallySmall.isZero_of_isZero_over_extensionByZero`: the
  same reflection through a restriction, along an arrow `p : W ⟶ V`: if `(j_{W!}M)|_V` is a zero
  object then so is `M`. This is the form a hypothesis available on the slice over `V` and a
  conclusion wanted on the slice over `W` need.

## Implementation notes

Every proof here is the single-universe one, with its two inputs replaced by their essentially
small versions: `presheafRestrictionSheafIsRightAdjoint`, which is where essential smallness is
spent, and `extensionByZeroPresheafSectionIso`, the direct-sum formula of Stacks 03DI. Neither
exactness argument touches the universe of the objects of the site: right exactness is formal,
because `j_{U!}` is a left adjoint; left exactness is preservation of monomorphisms together
with preservation of cokernels; and the reflection is faithfulness, which comes from the unit
being a monomorphism, itself read off the direct-sum formula, whose index type `V ⟶ U` lies in
`Type u` whatever the universe of the objects.

`isZero_of_isZero_extensionByZero` is the reflection applied to the short complex `0 ⟶ M ⟶ 0`;
it is derived directly from the unit being a monomorphism rather than through
`extensionByZero_exact_iff`.

## References

* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
* [Stacks Project, Tag 0E8G](https://stacks.math.columbia.edu/tag/0E8G)
* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites.ExtensionByZero.OfEssentiallySmall

universe u c

variable {C : Type c} [Category.{u} C] [EssentiallySmall.{u} C]
  (J : GrothendieckTopology C) (R : Sheaf J RingCat.{u}) (U : C)
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Abelian presheaves on the slice site sheafify: `Over U` is essentially `u`-small because
`C` is and `C` is locally `u`-small. The module category of the slice site has to be abelian
for the exactness statements below to be about anything, and over a site with large objects
that is not an instance. -/
local instance sliceHasSheafify : HasSheafify (J.over U) AddCommGrpCat.{u} :=
  have := essentiallySmall_over U
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u, _, _} (J.over U)

/-- On the slice site the maps of abelian presheaves inverted by sheafification are exactly the
locally bijective ones, again by essential smallness of `Over U`. -/
local instance sliceWEqualsLocallyBijective :
    (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  have := essentiallySmall_over U
  .ofEssentiallySmall (J.over U)

/-- Restriction of presheaves of modules along `Over.forget U` is a right adjoint, restated in
the elaboration context of this file so that the instance the adjunctions below are formed
through is found by synthesis rather than carried by hand. Both spellings of the morphism of
presheaves of rings are needed: the sheaf-level adjunction of
`SheafOfModules.PullbackConstruction` asks for the one whose source is read off the sheaf
pushforward, which is not the spelling the statements about `R.over U` produce. -/
local instance presheafRestrictionIsRightAdjoint' :
    (PresheafOfModules.pushforward.{u} (F := Over.forget U)
      (𝟙 ((Over.forget U).op ⋙ R.obj))).IsRightAdjoint :=
  presheafRestrictionIsRightAdjoint U R.obj

/-- The same at the spelling that takes the identity morphism of `R.over U`. -/
local instance presheafRestrictionSheafIsRightAdjoint' :
    (PresheafOfModules.pushforward.{u} (F := Over.forget U) (R := R.obj)
      (S := (R.over U).obj)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).IsRightAdjoint :=
  presheafRestrictionSheafIsRightAdjoint J R U

/-- Extension by zero preserves finite limits. -/
instance instPreservesFiniteLimitsExtensionByZero :
    PreservesFiniteLimits (SheafOfModules.pullback.{u}
      (F := Over.forget U) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))) :=
  ((exactFunctor_iff _).mp (extensionByZero_exact J R U)).1

omit [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The unit of the presheaf-level extension-by-zero/restriction adjunction is a monomorphism:
over the object `φ : V ⟶ U` of `C/U` it is the inclusion of the summand indexed by `φ` in the
direct sum of Stacks 03DI. -/
private lemma presheafUnit_mono (G : SheafOfModules.{u} (R.over U)) :
    Mono ((PresheafOfModules.pullbackPushforwardAdjunction.{u} (F := Over.forget U)
      (R := R.obj) (S := (R.over U).obj)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).unit.app G.val) := by
  apply PresheafOfModules.mono_of_injective
  intro X
  have hinj : Function.Injective (ConcreteCategory.hom
      (Sigma.ι (extensionByZeroSummands J R U G X.unop.left) X.unop.hom ≫
        (extensionByZeroPresheafSectionIso J R U G X.unop.left).inv)) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hEq : (Sigma.ι (extensionByZeroSummands J R U G X.unop.left) X.unop.hom ≫
      (extensionByZeroPresheafSectionIso J R U G X.unop.left).inv) =
        ((PresheafOfModules.pullbackPushforwardAdjunction.{u} (F := Over.forget U)
          (R := R.obj) (S := (R.over U).obj)
          (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).unit.app G.val).app X :=
    HEq.eq (extensionByZeroPresheafSectionIso_inv_ι J R U G X.unop.left X.unop.hom)
  rw [← hEq]
  exact hinj

/-- The unit of the extension-by-zero/restriction adjunction of *sheaves* of modules is a
monomorphism: the presheaf-level unit is injective and sheafification is locally injective,
which on a separated presheaf is injectivity. -/
theorem unit_mono
    [(PresheafOfModules.pushforward.{u} (F := Over.forget U) (R := R.obj)
      (S := (R.over U).obj)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).IsRightAdjoint]
    (G : SheafOfModules.{u} (R.over U)) :
    Mono ((SheafOfModules.PullbackConstruction.adjunction.{u}
      (F := Over.forget U) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).unit.app G) := by
  let pAdj := PresheafOfModules.pullbackPushforwardAdjunction.{u} (F := Over.forget U)
    (R := R.obj) (S := (R.over U).obj) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom
  let P := (PresheafOfModules.pullback.{u} (F := Over.forget U) (R := R.obj)
    (S := (R.over U).obj) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).obj G.val
  let sAdj := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)
  let A := SheafOfModules.PullbackConstruction.adjunction.{u}
    (F := Over.forget U) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))
  let push := PresheafOfModules.pushforward.{u} (F := Over.forget U) (R := R.obj)
    (S := (R.over U).obj) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom
  have hform : (SheafOfModules.forget (R.over U)).map (A.unit.app G) =
      pAdj.unit.app G.val ≫ push.map (sAdj.unit.app P) := by
    dsimp [A, P, pAdj, sAdj, push, SheafOfModules.PullbackConstruction.adjunction,
      Adjunction.mkOfHomEquiv]
    rfl
  have hp : Presheaf.IsLocallyInjective (J.over U)
      ((PresheafOfModules.toPresheaf (R.over U).obj).map (pAdj.unit.app G.val)) := by
    have : Mono (pAdj.unit.app G.val) := presheafUnit_mono J R U G
    apply Presheaf.isLocallyInjective_of_injective
    intro X
    exact (AddCommGrpCat.mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1
      (Functor.map_mono (PresheafOfModules.toPresheaf (R.over U).obj) (pAdj.unit.app G.val)) X)
  have hs : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf R.obj).map (sAdj.unit.app P)) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact (J.W_toSheafify P.presheaf).isLocallyInjective
  have hpush : Presheaf.IsLocallyInjective (J.over U)
      ((PresheafOfModules.toPresheaf (R.over U).obj).map (push.map (sAdj.unit.app P))) :=
    Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U)
      ((PresheafOfModules.toPresheaf R.obj).map (sAdj.unit.app P))
  have hcomp : Presheaf.IsLocallyInjective (J.over U)
      ((PresheafOfModules.toPresheaf (R.over U).obj).map
        (pAdj.unit.app G.val ≫ push.map (sAdj.unit.app P))) := by
    have : Presheaf.IsLocallyInjective (J.over U)
        ((PresheafOfModules.toPresheaf (R.over U).obj).map (pAdj.unit.app G.val) ≫
          (PresheafOfModules.toPresheaf (R.over U).obj).map
            (push.map (sAdj.unit.app P))) := inferInstance
    simpa only [Functor.map_comp] using this
  have hlocal : Presheaf.IsLocallyInjective (J.over U)
      ((PresheafOfModules.toPresheaf (R.over U).obj).map (A.unit.app G).val) := by
    change Presheaf.IsLocallyInjective (J.over U)
      ((PresheafOfModules.toPresheaf (R.over U).obj).map
        ((SheafOfModules.forget (R.over U)).map (A.unit.app G)))
    rw [hform]
    exact hcomp
  have : Sheaf.IsLocallyInjective ((SheafOfModules.toSheaf (R.over U)).map (A.unit.app G)) :=
    hlocal
  exact (SheafOfModules.toSheaf (R.over U)).mono_of_mono_map (Sheaf.mono_of_isLocallyInjective _)

/-- Extension by zero from the slice site reflects, as well as preserves, exactness of
complexes of sheaves of modules, over a site whose objects need not lie in the universe of its
morphisms: objects in an arbitrary universe `c`, morphisms and modules in `u`, and `C`
essentially `u`-small. -/
@[stacks 0E8G "for a site essentially u-small, objects in Type c, morphisms and modules in u"]
theorem extensionByZero_exact_iff
    (S : ShortComplex (SheafOfModules.{u} (R.over U))) :
    (S.map (SheafOfModules.pullback.{u} (F := Over.forget U)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)))).Exact ↔ S.Exact := by
  have := presheafRestrictionSheafIsRightAdjoint J R U
  let F := SheafOfModules.pullback.{u} (F := Over.forget U)
    (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))
  let A := SheafOfModules.PullbackConstruction.adjunction.{u}
    (F := Over.forget U) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))
  have : ∀ X : SheafOfModules.{u} (R.over U), Mono (A.unit.app X) := unit_mono J R U
  have : (SheafOfModules.forget (R.over U) ⋙
      PresheafOfModules.pullback.{u} (F := Over.forget U) (R := R.obj)
        (S := (R.over U).obj) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom ⋙
      PresheafOfModules.sheafification (R₀ := R.obj) (𝟙 R.obj)).Faithful :=
    A.faithful_L_of_mono_unit_app
  have : F.Faithful := Functor.Faithful.of_iso
    (SheafOfModules.pullbackIso (F := Over.forget U)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).symm
  obtain ⟨_, _⟩ := (exactFunctor_iff F).mp (extensionByZero_exact J R U)
  simpa only [F] using ShortComplex.exact_map_iff_of_faithful S F

/-- A sheaf of modules `M` is zero if the restriction of `j_{U!}M` is: the unit is a
monomorphism. -/
private theorem isZero_of_isZero_pushforward_pullback (M : SheafOfModules.{u} (R.over U))
    (h : IsZero ((SheafOfModules.pushforward.{u} (F := Over.forget U)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).obj
        ((SheafOfModules.pullback.{u} (F := Over.forget U)
          (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).obj M))) :
    IsZero M := by
  have := presheafRestrictionSheafIsRightAdjoint J R U
  have := unit_mono J R U M
  exact IsZero.of_mono
    ((SheafOfModules.PullbackConstruction.adjunction.{u}
      (F := Over.forget U) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).unit.app M)
    (h.of_iso ((SheafOfModules.pushforward.{u} (F := Over.forget U)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).mapIso
        ((SheafOfModules.pullbackIso (F := Over.forget U)
          (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).app M)).symm)

/-- **Extension by zero reflects zero objects.** If `j_{U!}M` is a zero object then so is `M`:
the unit `M ⟶ j_U^*j_{U!}M` is a monomorphism and restriction is additive, so `M` admits a
monomorphism into a zero object.

This is the form in which the reflection of exactness is used to read a vanishing statement on
the slice site off one on `C`. -/
theorem isZero_of_isZero_extensionByZero (M : SheafOfModules.{u} (R.over U))
    (hM : IsZero ((SheafOfModules.pullback.{u} (F := Over.forget U)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).obj M)) :
    IsZero M := by
  have : (SheafOfModules.pushforward.{u} (F := Over.forget U)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).Additive :=
    ⟨by intros; ext; rfl⟩
  exact isZero_of_isZero_pushforward_pullback J R U M
    ((SheafOfModules.pushforward.{u} (F := Over.forget U)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).map_isZero hM)

/-- **Restriction between slices is additive**, being computed on sections. -/
instance additive_overMap {V W : C} (p : W ⟶ V) :
    (SheafOfModules.overMap.{u} R p).Additive where
  map_add := by intros; ext; rfl

/-- **Extension by zero reflects zero objects through a restriction to a larger slice.**  Let
`p : W ⟶ V` be an arrow of `C` and `M` a sheaf of `R|_W`-modules.  If the restriction to the
slice over `V` of `j_{W!}M` is a zero object, then `M` itself is a zero object.

Restriction to the slice over `W` factors through restriction to the slice over `V` followed by
restriction along `p` (`SheafOfModules.overFunctorMap`), and restriction along `p` is additive,
so the hypothesis already gives that `(j_{W!}M)|_W` is a zero object; the unit
`M ⟶ (j_{W!}M)|_W` is a monomorphism, which is `unit_mono`, so `M` admits a monomorphism into a
zero object.

This is the form in which the reflection is used to read a vanishing statement on the slice
over `W` off one on the slice over `V`, which is what a hypothesis available only at `V` and a
conclusion wanted at `W` need.  Note that no *splitting* of the unit is used, and none is
available: the objectwise retraction of `M ⟶ (j_{W!}M)|_W` — project the direct sum of Stacks
03DI onto the summand indexed by the structure map — is not natural, since a summand indexed by
some other arrow `φ : Z ⟶ W` is carried into the summand indexed by the structure map of `Z'`
whenever `φ` composes to it.  What makes this statement go through without one is that it is
about a single module and not about exactness of a complex. -/
theorem isZero_of_isZero_over_extensionByZero {V W : C} (p : W ⟶ V)
    (M : SheafOfModules.{u} (R.over W))
    (hM : IsZero (((SheafOfModules.pullback.{u} (F := Over.forget W)
      (𝟙 (R.over W) : (R.over W) ⟶ (R.over W))).obj M).over V)) :
    IsZero M := by
  let N := (SheafOfModules.pullback.{u} (F := Over.forget W)
    (𝟙 (R.over W) : (R.over W) ⟶ (R.over W))).obj M
  exact isZero_of_isZero_pushforward_pullback J R W M
    (((SheafOfModules.overMap.{u} R p).map_isZero hM).of_iso
      ((SheafOfModules.overFunctorMap.{u} R p).app N).symm)

end Stacks.Sites.ExtensionByZero.OfEssentiallySmall

end
