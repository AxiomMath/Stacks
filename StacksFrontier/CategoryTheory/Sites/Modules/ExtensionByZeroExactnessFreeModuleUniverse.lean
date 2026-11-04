module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SliceExtensionExact
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroFreeModuleUniverse
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroExactness
import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of extension by zero at a module universe free of the morphism universe

Let `(C, J)` be a site, `R` a sheaf of rings on it and `U` an object of `C`. This file proves
that extension by zero `j_{U!}` from the slice site `C/U` is exact (Stacks 03DJ) and that it
*reflects* exactness (Stacks 0E8G), with the universe of the module sections a free parameter:
the objects of `C` lie in `Type u`, its morphisms in `Type v`, the sections of `R` in `Type w`
and the sections of the modules in `Type (max v a)`, the four universes otherwise unrelated.

`StacksFrontier/CategoryTheory/Sites/Modules/ExtensionByZeroExactness.lean` proves both with all
four universes collapsed to one, and
`StacksFrontier/CategoryTheory/Sites/Modules/ExtensionByZeroExactnessEssentiallySmall.lean` with
the universe of the objects freed but the modules still tied to the morphisms. The site this
file is for is the constant-coefficient ringed site of Stacks 03TR: an
`AlgebraicGeometry.RingedSite.{u + 1, u, max (u + 1) w r}`, whose module sections lie in
`max (u + 1) w r` while its morphisms lie in `u`. Neither earlier statement can be
instantiated at it, since both ask the modules to live in the universe of the morphisms.

## The bound `v ≤ max v a`

The module universe is not entirely free: it is written `max v a`, which says exactly that it
dominates the universe `v` of the morphisms of the site. That bound is real, not bookkeeping.
The sections of `j_{U!}M` over `V` are the direct sum of the `M(φ)` over the arrows
`φ : V ⟶ U` (the extension formula of Stacks 03EJ), so the index type of that direct sum is a
hom-set of `C`, which lies in `Type v`; a direct sum of modules indexed by a type in `Type v`
is a module whose underlying type lies in `Type v` as well. Left exactness of `j_{U!}` is
Grothendieck's axiom AB4 for that direct sum, `Stacks.Sites.OverModules.mono_sigmaMap`, and
that is where the bound is spent. It is no restriction for the sites this is wanted for: a
ringed site whose objects lie in `Type (u + 1)` has its module sections at least there too, so
the bound `u ≤ max (u + 1) w r` is automatic.

## Main results

* `Stacks.Sites.ExtensionByZero.FreeModuleUniverse.unit_mono`: the unit of `j_{U!} ⊣ j_U^*` is
  a monomorphism.
* `Stacks.Sites.ExtensionByZero.FreeModuleUniverse.extensionByZero_exact`: `j_{U!}` is exact,
  Stacks 03DJ at this shape.
* `Stacks.Sites.ExtensionByZero.FreeModuleUniverse.extensionByZero_exact_iff`: `j_{U!}`
  reflects exactness, Stacks 0E8G at this shape.

## Implementation notes

No essential smallness of `C` is needed, and none is assumed. The one step of the
single-universe development that depends on the size of `C` is the existence of the left
adjoint `j_{U!}` of restriction, and at a free module universe that comes from the explicit
direct sum of the extension formula, through
`SheafOfModules.presheafOverRestriction_of_univLE` and
`SheafOfModules.sheafOverRestriction_of_univLE`, whose only hypothesis is `UnivLE.{v, a}`.

Both the faithfulness and the mono-preservation of the presheaf-level extension are read off
that direct-sum model, `Stacks.Sites.OverModules.extensionFunctor`, and transported to
Mathlib's `PresheafOfModules.pullback` by the uniqueness of left adjoints
(`CategoryTheory.Adjunction.leftAdjointUniq`): the two functors are both left adjoint to
restriction, and restriction is literally the same functor in both spellings, since
`PresheafOfModules.pushforwardIdIsoFree` is `Iso.refl`.

Faithfulness of the direct-sum model is immediate from its formula for the action on
morphisms, `Stacks.Sites.OverModules.extensionFunctor_map_app_eq`: a map is sent to the
coproduct of its components, and a coproduct inclusion is a split monomorphism, so the
components are recovered from it. Faithfulness of `j_{U!}` at presheaf level is what makes the
*unit* of the presheaf adjunction a monomorphism
(`CategoryTheory.Adjunction.unit_mono_of_L_faithful`), and that monomorphism — objectwise
injective, since monomorphisms of presheaves of modules are — is the input of the sheaf-level
`unit_mono`, exactly as in the single-universe development.

`HasSheafify` rather than `HasWeakSheafify` is asked of both topologies. The collapsed
statements ask for the weak form and produce the strong one from essential smallness, which is
not available here; and the strong form is what left exactness of the sheafification of
presheaves of modules is stated under, and what makes the two module categories abelian, so
that the exactness statements are about something.

*A call site has to name the universes.* The module universe appears in the statements as
`max v a`, and Lean's level unifier does not solve `max v ?a =?= m` for a compound `m`: at
`v := u` and `m := max (u + 1) w r` it gets stuck, even though `a := max (u + 1) w r` is a
solution. So a consumer at the constant-coefficient ringed site writes
`extensionByZero_exact_iff.{max (u + 1) w r, max (u + 1) w r, u, u + 1}` — module parameter,
ring universe, morphism universe, object universe, in that order. The last example of this
file is that call, checked. This is the same bookkeeping the proof of Stacks 0E8K
does for its own inputs.

## References

* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
* [Stacks Project, Tag 0E8G](https://stacks.math.columbia.edu/tag/0E8G)
* [Stacks Project, Tag 03EJ](https://stacks.math.columbia.edu/tag/03EJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites.ExtensionByZero.FreeModuleUniverse

universe a w v u

section Presheaf

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C) [UnivLE.{v, a}]

/-- **The direct-sum model of extension by zero is faithful.** On sections over `X` the map
`j_{U!} f` is the coproduct of the components of `f` at the objects of `C/U` over `X`, and a
coproduct inclusion is a split monomorphism, so each component is determined. -/
lemma presheafExtension_faithful :
    (Stacks.Sites.OverModules.extensionFunctor.{v, u, w, a} O U).Faithful where
  map_injective {M M'} {f g} h := by
    refine PresheafOfModules.hom_ext fun A => ?_
    have h₁ := congrArg (fun α => PresheafOfModules.Hom.app α (op A.unop.left)) h
    simp only [Stacks.Sites.OverModules.extensionFunctor_map_app_eq] at h₁
    have h₂ := Sigma.ι (Stacks.Sites.OverModules.extensionSummands O U M (op A.unop.left))
      A.unop.hom ≫= h₁
    simp only [Sigma.ι_map] at h₂
    exact (cancel_mono _).1 h₂

/-- Mathlib's presheaf-level extension by zero is the direct-sum model, up to the canonical
isomorphism of left adjoints of restriction: the right adjoint is literally the same functor
in the two spellings, by `PresheafOfModules.pushforwardIdIsoFree`. -/
noncomputable def presheafPullbackIsoExtension :
    PresheafOfModules.pullback.{a} (F := Over.forget U)
        (R := O) (S := (Over.forget U).op ⋙ O) (𝟙 ((Over.forget U).op ⋙ O)) ≅
      Stacks.Sites.OverModules.extensionFunctor.{v, u, w, a} O U :=
  Adjunction.leftAdjointUniq
    (PresheafOfModules.pullbackPushforwardAdjunction.{a} (F := Over.forget U)
      (R := O) (S := (Over.forget U).op ⋙ O) (𝟙 ((Over.forget U).op ⋙ O)))
    (Stacks.Sites.OverModules.extensionFunctorAdjunction.{v, u, w, a} O U)

/-- **Mathlib's presheaf-level extension by zero is faithful**, being isomorphic to the
direct-sum model. -/
lemma presheafPullback_faithful :
    (PresheafOfModules.pullback.{a} (F := Over.forget U)
      (R := O) (S := (Over.forget U).op ⋙ O)
      (𝟙 ((Over.forget U).op ⋙ O))).Faithful :=
  have : (Stacks.Sites.OverModules.extensionFunctor.{v, u, w, a} O U).Faithful :=
    presheafExtension_faithful O U
  Functor.Faithful.of_iso (presheafPullbackIsoExtension O U).symm

end Presheaf

section Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Sheaf J RingCat.{w}) (U : C)
  [HasSheafify J AddCommGrpCat.{max v a}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max v a}]
  [HasSheafify (J.over U) AddCommGrpCat.{max v a}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max v a}]

/-- Restriction of presheaves of modules along `Over.forget U` is a right adjoint, restated at
the spelling that takes the identity morphism of `R.over U`, which is the spelling the
sheaf-level adjunction of `SheafOfModules.PullbackConstruction` asks for and which the instance
discrimination tree does not match against the generic one. -/
local instance presheafRestrictionIsRightAdjoint' :
    (PresheafOfModules.pushforward.{max v a} (F := Over.forget U) (R := R.obj)
      (S := (R.over U).obj)
      (𝟙 (R.over U) : R.over U ⟶ R.over U).hom).IsRightAdjoint :=
  SheafOfModules.presheafOverRestriction_of_univLE R U

omit [HasSheafify J AddCommGrpCat.{max v a}] [J.WEqualsLocallyBijective AddCommGrpCat.{max v a}]
  [HasSheafify (J.over U) AddCommGrpCat.{max v a}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max v a}] in
/-- `presheafPullback_faithful` at the spelling that takes the identity morphism of the
restricted sheaf of rings `R.over U`, which is the spelling the sheaf-level adjunction of
`SheafOfModules.PullbackConstruction` is built at. The two types are definitionally equal; the
restatement is what makes the instance recognisable. -/
@[sga "4 IV 11.3.1" "special case"]
private lemma presheafPullbackSheaf_faithful :
    (PresheafOfModules.pullback.{max v a} (F := Over.forget U) (R := R.obj)
      (S := (R.over U).obj)
      (𝟙 (R.over U) : R.over U ⟶ R.over U).hom).Faithful :=
  presheafPullback_faithful R.obj U

omit [HasSheafify J AddCommGrpCat.{max v a}] [J.WEqualsLocallyBijective AddCommGrpCat.{max v a}]
  [HasSheafify (J.over U) AddCommGrpCat.{max v a}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max v a}] in
/-- The unit of the presheaf-level extension-by-zero/restriction adjunction is a monomorphism:
extension by zero is faithful at presheaf level. -/
private lemma presheafUnit_mono (G : SheafOfModules.{max v a} (R.over U)) :
    Mono ((PresheafOfModules.pullbackPushforwardAdjunction.{max v a} (F := Over.forget U)
      (R := R.obj) (S := (R.over U).obj)
      (𝟙 (R.over U) : R.over U ⟶ R.over U).hom).unit.app G.val) :=
  have : (PresheafOfModules.pullback.{max v a} (F := Over.forget U) (R := R.obj)
      (S := (R.over U).obj)
      (𝟙 (R.over U) : R.over U ⟶ R.over U).hom).Faithful :=
    presheafPullbackSheaf_faithful J R U
  Adjunction.unit_mono_of_L_faithful _ G.val

omit [HasSheafify J AddCommGrpCat.{max v a}] [J.WEqualsLocallyBijective AddCommGrpCat.{max v a}]
  [HasSheafify (J.over U) AddCommGrpCat.{max v a}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max v a}] in
/-- The underlying map of abelian presheaves of the presheaf-level unit is locally injective. -/
private lemma presheafUnit_isLocallyInjective (G : SheafOfModules.{max v a} (R.over U)) :
    Presheaf.IsLocallyInjective (J.over U)
      ((PresheafOfModules.toPresheaf (R.over U).obj).map
        ((PresheafOfModules.pullbackPushforwardAdjunction.{max v a} (F := Over.forget U)
          (R := R.obj) (S := (R.over U).obj)
          (𝟙 (R.over U) : R.over U ⟶ R.over U).hom).unit.app G.val)) := by
  have := presheafUnit_mono J R U G
  have hm := Functor.map_mono (PresheafOfModules.toPresheaf (R.over U).obj)
    ((PresheafOfModules.pullbackPushforwardAdjunction.{max v a} (F := Over.forget U)
      (R := R.obj) (S := (R.over U).obj)
      (𝟙 (R.over U) : R.over U ⟶ R.over U).hom).unit.app G.val)
  exact Presheaf.isLocallyInjective_of_injective _ _ fun X =>
    (AddCommGrpCat.mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 hm X)

omit [HasSheafify (J.over U) AddCommGrpCat.{max v a}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max v a}] in
/-- **The unit of the extension-by-zero/restriction adjunction of sheaves of modules is a
monomorphism.** The presheaf-level unit is injective and sheafification is locally injective,
which on a separated presheaf is injectivity. -/
theorem unit_mono (G : SheafOfModules.{max v a} (R.over U)) :
    Mono ((SheafOfModules.PullbackConstruction.adjunction.{max v a}
      (F := Over.forget U) (𝟙 (R.over U) : R.over U ⟶ R.over U)).unit.app G) := by
  let pAdj := PresheafOfModules.pullbackPushforwardAdjunction.{max v a} (F := Over.forget U)
    (R := R.obj) (S := (R.over U).obj) (𝟙 (R.over U) : R.over U ⟶ R.over U).hom
  let P := (PresheafOfModules.pullback.{max v a} (F := Over.forget U) (R := R.obj)
    (S := (R.over U).obj) (𝟙 (R.over U) : R.over U ⟶ R.over U).hom).obj G.val
  let sAdj := PresheafOfModules.sheafificationAdjunction.{max v a} (𝟙 R.obj)
  let A := SheafOfModules.PullbackConstruction.adjunction.{max v a}
    (F := Over.forget U) (𝟙 (R.over U) : R.over U ⟶ R.over U)
  let push := PresheafOfModules.pushforward.{max v a} (F := Over.forget U) (R := R.obj)
    (S := (R.over U).obj) (𝟙 (R.over U) : R.over U ⟶ R.over U).hom
  have hform : (SheafOfModules.forget (R.over U)).map (A.unit.app G) =
      pAdj.unit.app G.val ≫ push.map (sAdj.unit.app P) := by
    dsimp [A, P, pAdj, sAdj, push, SheafOfModules.PullbackConstruction.adjunction,
      Adjunction.mkOfHomEquiv]
    rfl
  have hp : Presheaf.IsLocallyInjective (J.over U)
      ((PresheafOfModules.toPresheaf (R.over U).obj).map (pAdj.unit.app G.val)) :=
    presheafUnit_isLocallyInjective J R U G
  have hs : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf R.obj).map (sAdj.unit.app P)) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact (J.W_toSheafify P.presheaf).isLocallyInjective
  have hpushlocal : Presheaf.IsLocallyInjective (J.over U)
      ((PresheafOfModules.toPresheaf (R.over U).obj).map (push.map (sAdj.unit.app P))) :=
    Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U)
      ((PresheafOfModules.toPresheaf R.obj).map (sAdj.unit.app P))
  have hcomp : Presheaf.IsLocallyInjective (J.over U)
      ((PresheafOfModules.toPresheaf (R.over U).obj).map
        (pAdj.unit.app G.val ≫ push.map (sAdj.unit.app P))) := by
    have : Presheaf.IsLocallyInjective (J.over U)
        ((PresheafOfModules.toPresheaf (R.over U).obj).map (pAdj.unit.app G.val) ≫
          (PresheafOfModules.toPresheaf (R.over U).obj).map (push.map (sAdj.unit.app P))) :=
      inferInstance
    simpa only [Functor.map_comp] using this
  have : Sheaf.IsLocallyInjective ((SheafOfModules.toSheaf (R.over U)).map (A.unit.app G)) := by
    change Presheaf.IsLocallyInjective (J.over U)
      ((PresheafOfModules.toPresheaf (R.over U).obj).map
        ((SheafOfModules.forget (R.over U)).map (A.unit.app G)))
    rw [hform]
    exact hcomp
  exact (SheafOfModules.toSheaf (R.over U)).mono_of_mono_map (Sheaf.mono_of_isLocallyInjective _)

omit [HasSheafify (J.over U) AddCommGrpCat.{max v a}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max v a}] in
/-- **Extension by zero preserves monomorphisms.** The presheaf-level extension does, being
isomorphic to the direct-sum model; sheafification of presheaves of modules is left exact; and
`SheafOfModules.pullbackIso` exhibits `j_{U!}` as their composite with the forgetful functor. -/
@[sga "4 IV 11.3.1" "Exactness clause", sga "4 XVII 5.1.1" "module version"]
lemma extensionByZero_preservesMonomorphisms :
    Functor.PreservesMonomorphisms (SheafOfModules.pullback.{max v a}
      (F := Over.forget U) (𝟙 (R.over U) : R.over U ⟶ R.over U)) := by
  have hP : Functor.PreservesMonomorphisms
      (PresheafOfModules.pullback.{max v a} (F := Over.forget U) (R := R.obj)
        (S := (R.over U).obj) (𝟙 (R.over U) : R.over U ⟶ R.over U).hom) :=
    (Functor.PreservesMonomorphisms.iso_iff
      (presheafPullbackIsoExtension R.obj U)).2
      (Stacks.Sites.OverModules.extensionFunctor_preservesMonos R.obj U)
  refine (Functor.PreservesMonomorphisms.iso_iff
    (SheafOfModules.pullbackIso.{max v a} (F := Over.forget U)
      (𝟙 (R.over U) : R.over U ⟶ R.over U))).2 ?_
  infer_instance

/-- **Stacks 03DJ at a free module universe.** Extension by zero of sheaves of modules along
the localization `C/U ⟶ C` is exact.

Extension by zero is a left adjoint, so it preserves colimits and in particular is right
exact; and it preserves monomorphisms, so it is exact.

The tag is carried in full by `Stacks.Sites.ExtensionByZero.extensionByZero_exact`, the
single-universe statement, which this one generalises; that registration stands and this one
does not replace it. -/
theorem extensionByZero_exact :
    exactFunctor (SheafOfModules.{max v a} (R.over U)) (SheafOfModules.{max v a} R)
      (SheafOfModules.pullback.{max v a}
        (F := Over.forget U) (𝟙 (R.over U) : R.over U ⟶ R.over U)) := by
  have hadd₀ : (SheafOfModules.pushforward.{max v a} (F := Over.forget U)
      (𝟙 (R.over U) : R.over U ⟶ R.over U)).Additive :=
    ⟨by intros; ext; rfl⟩
  have hadd : (SheafOfModules.pullback.{max v a} (F := Over.forget U)
      (𝟙 (R.over U) : R.over U ⟶ R.over U)).Additive :=
    (SheafOfModules.pullbackPushforwardAdjunction.{max v a} (F := Over.forget U)
      (𝟙 (R.over U) : R.over U ⟶ R.over U)).left_adjoint_additive
  have hmono : Functor.PreservesMonomorphisms (SheafOfModules.pullback.{max v a}
      (F := Over.forget U) (𝟙 (R.over U) : R.over U ⟶ R.over U)) :=
    extensionByZero_preservesMonomorphisms J R U
  have hcol : PreservesColimitsOfSize.{0, 0} (SheafOfModules.pullback.{max v a}
      (F := Over.forget U) (𝟙 (R.over U) : R.over U ⟶ R.over U)) :=
    (SheafOfModules.pullbackPushforwardAdjunction.{max v a} (F := Over.forget U)
      (𝟙 (R.over U) : R.over U ⟶ R.over U)).leftAdjoint_preservesColimits
  have hhom : Functor.PreservesHomology (SheafOfModules.pullback.{max v a}
      (F := Over.forget U) (𝟙 (R.over U) : R.over U ⟶ R.over U)) :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels _
  exact (exactFunctor_iff _).2 ⟨Functor.preservesFiniteLimits_of_preservesHomology _,
    PreservesColimitsOfSize.preservesFiniteColimits _⟩

/-- **Stacks 0E8G at a free module universe.** Extension by zero from the slice site reflects,
as well as preserves, exactness of complexes of sheaves of modules, over a site whose module
sections need not lie in the universe of its morphisms.

The attribute records the universe shape: the objects of `C` in an arbitrary universe `u`, its
morphisms in `v`, the sections of `R` in `w` and the module sections in `max v a`. The tag is
carried in full by `Stacks.Sites.ExtensionByZero.extensionByZero_exact_iff`, the
single-universe statement, which this one generalises; that registration stands and this one
does not replace it. -/
@[stacks 0E8G "objects in Type u, morphisms in v, ring sections in w, modules in max v a"]
theorem extensionByZero_exact_iff
    (S : ShortComplex (SheafOfModules.{max v a} (R.over U))) :
    (S.map (SheafOfModules.pullback.{max v a} (F := Over.forget U)
      (𝟙 (R.over U) : R.over U ⟶ R.over U))).Exact ↔ S.Exact := by
  let F := SheafOfModules.pullback.{max v a} (F := Over.forget U)
    (𝟙 (R.over U) : R.over U ⟶ R.over U)
  let A := SheafOfModules.PullbackConstruction.adjunction.{max v a}
    (F := Over.forget U) (𝟙 (R.over U) : R.over U ⟶ R.over U)
  have : ∀ X : SheafOfModules.{max v a} (R.over U), Mono (A.unit.app X) := unit_mono J R U
  have : (SheafOfModules.forget (R.over U) ⋙
      PresheafOfModules.pullback.{max v a} (F := Over.forget U) (R := R.obj)
        (S := (R.over U).obj) (𝟙 (R.over U) : R.over U ⟶ R.over U).hom ⋙
      PresheafOfModules.sheafification.{max v a} (R₀ := R.obj) (𝟙 R.obj)).Faithful :=
    A.faithful_L_of_mono_unit_app
  have : F.Faithful := Functor.Faithful.of_iso
    (SheafOfModules.pullbackIso.{max v a} (F := Over.forget U)
      (𝟙 (R.over U) : R.over U ⟶ R.over U)).symm
  obtain ⟨_, _⟩ := (exactFunctor_iff F).mp (extensionByZero_exact J R U)
  simpa only [F] using ShortComplex.exact_map_iff_of_faithful S F

end Sheaf

section Instantiations

universe c r

/-- The shape the earlier `OfEssentiallySmall` statement is at — objects in an arbitrary
universe `c`, morphisms, ring sections and module sections all in `u` — is the case
`v := u`, `a := u` of `extensionByZero_exact_iff`, so nothing is lost by generalising. -/
example {C : Type c} [Category.{u} C] (J : GrothendieckTopology C)
    (R : Sheaf J RingCat.{u}) (U : C)
    [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (S : ShortComplex (SheafOfModules.{u} (R.over U))) :
    (S.map (SheafOfModules.pullback.{u} (F := Over.forget U)
      (𝟙 (R.over U) : R.over U ⟶ R.over U))).Exact ↔ S.Exact :=
  extensionByZero_exact_iff J R U S

/-- The shape of the constant-coefficient ringed site of Stacks 03TR — an
`AlgebraicGeometry.RingedSite.{u + 1, u, max (u + 1) w r}`, whose module sections lie in
`max (u + 1) w r` and whose morphisms lie in `u` — which neither of the collapsed statements
reaches. The universes have to be named, for the reason recorded in the implementation notes
above. -/
example {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (R : Sheaf J RingCat.{max (u + 1) w r}) (U : C)
    [HasSheafify J AddCommGrpCat.{max (u + 1) w r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) w r}]
    [HasSheafify (J.over U) AddCommGrpCat.{max (u + 1) w r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) w r}]
    (S : ShortComplex (SheafOfModules.{max (u + 1) w r} (R.over U))) :
    (S.map (SheafOfModules.pullback.{max (u + 1) w r} (F := Over.forget U)
      (𝟙 (R.over U) : R.over U ⟶ R.over U))).Exact ↔ S.Exact :=
  extensionByZero_exact_iff.{max (u + 1) w r, max (u + 1) w r, u, u + 1} J R U S

end Instantiations

end Stacks.Sites.ExtensionByZero.FreeModuleUniverse

end
