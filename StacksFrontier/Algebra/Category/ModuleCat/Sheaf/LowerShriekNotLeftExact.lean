module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.Data.ZMod.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriek
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact

/-!
# Lower shriek on modules is not left exact, however good the functor of sites

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites, `O` a sheaf of rings on `D`
and `O_C = u^{-1}O` its restriction, so that `u` is a morphism of ringed topoi whose structure
map is the identity.  The lower shriek `u_! : Mod(O_C) ⥤ Mod(O)` of [Stacks, Tag 0797] is a left
adjoint, hence right exact.  **It is not left exact**, and this file shows that no formal
property of the functor of sites can make it so: the example below has `u` fully faithful,
continuous, cocontinuous and final, the objects of the image cover every object of the target
site (`CategoryTheory.GrothendieckTopology.CoversTop`), the structure map of the ringed situation
is the identity of `u^{-1}O` by construction — and `u_!` does not preserve the monomorphism
`𝟙 + 𝟙` of the structure sheaf.

The obstruction is the extension of scalars that the module-level lower shriek carries and the
abelian-level one does not.  Writing `u_!^{Ab}` for the lower shriek of the underlying abelian
sheaves, which is exact under [Stacks, Tag 00X6], the module-level one is

`u_!M = (u_!^{Ab}M ⊗_{u_!^{Ab}O_C} O)^#`,

because the tensor product commutes with colimits in both variables; so it is exact exactly when
`O` is flat over the counit `u_!^{Ab}O_C ⟶ O`.  In the example that map is `ℤ ⟶ ℤ/2`, as non-flat
as a ring map gets, and the failure is visible already at the structure sheaf itself: `𝟙 + 𝟙`
is injective on the sections `ℤ` of `O_C` and is zero on the sections `ℤ/2` of `O` over the
object `false`.

## The example

The target site is `Bool` ordered by `false ≤ true`, with the trivial topology; the source site
is the one-object category `PUnit`, with the trivial topology, mapping to `true`.  The sheaf of
rings is `ℤ` at `true`, `ℤ/2` at `false` and the reduction `ℤ ⟶ ℤ/2` as its restriction map.
`true` is the terminal object of `Bool` and `false` admits a morphism to it, so the single object
`true` of the image covers the whole site, and the index category of the pointwise left Kan
extension along `u.op` has a terminal object over each of the two objects — which is why the
unit is invertible and why the module lower shriek at `false` is exactly
`− ⊗_ℤ ℤ/2`.

## Main results

* `Stacks.SheafOfModules.lowerShriek_not_preservesMonomorphisms` — **there is a continuous,
  cocontinuous, fully faithful and final functor of sites whose image covers the target site,
  with the identity structure map, for which the lower shriek of [Stacks, Tag 0797] on sheaves of
  modules does not preserve monomorphisms**; hence it is neither left exact nor exact, although
  it is right exact and fully faithful.
* `Stacks.SheafOfModules.lowerShriek_not_preservesFiniteLimits` — the same statement as a failure
  of `CategoryTheory.Limits.PreservesFiniteLimits`, which is the form in which exactness of a
  lower shriek is asked for.

## What is and is not proved

The two statements prove, of the one functor of sites exhibited, that it is continuous,
cocontinuous, full, faithful and final, that its image covers the target site, and that its
module-level lower shriek preserves neither monomorphisms nor finite limits.  Two further
properties of the example are remarks rather than theorems here, because no statement below uses
them: the source site `PUnit` has all finite limits and `u` preserves them, which is immediate
since `PUnit` is the terminal category and `true` is the terminal object of `Bool`; and the unit
`id ⟶ u^{-1}u_!` is invertible, because the index category of the pointwise left Kan extension
over `true` is the one-morphism category.  Neither is needed to read the moral: these are the
properties a "direct" argument for a particular inclusion of sites would appeal to, and the
conclusion fails with all of them in hand.

## Implementation notes

The two statements are existential in the topologies, the functor and the sheaf of rings, and
bundle the good properties of the functor of sites as conjuncts; the two sites themselves are
written out, as in `Stacks.SheafOfModules.lowerShriekForget_not_isomorphic`.  Finality of `u` is
what makes the comparison `u_!(O_C) ⟶ O` of `SheafOfModules.pullbackObjUnitToUnit` an
isomorphism, so the morphism whose mononess fails is transported to `𝟙 + 𝟙` of the structure
sheaf of the target, where it is read off from the sections over `false`.

Monomorphisms of sheaves of modules are tested on sections through
`PresheafOfModules.mono_iff_surjective` (whose name says `surjective` but whose content is
injectivity) along the fully faithful `SheafOfModules.forget`, which preserves monomorphisms
being a right adjoint; nothing here needs the abelian structure.

This is the exactness counterpart of
`Stacks.SheafOfModules.lowerShriekForget_not_isomorphic`, which exhibits a situation where the
comparison of [Stacks, Tag 0798] between the two lower shrieks fails.  That example cannot
settle exactness: its restriction map of structure sheaves is the diagonal `ℤ/2 ⟶ ℤ/2 × ℤ/2`,
which *is* flat, so its module lower shriek is exact even though the comparison is not
invertible.

## References

* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
* [Stacks Project, Tag 00X6](https://stacks.math.columbia.edu/tag/00X6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules

/-! ### The two sites and the functor between them -/

/-- The functor of sites of the counterexample: the one-object site `PUnit` to `Bool` ordered by
`false ≤ true`, hitting `true`. -/
private def notExactFunctor : PUnit.{1} ⥤ Bool where
  obj _ := true
  map _ := 𝟙 true

private abbrev notExactBig : GrothendieckTopology Bool := ⊥

private instance : notExactFunctor.Full where
  map_surjective _ := ⟨𝟙 _, Subsingleton.elim _ _⟩

private instance : notExactFunctor.Faithful where
  map_injective _ := Subsingleton.elim _ _

private instance : notExactFunctor.IsContinuous
    (⊥ : GrothendieckTopology PUnit.{1}) notExactBig :=
  ⟨fun _ => Presieve.isSheaf_bot⟩

private instance : notExactFunctor.IsCocontinuous
    (⊥ : GrothendieckTopology PUnit.{1}) notExactBig := by
  refine ⟨?_⟩
  intro U S hS
  obtain rfl := (GrothendieckTopology.bot_covering).mp hS
  exact (GrothendieckTopology.bot_covering).mpr (Sieve.functorPullback_top notExactFunctor U)

private instance : notExactFunctor.Final where
  out d := by
    have : Subsingleton (StructuredArrow d notExactFunctor) :=
      ⟨fun X Y => by cases X; cases Y; congr <;> subsingleton⟩
    have : Nonempty (StructuredArrow d notExactFunctor) :=
      ⟨StructuredArrow.mk (Y := PUnit.unit)
        (homOfLE (show d ≤ true from le_top))⟩
    exact isConnected_of_nonempty_and_subsingleton

/-- Every object of `Bool` admits a morphism to `true`, so the single object of the image of the
functor of sites covers the whole target site. -/
private theorem notExactFunctor_coversTop :
    notExactBig.CoversTop notExactFunctor.obj := by
  intro X
  refine notExactBig.superset_covering ?_ (notExactBig.top_mem X)
  intro Y f _
  exact ⟨PUnit.unit, ⟨homOfLE le_top⟩⟩

/-! ### The sheaf of rings `ℤ` at `true` and `ℤ/2` at `false` -/

/-- There is no morphism `true ⟶ false` in `Bool` ordered by `false ≤ true`. -/
private theorem false_of_hom_true_false (f : (true : Bool) ⟶ false) : False :=
  absurd f.down.down (by decide)

/-- The presheaf of rings of the counterexample: `ℤ` at `true`, `ℤ/2` at `false`, and the
reduction `ℤ ⟶ ℤ/2` as the restriction map. -/
private def notExactRingPresheaf : Boolᵒᵖ ⥤ RingCat.{0} where
  obj X := match X.unop with
    | false => RingCat.of (ZMod 2)
    | true => RingCat.of ℤ
  map := by
    intro X Y f
    cases X with
    | op x =>
      cases Y with
      | op y =>
        cases x <;> cases y
        · exact 𝟙 _
        · exact (false_of_hom_true_false f.unop).elim
        · exact RingCat.ofHom (Int.castRingHom (ZMod 2))
        · exact 𝟙 _
  map_id := by
    intro X
    cases X with
    | op x => cases x <;> rfl
  map_comp := by
    intro X Y Z f g
    cases X with
    | op x =>
      cases Y with
      | op y =>
        cases Z with
        | op z =>
          cases x <;> cases y <;> cases z
          case op.op.op.false.true.false =>
            exact (false_of_hom_true_false f.unop).elim
          case op.op.op.true.false.true =>
            exact (false_of_hom_true_false g.unop).elim
          all_goals ext a; simp_all

/-- The presheaf of rings of the counterexample, as a sheaf for the trivial topology. -/
private def notExactRing : Sheaf notExactBig RingCat.{0} :=
  ⟨notExactRingPresheaf, Presheaf.isSheaf_bot _⟩

private instance : HasSheafify notExactBig AddCommGrpCat.{0} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{0} _

private instance : HasSheafify (⊥ : GrothendieckTopology PUnit.{1}) AddCommGrpCat.{0} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{0} _

private instance : notExactBig.WEqualsLocallyBijective AddCommGrpCat.{0} :=
  GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat.{0} _

private instance : (⊥ : GrothendieckTopology PUnit.{1}).WEqualsLocallyBijective AddCommGrpCat.{0} :=
  GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat.{0} _

/-- The restriction of the structure sheaf to the source site: the sheaf of rings with value `ℤ`
at the unique object. -/
private abbrev notExactSmallRing : Sheaf (⊥ : GrothendieckTopology PUnit.{1}) RingCat.{0} :=
  inverseImageRing ⊥ notExactBig notExactFunctor notExactRing

private instance :
    (_root_.SheafOfModules.pushforward.{0}
      (structureMap ⊥ notExactBig notExactFunctor notExactRing)).IsRightAdjoint :=
  isRightAdjoint_inverseImage.{0} ⊥ notExactBig notExactFunctor notExactRing

/-! ### `𝟙 + 𝟙` on the structure sheaf -/

/-- The sections of `𝟙 + 𝟙` on a sheaf of modules are `x ↦ x + x`. -/
private theorem add_id_app_apply {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{0}} (M : _root_.SheafOfModules.{0} R) (X : Cᵒᵖ) (x : M.val.obj X) :
    ((_root_.SheafOfModules.forget R).map (𝟙 M + 𝟙 M)).app X x = x + x := rfl

/-- `𝟙 + 𝟙` is a monomorphism as soon as `x ↦ x + x` is injective on all sections. -/
private theorem mono_add_id {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{0}} (M : _root_.SheafOfModules.{0} R)
    (h : ∀ (X : Cᵒᵖ) (x y : M.val.obj X), x + x = y + y → x = y) :
    Mono (𝟙 M + 𝟙 M) := by
  refine (_root_.SheafOfModules.forget R).mono_of_mono_map (f := 𝟙 M + 𝟙 M) ?_
  refine PresheafOfModules.mono_of_injective (fun X a b hab => h X a b ?_)
  rw [← add_id_app_apply M X a, ← add_id_app_apply M X b]
  exact hab

/-- If `𝟙 + 𝟙` is a monomorphism then `x ↦ x + x` is injective on every sections module. -/
private theorem injective_of_mono_add_id {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{0}} (M : _root_.SheafOfModules.{0} R) (hM : Mono (𝟙 M + 𝟙 M))
    (X : Cᵒᵖ) (x y : M.val.obj X) (hxy : x + x = y + y) : x = y := by
  have : Mono ((_root_.SheafOfModules.forget R).map (𝟙 M + 𝟙 M)) :=
    (_root_.SheafOfModules.forget R).map_mono _
  refine PresheafOfModules.injective_of_mono
    ((_root_.SheafOfModules.forget R).map (𝟙 M + 𝟙 M)) X ?_
  rw [add_id_app_apply, add_id_app_apply]
  exact hxy

/-! ### The failure of left exactness -/

/-- The lower shriek on sheaves of modules of the counterexample. -/
private abbrev notExactShriek :=
  lowerShriek.{0} ⊥ notExactBig notExactFunctor notExactRing

/-- `𝟙 + 𝟙` is a monomorphism on the structure sheaf of the source site, whose sections are
`ℤ`. -/
private theorem mono_add_id_unit_small :
    Mono (𝟙 (_root_.SheafOfModules.unit notExactSmallRing) +
      𝟙 (_root_.SheafOfModules.unit notExactSmallRing)) :=
  mono_add_id _ fun _ x y h =>
    (show ∀ a b : ℤ, a + a = b + b → a = b from fun _ _ hab => by omega) x y h

/-- `𝟙 + 𝟙` is not a monomorphism on the structure sheaf of the target site: over `false` its
sections are `ℤ/2`, where `x + x = 0`. -/
private theorem not_mono_add_id_unit_big :
    ¬ Mono (𝟙 (_root_.SheafOfModules.unit notExactRing) +
      𝟙 (_root_.SheafOfModules.unit notExactRing)) := fun h =>
  absurd (injective_of_mono_add_id _ h (op false) (0 : ZMod 2) (1 : ZMod 2)
      (show (0 : ZMod 2) + 0 = 1 + 1 by decide))
    (show ¬ ((0 : ZMod 2) = 1) by decide)

/-- **The lower shriek of the structure sheaf is the structure sheaf**: the comparison
`u_!(u^{-1}O) ⟶ O` of `SheafOfModules.pullbackObjUnitToUnit` is invertible because the functor of
sites is final. -/
private def notExactShriekUnitIso :
    notExactShriek.obj (_root_.SheafOfModules.unit notExactSmallRing) ≅
      _root_.SheafOfModules.unit notExactRing :=
  (lowerShriekIsoPullback.{0} ⊥ notExactBig notExactFunctor notExactRing).app _ ≪≫
    asIso (_root_.SheafOfModules.pullbackObjUnitToUnit
      (structureMap ⊥ notExactBig notExactFunctor notExactRing))

private instance :
    (inverseImage.{0} ⊥ notExactBig notExactFunctor notExactRing).Additive where
  map_add := rfl

/-- The lower shriek of the counterexample does not preserve the monomorphism `𝟙 + 𝟙` of the
structure sheaf. -/
private theorem notExactShriek_not_preservesMonomorphisms :
    ¬ notExactShriek.PreservesMonomorphisms := by
  intro h
  have : notExactShriek.Additive :=
    (lowerShriekAdjunction.{0} ⊥ notExactBig notExactFunctor
      notExactRing).left_adjoint_additive
  have := mono_add_id_unit_small
  have hm : Mono (notExactShriek.map
      (𝟙 (_root_.SheafOfModules.unit notExactSmallRing) +
        𝟙 (_root_.SheafOfModules.unit notExactSmallRing))) :=
    h.preserves _
  rw [Functor.map_add, CategoryTheory.Functor.map_id] at hm
  refine not_mono_add_id_unit_big ?_
  have hconj : (𝟙 (_root_.SheafOfModules.unit notExactRing) +
        𝟙 (_root_.SheafOfModules.unit notExactRing)) =
      notExactShriekUnitIso.inv ≫
        (𝟙 (notExactShriek.obj (_root_.SheafOfModules.unit notExactSmallRing)) +
          𝟙 (notExactShriek.obj (_root_.SheafOfModules.unit notExactSmallRing))) ≫
        notExactShriekUnitIso.hom := by
    simp [Preadditive.add_comp, Preadditive.comp_add]
  rw [hconj]
  infer_instance

/-- The lower shriek of the counterexample does not preserve finite limits. -/
private theorem notExactShriek_not_preservesFiniteLimits :
    ¬ PreservesFiniteLimits notExactShriek := by
  intro h
  have := h
  exact notExactShriek_not_preservesMonomorphisms inferInstance

/-- **The lower shriek of [Stacks, Tag 0797] on sheaves of modules does not preserve
monomorphisms**, and no formal property of the functor of sites can make it do so.  No tag is
registered: this is the negation of an assertion the source does not make.

There is a functor of sites `u : C ⥤ D` which is continuous, cocontinuous, fully faithful and
final, whose image covers the target site
(`CategoryTheory.GrothendieckTopology.CoversTop`), and a sheaf of rings `O` on `D`, for which the
lower shriek `u_! : Mod(u^{-1}O) ⥤ Mod(O)` of [Stacks, Tag 0797] — whose structure map is the
identity of `u^{-1}O` by construction, and whose unit `id ⟶ u^{-1}u_!` is therefore invertible —
does not preserve monomorphisms, hence is not left exact.

The example is `u : PUnit ⥤ Bool` hitting `true`, both sites with the trivial topology, and the
sheaf of rings `ℤ` at `true`, `ℤ/2` at `false`, with the reduction as its restriction map; the
monomorphism not preserved is `𝟙 + 𝟙` on the structure sheaf, which is injective on the sections
`ℤ` of `u^{-1}O` and zero on the sections `ℤ/2` of `O` over `false`.

This is the counterexample that `Stacks.SheafOfModules.lowerShriekForget_not_isomorphic` does
*not* give: there the restriction map of structure sheaves is the flat `ℤ/2 ⟶ ℤ/2 × ℤ/2`, so the
module-level lower shriek of that example is exact and only the comparison of
[Stacks, Tag 0798] fails. -/
theorem lowerShriek_not_preservesMonomorphisms :
    ∃ (J : GrothendieckTopology PUnit.{1}) (K : GrothendieckTopology Bool)
      (u : PUnit.{1} ⥤ Bool) (hu : u.IsContinuous J K) (huc : u.IsCocontinuous J K)
      (hsh : HasWeakSheafify K AddCommGrpCat.{0})
      (hwb : K.WEqualsLocallyBijective AddCommGrpCat.{0})
      (O : Sheaf K RingCat.{0}),
      letI := hu
      letI := huc
      letI := hsh
      letI := hwb
      u.Full ∧ u.Faithful ∧ u.Final ∧ K.CoversTop u.obj ∧
        ¬ (lowerShriek.{0} J K u O).PreservesMonomorphisms :=
  ⟨⊥, notExactBig, notExactFunctor, inferInstance, inferInstance, inferInstance,
    inferInstance, notExactRing, inferInstance, inferInstance, inferInstance,
    notExactFunctor_coversTop, notExactShriek_not_preservesMonomorphisms⟩

/-- **The lower shriek of [Stacks, Tag 0797] on sheaves of modules is not left exact**, in
the same situation as `Stacks.SheafOfModules.lowerShriek_not_preservesMonomorphisms` and in the
form in which exactness of a lower shriek is asked for.  Preservation of finite *co*limits is
free, lower shriek being a left adjoint; preservation of finite limits fails. -/
theorem lowerShriek_not_preservesFiniteLimits :
    ∃ (J : GrothendieckTopology PUnit.{1}) (K : GrothendieckTopology Bool)
      (u : PUnit.{1} ⥤ Bool) (hu : u.IsContinuous J K) (huc : u.IsCocontinuous J K)
      (hsh : HasWeakSheafify K AddCommGrpCat.{0})
      (hwb : K.WEqualsLocallyBijective AddCommGrpCat.{0})
      (O : Sheaf K RingCat.{0}),
      letI := hu
      letI := huc
      letI := hsh
      letI := hwb
      u.Full ∧ u.Faithful ∧ u.Final ∧ K.CoversTop u.obj ∧
        ¬ PreservesFiniteLimits (lowerShriek.{0} J K u O) :=
  ⟨⊥, notExactBig, notExactFunctor, inferInstance, inferInstance, inferInstance,
    inferInstance, notExactRing, inferInstance, inferInstance, inferInstance,
    notExactFunctor_coversTop, notExactShriek_not_preservesFiniteLimits⟩

end Stacks.SheafOfModules

end
