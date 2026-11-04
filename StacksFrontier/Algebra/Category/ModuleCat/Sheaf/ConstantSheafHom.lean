module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.SheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafExactness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The constant sheaf on a module of homomorphisms

Let `(C, J)` be a site and `Λ` a commutative ring. For a finitely presented `Λ`-module `M` and an
arbitrary `Λ`-module `N`, Stacks Tag 093T (1) asserts the isomorphism of sheaves of `Λ`-modules
`Hom_Λ(M, N)̲ = SheafHom_{Λ̲}(M̲, N̲)`,
where `-̲` is the constant sheaf and `SheafHom` is the internal hom, whose sections over an object
`X` are the morphisms between the restrictions to the slice site `C/X`. This file constructs that
isomorphism and shows it is the canonical comparison.

The computation of the sections is `Stacks.ConstantSheaf.bijective_homComparison`
(`ConstantSheafExactness.lean`): for `M` finitely presented, `Γ(X, Hom_Λ(M, N)̲)` is
`Hom_Λ(M, Γ(X, N̲))`. What this file adds is everything needed to turn that objectwise statement
into an isomorphism of sheaves, namely the internal hom as a sheaf of modules, the compatibility
of the constant sheaf with restriction to a slice site, and the two naturality statements which
exhibit both sides as presheaves comparable with `X ↦ Hom_Λ(M, Γ(X, N̲))`.

## Main definitions

* `Stacks.ConstantSheaf.overPullbackConstantSheafIso`: the restriction to the slice site `C/X` of
  the constant sheaf on `M` is the constant sheaf on `M` for the localized topology `J.over X`.
  This holds for an arbitrary target category with a sheafification.
* `Stacks.ConstantSheaf.moduleSheafHom`: the internal hom `SheafHom_{Λ̲}(F, G)` of two sheaves of
  `Λ`-modules, as a sheaf of `Λ`-modules.
* `Stacks.ConstantSheaf.moduleSheafHomMap` and `Stacks.ConstantSheaf.moduleSheafHomMapIso`: the
  functoriality of the internal hom, contravariant in the source and covariant in the target, and
  the isomorphism it produces from isomorphisms of the two arguments.
* `Stacks.ConstantSheaf.constantHomPresheaf`: the presheaf `X ↦ Hom_Λ(M, G(X))`, the common target
  of the two comparisons.
* `Stacks.ConstantSheaf.sheafHomEval`: evaluation of a section of the internal hom at the terminal
  object `𝟙 X` of the slice site `C/X`, precomposed with a map out of the constant presheaf on
  `M`. This is the comparison `SheafHom(F, G) ⟶ Hom_Λ(M, G(-))`.
* `Stacks.ConstantSheaf.homComparisonNatTrans`: the comparison `Hom_Λ(M, N)̲ ⟶ Hom_Λ(M, N̲(-))`,
  i.e. `Stacks.ConstantSheaf.homComparison` assembled into a morphism of presheaves.
* `Stacks.ConstantSheaf.constantUnit`: the canonical map from a module to the sections of the
  constant sheaf it generates.

## Main results

* `Stacks.ConstantSheaf.toSheafify_overPullbackConstantSheafIso`: read off at `𝟙 X`, the
  comparison above carries the canonical map `M ⟶ Γ(𝟙 X, M̲_{C/X})` to the canonical map
  `M ⟶ Γ(X, M̲)`.
* `Stacks.ConstantSheaf.bijective_sheafHomEval_app`: evaluation at the identity of the slice is
  bijective when the source is a constant sheaf. This is the constant sheaf adjunction on `C/X`,
  whose terminal object is `𝟙 X`, together with the previous item.
* `Stacks.ConstantSheaf.constantSheafHomIso`: **Stacks Tag 093T (1)**. For `M` finitely presented,
  `Hom_Λ(M, N)̲ ≅ SheafHom_{Λ̲}(M̲, N̲)` as sheaves of `Λ`-modules.
  `Stacks.ConstantSheaf.constantSheafHomIsoOfHom` is the same statement with `Hom_Λ(M, N)`
  represented by the morphism type of `ModuleCat Λ` rather than by an abstract representative.
* `Stacks.ConstantSheaf.constantSheafHomIso_hom_app_apply`: the isomorphism is the *canonical*
  comparison — the section it assigns to the constant section determined by `f : M ⟶ N` is the
  restriction of `f̲` to `C/X`. `constantSheafHomIso_hom_app_id` and
  `constantSheafHomIso_hom_app_comp` are the resulting compatibility with identities and with
  composition.
* `Stacks.ConstantSheaf.hasSheafify_moduleCat`: the sheafification hypothesis used above holds on
  every site, for the module universe `max u v x`. This one, and the `_of_univLE` variants below,
  need only `[Ring Λ]`: sheafification of modules is indifferent to commutativity, and the
  finite type locally constant sheaves of Tag 093U are wanted over a possibly noncommutative
  ring.
* `Stacks.ConstantSheaf.hasSheafify_moduleCat_of_univLE`,
  `Stacks.ConstantSheaf.hasWeakSheafify_addCommGrp_of_univLE`,
  `Stacks.ConstantSheaf.preservesSheafification_forget_moduleCat_of_univLE` and
  `Stacks.ConstantSheaf.hasSheafify_over_moduleCat_of_univLE`: the same
  sheafification data under the weaker hypothesis `UnivLE.{max u v, x}`, which is what a
  statement whose module universe is a free variable can assume. The last one is what lets the
  main results be instantiated at a module universe not written as `max u v x`; see the
  implementation notes.

## Implementation notes

**What was missing from Mathlib.** The compatibility of `constantSheaf` with pullback is an
explicit `TODO` in `Mathlib/CategoryTheory/Sites/ConstantSheaf.lean`, which proves only the
compatibility with the equivalence of sheaf categories induced by a dense subsite. The case
needed here, restriction along `Over.forget X`, is immediate once one notices that `Over.forget X`
is both continuous and cocontinuous for `J.over X` and `J`, so that
`Functor.pushforwardContinuousSheafificationCompatibility` applies, and that restricting the
constant presheaf along `(Over.forget X).op` gives the constant presheaf *definitionally*. That is
`overPullbackConstantSheafIso`, and it is stated for a general target category because nothing
about modules enters.

**Why the proof goes through a third presheaf.** The two sides of Tag 093T (1) are compared
objectwise by two different mechanisms — `bijective_homComparison` on the left, the constant sheaf
adjunction on the slice site on the right — and neither comparison is directly a map to the other
side. Both are, however, maps to the presheaf `constantHomPresheaf`, and both are natural, so the
isomorphism is obtained as `homComparisonNatTrans ≫ (sheafHomEval)⁻¹` and then transported along
the fully faithful `sheafToPresheaf`. The sheaf condition on `constantHomPresheaf` is never
needed, so it is not proved: it is only used as a comparison object.

**Universes.** `moduleSheafHom` raises the module universe: the sections of the internal hom over
`X` are natural transformations indexed by `(Over X)ᵒᵖ`, which lives in `Type (max u v)`, so the
internal hom of two sheaves valued in `ModuleCat.{x} Λ` is valued in `ModuleCat.{max u v x} Λ`.
Consequently the tagged statement can only be an isomorphism of sheaves when the module universe
already absorbs `max u v`, and the main results are therefore stated for modules in
`ModuleCat.{max u v x} Λ`. This is forced by the shape of the statement, not chosen: there is no
isomorphism to state at a smaller module universe. The universes of the site (`u`, `v`), of the
ring (`w`) and of the modules (`x`) are otherwise independent.

**The sheafification hypotheses.** The main results take `HasSheafify J (ModuleCat.{max u v x} Λ)`
and `HasWeakSheafify (J.over Y) (ModuleCat.{max u v x} Λ)` as hypotheses, matching the companion
files `ConstantSheafModules.lean` and `ConstantSheafExactness.lean`, and the final section proves
both are automatic at this universe: `hasSheafify_moduleCat`. As the implementation notes of
`ConstantSheafModules.lean` record, these are *derivable* but not found by `infer_instance`,
because Mathlib's generic instance additionally wants
`PreservesColimitsOfShape (J.Cover Y)ᵒᵖ (forget (ModuleCat.{max u v x} Λ))`, whose only route is
the size shrink `preservesFilteredColimitsOfSize_of_univLE` — a lemma, not an instance. That step
is isolated as `preservesColimitsOfShape_forget_addCommGrp`. Both classes are propositions, so
registering them as instances carries no risk of incompatible data.

The `_of_univLE` variants replace the module universe `max u v x` by the inequality
`UnivLE.{max u v, x}`, which is what a statement with a free module universe can carry as a
hypothesis; `max u v x` satisfies it. Mathlib states the two further ingredients they need —
`preservesFilteredColimitsOfSize_of_univLE` and `ModuleCat.hasLimitsOfSize` — as lemmas rather
than instances, and the `PreservesSheafification` instance has to be applied by name because
instance search for it exhausts its heartbeat budget.

**Instantiating the main results at a module universe presented otherwise.** The module universe
`max u v x` is the general one — any universe dominating `max u v` is of that form — but `x` is
not *inferred*: a consumer whose module universe reads, say, `max (u' + 1) r w` over a site in
`Type (u' + 1)` with `Category.{u'}` must pin it, as `constantSheafHomIsoOfHom.{u' + 1, u', r,
max r w}`, since `max u v ?x =?= max (u' + 1) r w` is a universe constraint Lean leaves stuck.
With `x` pinned, `HasSheafify J (ModuleCat.{max (u' + 1) r w} Λ)` is then found by instance
search through `hasSheafify_moduleCat_of_univLE`, whose module universe is the bare variable
`x` and so matches any presentation. The slice hypothesis is the one that has to be supplied by
hand, as `haveI := hasSheafify_over_moduleCat_of_univLE.{_, _, _, max (u' + 1) r w} J Λ Y`: the
only instance for it is the `max u v x`-shaped `hasSheafify_over_moduleCat`, unmatchable for the
reason just given, and `hasSheafify_over_moduleCat_of_univLE` cannot be made an instance without
breaking the `max u v x`-shaped slice goals of `CategoryTheory/Sites/LocallyConstant/` — see its
docstring.

**Only part (1) is proved here.** Part (3), the statement that the internal hom of two locally
constant sheaves is locally constant, is proved in `LocallyConstantSheafHom.lean` from part (1)
and the functoriality added here. Parts (2) and (4), the corresponding statements for `Isom`
rather than `Hom`, are proved in `ConstantSheafIsom.lean` from the subsheaf of invertible sections
built in `ModuleSheafIsom.lean` and the comparison of part (1) established here.

## References

* [Stacks Project, Tag 093T](https://stacks.math.columbia.edu/tag/093T)
* [Stacks Project, Tag 093J](https://stacks.math.columbia.edu/tag/093J)
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v w x

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-! ### The unit of the constant-sheaf adjunction -/

section Adj

variable (A : Type*) [Category A] [HasWeakSheafify J A]

/-- The unit of the constant sheaf adjunction is the canonical map to the sheafification of the
constant presheaf, read off at the terminal object. -/
theorem constantSheafAdj_unit_app {T : C} (hT : IsTerminal T) (M : A) :
    (constantSheafAdj J A hT).unit.app M =
      (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op T) := by
  simp only [constantSheafAdj, Adjunction.comp_unit_app, constantPresheafAdj, Functor.comp_obj,
    Functor.constCompEvaluationObj, NatIso.ofComponents_hom_app, Iso.refl_hom]
  exact Category.id_comp _

/-- The bijection of the constant sheaf adjunction: a morphism out of a constant sheaf is read
off at the terminal object, after the canonical map from the value of the constant presheaf. -/
theorem constantSheafAdj_homEquiv_apply {T : C} (hT : IsTerminal T) (M : A) (S : Sheaf J A)
    (φ : (constantSheaf J A).obj M ⟶ S) :
    (constantSheafAdj J A hT).homEquiv M S φ =
      (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op T) ≫ φ.hom.app (op T) := by
  rw [Adjunction.homEquiv_unit, constantSheafAdj_unit_app]
  rfl

/-- The canonical map from a module to the sections of the constant sheaf it generates is natural
in the module. -/
theorem toSheafify_const_naturality_app {M N : A} (f : M ⟶ N) (X : Cᵒᵖ) :
    f ≫ (toSheafify J ((Functor.const Cᵒᵖ).obj N)).app X =
      (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app X ≫
        ((constantSheaf J A).map f).hom.app X :=
  congrArg (fun α => NatTrans.app α X)
    (toSheafify_naturality J ((Functor.const Cᵒᵖ).map f))

end Adj

/-! ### The constant sheaf is compatible with restriction to a slice site -/

section OverPullback

variable (A : Type*) [Category A] [HasWeakSheafify J A]

/-- Restricting the constant presheaf to a slice category gives the constant presheaf. -/
theorem const_comp_whiskeringLeft_overForget (X : C) :
    Functor.const Cᵒᵖ ⋙ (Functor.whiskeringLeft (Over X)ᵒᵖ Cᵒᵖ A).obj (Over.forget X).op =
      Functor.const (Over X)ᵒᵖ :=
  rfl

/-- **The constant sheaf commutes with restriction to a slice site.** For an object `X` of the
site, the restriction to `C/X` of the constant sheaf on `M` is the constant sheaf on `M` for the
localized topology `J.over X`.

This is absent from Mathlib: `Mathlib/CategoryTheory/Sites/ConstantSheaf.lean` records the
compatibility of `constantSheaf` with an equivalence of sheaf categories induced by a dense
subsite and leaves the compatibility with pullback as a `TODO`. The construction is immediate
from the compatibility of sheafification with restriction along a functor that is both
continuous and cocontinuous, which `Over.forget X` is. -/
noncomputable def overPullbackConstantSheafIso (X : C) [HasWeakSheafify (J.over X) A]
    [∀ (F : (Over X)ᵒᵖ ⥤ A), (Over.forget X).op.HasPointwiseRightKanExtension F] :
    constantSheaf (J.over X) A ≅ constantSheaf J A ⋙ J.overPullback A X :=
  Functor.isoWhiskerLeft (Functor.const Cᵒᵖ)
    ((Over.forget X).pushforwardContinuousSheafificationCompatibility A (J.over X) J)

/-- The comparison of the previous definition carries the canonical map out of the constant
presheaf on the slice site to the canonical map out of the constant presheaf on the site: read
off at the terminal object `𝟙 X` of `C/X`, it is the canonical map `M ⟶ Γ(X, M̲)`. -/
theorem toSheafify_overPullbackConstantSheafIso (X : C) [HasWeakSheafify (J.over X) A]
    [∀ (F : (Over X)ᵒᵖ ⥤ A), (Over.forget X).op.HasPointwiseRightKanExtension F] (M : A) :
    (toSheafify (J.over X) ((Functor.const (Over X)ᵒᵖ).obj M)).app (op (Over.mk (𝟙 X))) ≫
        ((overPullbackConstantSheafIso J A X).hom.app M).hom.app (op (Over.mk (𝟙 X))) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op X) := by
  have h := congrArg (fun α => NatTrans.app α (op (Over.mk (𝟙 X))))
    ((Over.forget X).toSheafify_pullbackSheafificationCompatibility A (J.over X) J
      ((Functor.const Cᵒᵖ).obj M))
  exact h

end OverPullback

/-! ### The internal hom of two sheaves of modules -/

section ModuleSheafHom

variable (Λ : Type w) [CommRing Λ]

/-- The internal hom of two sheaves of `Λ`-modules, as a sheaf of `Λ`-modules: its sections over
`X` are the morphisms between the restrictions of the two sheaves to the slice site `C/X`, with
the pointwise `Λ`-module structure. -/
def moduleSheafHom (F G : Sheaf J (ModuleCat.{x} Λ)) : Sheaf J (ModuleCat.{max u v x} Λ) where
  obj :=
    { obj := fun X => ModuleCat.of Λ
        ((J.overPullback (ModuleCat.{x} Λ) X.unop).obj F ⟶
          (J.overPullback (ModuleCat.{x} Λ) X.unop).obj G)
      map := fun f => ModuleCat.ofHom
        { toFun := (J.overMapPullback (ModuleCat.{x} Λ) f.unop).map
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      map_id X := ModuleCat.hom_ext <| LinearMap.ext fun a =>
        ConcreteCategory.congr_hom ((sheafHom F G).obj.map_id X) a
      map_comp f g := ModuleCat.hom_ext <| LinearMap.ext fun a =>
        ConcreteCategory.congr_hom ((sheafHom F G).obj.map_comp f g) a }
  property := Presheaf.isSheaf_of_isSheaf_comp J _
    (forget₂ (ModuleCat.{max u v x} Λ) AddCommGrpCat.{max u v x})
    (Presheaf.isSheaf_of_isSheaf_comp J _ (forget AddCommGrpCat.{max u v x})
      (sheafHom F G).property)

/-- The restriction map of the internal hom along `f : X ⟶ Y` sends a morphism on the slice
site over `X` to its pullback along the induced functor between slice sites. -/
theorem moduleSheafHom_obj_map_apply (F G : Sheaf J (ModuleCat.{x} Λ)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (α : (moduleSheafHom J Λ F G).obj.obj X) :
    (moduleSheafHom J Λ F G).obj.map f α = (J.overMapPullback (ModuleCat.{x} Λ) f.unop).map α :=
  rfl

/-- The internal hom is contravariantly functorial in its source and covariantly functorial in
its target: a section `α` over `X` is carried to the composite with the restrictions to `C/X` of
the two given morphisms. -/
def moduleSheafHomMap {F F' G G' : Sheaf J (ModuleCat.{x} Λ)} (u : F' ⟶ F) (w : G ⟶ G') :
    moduleSheafHom J Λ F G ⟶ moduleSheafHom J Λ F' G' :=
  ⟨{ app := fun X => ModuleCat.ofHom
       { toFun := fun α => (J.overPullback (ModuleCat.{x} Λ) X.unop).map u ≫ α ≫
           (J.overPullback (ModuleCat.{x} Λ) X.unop).map w
         map_add' := fun _ _ => by
           simp only [Preadditive.comp_add, Preadditive.add_comp]
         map_smul' := fun _ _ => by
           simp only [Linear.comp_smul, Linear.smul_comp, RingHom.id_apply] }
     naturality := fun {X Y} f => by
       apply ModuleCat.hom_ext
       apply LinearMap.ext
       intro α
       apply Sheaf.hom_ext
       apply NatTrans.ext
       rfl }⟩

/-- The component of `moduleSheafHomMap J Λ u w` at `X` sends a section `α` to the composite of
`α` with the restrictions of `u` and `w` to the slice site over `X`. -/
@[simp]
theorem moduleSheafHomMap_app_apply {F F' G G' : Sheaf J (ModuleCat.{x} Λ)} (u : F' ⟶ F)
    (w : G ⟶ G') (X : Cᵒᵖ) (α : (moduleSheafHom J Λ F G).obj.obj X) :
    (moduleSheafHomMap J Λ u w).hom.app X α =
      (J.overPullback (ModuleCat.{x} Λ) X.unop).map u ≫ α ≫
        (J.overPullback (ModuleCat.{x} Λ) X.unop).map w :=
  rfl

/-- Conjugating a local morphism by the restrictions of two isomorphisms and then by the
restrictions of their inverses changes nothing. -/
theorem map_hom_comp_map_inv_conj {F F' G G' : Sheaf J (ModuleCat.{x} Λ)} (eF : F ≅ F')
    (eG : G ≅ G') (Y : C)
    (a : (J.overPullback (ModuleCat.{x} Λ) Y).obj F ⟶
      (J.overPullback (ModuleCat.{x} Λ) Y).obj G) :
    (J.overPullback (ModuleCat.{x} Λ) Y).map eF.hom ≫
        ((J.overPullback (ModuleCat.{x} Λ) Y).map eF.inv ≫ a ≫
          (J.overPullback (ModuleCat.{x} Λ) Y).map eG.hom) ≫
        (J.overPullback (ModuleCat.{x} Λ) Y).map eG.inv = a := by
  simp only [Category.assoc]
  rw [← Category.assoc ((J.overPullback (ModuleCat.{x} Λ) Y).map eF.hom),
    ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]

/-- **The internal hom transported along isomorphisms of its two arguments.** -/
def moduleSheafHomMapIso {F F' G G' : Sheaf J (ModuleCat.{x} Λ)} (eF : F ≅ F') (eG : G ≅ G') :
    moduleSheafHom J Λ F G ≅ moduleSheafHom J Λ F' G' where
  hom := moduleSheafHomMap J Λ eF.inv eG.hom
  inv := moduleSheafHomMap J Λ eF.hom eG.inv
  hom_inv_id := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    exact map_hom_comp_map_inv_conj J Λ eF eG X.unop α
  inv_hom_id := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    exact map_hom_comp_map_inv_conj J Λ eF.symm eG.symm X.unop α

end ModuleSheafHom

/-! ### Reading a section of the internal hom out of a constant sheaf on the generators -/

section Eval

variable (Λ : Type w) [CommRing Λ]

/-- The presheaf of homomorphisms out of a fixed module into the sections of a sheaf:
`X ↦ Hom_Λ(M, G(X))`, with the restriction maps given by postcomposition. This is the presheaf
that both sides of Tag 093T (1) are compared with. -/
def constantHomPresheaf (M : ModuleCat.{max u v x} Λ)
    (G : Sheaf J (ModuleCat.{max u v x} Λ)) : Cᵒᵖ ⥤ ModuleCat.{max u v x} Λ where
  obj X := ModuleCat.of Λ
    ((M : Type (max u v x)) →ₗ[Λ] (G.obj.obj X : Type (max u v x)))
  map f := ModuleCat.ofHom (LinearMap.llcomp Λ _ _ _ (G.obj.map f).hom)
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro a
    simp [G.obj.map_id X]
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro a
    simp [G.obj.map_comp f g]

/-- **Evaluation at the identity of the slice.** A section of the internal hom
`SheafHom(F, G)` over `X` is a morphism `F|_X ⟶ G|_X` on the slice site `C/X`; its component at
the terminal object `𝟙 X` of `C/X` is a map `F(X) ⟶ G(X)`, which may be precomposed with a
morphism `η` out of the constant presheaf on `M`. This is the comparison
`SheafHom(F, G) ⟶ Hom_Λ(M, G(-))`, and it is natural because of the naturality of `η` and of the
components of the sections. -/
def sheafHomEval (M : ModuleCat.{max u v x} Λ) {F G : Sheaf J (ModuleCat.{max u v x} Λ)}
    (η : (Functor.const Cᵒᵖ).obj M ⟶ F.obj) :
    (moduleSheafHom J Λ F G).obj ⟶ constantHomPresheaf J Λ M G where
  app X := ModuleCat.ofHom
    { toFun := fun α => (η.app X ≫ α.hom.app (op (Over.mk (𝟙 X.unop)))).hom
      map_add' := fun _ _ => LinearMap.ext fun _ => rfl
      map_smul' := fun _ _ => LinearMap.ext fun _ => rfl }
  naturality {X Y} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    apply LinearMap.ext
    intro a
    have hα : F.obj.map f ≫ α.hom.app (op (Over.mk f.unop)) =
        α.hom.app (op (Over.mk (𝟙 X.unop))) ≫ G.obj.map f :=
      α.hom.naturality (Over.homMk f.unop : Over.mk f.unop ⟶ Over.mk (𝟙 X.unop)).op
    have hη : η.app X ≫ F.obj.map f = η.app Y :=
      ((η.naturality f).symm).trans (Category.id_comp _)
    have key : ((moduleSheafHom J Λ F G).obj.map f α).hom.app (op (Over.mk (𝟙 Y.unop))) =
        α.hom.app (op (Over.mk f.unop)) := by
      rw [moduleSheafHom_obj_map_apply]
      exact CategoryTheory.presheafHom_map_app (𝟙 Y.unop) f.unop f.unop
        (Category.id_comp _) α.hom
    have main : η.app Y ≫
          ((moduleSheafHom J Λ F G).obj.map f α).hom.app (op (Over.mk (𝟙 Y.unop))) =
        η.app X ≫ α.hom.app (op (Over.mk (𝟙 X.unop))) ≫ G.obj.map f := by
      rw [key]
      exact (congrArg (fun t => t ≫ α.hom.app (op (Over.mk f.unop))) hη.symm).trans
        ((Category.assoc _ _ _).trans (congrArg (fun t => η.app X ≫ t) hα))
    exact ConcreteCategory.congr_hom main a

end Eval

/-! ### Evaluation at the identity is bijective on a constant source -/

section Bijective

variable (Λ : Type w) [CommRing Λ]

/-- The canonical map out of the constant presheaf on `M`, for the constant sheaf on `M`. -/
noncomputable abbrev constantUnit [HasWeakSheafify J (ModuleCat.{max u v x} Λ)]
    (M : ModuleCat.{max u v x} Λ) :
    (Functor.const Cᵒᵖ).obj M ⟶ ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj M).obj :=
  toSheafify J ((Functor.const Cᵒᵖ).obj M)

/-- **Evaluation at the identity of the slice is bijective when the source is a constant sheaf.**
By the compatibility of the constant sheaf with restriction to the slice site `C/X`, the
restriction of `M̲` to `C/X` is the constant sheaf on `M` there; the terminal object of `C/X` is
`𝟙 X`, so the constant sheaf adjunction identifies `Hom_{C/X}(M̲|_X, G|_X)` with
`Hom_Λ(M, G(X))`, and that identification is exactly `sheafHomEval`. -/
theorem bijective_sheafHomEval_app [HasWeakSheafify J (ModuleCat.{max u v x} Λ)]
    [∀ Y : C, HasWeakSheafify (J.over Y) (ModuleCat.{max u v x} Λ)]
    (M : ModuleCat.{max u v x} Λ) (G : Sheaf J (ModuleCat.{max u v x} Λ)) (X : Cᵒᵖ) :
    Function.Bijective
      (((sheafHomEval J Λ M (G := G) (constantUnit J Λ M)).app X).hom) := by
  set K := J.over X.unop with hK
  set ι := (overPullbackConstantSheafIso J (ModuleCat.{max u v x} Λ) X.unop).app M with hι
  set S := (J.overPullback (ModuleCat.{max u v x} Λ) X.unop).obj G with hS
  -- the two bijections: precomposition with `ι` and the constant sheaf adjunction on `C/X`
  let e : ((J.overPullback (ModuleCat.{max u v x} Λ) X.unop).obj
        ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj M) ⟶ S) ≃
      ((M : Type (max u v x)) →ₗ[Λ] (G.obj.obj X : Type (max u v x))) :=
    (ι.symm.homCongr (Iso.refl S)).trans
      (((constantSheafAdj K (ModuleCat.{max u v x} Λ) Over.mkIdTerminal).homEquiv M S).trans
        (ModuleCat.homLinearEquiv (S := Λ)).toEquiv)
  have hfun : ∀ α, ((sheafHomEval J Λ M (G := G) (constantUnit J Λ M)).app X).hom α = e α := by
    intro α
    have hadj := constantSheafAdj_homEquiv_apply K (ModuleCat.{max u v x} Λ)
      (Over.mkIdTerminal (X := X.unop)) M S (ι.hom ≫ α)
    have hcompat := toSheafify_overPullbackConstantSheafIso J (ModuleCat.{max u v x} Λ) X.unop M
    have hstep : (toSheafify K ((Functor.const (Over X.unop)ᵒᵖ).obj M)).app
          (op (Over.mk (𝟙 X.unop))) ≫ (ι.hom ≫ α).hom.app (op (Over.mk (𝟙 X.unop))) =
        (constantUnit J Λ M).app X ≫ α.hom.app (op (Over.mk (𝟙 X.unop))) :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun t => t ≫ α.hom.app (op (Over.mk (𝟙 X.unop)))) hcompat)
    have hid : ι.hom ≫ α ≫ 𝟙 S = ι.hom ≫ α :=
      congrArg (fun t => ι.hom ≫ t) (Category.comp_id α)
    have hmain : (constantSheafAdj K (ModuleCat.{max u v x} Λ) Over.mkIdTerminal).homEquiv M S
          (ι.hom ≫ α ≫ 𝟙 S) =
        (constantUnit J Λ M).app X ≫ α.hom.app (op (Over.mk (𝟙 X.unop))) :=
      (congrArg ((constantSheafAdj K (ModuleCat.{max u v x} Λ) Over.mkIdTerminal).homEquiv M S)
        hid).trans (hadj.trans hstep)
    exact (congrArg ModuleCat.Hom.hom hmain).symm
  exact (funext hfun ▸ e.bijective :
    Function.Bijective ((ModuleCat.Hom.hom
      ((sheafHomEval J Λ M (G := G) (constantUnit J Λ M)).app X) : _ → _)))

end Bijective

/-! ### The comparison of Tag 093T (1) -/

section Comparison

variable (Λ : Type w) [CommRing Λ]

/-- The comparison of `Stacks.ConstantSheaf.homComparison`, assembled into a morphism of
presheaves `E̲ ⟶ Hom_Λ(M, N̲(-))`. Its naturality is the naturality of the morphism of constant
sheaves induced by evaluation at an element of `M`. -/
noncomputable def homComparisonNatTrans [HasWeakSheafify J (ModuleCat.{max u v x} Λ)]
    (M N E : ModuleCat.{max u v x} Λ)
    (e : ((M : Type (max u v x)) →ₗ[Λ] (N : Type (max u v x))) ≃ₗ[Λ] E) :
    ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj E).obj ⟶
      constantHomPresheaf J Λ M ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj N) where
  app X := ModuleCat.ofHom (homComparison J M N E e X.unop).1
  naturality {X Y} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply LinearMap.ext
    intro m
    have hX := (homComparison J M N E e X.unop).2 s m
    have hY := (homComparison J M N E e Y.unop).2
      ((((constantSheaf J (ModuleCat.{max u v x} Λ)).obj E).obj.map f).hom s) m
    have hnat := ConcreteCategory.congr_hom
      (((constantSheaf J (ModuleCat.{max u v x} Λ)).map (ModuleCat.ofHom
        (LinearMap.lcomp Λ (N : Type (max u v x)) e.symm.toLinearMap
          (evalHom (M : Type (max u v x)) (N : Type (max u v x)) m)))).hom.naturality f) s
    exact hY.trans (hnat.trans (congrArg (((constantSheaf J
      (ModuleCat.{max u v x} Λ)).obj N).obj.map f).hom hX.symm))

section Main

variable (Λ : Type w) [CommRing Λ]
variable [HasSheafify J (ModuleCat.{max u v x} Λ)]
  [∀ Y : C, HasWeakSheafify (J.over Y) (ModuleCat.{max u v x} Λ)]
variable (M N E : ModuleCat.{max u v x} Λ)
  (e : ((M : Type (max u v x)) →ₗ[Λ] (N : Type (max u v x))) ≃ₗ[Λ] E)

/-- For a finitely presented `Λ`-module `M`, the comparison `E̲ ⟶ Hom_Λ(M, N̲(-))` is an
isomorphism of presheaves. -/
instance isIso_homComparisonNatTrans
    [Module.FinitePresentation Λ (M : Type (max u v x))] :
    IsIso (homComparisonNatTrans J Λ M N E e) := by
  have : ∀ X : Cᵒᵖ, IsIso ((homComparisonNatTrans J Λ M N E e).app X) := by
    intro X
    rw [ConcreteCategory.isIso_iff_bijective]
    exact bijective_homComparison J M N E e X.unop
  exact NatIso.isIso_of_isIso_app _

/-- Evaluation at the identity of the slice, precomposed with the canonical map out of the
constant presheaf on `M`, is an isomorphism `SheafHom(M̲, N̲) ⟶ Hom_Λ(M, N̲(-))`. -/
instance isIso_sheafHomEval_constantUnit :
    IsIso (sheafHomEval J Λ M
      (G := (constantSheaf J (ModuleCat.{max u v x} Λ)).obj N) (constantUnit J Λ M)) := by
  have : ∀ X : Cᵒᵖ, IsIso ((sheafHomEval J Λ M
      (G := (constantSheaf J (ModuleCat.{max u v x} Λ)).obj N) (constantUnit J Λ M)).app X) := by
    intro X
    rw [ConcreteCategory.isIso_iff_bijective]
    exact bijective_sheafHomEval_app J Λ M _ X
  exact NatIso.isIso_of_isIso_app _

/-- **Stacks Project, Tag 093T (1).** For a finitely presented `Λ`-module `M` and any
`Λ`-module `N`, the constant sheaf on `Hom_Λ(M, N)` is the internal hom of the constant sheaves
on `M` and on `N`:
`Hom_Λ(M, N)̲ ≅ SheafHom_{Λ̲}(M̲, N̲)`,
as sheaves of `Λ`-modules. The module `E` is any representative of `Hom_Λ(M, N)`, supplied with
the identification `e`. -/
@[stacks 093T "constant_hom"]
noncomputable def constantSheafHomIso
    [Module.FinitePresentation Λ (M : Type (max u v x))] :
    (constantSheaf J (ModuleCat.{max u v x} Λ)).obj E ≅
      moduleSheafHom J Λ ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj M)
        ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj N) :=
  (fullyFaithfulSheafToPresheaf J (ModuleCat.{max u v x} Λ)).preimageIso
    (asIso (homComparisonNatTrans J Λ M N E e) ≪≫
      (asIso (sheafHomEval J Λ M
        (G := (constantSheaf J (ModuleCat.{max u v x} Λ)).obj N) (constantUnit J Λ M))).symm)

/-- **Stacks Project, Tag 093T (1), the comparison is the canonical one.** The section of the
internal hom over `X` which the isomorphism assigns to the constant section determined by a
homomorphism `f : M ⟶ N` is the restriction to the slice site `C/X` of the morphism of constant
sheaves induced by `f`. -/
@[stacks 093T "constant_hom", sga "3 VIII 1.4" "partial"]
theorem constantSheafHomIso_hom_app_apply
    [Module.FinitePresentation Λ (M : Type (max u v x))] (X : Cᵒᵖ) (f : M ⟶ N) :
    ((constantSheafHomIso J Λ M N E e).hom.hom.app X).hom
        (((constantUnit J Λ E).app X).hom (e (ModuleCat.homLinearEquiv (S := Λ) f))) =
      (J.overPullback (ModuleCat.{max u v x} Λ) X.unop).map
        ((constantSheaf J (ModuleCat.{max u v x} Λ)).map f) := by
  set Ξ := sheafHomEval J Λ M
    (G := (constantSheaf J (ModuleCat.{max u v x} Λ)).obj N) (constantUnit J Λ M) with hΞ
  set Ψ := homComparisonNatTrans J Λ M N E e with hΨ
  set z := ((constantUnit J Λ E).app X).hom (e (ModuleCat.homLinearEquiv (S := Λ) f)) with hz
  have hA : (constantSheafHomIso J Λ M N E e).hom.hom ≫ Ξ = Ψ := by
    have h0 : (constantSheafHomIso J Λ M N E e).hom.hom = Ψ ≫ inv Ξ := rfl
    rw [h0, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hA2 := ConcreteCategory.congr_hom (NatTrans.congr_app hA X) z
  refine (bijective_sheafHomEval_app J Λ M
    ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj N) X).injective ?_
  -- both sides, read through their definitions
  have hL : (ConcreteCategory.hom (Ψ.app X)) z = (homComparison J M N E e X.unop).1 z := rfl
  have hR : (ConcreteCategory.hom (Ξ.app X))
        ((J.overPullback (ModuleCat.{max u v x} Λ) X.unop).map
          ((constantSheaf J (ModuleCat.{max u v x} Λ)).map f)) =
      ((constantUnit J Λ M).app X ≫
        ((constantSheaf J (ModuleCat.{max u v x} Λ)).map f).hom.app X).hom := rfl
  refine hA2.trans (Eq.trans (hL.trans ?_) hR.symm)
  apply LinearMap.ext
  intro m
  -- the left hand side: the characterizing formula for `homComparison`, then naturality
  have hLnat := ConcreteCategory.congr_hom
    (toSheafify_const_naturality_app J (ModuleCat.{max u v x} Λ)
      (ModuleCat.ofHom (LinearMap.lcomp Λ (N : Type (max u v x)) e.symm.toLinearMap
        (evalHom (M : Type (max u v x)) (N : Type (max u v x)) m))) X)
    (e (ModuleCat.homLinearEquiv (S := Λ) f))
  have hψval : (e.symm (e (ModuleCat.homLinearEquiv (S := Λ) f))) m = f.hom m := by
    rw [e.symm_apply_apply]
    rfl
  -- the right hand side: naturality of the canonical map at `f`
  have hRnat := ConcreteCategory.congr_hom
    (toSheafify_const_naturality_app J (ModuleCat.{max u v x} Λ) f X) m
  refine ((homComparison J M N E e X.unop).2 z m).trans (hLnat.symm.trans ?_)
  exact (congrArg (fun t => (((constantUnit J Λ N).app X).hom) t) hψval).trans hRnat

/-- **Stacks Project, Tag 093T (1)**, applied to the identity: the comparison sends the constant
section given by `𝟙 M` to the identity on every slice. -/
@[stacks 093T "constant_hom"]
theorem constantSheafHomIso_hom_app_id
    [Module.FinitePresentation Λ (M : Type (max u v x))] (E' : ModuleCat.{max u v x} Λ)
    (e' : ((M : Type (max u v x)) →ₗ[Λ] (M : Type (max u v x))) ≃ₗ[Λ] E') (X : Cᵒᵖ) :
    ((constantSheafHomIso J Λ M M E' e').hom.hom.app X).hom
        (((constantUnit J Λ E').app X).hom (e' (ModuleCat.homLinearEquiv (S := Λ) (𝟙 M)))) =
      𝟙 ((J.overPullback (ModuleCat.{max u v x} Λ) X.unop).obj
        ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj M)) := by
  rw [constantSheafHomIso_hom_app_apply, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]

/-- **Stacks Project, Tag 093T (1)**, applied to a composition: the comparison respects
composition of constant homomorphisms on every slice. -/
@[stacks 093T "constant_hom"]
theorem constantSheafHomIso_hom_app_comp
    [Module.FinitePresentation Λ (M : Type (max u v x))]
    [Module.FinitePresentation Λ (N : Type (max u v x))] (P : ModuleCat.{max u v x} Λ)
    (E₁ E₂ : ModuleCat.{max u v x} Λ)
    (e₁ : ((N : Type (max u v x)) →ₗ[Λ] (P : Type (max u v x))) ≃ₗ[Λ] E₁)
    (e₂ : ((M : Type (max u v x)) →ₗ[Λ] (P : Type (max u v x))) ≃ₗ[Λ] E₂)
    (X : Cᵒᵖ) (f : M ⟶ N) (g : N ⟶ P) :
    ((constantSheafHomIso J Λ M P E₂ e₂).hom.hom.app X).hom
        (((constantUnit J Λ E₂).app X).hom
          (e₂ (ModuleCat.homLinearEquiv (S := Λ) (f ≫ g)))) =
      ((constantSheafHomIso J Λ M N E e).hom.hom.app X).hom
          (((constantUnit J Λ E).app X).hom (e (ModuleCat.homLinearEquiv (S := Λ) f))) ≫
        ((constantSheafHomIso J Λ N P E₁ e₁).hom.hom.app X).hom
          (((constantUnit J Λ E₁).app X).hom
            (e₁ (ModuleCat.homLinearEquiv (S := Λ) g))) := by
  rw [constantSheafHomIso_hom_app_apply, constantSheafHomIso_hom_app_apply,
    constantSheafHomIso_hom_app_apply, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp]

end Main

/-! ### The form in which the module of homomorphisms is the `Hom` type itself -/

section Hom

variable (Λ : Type w) [CommRing Λ]
variable [HasSheafify J (ModuleCat.{max u v x} Λ)]
  [∀ Y : C, HasWeakSheafify (J.over Y) (ModuleCat.{max u v x} Λ)]

/-- **Stacks Project, Tag 093T (1)**, with `Hom_Λ(M, N)` represented by the morphism type of the
category of `Λ`-modules rather than by an abstract representative. -/
@[stacks 093T "constant_hom"]
noncomputable def constantSheafHomIsoOfHom (M N : ModuleCat.{max u v x} Λ)
    [Module.FinitePresentation Λ (M : Type (max u v x))] :
    (constantSheaf J (ModuleCat.{max u v x} Λ)).obj (ModuleCat.of Λ (M ⟶ N)) ≅
      moduleSheafHom J Λ ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj M)
        ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj N) :=
  constantSheafHomIso J Λ M N (ModuleCat.of Λ (M ⟶ N))
    (ModuleCat.homLinearEquiv (S := Λ)).symm

end Hom

/-! ### The sheafification hypotheses are dischargeable -/

section Instances

variable (Λ : Type w) [Ring Λ]

/-- The size shrink that makes the forgetful functor of abelian groups commute with the filtered
colimits over the covers of a site. This is `preservesFilteredColimitsOfSize_of_univLE`, which is
a lemma rather than an instance; supplying it is what makes sheafification of presheaves of
modules available. -/
theorem preservesColimitsOfShape_forget_addCommGrp (Y : C) :
    Limits.PreservesColimitsOfShape (J.Cover Y)ᵒᵖ (forget AddCommGrpCat.{max u v x}) := by
  have : Limits.PreservesFilteredColimitsOfSize.{max u v, max u v}
      (forget AddCommGrpCat.{max u v x}) :=
    Limits.preservesFilteredColimitsOfSize_of_univLE.{max u v x, max u v x, max u v, max u v} _
  infer_instance

/-- Sheafification of presheaves of `Λ`-modules in a universe containing the site is available on
every site, together with its left exactness. -/
instance hasSheafify_moduleCat : HasSheafify J (ModuleCat.{max u v x} Λ) := by
  have h : ∀ Y : C, Limits.PreservesColimitsOfShape (J.Cover Y)ᵒᵖ
      (forget (ModuleCat.{max u v x} Λ)) := by
    intro Y
    have := preservesColimitsOfShape_forget_addCommGrp.{u, v, x} J Y
    exact Limits.comp_preservesColimitsOfShape
      (forget₂ (ModuleCat.{max u v x} Λ) AddCommGrpCat.{max u v x})
      (forget AddCommGrpCat.{max u v x})
  infer_instance

/-- The same for the localized topology on a slice site. -/
instance hasSheafify_over_moduleCat (Y : C) :
    HasSheafify (J.over Y) (ModuleCat.{max u v x} Λ) :=
  hasSheafify_moduleCat.{max u v, v, w, x} (J.over Y) Λ

end Instances

/-! ### The same hypotheses under a universe inequality

The section above is stated at the section universe `max u v x`, which is the shape that
instance search can match when the module universe is built from the site universes. The
same arguments run whenever the section universe merely *dominates* the site universes,
which is the form a universe-polymorphic statement needs: `UnivLE.{max u v, x}` is implied
by `x = max u v x'` but is also available as a hypothesis on its own.
-/

section UnivLEInstances

variable [UnivLE.{max u v, x}]

/-- The forgetful functor of abelian groups commutes with the colimits over the covers of a
site as soon as the section universe dominates the site universes. This generalizes
`preservesColimitsOfShape_forget_addCommGrp` from `max u v x` to the inequality. -/
theorem preservesColimitsOfShape_forget_addCommGrp_of_univLE (Y : C) :
    Limits.PreservesColimitsOfShape (J.Cover Y)ᵒᵖ (forget AddCommGrpCat.{x}) := by
  have : Limits.PreservesFilteredColimitsOfSize.{max u v, max u v} (forget AddCommGrpCat.{x}) :=
    Limits.preservesFilteredColimitsOfSize_of_univLE.{x, x, max u v, max u v} _
  infer_instance

/-- Weak sheafification of presheaves of abelian groups is available on every site whose
universes the section universe dominates. -/
instance hasWeakSheafify_addCommGrp_of_univLE : HasWeakSheafify J AddCommGrpCat.{x} := by
  have h : ∀ Y : C, Limits.PreservesColimitsOfShape (J.Cover Y)ᵒᵖ (forget AddCommGrpCat.{x}) :=
    fun Y => preservesColimitsOfShape_forget_addCommGrp_of_univLE J Y
  infer_instance

/-- Sheafification of presheaves of `Λ`-modules, together with its left exactness, on every
site whose universes the module universe dominates. This generalizes `hasSheafify_moduleCat`
from `max u v x` to the inequality. -/
instance hasSheafify_moduleCat_of_univLE (Λ : Type w) [Ring Λ] :
    HasSheafify J (ModuleCat.{x} Λ) := by
  have h : ∀ Y : C, Limits.PreservesColimitsOfShape (J.Cover Y)ᵒᵖ
      (forget (ModuleCat.{x} Λ)) := by
    intro Y
    have : Limits.PreservesColimitsOfShape (J.Cover Y)ᵒᵖ (forget AddCommGrpCat.{x}) :=
      preservesColimitsOfShape_forget_addCommGrp_of_univLE J Y
    exact Limits.comp_preservesColimitsOfShape
      (forget₂ (ModuleCat.{x} Λ) AddCommGrpCat.{x}) (forget AddCommGrpCat.{x})
  exact HasSheafify.mk' J (ModuleCat.{x} Λ) (plusPlusAdjunction J (ModuleCat.{x} Λ))

/-- Sheafification of presheaves of `Λ`-modules commutes with the forgetful functor to types,
on every site whose universes the module universe dominates. -/
instance preservesSheafification_forget_moduleCat_of_univLE (Λ : Type w) [Ring Λ] :
    J.PreservesSheafification (forget (ModuleCat.{x} Λ)) := by
  -- `ModuleCat.hasLimitsOfSize` is a lemma rather than an instance; supplying it is what
  -- unblocks the multicospan limits in Mathlib's `PreservesSheafification` instance.
  have hlim : Limits.HasLimitsOfSize.{max u v, max u v} (ModuleCat.{x} Λ) :=
    ModuleCat.hasLimitsOfSize
  have hcol : ∀ Y : C, Limits.PreservesColimitsOfShape (J.Cover Y)ᵒᵖ
      (forget (ModuleCat.{x} Λ)) := by
    intro Y
    have : Limits.PreservesColimitsOfShape (J.Cover Y)ᵒᵖ (forget AddCommGrpCat.{x}) :=
      preservesColimitsOfShape_forget_addCommGrp_of_univLE J Y
    exact Limits.comp_preservesColimitsOfShape
      (forget₂ (ModuleCat.{x} Λ) AddCommGrpCat.{x}) (forget AddCommGrpCat.{x})
  exact GrothendieckTopology.instPreservesSheafification J (forget (ModuleCat.{x} Λ))

/-- Sheafification of presheaves of `Λ`-modules on the localized topology of a slice site, on
every site whose universes the module universe dominates. This generalizes
`hasSheafify_over_moduleCat` from `max u v x` to the inequality, and it is what discharges the
slice hypothesis `∀ Y : C, HasWeakSheafify (J.over Y) (ModuleCat.{m} Λ)` of the results above
when the module universe `m` is presented in some other way than as `max u v x`: a goal
`ModuleCat.{m} Λ` leaves the `x` of the `max u v x` form a universe metavariable, and
`max u v ?x =?= m` is a universe constraint Lean does not solve.

Deliberately not an instance, with the universes to be supplied by the caller: as an instance
it would be tried ahead of `hasSheafify_over_moduleCat` on every slice goal, and because
`UnivLE` carries `@[univ_out_params]` the extra query reorders the typeclass cache and the
`max u v x`-shaped goals of `CategoryTheory/Sites/LocallyConstant/` then fail to resolve
`UnivLE.{max u v, max u v w}` at all. A consumer at another module universe supplies it as
`haveI := hasSheafify_over_moduleCat_of_univLE.{_, _, _, m} J Λ Y`. -/
theorem hasSheafify_over_moduleCat_of_univLE (Λ : Type w) [Ring Λ] (Y : C) :
    HasSheafify (J.over Y) (ModuleCat.{x} Λ) :=
  hasSheafify_moduleCat_of_univLE.{max u v, v, w, x} (J.over Y) Λ

end UnivLEInstances

end Comparison

end Stacks.ConstantSheaf
