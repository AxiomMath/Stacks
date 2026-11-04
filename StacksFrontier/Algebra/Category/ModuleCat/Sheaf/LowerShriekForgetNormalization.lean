module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForget

/-!
# Recognising the comparison of the two lower shrieks at a single object

Let `F : C ⥤ D` be a continuous functor of sites and `φ : S ⟶ F_* R` a morphism of sheaves of
rings, so that `Stacks.SheafOfModules.lowerShriekForgetComparison` is the canonical
transformation `g_!^{Ab} ∘ forget ⟶ forget ∘ g_!` of Stacks 0798. Tag 0798's criterion,
`Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_iff`, reduces its invertibility to the
invertibility of its components at the extensions by zero of the structure sheaf, and in
Situation 08PA those components are abstractly invertible: a composite of known isomorphisms
connects `g_!^{Ab}(forget j_{U!} O_U)` to `forget(g_! j_{U!} O_U)`.

An abstract isomorphism with the right source and target is not the component of the
comparison, and this file supplies what turns one into the other. The comparison is *defined* as
an adjoint transpose, so its component at `M` is pinned by a single equation in
`Hom(forget M, g_*^{Ab} -)`, and that equation is all one has to check: given a candidate
isomorphism `θ` and an identification `k` of `g_! M` with the object `θ` actually lands at, if
the transpose of `θ` is the transpose of `k` forgotten, then the component of the comparison at
`M` is invertible.

## Main results

* `Stacks.SheafOfModules.homEquiv_lowerShriekForgetComparison_app_comp`: the adjoint transpose
  of the component of the comparison at `M` followed by `forget k`, for a morphism
  `k : g_! M ⟶ N` of sheaves of modules on the target, is the transpose of `k` itself under the
  module lower-shriek adjunction, forgotten. This is
  `Stacks.SheafOfModules.lowerShriekForgetComparison_homEquiv` made usable: that lemma computes
  the transpose of the bare component, whose target `forget(g_! M)` is a spelling no composite
  of isomorphisms produced elsewhere will match, whereas `N` is arbitrary here.
* `Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_app_of_homEquiv`: the comparison is
  invertible at `M` as soon as some isomorphism `θ : g_!^{Ab}(forget M) ≅ forget N` has that
  transpose, for some isomorphism `k : g_! M ≅ N`.
* `Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_app_comp_of_bijective`: the Yoneda
  form. If `k : g_! M ⟶ N` has an invertible forgotten transpose `M ⟶ g_* N`, and `g^{-1}` is
  bijective on morphisms out of `forget N`, then the component of the comparison at `M`, followed
  by `forget k`, is invertible. No candidate isomorphism has to be written down.
* `Stacks.SheafOfModules.isIso_toSheaf_map_unitToPushforwardObjUnit`: the comparison
  `O_C ⟶ g_* O_D` of the two rank-one modules is invertible when the structure map is; with the
  previous item at `k = SheafOfModules.pullbackObjUnitToUnit` this is the form in which the
  criterion is applied to the structure sheaf.
* `CategoryTheory.Adjunction.map_bijective_of_homEquiv_comp` and
  `CategoryTheory.Functor.map_bijective_of_iso`: a right adjoint is bijective on morphisms out of
  an object `B` as soon as the transposes of morphisms out of `B`, precomposed with an
  isomorphism `L A ≅ B`, are the right adjoint's own action up to a fixed isomorphism; and this
  property only depends on the isomorphism class of `B`.

## Implementation notes

The adjoint transpose of a composite is the transpose of the first factor followed by the right
adjoint applied to the rest, which is `CategoryTheory.Adjunction.homEquiv_naturality_right`.
That is what makes the criterion below cheap to apply to a long composite of isomorphisms: only
the *first* factor needs its transpose computed, the others being carried along by `g_*^{Ab}`.
The equality `g_* ∘ forget = forget ∘ g_*` of the two right adjoints, on morphisms as well as on
objects, holds by `rfl` — the underlying abelian sheaf of a pushforward of modules is
restriction along `F.op` on the nose — and that is what lets the two sides of the transpose
equation be compared at all; it is used implicitly by
`Stacks.SheafOfModules.lowerShriekForgetComparison_homEquiv` already, whose statement would not
typecheck without it.

## References

* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC)
-/

@[expose] public section

open CategoryTheory

universe u w u₁ u₂ v₁ v₂

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : Functor C D) [F.IsContinuous J K]
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  (phi : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  [(_root_.SheafOfModules.pushforward.{w} phi).IsRightAdjoint]
  [(F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]

/-- **The transpose of the comparison at `M`, followed by a morphism of modules.** For a
morphism `k : g_! M ⟶ N` of sheaves of modules on the target site, the adjoint transpose of

`g_!^{Ab}(forget M) --comparison--> forget(g_! M) --forget k--> forget N`

is the transpose of `k` under the module lower-shriek adjunction, forgotten.

This is `Stacks.SheafOfModules.lowerShriekForgetComparison_homEquiv` with a morphism of modules
absorbed. The bare lemma computes the transpose of the component itself, whose target is the
particular object `forget (g_! M)`; a candidate isomorphism assembled from other results lands
at some `forget N` instead, and comparing the two needs the morphism `k` identifying them to be
carried through the transpose, which is what this does. -/
theorem homEquiv_lowerShriekForgetComparison_app_comp (M : _root_.SheafOfModules.{w} S)
    (N : _root_.SheafOfModules.{w} R)
    (k : (_root_.SheafOfModules.pullback.{w} phi).obj M ⟶ N) :
    (F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).homEquiv
        ((_root_.SheafOfModules.toSheaf.{w} S).obj M)
        ((_root_.SheafOfModules.toSheaf.{w} R).obj N)
        ((lowerShriekForgetComparison F phi).app M ≫
          (_root_.SheafOfModules.toSheaf.{w} R).map k) =
      (_root_.SheafOfModules.toSheaf.{w} S).map
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w} phi).homEquiv M N k) := by
  refine (Adjunction.homEquiv_naturality_right
    (adj := F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K)
    (Y := (_root_.SheafOfModules.toSheaf.{w} R).obj
      ((_root_.SheafOfModules.pullback.{w} phi).obj M))
    ((lowerShriekForgetComparison F phi).app M)
    ((_root_.SheafOfModules.toSheaf.{w} R).map k)).trans ?_
  rw [lowerShriekForgetComparison_homEquiv]
  exact ((_root_.SheafOfModules.toSheaf.{w} S).map_comp
    ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w} phi).unit.app M)
    ((_root_.SheafOfModules.pushforward.{w} phi).map k)).symm

/-- **Recognising the component of the comparison.** The canonical comparison between the two
lower shrieks is invertible at a sheaf of modules `M` on the source as soon as there are

* an isomorphism `k : g_! M ≅ N` of sheaves of modules on the target, and
* an isomorphism `θ : g_!^{Ab}(forget M) ≅ forget N` of abelian sheaves whose adjoint transpose
  is the transpose of `k`, forgotten.

The comparison being defined as an adjoint transpose, the hypothesis says exactly that `θ` is
the component of the comparison at `M` followed by `forget k`; so the component is `θ`
conjugated by an isomorphism, hence invertible. This is the shape in which the right-hand side
of the Stacks 0798 criterion is discharged: the composite of isomorphisms produced by the
reduction of Stacks 08PC part (2) is such a `θ`. -/
theorem isIso_lowerShriekForgetComparison_app_of_homEquiv (M : _root_.SheafOfModules.{w} S)
    (N : _root_.SheafOfModules.{w} R)
    (k : (_root_.SheafOfModules.pullback.{w} phi).obj M ≅ N)
    (θ : (F.sheafPullback AddCommGrpCat.{w} J K).obj
          ((_root_.SheafOfModules.toSheaf.{w} S).obj M) ≅
        (_root_.SheafOfModules.toSheaf.{w} R).obj N)
    (h : (F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).homEquiv
          ((_root_.SheafOfModules.toSheaf.{w} S).obj M)
          ((_root_.SheafOfModules.toSheaf.{w} R).obj N) θ.hom =
        (_root_.SheafOfModules.toSheaf.{w} S).map
          ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w} phi).homEquiv M N k.hom)) :
    IsIso ((lowerShriekForgetComparison F phi).app M) := by
  have key : (lowerShriekForgetComparison F phi).app M ≫
      (_root_.SheafOfModules.toSheaf.{w} R).map k.hom = θ.hom := by
    refine ((F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).homEquiv
      ((_root_.SheafOfModules.toSheaf.{w} S).obj M)
      ((_root_.SheafOfModules.toSheaf.{w} R).obj N)).injective ?_
    rw [homEquiv_lowerShriekForgetComparison_app_comp, h]
  have hcomp : (lowerShriekForgetComparison F phi).app M =
      θ.hom ≫ (_root_.SheafOfModules.toSheaf.{w} R).map k.inv := by
    rw [← key, Category.assoc, ← Functor.map_comp, k.hom_inv_id,
      CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).symm
  rw [hcomp]
  exact (θ ≪≫ (_root_.SheafOfModules.toSheaf.{w} R).mapIso k.symm).isIso_hom

/-- **The Yoneda form of the recognition criterion.** Let `k : g_! M ⟶ N` be a morphism of
sheaves of modules whose transpose `M ⟶ g_* N` becomes invertible after forgetting the module
structures, and suppose that `g^{-1}` is bijective on morphisms of abelian sheaves out of
`forget N`. Then the component of the comparison at `M`, followed by `forget k`, is an
isomorphism.

For an abelian sheaf `Y` the transpose of `(comparison ≫ forget k) ≫ x` is the forgotten
transpose of `k` followed by `g^{-1} x`, by `homEquiv_lowerShriekForgetComparison_app_comp`; so
precomposition with `comparison ≫ forget k` is, up to the adjunction bijection and an
isomorphism, the action of `g^{-1}` on morphisms out of `forget N`, hence bijective for every
`Y`, and Yoneda concludes. -/
theorem isIso_lowerShriekForgetComparison_app_comp_of_bijective
    (M : _root_.SheafOfModules.{w} S) (N : _root_.SheafOfModules.{w} R)
    (k : (_root_.SheafOfModules.pullback.{w} phi).obj M ⟶ N)
    [IsIso ((_root_.SheafOfModules.toSheaf.{w} S).map
      ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w} phi).homEquiv M N k))]
    (h : ∀ Y : Sheaf K AddCommGrpCat.{w}, Function.Bijective
      (fun f : (_root_.SheafOfModules.toSheaf.{w} R).obj N ⟶ Y =>
        (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map f)) :
    IsIso ((lowerShriekForgetComparison F phi).app M ≫
      (_root_.SheafOfModules.toSheaf.{w} R).map k) := by
  let adj := F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K
  let e := asIso ((_root_.SheafOfModules.toSheaf.{w} S).map
      ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w} phi).homEquiv M N k))
  have key : ∀ {Y : Sheaf K AddCommGrpCat.{w}}
      (x : (_root_.SheafOfModules.toSheaf.{w} R).obj N ⟶ Y),
      adj.homEquiv _ Y (((lowerShriekForgetComparison F phi).app M ≫
        (_root_.SheafOfModules.toSheaf.{w} R).map k) ≫ x) =
        e.hom ≫ (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map x := fun x => by
    rw [Adjunction.homEquiv_naturality_right, homEquiv_lowerShriekForgetComparison_app_comp]
    rfl
  refine isIso_of_coyoneda_map_bijective _ fun Y => ⟨fun x y hxy => ?_, fun t => ?_⟩
  · have hxy' := congrArg (adj.homEquiv _ Y) hxy
    simp only [key] at hxy'
    exact (h Y).1 ((cancel_epi e.hom).1 hxy')
  · obtain ⟨x, hx⟩ := (h Y).2 (e.inv ≫ adj.homEquiv _ Y t)
    refine ⟨x, (adj.homEquiv _ Y).injective ?_⟩
    simp only at hx
    rw [key, hx]
    exact e.hom_inv_id_assoc _

end Stacks.SheafOfModules

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : Functor C D} [F.IsContinuous J K]
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  (phi : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

/-- The canonical morphism `O_C ⟶ g_* O_D` of rank-one modules,
`SheafOfModules.unitToPushforwardObjUnit`, is invertible on underlying abelian sheaves when the
structure map of rings is invertible: over an object its component is the structure map itself,
read as a map of abelian groups. -/
instance isIso_toSheaf_map_unitToPushforwardObjUnit [IsIso phi] :
    IsIso ((_root_.SheafOfModules.toSheaf.{u} S).map
      (_root_.SheafOfModules.unitToPushforwardObjUnit phi)) := by
  have : IsIso phi.hom := inferInstanceAs (IsIso ((sheafToPresheaf J RingCat.{u}).map phi))
  have : IsIso ((sheafToPresheaf J AddCommGrpCat.{u}).map
      ((_root_.SheafOfModules.toSheaf.{u} S).map
        (_root_.SheafOfModules.unitToPushforwardObjUnit phi))) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    exact (inferInstance : IsIso ((forget₂ RingCat AddCommGrpCat).map (phi.hom.app X)))
  exact isIso_of_reflects_iso _ (sheafToPresheaf J AddCommGrpCat.{u})

end Stacks.SheafOfModules

namespace CategoryTheory

variable {C : Type*} [Category* C] {D : Type*} [Category* D]

/-- **A right adjoint is bijective on morphisms out of `B` once its transposes are its own
action.** Let `L ⊣ G`, let `θ : L A ⟶ B` and `ε : A ⟶ G B` be isomorphisms, and suppose that
for every `g : B ⟶ Y` the transpose of `θ ≫ g` is `ε ≫ G g`. Then `G` is bijective on morphisms
out of `B`: it is, up to the isomorphisms `θ` and `ε`, the adjunction bijection. -/
theorem Adjunction.map_bijective_of_homEquiv_comp {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G)
    {A : C} {B : D} (θ : L.obj A ⟶ B) [IsIso θ] (ε : A ⟶ G.obj B) [IsIso ε]
    (h : ∀ {Y : D} (g : B ⟶ Y), adj.homEquiv A Y (θ ≫ g) = ε ≫ G.map g) (Y : D) :
    Function.Bijective (fun g : B ⟶ Y => G.map g) := by
  have he : (fun g : B ⟶ Y => G.map g) =
      (fun t => inv ε ≫ t) ∘ adj.homEquiv A Y ∘ (fun g => θ ≫ g) := by
    funext g
    simp only [Function.comp_apply, h, IsIso.inv_hom_id_assoc]
  rw [he]
  exact ((isIso_iff_coyoneda_map_bijective (inv ε)).1 inferInstance _).comp
    ((adj.homEquiv A Y).bijective.comp ((isIso_iff_coyoneda_map_bijective θ).1 inferInstance Y))

/-- Being bijective on morphisms out of an object is invariant under isomorphism of the object:
the action of `G` on morphisms out of `X` is its action on morphisms out of `B`, conjugated by
`X ≅ B` and by its image under `G`. -/
theorem Functor.map_bijective_of_iso (G : D ⥤ C) {X B : D} (a : X ≅ B)
    (h : ∀ Y : D, Function.Bijective (fun g : B ⟶ Y => G.map g)) (Y : D) :
    Function.Bijective (fun f : X ⟶ Y => G.map f) := by
  have he : (fun f : X ⟶ Y => G.map f) =
      (fun t => G.map a.hom ≫ t) ∘ (fun g : B ⟶ Y => G.map g) ∘ (fun f => a.inv ≫ f) := by
    funext f
    simp only [Function.comp_apply, ← G.map_comp, Iso.hom_inv_id_assoc]
  rw [he]
  exact ((isIso_iff_coyoneda_map_bijective (G.map a.hom)).1 inferInstance _).comp
    ((h Y).comp ((isIso_iff_coyoneda_map_bijective a.inv).1 inferInstance Y))

end CategoryTheory

end
