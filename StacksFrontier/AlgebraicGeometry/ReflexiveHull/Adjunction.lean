module

public import StacksFrontier.AlgebraicGeometry.Reflexive.DualMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent

/-!
# The reflexive-hull adjunction

Let `X` be a scheme.  The dual `F^∨ = SheafHom(F, 𝒪_X)` of an `𝒪_X`-module is contravariantly
functorial and the reflexive hull `F^∨∨` is a covariant endofunctor satisfying the triangle
identity `j_{F^∨} ≫ (j_F)^∨ = 𝟙` of a (lax) idempotent unit; that is
`StacksFrontier/AlgebraicGeometry/Reflexive/DualMap.lean`.

Granted that the hull of a coherent module is again coherent *and reflexive* — the first half
of [Stacks, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH) — these identities make the hull
a left adjoint to the inclusion of coherent reflexive modules into coherent modules, with
`toDoubleDual` as its unit.  That is the second half of Tag 0EBH and is
`reflexiveHullAdjunctionOfHull`.

## Main definitions

* `reflexiveHullHomEquiv F G`: the bijection `(F^∨∨ ⟶ G) ≃ (F ⟶ G)` available when the hull of
  `F` and the module `G` are reflexive.
* `CoherentReflexiveModules X`: the full subcategory of coherent `𝒪_X`-modules that are
  reflexive, and `CoherentReflexiveModules.ι X` its inclusion into coherent modules.

## Main results

* `isReflexive_of_split`: a retract of a reflexive module is reflexive, and
  `isReflexive_of_iso`: reflexivity is invariant under isomorphism.
* `reflexiveHullAdjunctionOfHull`: the adjunction of Tag 0EBH, from the coherence and
  reflexivity of the hull.
* `reflexiveHullAdjunctionOfDual`: the same adjunction from the two *one-step* statements that
  the dual of a coherent module is coherent and reflexive, which are the instances at
  `𝒢 = 𝒪_X` of Tags 01Y2 and 0AY4.
* `isCoherent_and_isReflexive_dualSheaf_dualSheaf_of_adjunction`: conversely, the adjunction
  implies the coherence and reflexivity of the hull, so those hypotheses cannot be dropped.

## Implementation notes

The dual, the canonical map `toDoubleDual`, the dual of a morphism and the triangle identity
are those of `StacksFrontier/AlgebraicGeometry/Reflexive/`, built on the internal Hom of Tag 03EM.

The hull is spelled out as `dualSheaf (dualSheaf F)` rather than abbreviated: an
`abbrev reflexiveHull F := dualSheaf (dualSheaf F)` makes the kernel time out on
`doubleDualMap_toDoubleDual`, because the extra reducible layer is unfolded repeatedly inside the
internal-Hom terms.

`reflexiveHullAdjunctionOfHull` takes the two assertions of Tag 0EBH's hull — that `F^∨∨` is
coherent, and that it is reflexive — as explicit hypotheses, and therefore does **not** carry
the `0EBH` tag.  They are not removable: the conclusion asserts that the left adjoint lands in
coherent reflexive modules at the object `F^∨∨`, so it *implies* both of them, which is
`isCoherent_and_isReflexive_dualSheaf_dualSheaf_of_adjunction`.

`reflexiveHullAdjunctionOfDual` reduces those two compound hypotheses to the two one-step
statements about a single dual, which is the granularity at which the Stacks Project proves
them: that `SheafHom(ℱ, 𝒢)` is coherent for coherent `ℱ, 𝒢` (Tag 01Y2, by way of Tag 01CQ), and
that it is reflexive when `𝒢` is (Tag 0AY4).  Both are applied at `𝒢 = 𝒪_X`.

## References

* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
* [Stacks Project, Tag 0AVU](https://stacks.math.columbia.edu/tag/0AVU)
* [Stacks Project, Tag 0AY4](https://stacks.math.columbia.edu/tag/0AY4)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

variable {X : Scheme.{u}}

/-! ### Reflexivity and retracts -/

/-- **A retract of a reflexive module is reflexive.**  If `i : G ⟶ F` has a retraction and `F`
is reflexive, then `G` is reflexive.  This is the sheaf-level form of Mathlib's
`Module.IsReflexive.of_split`, and it is proved the same way: naturality makes `j_G` a
monomorphism because `i ≫ j_F` is one, and `(F^∨∨ ⟶ G^∨∨` applied to `i`, followed by the
inverse of `j_F` and the retraction) is a left inverse of `j_G`, which a monomorphism upgrades
to a two-sided inverse. -/
public theorem isReflexive_of_split {F G : X.Modules} (i : G ⟶ F) (r : F ⟶ G)
    (h : i ≫ r = 𝟙 G) (hF : IsReflexive F) : IsReflexive G := by
  have hiso : IsIso (toDoubleDual F) := hF
  have : IsSplitMono i := .mk' ⟨r, h⟩
  have : Mono (toDoubleDual G ≫ doubleDualMap i) := by
    rw [← toDoubleDual_naturality i]
    infer_instance
  have : Mono (toDoubleDual G) := mono_of_mono _ (doubleDualMap i)
  have key : doubleDualMap i ≫ inv (toDoubleDual F) ≫ r ≫ toDoubleDual G = 𝟙 _ := by
    rw [toDoubleDual_naturality r, ← Category.assoc (inv (toDoubleDual F)), IsIso.inv_hom_id,
      Category.id_comp, ← doubleDualMap_comp, h, doubleDualMap_id]
  refine ⟨⟨doubleDualMap i ≫ inv (toDoubleDual F) ≫ r, ?_, key⟩⟩
  refine (cancel_mono (toDoubleDual G)).mp ?_
  simp only [Category.assoc, Category.id_comp] at key ⊢
  rw [key, Category.comp_id]

/-- Reflexivity is invariant under isomorphism: an isomorphism is a retract in both
directions. -/
public theorem isReflexive_of_iso {F G : X.Modules} (e : F ≅ G) (hF : IsReflexive F) :
    IsReflexive G :=
  isReflexive_of_split e.inv e.hom e.inv_hom_id hF

/-! ### The hull-inclusion hom bijection -/

/-- **The reflexive-hull hom bijection.**  If the hull of `F` is reflexive and `G` is
reflexive, then composing with the canonical map `F ⟶ F^∨∨` identifies the morphisms
`F^∨∨ ⟶ G` with the morphisms `F ⟶ G`. -/
public noncomputable def reflexiveHullHomEquiv (F G : X.Modules)
    [IsIso (toDoubleDual (dualSheaf (dualSheaf F)))] [IsIso (toDoubleDual G)] :
    (dualSheaf (dualSheaf F) ⟶ G) ≃ (F ⟶ G) where
  toFun g := toDoubleDual F ≫ g
  invFun f := doubleDualMap f ≫ inv (toDoubleDual G)
  left_inv g := by
    dsimp only
    rw [doubleDualMap_comp, doubleDualMap_toDoubleDual, ← toDoubleDual_naturality,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  right_inv f := by
    dsimp only
    rw [← Category.assoc, ← toDoubleDual_naturality, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]

/-! ### The category of coherent reflexive modules -/

/-- The full subcategory of coherent modules on a scheme whose underlying module is
reflexive. -/
public abbrev CoherentReflexiveModules (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory
    (C := _root_.Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)
    (fun F => IsReflexive F.obj)

/-- The inclusion of coherent reflexive modules into coherent modules. -/
public noncomputable abbrev CoherentReflexiveModules.ι (X : Scheme.{u}) :
    CoherentReflexiveModules X ⥤
      _root_.Stacks.SheafOfModules.CoherentModules X.ringCatSheaf :=
  ObjectProperty.ι _

/-- **Stacks, Tag 0EBH, the adjunction**, granted the two assertions of Tag 0EBH's hull:
taking reflexive hulls is left adjoint to the inclusion of coherent reflexive modules into
coherent modules, and the unit of the adjunction is the canonical map to the double dual.

The two hypotheses are exactly the content of Tag 0EBH's first half: that the reflexive hull of
a coherent module is coherent and reflexive.  The conclusion implies them, so they cannot be
dispensed with. -/
public noncomputable def reflexiveHullAdjunctionOfHull (X : Scheme.{u})
    (hCoh : ∀ F : X.Modules, _root_.Stacks.SheafOfModules.IsCoherent F →
      _root_.Stacks.SheafOfModules.IsCoherent (dualSheaf (dualSheaf F)))
    (hRefl : ∀ F : X.Modules, _root_.Stacks.SheafOfModules.IsCoherent F →
      IsReflexive (dualSheaf (dualSheaf F))) :
    { p : (Σ L : _root_.Stacks.SheafOfModules.CoherentModules X.ringCatSheaf ⥤
        CoherentReflexiveModules X, L ⊣ CoherentReflexiveModules.ι X) //
      ∀ F : _root_.Stacks.SheafOfModules.CoherentModules X.ringCatSheaf,
        ∃ h : (p.1.obj F).obj.obj = dualSheaf (dualSheaf F.obj),
          (p.2.unit.app F).hom ≫ eqToHom h = toDoubleDual F.obj } := by
  let obj : _root_.Stacks.SheafOfModules.CoherentModules X.ringCatSheaf →
      CoherentReflexiveModules X := fun F =>
    ⟨⟨dualSheaf (dualSheaf F.obj), hCoh F.obj F.property⟩, hRefl F.obj F.property⟩
  let e : ∀ F G, (obj F ⟶ G) ≃ (F ⟶ (CoherentReflexiveModules.ι X).obj G) := fun F G => by
    letI : IsIso (toDoubleDual (dualSheaf (dualSheaf F.obj))) := hRefl F.obj F.property
    letI : IsIso (toDoubleDual G.obj.obj) := G.property
    exact
      { toFun := fun g => ⟨reflexiveHullHomEquiv F.obj G.obj.obj g.hom.hom⟩
        invFun := fun f => ⟨⟨(reflexiveHullHomEquiv F.obj G.obj.obj).symm f.hom⟩⟩
        left_inv := fun g => ObjectProperty.hom_ext _ <| ObjectProperty.hom_ext _ <|
          (reflexiveHullHomEquiv F.obj G.obj.obj).symm_apply_apply g.hom.hom
        right_inv := fun f => ObjectProperty.hom_ext _ <|
          (reflexiveHullHomEquiv F.obj G.obj.obj).apply_symm_apply f.hom }
  have he : ∀ F G G' (g : G ⟶ G') (h : obj F ⟶ G),
      e F G' (h ≫ g) = e F G h ≫ (CoherentReflexiveModules.ι X).map g :=
    fun F _ _ g h =>
      ObjectProperty.hom_ext _ (Category.assoc (toDoubleDual F.obj) h.hom.hom g.hom.hom).symm
  refine ⟨⟨Adjunction.leftAdjointOfEquiv e he, Adjunction.adjunctionOfEquivLeft e he⟩, ?_⟩
  intro F
  refine ⟨rfl, ?_⟩
  refine Eq.trans (Category.comp_id _) ?_
  exact Category.comp_id (toDoubleDual F.obj)

/-- **Stacks, Tag 0EBH, the adjunction**, from the two one-step statements about a *single*
dual: that the dual of a coherent module is coherent, and that it is reflexive.  Those are the
instances at `𝒢 = 𝒪_X` of Tags 01Y2 and 0AY4, and iterating them gives the two assertions of Tag
0EBH's hull, the hypotheses of `reflexiveHullAdjunctionOfHull`.  As there, the conclusion implies
the hypotheses, so the statement is strictly weaker than Tag 0EBH. -/
public noncomputable def reflexiveHullAdjunctionOfDual (X : Scheme.{u})
    (hDualCoh : ∀ F : X.Modules, _root_.Stacks.SheafOfModules.IsCoherent F →
      _root_.Stacks.SheafOfModules.IsCoherent (dualSheaf F))
    (hDualRefl : ∀ F : X.Modules, _root_.Stacks.SheafOfModules.IsCoherent F →
      IsReflexive (dualSheaf F)) :
    { p : (Σ L : _root_.Stacks.SheafOfModules.CoherentModules X.ringCatSheaf ⥤
        CoherentReflexiveModules X, L ⊣ CoherentReflexiveModules.ι X) //
      ∀ F : _root_.Stacks.SheafOfModules.CoherentModules X.ringCatSheaf,
        ∃ h : (p.1.obj F).obj.obj = dualSheaf (dualSheaf F.obj),
          (p.2.unit.app F).hom ≫ eqToHom h = toDoubleDual F.obj } :=
  reflexiveHullAdjunctionOfHull X (fun F hF => hDualCoh _ (hDualCoh F hF))
    (fun F hF => hDualRefl _ (hDualCoh F hF))

/-- The hypotheses of `reflexiveHullAdjunctionOfHull` are not removable: the statement of Tag
0EBH's adjunction *implies* both assertions of Tag 0EBH's hull.  The left adjoint lands in
coherent reflexive modules and its value at `F` is the hull of `F`, so the hull of a coherent
module is coherent and reflexive. -/
public theorem isCoherent_and_isReflexive_dualSheaf_dualSheaf_of_adjunction (X : Scheme.{u})
    (p : { p : (Σ L : _root_.Stacks.SheafOfModules.CoherentModules X.ringCatSheaf ⥤
        CoherentReflexiveModules X, L ⊣ CoherentReflexiveModules.ι X) //
      ∀ F : _root_.Stacks.SheafOfModules.CoherentModules X.ringCatSheaf,
        ∃ h : (p.1.obj F).obj.obj = dualSheaf (dualSheaf F.obj),
          (p.2.unit.app F).hom ≫ eqToHom h = toDoubleDual F.obj })
    (F : X.Modules) (hF : _root_.Stacks.SheafOfModules.IsCoherent F) :
    _root_.Stacks.SheafOfModules.IsCoherent (dualSheaf (dualSheaf F)) ∧
      IsReflexive (dualSheaf (dualSheaf F)) := by
  obtain ⟨h, -⟩ := p.2 ⟨F, hF⟩
  exact ⟨h ▸ (p.1.1.obj ⟨F, hF⟩).obj.property, h ▸ (p.1.1.obj ⟨F, hF⟩).property⟩

end Stacks.AlgebraicGeometry.ReflexiveModules

end
