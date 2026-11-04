module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Combinatorics.Quiver.ReflQuiver

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Localization of morphisms of ringed sites

Let `(f, f^#) : (C, O) → (D, O')` be a morphism of ringed sites whose morphism of sites
`f : C → D` is given by a continuous functor `u : D ⥤ C`, with structure map in pushforward form
`α = f^# : O' ⟶ f_* O`, where `f_* = u.sheafPushforwardContinuous`. Let `V` be an object of `D`
and `U = u(V)`, and let `f' : C/U → D/V` be the morphism of sites given by
`u' = Over.post u : Over V ⥤ Over U` (Tag 03CF). The localization `j_U^{-1}` is
`JC.overPullback A U`, that is `(Over.forget U).sheafPushforwardContinuous`, with
`O_U = j_U^{-1} O` and `j_U^# = 𝟙`.

Then `(f')^# = j_V^{-1}(f^#)`, transported along the comparison isomorphism
`f'_* j_U^{-1} ≅ j_V^{-1} f_*`, makes `f'` a morphism of ringed topoi; it is the unique map of
sheaves of rings compatible with `f^#` under the localization identifications, so the square
formed by `f`, `f'`, `j_U`, `j_V` commutes; and `f'_* j_U^* = j_V^* f_*` on sheaves of modules,
while `f'_* j_U^{-1} ≅ j_V^{-1} f_*` for sheaves valued in any category.

## Main definitions

* `AlgebraicGeometry.RingedSite.MorphismLocalization.localizationComparisonIso`: the comparison
  isomorphism `f'_* ∘ j_U^{-1} ≅ j_V^{-1} ∘ f_*` of Tag 03CF.
* `AlgebraicGeometry.RingedSite.MorphismLocalization.localizedStructureMap`: the structure map
  `(f')^# : O'_V ⟶ f'_* O_U` of the localized morphism.

## Main results

* `AlgebraicGeometry.RingedSite.MorphismLocalization.localizedStructureMap_comp_comparisonIso_hom`:
  `(f')^#` followed by the comparison isomorphism is `j_V^{-1}(f^#)`.
* `AlgebraicGeometry.RingedSite.MorphismLocalization.eq_localizedStructureMap`: `(f')^#` is the
  unique map with that property.
* `AlgebraicGeometry.RingedSite.MorphismLocalization.pushforward_overPullback_comm_modules`:
  `f'_* j_U^* = j_V^* f_*` as functors of sheaves of modules.
* `AlgebraicGeometry.RingedSite.MorphismLocalization.nonempty_overPullback_pushforward_iso`:
  `f'_* j_U^{-1} ≅ j_V^{-1} f_*` for sheaves valued in any category.

## Implementation notes

The continuity of `Over.post u` is an instance hypothesis, since Mathlib does not derive it from
the continuity of `u`. The comparison isomorphism is built from
`Functor.sheafPushforwardContinuousComp'` and the functor equation
`Over.post u ⋙ Over.forget U = Over.forget V ⋙ u` (`Over.post_forget_eq_forget_comp`), and it is
the identity on each component. For a localization morphism `j^# = 𝟙`, so the module
restriction `j_U^*` is `SheafOfModules.pushforward (𝟙 O_U)` and agrees with `j_U^{-1}`.

## References

* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 03CF](https://stacks.math.columbia.edu/tag/03CF)
-/

open CategoryTheory

namespace AlgebraicGeometry.RingedSite.MorphismLocalization

-- The whole statement is parameterized by the following data of a morphism of ringed sites.
variable {C D : Type*} [Category C] [Category D] (u : D ⥤ C)
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D) [u.IsContinuous JD JC]
    -- the object `V` of `D`; we write `U = u.obj V`:
    (V : D)
    -- Stacks Lemma 7.28.1: the functor `u' = Over.post u` is continuous.
    [(Over.post u (X := V)).IsContinuous (JD.over V) (JC.over (u.obj V))]

/-- **The Tag 03CF comparison isomorphism.** For sheaves valued in any category `A`, the
canonical natural isomorphism `f'_* ∘ j_U^{-1} ≅ j_V^{-1} ∘ f_*`, i.e.
`(overPullback A U ⋙ (Over.post u)_*) ≅ (u_* ⋙ overPullback A V)`.

This is constructed from the functor equation `Over.post u ⋙ Over.forget U = Over.forget V ⋙ u`
(`Over.post_forget_eq_forget_comp`) via the pseudofunctoriality isomorphism
`Functor.sheafPushforwardContinuousComp'` of `sheafPushforwardContinuous`, using that
`overPullback A X = (Over.forget X).sheafPushforwardContinuous`.  It is the content of
Stacks Lemma 7.28.1 (Tag 03CF). -/
noncomputable def localizationComparisonIso (A : Type*) [Category A] :
    (JC.overPullback A (u.obj V) ⋙
        (Over.post u).sheafPushforwardContinuous A (JD.over V) (JC.over (u.obj V)))
      ≅ (u.sheafPushforwardContinuous A JD JC ⋙ JD.overPullback A V) :=
  haveI : (Over.forget V ⋙ u).IsContinuous (JD.over V) JC :=
    Functor.isContinuous_comp (Over.forget V) u (JD.over V) JD JC
  (Functor.sheafPushforwardContinuousComp'
      (F := Over.post u) (G := Over.forget (u.obj V))
      (FG := Over.forget V ⋙ u) (eqToIso (Over.post_forget_eq_forget_comp u V))
      A (JD.over V) (JC.over (u.obj V)) JC) ≪≫
  (Functor.sheafPushforwardContinuousComp'
      (F := Over.forget V) (G := u)
      (FG := Over.forget V ⋙ u) (Iso.refl _)
      A (JD.over V) JD JC).symm

-- Structure sheaves of the ringed sites `(C, O)` and `(D, O')`, and the structure map
-- `f^# = α` (in pushforward form) of the morphism of ringed sites `(f, f^#)`.
variable (OC : Sheaf JC RingCat) (OD : Sheaf JD RingCat)
    (α : OD ⟶ (u.sheafPushforwardContinuous RingCat JD JC).obj OC)

/-- **Part (1), the construction of `(f')^#`.** The canonical structure map of the
localized morphism `f'`, in pushforward (`f'_*`) form:
`(f')^# : O'_V ⟶ f'_* O_U`, where `O_U = j_U^{-1} O = (overPullback RingCat U).obj OC`,
`O'_V = j_V^{-1} O' = (overPullback RingCat V).obj OD`, and `f'_* = (Over.post u)_*`.

It is `j_V^{-1}` applied to `α = f^#`, post-composed with the (inverse of the) Tag 03CF
comparison isomorphism; this is the pushforward form of the adjoint composite
`(f')^{-1} O'_V = j_U^{-1} f^{-1} O' →[j_U^{-1} f^#] j_U^{-1} O = O_U` of Stacks 04J0. -/
noncomputable def localizedStructureMap :
    (JD.overPullback RingCat V).obj OD ⟶
      ((Over.post u).sheafPushforwardContinuous RingCat (JD.over V) (JC.over (u.obj V))).obj
        ((JC.overPullback RingCat (u.obj V)).obj OC) :=
  (JD.overPullback RingCat V).map α ≫
    (localizationComparisonIso u JC JD V RingCat).inv.app OC

-- The Tag 03CF comparison isomorphism is the identity on each component, because
-- `localizationComparisonIso` is built entirely from identity/`rfl` data: the functor equation
-- `Over.post u ⋙ Over.forget U = Over.forget V ⋙ u` is `rfl`
-- (`Over.post_forget_eq_forget_comp`), so `eqToIso` of it is `eqToIso rfl = Iso.refl`, and
-- `sheafPushforwardContinuousComp` is itself `Iso.refl`.  Unfolding all the
-- `sheafPushforwardContinuous*` combinators and the `whiskerRight (NatTrans.op (𝟙 _))`
-- collapses to the identity natural transformation, checked at the value (presheaf) level.

/-- The Tag 03CF comparison isomorphism is the identity on each component `OC`. -/
theorem localizationComparisonIso_hom_app :
    (localizationComparisonIso u JC JD V RingCat).hom.app OC = 𝟙 _ := by
  unfold localizationComparisonIso
  simp only [Functor.comp_obj, eqToIso_refl, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousComp,
    Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans,
    Iso.refl_hom, Iso.refl_inv, NatTrans.op_id, Functor.whiskerRight_id']
  apply Sheaf.hom_ext
  ext X x
  simp only [NatTrans.id_app, Functor.comp_obj, ObjectProperty.ι_obj, Category.id_comp,
    Iso.refl_trans, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.op_obj, Over.forget_obj, NatTrans.op_app, RingCat.hom_comp,
    RingHom.coe_comp, Function.comp_apply, ObjectProperty.FullSubcategory.id_hom, RingCat.hom_id]
  rw [show OC.obj.map (𝟙 ((Over.post u).obj (Opposite.unop X)).left).op = 𝟙 _ from
    CategoryTheory.Functor.map_id _ _]
  rfl

/-- Consequently the inverse comparison map is also the identity on each component. -/
theorem localizationComparisonIso_inv_app :
    (localizationComparisonIso u JC JD V RingCat).inv.app OC = 𝟙 _ := by
  simpa only [localizationComparisonIso_hom_app, Category.comp_id] using
    (localizationComparisonIso u JC JD V RingCat).inv_hom_id_app OC

/-- Hence the localized structure map is literally `j_V^{-1}` applied to `f^# = α`
(the comparison correction being trivial). -/
theorem localizedStructureMap_eq :
    localizedStructureMap u JC JD V OC OD α = (JD.overPullback RingCat V).map α := by
  simp [localizedStructureMap, localizationComparisonIso_inv_app]

/-- **Part (1): the defining characterisation of `(f')^#`.** The canonical structure map
`(f')^# = localizedStructureMap`, transported across the Tag 03CF comparison isomorphism,
equals `j_V^{-1}` applied to the structure map `f^# = α`.  This is the formal content of
the composite formula of part (1): up to the localization identifications
`O'_V = j_V^{-1} O'`, `O_U = j_U^{-1} O` and the identity `f'_* j_U^{-1} = j_V^{-1} f_*`,
the map `(f')^#` is `j_U^{-1}(f^#)`. -/
@[stacks 04J0 "(1)"]
theorem localizedStructureMap_comp_comparisonIso_hom :
    localizedStructureMap u JC JD V OC OD α ≫
        (localizationComparisonIso u JC JD V RingCat).hom.app OC
      = (JD.overPullback RingCat V).map α := by
  simp [localizedStructureMap_eq, localizationComparisonIso_hom_app]

/-- **Part (2): commutativity of the square of ringed topoi.** With `(f')^#` chosen as in
`localizedStructureMap`, the square of ringed topoi formed by `(f, f^#)`, `(f', (f')^#)`,
`(j_U, j_U^#)`, `(j_V, j_V^#)` commutes.  The underlying square of topoi commutes by Stacks
Lemma 7.28.1 (encoded by `localizationComparisonIso`); the new content is the
compatibility of the structure-sheaf maps, namely that `(f')^#` is the *unique* map of
sheaves of rings `g : O'_V ⟶ f'_* O_U` intertwining `f^#` with the localization
identifications, i.e. satisfying `g ≫ cmp = j_V^{-1}(f^#)` (both `j_U^#`, `j_V^#` being
identities).  Uniqueness expresses that the commuting choice of structure map is canonical. -/
@[stacks 04J0 "(2)"]
theorem eq_localizedStructureMap
    (g : (JD.overPullback RingCat V).obj OD ⟶
          ((Over.post u).sheafPushforwardContinuous RingCat (JD.over V)
              (JC.over (u.obj V))).obj ((JC.overPullback RingCat (u.obj V)).obj OC))
    (hg : g ≫ (localizationComparisonIso u JC JD V RingCat).hom.app OC
        = (JD.overPullback RingCat V).map α) :
    g = localizedStructureMap u JC JD V OC OD α := by
  rw [localizedStructureMap_eq, ← hg]
  simp [localizationComparisonIso_hom_app]

/-- **Part (3), module form: `f'_* j_U^* = j_V^* f_*`.** Equality of functors
`SheafOfModules OC ⥤ SheafOfModules O'_V`.  On the left we first apply the module
restriction `j_U^* = j_U^{-1}` (the localization pushforward along `Over.forget U` with the
identity structure map, since `O_U = j_U^{-1} O`) and then push forward along `f'` (using
`(f')^# = localizedStructureMap`); on the right we first push forward along `f` (using
`f^# = α`) and then restrict along `j_V`.  Because `j^# = id` for a localization morphism,
`j_U^* = j_U^{-1}` and `j_V^* = j_V^{-1}` on modules, so this single equality realizes both
functor identities of part (3) at the level of sheaves of modules. -/
@[stacks 04J0 "(3)"]
theorem pushforward_overPullback_comm_modules :
    SheafOfModules.pushforward (F := Over.forget (u.obj V))
        (𝟙 ((JC.overPullback RingCat (u.obj V)).obj OC))
      ⋙ SheafOfModules.pushforward (localizedStructureMap u JC JD V OC OD α)
    = SheafOfModules.pushforward α
      ⋙ SheafOfModules.pushforward (F := Over.forget V)
          (𝟙 ((JD.overPullback RingCat V).obj OD)) := by
  -- After the rewrite both sides are, definitionally, a single `pushforward` along
  -- `Over.post u ⋙ Over.forget U = Over.forget V ⋙ u` with the same ring map.
  rw [localizedStructureMap_eq]
  congr 1

/-- **Part (3), abelian / value-category form: `f'_* j_U^{-1} = j_V^{-1} f_*`.** At the
level of sheaves valued in an arbitrary category `A` (in particular abelian sheaves,
`A := AddCommGrp`), the functors `f'_* ∘ j_U^{-1}` and `j_V^{-1} ∘ f_*` are canonically
isomorphic, by `localizationComparisonIso`, the identification of functors of Stacks
Lemma 7.28.1. -/
@[stacks 04J0 "(3)"]
theorem nonempty_overPullback_pushforward_iso (A : Type*) [Category A] :
    Nonempty
      ((JC.overPullback A (u.obj V) ⋙
          (Over.post u).sheafPushforwardContinuous A (JD.over V) (JC.over (u.obj V)))
        ≅ (u.sheafPushforwardContinuous A JD JC ⋙ JD.overPullback A V)) :=
  ⟨localizationComparisonIso u JC JD V A⟩

end AlgebraicGeometry.RingedSite.MorphismLocalization
