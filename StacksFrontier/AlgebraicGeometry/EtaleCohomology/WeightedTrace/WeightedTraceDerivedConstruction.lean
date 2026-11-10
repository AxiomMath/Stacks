module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLiftFunctorial
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.EtaleModulePullbackAdjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceExistence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The weighted trace with coefficients in a ring, on unbounded derived categories, constructed

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site, let `w` be a weighting
of `f` and let `Λ` be a ring. Part (3) of Stacks 0GKH says that the trace maps of Stacks 0GKG
give, for every object `K` of `D(Y_étale, Λ)`, a morphism `Tr_{f, w, K} : f_! f^{-1}K ⟶ K`,
functorial in `K` and compatible with arbitrary base change. This file constructs every piece of
that statement at `Λ`-module coefficients and proves it:

* the `Λ`-linear inverse image is `AlgebraicGeometry.SmallEtale.pullbackMod`, the lift
  `Stacks.ModuleCatLift.moduleLift` of the abelian `f^{-1}` of Stacks 03Q1; its identification
  `AlgebraicGeometry.SmallEtale.pullbackModForgetIso` with the abelian `f^{-1}` on underlying
  abelian sheaves is the identity;
* the base-change comparison `g^{-1}f_!G ≅ f'_!p^{-1}G` and the comparison
  `p^{-1}f^{-1}F ≅ f'^{-1}g^{-1}F` of the two iterated inverse images at `Λ`-coefficients are
  the lifts `Stacks.ModuleCatLift.moduleLiftNatIso` of the abelian ones, the isomorphism of
  Stacks 0F5J and `AlgebraicGeometry.SmallEtale.inverseImageSquareIso`;
* the trace map at `Λ`-coefficients is the trace map of Stacks 0GKG on the underlying abelian
  sheaf, read as a morphism of sheaves of `Λ`-modules.

## Main definitions

* `AlgebraicGeometry.SmallEtale.weightedTraceMod` — **the trace map
  `Tr_{f, w, M} : f_! f^{-1}M ⟶ M` of Stacks 0GKG at `Λ`-module coefficients**, with
  `AlgebraicGeometry.SmallEtale.weightedTraceModTrans` the natural transformation
  `f^{-1} ⋙ f_! ⟶ id` it assembles into.
* `AlgebraicGeometry.SmallEtale.derivedWeightedTraceMod` — **the derived trace of Stacks 0GKH
  part (3)**: the natural transformation `f^{-1} ⋙ f_! ⟶ id` of `D(Y_étale, Λ)` whose component
  at `K` is `Tr_{f, w, K}`.
* `AlgebraicGeometry.SmallEtale.fShriekBaseChangeMod` and
  `AlgebraicGeometry.SmallEtale.inverseImageSquareMod` — the two comparisons attached to a
  cartesian square at `Λ`-coefficients.

## Main results

* `AlgebraicGeometry.SmallEtale.weightedTraceMod_hasWeightedTraceStalksMod` — **the constructed
  map is the trace**: it has the behaviour on geometric stalks by which Stacks 0GKG
  characterises the trace of `(f, w)`, and
  `AlgebraicGeometry.SmallEtale.eq_weightedTraceMod` is the uniqueness.
* `AlgebraicGeometry.SmallEtale.fShriekBaseChangeMod_forget` and
  `AlgebraicGeometry.SmallEtale.inverseImageSquareMod_forget` — the two comparisons at
  `Λ`-coefficients induce the abelian ones on underlying abelian sheaves.
* `AlgebraicGeometry.SmallEtale.derivedWeightedTraceMod_spec` — **Stacks 0GKH, part (3)**: the
  trace at `Λ`-module coefficients exists, is unique, assembles into a natural transformation of
  unbounded derived categories which is functorial in `K`, restricts to the sheaf-level trace,
  and is compatible with arbitrary base change.

## References

* [Stacks Project, Tag 0GKH](https://stacks.math.columbia.edu/tag/0GKH)
* [Stacks Project, Tag 0GKG](https://stacks.math.columbia.edu/tag/0GKG)
* [Stacks Project, Tag 0F5J](https://stacks.math.columbia.edu/tag/0F5J)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 0F3B](https://stacks.math.columbia.edu/tag/0F3B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.SmallEtale

universe u v t r

attribute [local instance] additive_abPullback

/-- A morphism composed with two identities on either side is itself:
`a ≫ 𝟙 A' ≫ 𝟙 A' = 𝟙 A ≫ 𝟙 A ≫ a`. -/
private theorem comp_id_comp_id {C : Type*} [Category* C] {A A' : C} (a : A ⟶ A') :
    a ≫ 𝟙 A' ≫ 𝟙 A' = 𝟙 A ≫ 𝟙 A ≫ a := by
  simp

/-- A functor sends an endomorphism equal to the identity to the identity. -/
private theorem map_eq_id_of_eq_id {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {A : C}
    {a : A ⟶ A} (h : a = 𝟙 A) : F.map a = 𝟙 _ :=
  h ▸ F.map_id A

/-! ### The `Λ`-linear inverse image on components -/

section PullbackMod

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ] {X Y : B.Scheme} (f : X ⟶ Y)

/-- The identification of the abelian sheaf underlying `f^{-1}M` with the abelian `f^{-1}` of the
abelian sheaf underlying `M` is the identity. -/
@[simp]
public lemma pullbackModForgetIso_hom_app (M : ModuleSheaf.{u, v, r} B Y Λ) :
    (pullbackModForgetIso.{u, v, r} B Λ f).hom.app M = 𝟙 _ :=
  rfl

/-- The inverse of the identification of the abelian sheaf underlying `f^{-1}M` with the abelian
`f^{-1}` of the abelian sheaf underlying `M` is the identity. -/
@[simp]
public lemma pullbackModForgetIso_inv_app (M : ModuleSheaf.{u, v, r} B Y Λ) :
    (pullbackModForgetIso.{u, v, r} B Λ f).inv.app M = 𝟙 _ :=
  rfl

end PullbackMod

/-! ### The `Λ`-linear direct image with compact support, on the nose -/

section FShriekMod

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ] {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- The identification of the abelian sheaf underlying `f_!M` with `f_!` of the abelian sheaf
underlying `M` is the identity. -/
@[simp]
public lemma fShriekModForgetIso_hom_app (n : ModuleSheaf.{u, v, r} B X Λ) :
    (fShriekModForgetIso.{u, v, r} B Λ f).hom.app n = 𝟙 _ :=
  rfl

/-- The inverse of the identification of the abelian sheaf underlying `f_!M` with `f_!` of the
abelian sheaf underlying `M` is the identity. -/
@[simp]
public lemma fShriekModForgetIso_inv_app (n : ModuleSheaf.{u, v, r} B X Λ) :
    (fShriekModForgetIso.{u, v, r} B Λ f).inv.app n = 𝟙 _ :=
  rfl

/-- **The abelian sheaf underlying `f_! f^{-1}M` is `f_! f^{-1}` of the abelian sheaf underlying
`M` on the nose**: the identification `AlgebraicGeometry.SmallEtale.forgetFShriekModPullNatIso`
is the identity. -/
@[simp]
public lemma forgetFShriekModPullNatIso_hom_app (M : ModuleSheaf.{u, v, r} B Y Λ) :
    (forgetFShriekModPullNatIso.{u, v, r} B Λ f (pullbackMod.{u, v, r} B Λ f)
        (pullbackModForgetIso.{u, v, r} B Λ f)).hom.app M = 𝟙 _ := by
  have h := map_eq_id_of_eq_id (fShriekFunctor.{u, max v r} B f)
    (pullbackModForgetIso_inv_app.{u, v, r} B Λ f M)
  change (fShriekFunctor.{u, max v r} B f).map
      ((pullbackModForgetIso.{u, v, r} B Λ f).inv.app M) ≫
    (fShriekModForgetIso.{u, v, r} B Λ f).inv.app ((pullbackMod.{u, v, r} B Λ f).obj M) = 𝟙 _
  erw [h, fShriekModForgetIso_inv_app]
  exact Category.id_comp _

end FShriekMod

/-! ### The trace map at `Λ`-module coefficients -/

section Trace

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ] {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  {w : X.obj → ℤ} (hw : IsWeighting (B.inclusion.map f) w)

/-- **Multiplication by a scalar on the abelian sheaf underlying `f_! f^{-1}M`** is the image
under the abelian `f_! f^{-1}` of multiplication by that scalar on the abelian sheaf underlying
`M`. -/
public lemma sheafScalarEnd_fShriekMod_pullbackMod (M : ModuleSheaf.{u, v, r} B Y Λ) (a : Λ) :
    (Stacks.ModuleCatLift.sheafScalarEnd Λ (SmallEtale.topology B Y.obj Y.property)
        ((fShriekMod.{u, v, r} B Λ f).obj ((pullbackMod.{u, v, r} B Λ f).obj M)) a).asHom =
      (fShriekFunctor.{u, max v r} B f).map ((abPullback.{u, max v r} B f).map
        (Stacks.ModuleCatLift.sheafScalarEnd Λ (SmallEtale.topology B Y.obj Y.property) M
          a).asHom) :=
  rfl

include hw in
/-- **The trace map of Stacks 0GKG commutes with multiplication by a scalar**: on the abelian
sheaf underlying a sheaf of `Λ`-modules `M`, multiplication by `a` on `f_! f^{-1}M` followed by
the trace map is the trace map followed by multiplication by `a` on `M`. -/
public theorem weightedTrace_sheafScalarEnd_comm (M : ModuleSheaf.{u, v, r} B Y Λ) (a : Λ) :
    (Stacks.ModuleCatLift.sheafScalarEnd Λ (SmallEtale.topology B Y.obj Y.property)
          ((fShriekMod.{u, v, r} B Λ f).obj ((pullbackMod.{u, v, r} B Λ f).obj M)) a).asHom ≫
        weightedTrace.{u, max v r} B f hw ((forgetModuleSheaf.{u, v, r} B Y Λ).obj M) =
      weightedTrace.{u, max v r} B f hw ((forgetModuleSheaf.{u, v, r} B Y Λ).obj M) ≫
        (Stacks.ModuleCatLift.sheafScalarEnd Λ (SmallEtale.topology B Y.obj Y.property) M
          a).asHom := by
  rw [sheafScalarEnd_fShriekMod_pullbackMod.{u, v, r} B Λ f M a]
  exact hasWeightedTraceStalks_naturality.{u, max v r} B f w
    (Stacks.ModuleCatLift.sheafScalarEnd Λ (SmallEtale.topology B Y.obj Y.property) M a).asHom
    (weightedTrace_hasWeightedTraceStalks.{u, max v r} B f hw _)
    (weightedTrace_hasWeightedTraceStalks.{u, max v r} B f hw _)

include hw in
/-- **The trace map of Stacks 0GKG at `Λ`-module coefficients**,
`Tr_{f, w, M} : f_! f^{-1}M ⟶ M`: the trace map of Stacks 0GKG of the abelian sheaf underlying
`M`, which is `Λ`-linear, read as a morphism of sheaves of `Λ`-modules. -/
@[sga "4 XVII 6.2.5" "partial"]
public def weightedTraceMod (M : ModuleSheaf.{u, v, r} B Y Λ) :
    (fShriekMod.{u, v, r} B Λ f).obj ((pullbackMod.{u, v, r} B Λ f).obj M) ⟶ M :=
  Stacks.ModuleCatLift.sheafHomOfScalarComm.{max (u + 1) v r, r, _, _} Λ
    (SmallEtale.topology B Y.obj Y.property)
    (weightedTrace.{u, max v r} B f hw ((forgetModuleSheaf.{u, v, r} B Y Λ).obj M))
    (weightedTrace_sheafScalarEnd_comm.{u, v, r} B Λ f hw M)

include hw in
/-- The morphism of abelian sheaves underlying the trace map at `Λ`-coefficients is the trace
map of Stacks 0GKG. -/
@[simp]
public lemma forgetModuleSheaf_map_weightedTraceMod (M : ModuleSheaf.{u, v, r} B Y Λ) :
    (forgetModuleSheaf.{u, v, r} B Y Λ).map (weightedTraceMod.{u, v, r} B Λ f hw M) =
      weightedTrace.{u, max v r} B f hw ((forgetModuleSheaf.{u, v, r} B Y Λ).obj M) :=
  rfl

include hw in
/-- **The trace map at `Λ`-coefficients is the trace map of Stacks 0GKG**: it has the behaviour
on geometric stalks by which that tag characterises the trace of `(f, w)`. -/
public theorem weightedTraceMod_hasWeightedTraceStalksMod (M : ModuleSheaf.{u, v, r} B Y Λ) :
    HasWeightedTraceStalksMod.{u, v, r} B Λ f (pullbackMod.{u, v, r} B Λ f)
      (pullbackModForgetIso.{u, v, r} B Λ f) w M (weightedTraceMod.{u, v, r} B Λ f hw M) := by
  have h : forgetModTrace.{u, v, r} B Λ f (pullbackMod.{u, v, r} B Λ f)
        (pullbackModForgetIso.{u, v, r} B Λ f) M (weightedTraceMod.{u, v, r} B Λ f hw M) =
      (forgetModuleSheaf.{u, v, r} B Y Λ).map (weightedTraceMod.{u, v, r} B Λ f hw M) := by
    change (forgetFShriekModPullNatIso.{u, v, r} B Λ f (pullbackMod.{u, v, r} B Λ f)
        (pullbackModForgetIso.{u, v, r} B Λ f)).hom.app M ≫
      (forgetModuleSheaf.{u, v, r} B Y Λ).map (weightedTraceMod.{u, v, r} B Λ f hw M) = _
    rw [forgetFShriekModPullNatIso_hom_app.{u, v, r} B Λ f M]
    exact Category.id_comp _
  change HasWeightedTraceStalks.{u, max v r} B f w _
    (forgetModTrace.{u, v, r} B Λ f (pullbackMod.{u, v, r} B Λ f)
      (pullbackModForgetIso.{u, v, r} B Λ f) M (weightedTraceMod.{u, v, r} B Λ f hw M))
  rw [h, forgetModuleSheaf_map_weightedTraceMod.{u, v, r} B Λ f hw M]
  exact weightedTrace_hasWeightedTraceStalks.{u, max v r} B f hw _

include hw in
/-- **Uniqueness of the trace at `Λ`-coefficients.** Any morphism of sheaves of `Λ`-modules
whose underlying morphism of abelian sheaves has the behaviour on geometric stalks of
Stacks 0GKG is the trace map. -/
public theorem eq_weightedTraceMod (M : ModuleSheaf.{u, v, r} B Y Λ)
    {σ : (fShriekMod.{u, v, r} B Λ f).obj ((pullbackMod.{u, v, r} B Λ f).obj M) ⟶ M}
    (hσ : HasWeightedTraceStalksMod.{u, v, r} B Λ f (pullbackMod.{u, v, r} B Λ f)
      (pullbackModForgetIso.{u, v, r} B Λ f) w M σ) :
    σ = weightedTraceMod.{u, v, r} B Λ f hw M :=
  hasWeightedTraceStalksMod_unique.{u, v, r} B Λ f (pullbackMod.{u, v, r} B Λ f)
    (pullbackModForgetIso.{u, v, r} B Λ f) w M hσ
    (weightedTraceMod_hasWeightedTraceStalksMod.{u, v, r} B Λ f hw M)

include hw in
/-- **The trace maps at `Λ`-coefficients form a natural transformation** `f^{-1} ⋙ f_! ⟶ id` of
functors on sheaves of `Λ`-modules. -/
@[sga "4 XVII 6.2.5" "more general"]
public def weightedTraceModTrans :
    pullbackMod.{u, v, r} B Λ f ⋙ fShriekMod.{u, v, r} B Λ f ⟶
      𝟭 (ModuleSheaf.{u, v, r} B Y Λ) :=
  weightedTraceModNatTrans.{u, v, r} B Λ f (pullbackMod.{u, v, r} B Λ f)
    (pullbackModForgetIso.{u, v, r} B Λ f) w (weightedTraceMod.{u, v, r} B Λ f hw)
    (weightedTraceMod_hasWeightedTraceStalksMod.{u, v, r} B Λ f hw)

include hw in
/-- The component of `AlgebraicGeometry.SmallEtale.weightedTraceModTrans` at `M` is the trace
map `Tr_{f, w, M}`. -/
@[simp]
public lemma weightedTraceModTrans_app (M : ModuleSheaf.{u, v, r} B Y Λ) :
    (weightedTraceModTrans.{u, v, r} B Λ f hw).app M = weightedTraceMod.{u, v, r} B Λ f hw M :=
  rfl

variable [HasDerivedCategory.{t} (ModuleSheaf.{u, v, r} B X Λ)]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, v, r} B Y Λ)]

include hw in
/-- **The derived trace of Stacks 0GKH part (3).** The `Λ`-linear `f^{-1}` and `f_!` are exact,
so each induces a functor on unbounded derived categories of sheaves of `Λ`-modules, and the
sheaf-level trace induces a natural transformation `f^{-1} ⋙ f_! ⟶ id` between them; its
component at an object `K` of `D(Y_étale, Λ)` is `Tr_{f, w, K} : f_! f^{-1}K ⟶ K`. -/
public def derivedWeightedTraceMod :
    (pullbackMod.{u, v, r} B Λ f).mapDerivedCategory ⋙
        (fShriekMod.{u, v, r} B Λ f).mapDerivedCategory ⟶
      𝟭 (DerivedCategory (ModuleSheaf.{u, v, r} B Y Λ)) :=
  derivedWeightedTrace.{u, v, t, r} B Λ f (pullbackMod.{u, v, r} B Λ f)
    (pullbackModForgetIso.{u, v, r} B Λ f) w (weightedTraceMod.{u, v, r} B Λ f hw)
    (weightedTraceMod_hasWeightedTraceStalksMod.{u, v, r} B Λ f hw)

end Trace

/-! ### The comparisons attached to a cartesian square at `Λ`-coefficients -/

section Square

variable (B : BigEtaleSite.{u}) (Λ : Type u) [Ring Λ] {X Y X' Y' : B.Scheme}
  (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map f')] [LocallyQuasiFinite (B.inclusion.map f')]
  (sq : IsPullback p f' f g)

/-- **The base-change isomorphism of Stacks 0F5J at `Λ`-module coefficients**,
`g^{-1}f_!N ≅ f'_!p^{-1}N`: the lift of the abelian base-change isomorphism. -/
public def fShriekBaseChangeMod :
    fShriekMod.{u, u + 1, u} B Λ f ⋙ pullbackMod.{u, u + 1, u} B Λ g ≅
      pullbackMod.{u, u + 1, u} B Λ p ⋙ fShriekMod.{u, u + 1, u} B Λ f' :=
  Stacks.ModuleCatLift.moduleLiftNatIso.{u + 1, u, _, _, _, _} Λ
    (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B Y'.obj Y'.property)
    (fShriekFunctor.{u, u + 1} B f ⋙ abPullback.{u, u + 1} B g)
    (abPullback.{u, u + 1} B p ⋙ fShriekFunctor.{u, u + 1} B f')
    (fShriekBaseChangeNatIso.{u} B p f' f g sq)

/-- **The comparison of the two iterated inverse images of a cartesian square at `Λ`-module
coefficients**, `p^{-1}f^{-1}M ≅ f'^{-1}g^{-1}M`: the lift of the abelian comparison
`AlgebraicGeometry.SmallEtale.inverseImageSquareIso`. -/
public def inverseImageSquareMod :
    pullbackMod.{u, u + 1, u} B Λ f ⋙ pullbackMod.{u, u + 1, u} B Λ p ≅
      pullbackMod.{u, u + 1, u} B Λ g ⋙ pullbackMod.{u, u + 1, u} B Λ f' :=
  Stacks.ModuleCatLift.moduleLiftNatIso.{u + 1, u, _, _, _, _} Λ
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X'.obj X'.property)
    (abPullback.{u, u + 1} B f ⋙ abPullback.{u, u + 1} B p)
    (abPullback.{u, u + 1} B g ⋙ abPullback.{u, u + 1} B f')
    (inverseImageSquareIso.{u} B p f' f g sq)

/-- The morphism of abelian sheaves underlying a component of
`AlgebraicGeometry.SmallEtale.fShriekBaseChangeMod` is the corresponding component of the abelian
base-change isomorphism of Stacks 0F5J. -/
@[simp]
public lemma forgetModuleSheaf_map_fShriekBaseChangeMod_hom_app
    (n : ModuleSheaf.{u, u + 1, u} B X Λ) :
    (forgetModuleSheaf.{u, u + 1, u} B Y' Λ).map
        ((fShriekBaseChangeMod.{u} B Λ p f' f g sq).hom.app n) =
      (fShriekBaseChangeNatIso.{u} B p f' f g sq).hom.app
        ((forgetModuleSheaf.{u, u + 1, u} B X Λ).obj n) :=
  rfl

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map f')] [LocallyQuasiFinite (B.inclusion.map f')] in
/-- The morphism of abelian sheaves underlying a component of
`AlgebraicGeometry.SmallEtale.inverseImageSquareMod` is the corresponding component of the
abelian comparison `AlgebraicGeometry.SmallEtale.inverseImageSquareIso`. -/
@[simp]
public lemma forgetModuleSheaf_map_inverseImageSquareMod_hom_app
    (M : ModuleSheaf.{u, u + 1, u} B Y Λ) :
    (forgetModuleSheaf.{u, u + 1, u} B X' Λ).map
        ((inverseImageSquareMod.{u} B Λ p f' f g sq).hom.app M) =
      (inverseImageSquareIso.{u} B p f' f g sq).hom.app
        ((forgetModuleSheaf.{u, u + 1, u} B Y Λ).obj M) :=
  rfl

/-- **The base-change isomorphism at `Λ`-coefficients induces the one of Stacks 0F5J on
underlying abelian sheaves**, through the identifications of the `Λ`-linear `f_!` and `f^{-1}`
with the abelian ones. -/
public theorem fShriekBaseChangeMod_forget (n : ModuleSheaf.{u, u + 1, u} B X Λ) :
    (forgetModuleSheaf.{u, u + 1, u} B Y' Λ).map
          ((fShriekBaseChangeMod.{u} B Λ p f' f g sq).hom.app n) ≫
        (fShriekModForgetIso.{u, u + 1, u} B Λ f').hom.app
          ((pullbackMod.{u, u + 1, u} B Λ p).obj n) ≫
        (fShriekFunctor.{u, u + 1} B f').map
          ((pullbackModForgetIso.{u, u + 1, u} B Λ p).hom.app n) =
      (pullbackModForgetIso.{u, u + 1, u} B Λ g).hom.app
          ((fShriekMod.{u, u + 1, u} B Λ f).obj n) ≫
        (abPullback.{u, u + 1} B g).map
          ((fShriekModForgetIso.{u, u + 1, u} B Λ f).hom.app n) ≫
        (fShriekBaseChangeNatIso.{u} B p f' f g sq).hom.app
          ((forgetModuleSheaf.{u, u + 1, u} B X Λ).obj n) := by
  have h := map_eq_id_of_eq_id (fShriekFunctor.{u, u + 1} B f')
    (pullbackModForgetIso_hom_app.{u, u + 1, u} B Λ p n)
  have h' := map_eq_id_of_eq_id (abPullback.{u, u + 1} B g)
    (fShriekModForgetIso_hom_app.{u, u + 1, u} B Λ f n)
  erw [h, h', fShriekModForgetIso_hom_app, pullbackModForgetIso_hom_app]
  exact comp_id_comp_id _

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map f')] [LocallyQuasiFinite (B.inclusion.map f')] in
/-- **The comparison of the two iterated inverse images at `Λ`-coefficients induces the abelian
one on underlying abelian sheaves**, through the identifications of the `Λ`-linear inverse images
with the abelian ones. -/
public theorem inverseImageSquareMod_forget (M : ModuleSheaf.{u, u + 1, u} B Y Λ) :
    (forgetModuleSheaf.{u, u + 1, u} B X' Λ).map
          ((inverseImageSquareMod.{u} B Λ p f' f g sq).hom.app M) ≫
        (pullbackModForgetIso.{u, u + 1, u} B Λ f').hom.app
          ((pullbackMod.{u, u + 1, u} B Λ g).obj M) ≫
        (abPullback.{u, u + 1} B f').map
          ((pullbackModForgetIso.{u, u + 1, u} B Λ g).hom.app M) =
      (pullbackModForgetIso.{u, u + 1, u} B Λ p).hom.app
          ((pullbackMod.{u, u + 1, u} B Λ f).obj M) ≫
        (abPullback.{u, u + 1} B p).map
          ((pullbackModForgetIso.{u, u + 1, u} B Λ f).hom.app M) ≫
        (inverseImageSquareIso.{u} B p f' f g sq).hom.app
          ((forgetModuleSheaf.{u, u + 1, u} B Y Λ).obj M) := by
  have h := map_eq_id_of_eq_id (abPullback.{u, u + 1} B f')
    (pullbackModForgetIso_hom_app.{u, u + 1, u} B Λ g M)
  have h' := map_eq_id_of_eq_id (abPullback.{u, u + 1} B p)
    (pullbackModForgetIso_hom_app.{u, u + 1, u} B Λ f M)
  erw [h, h', pullbackModForgetIso_hom_app, pullbackModForgetIso_hom_app]
  exact comp_id_comp_id _

end Square

/-! ### Stacks 0GKH, part (3) -/

section Tagged

variable (B : BigEtaleSite.{u}) (Λ : Type u) [Ring Λ] {X Y X' Y' : B.Scheme}
  (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (sq : IsPullback p f' f g)
  [HasDerivedCategory.{t} (ModuleSheaf.{u, u + 1, u} B X Λ)]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, u + 1, u} B Y Λ)]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, u + 1, u} B X' Λ)]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, u + 1, u} B Y' Λ)]

omit [HasDerivedCategory.{t} (ModuleSheaf.{u, u + 1, u} B X' Λ)] in
include sq in
/-- **The weighted trace with coefficients in a ring, on unbounded derived categories.** Let
`f : X ⟶ Y` be locally quasi-finite, let `w` be a weighting of `f`, let `Λ` be a ring, and let

```
X' --p--> X
|f'       |f
Y' --g--> Y
```

be a cartesian square. Then:

* for every sheaf of `Λ`-modules `M` on the small étale site of `Y` the morphism
  `Tr_{f, w, M} : f_! f^{-1}M ⟶ M` of `AlgebraicGeometry.SmallEtale.weightedTraceMod` has the
  behaviour on geometric stalks by which Stacks 0GKG characterises the trace of `(f, w)`, and it
  is the only morphism of sheaves of `Λ`-modules with that behaviour;
* `f^{-1}` and `f_!` are exact on sheaves of `Λ`-modules, so each induces a functor on unbounded
  derived categories, and the trace maps induce a natural transformation
  `Tr_{f, w} : f_! f^{-1} ⟶ id` of `D(Y_étale, Λ)`, whose component at `K` is
  `Tr_{f, w, K} : f_! f^{-1}K ⟶ K`;
* that transformation is **functorial in `K`**: every naturality square commutes;
* it **restricts to the sheaf-level trace**: it is the derived form of the natural
  transformation whose component at a sheaf of `Λ`-modules `M` is `Tr_{f, w, M}`, read through
  the canonical identification of the derived functor of `f^{-1} ⋙ f_!` with the composite of
  the derived functors and of the derived functor of the identity with the identity;
* it is **compatible with arbitrary base change**: the two comparisons attached to the square at
  `Λ`-coefficients — the base-change isomorphism `g^{-1}f_!N ≅ f'_!p^{-1}N` of Stacks 0F5J and
  the comparison `p^{-1}f^{-1}M ≅ f'^{-1}g^{-1}M` of the two iterated inverse images — carry the
  derived trace of `(f, w)` to the derived trace of `(f', w ∘ p)`, both whiskered by the derived
  `g^{-1}`;
* and the weight attached to the base change is the right one: `w ∘ p` is a weighting of `f'`,
  which is Stacks 0F3B.

Every object of the statement is constructed: the `Λ`-linear inverse images along the four
morphisms of the square are `AlgebraicGeometry.SmallEtale.pullbackMod`, the two comparisons are
`AlgebraicGeometry.SmallEtale.fShriekBaseChangeMod` and
`AlgebraicGeometry.SmallEtale.inverseImageSquareMod`, and the trace maps at `Λ`-coefficients are
`AlgebraicGeometry.SmallEtale.weightedTraceMod` for `(f, w)` and for `(f', w ∘ p)`.

The finite-type and quasi-finiteness hypotheses on the base change `f'` are supplied from the
square, so the hypotheses are those of the source: `f` locally quasi-finite, `w` a weighting of
`f`, and the square cartesian.

The coefficient universes are the ones at which the base-change isomorphism of Stacks 0F5J is
available: the abelian étale sheaves have coefficients in `AddCommGrpCat.{u + 1}`, so the sheaves
of `Λ`-modules are taken at `ModuleSheaf.{u, u + 1, u}` with `Λ : Type u`. -/
@[stacks 0GKH "part (3), the weighted trace with coefficients in a ring Λ on unbounded derived \
categories, for an arbitrary cartesian square with locally quasi-finite vertical morphism and a \
weighting w of it: for every K in D(Y_étale, Λ) a morphism Tr_{f,w,K} : f_!f^{-1}K ⟶ K, \
functorial in K, restricting to the sheaf-level trace of 0GKG, and compatible with arbitrary \
base change. The Λ-linear inverse images along f, f', g and p are \
`AlgebraicGeometry.SmallEtale.pullbackMod`, the lift of the abelian inverse image of 03Q1; the \
two comparisons attached to the square are the lifts \
`AlgebraicGeometry.SmallEtale.fShriekBaseChangeMod` and \
`AlgebraicGeometry.SmallEtale.inverseImageSquareMod` of the isomorphism of 0F5J and of the \
comparison of the two iterated inverse images; the trace maps at Λ-coefficients are \
`AlgebraicGeometry.SmallEtale.weightedTraceMod`, the trace of 0GKG read as a morphism of sheaves \
of Λ-modules, which the first two clauses show to have the characterising behaviour on geometric \
stalks of 0GKG and to be the unique morphism with it. The base-change square at Λ-coefficients \
is deduced from part (2) at abelian coefficients, and the derived square is its image under the \
deriving operation. The finite-type and quasi-finiteness conditions on the base change are \
supplied from the square, so the hypotheses are those of the source. The coefficient universes \
are those at which 0F5J is available: ModuleSheaf.{u, u+1, u} with Λ : Type u.",
  sga "4 XVII 6.2.5" "more general"]
public theorem derivedWeightedTraceMod_spec {w : X.obj → ℤ}
    (hw : IsWeighting (B.inclusion.map f) w) :
    letI := locallyOfFiniteType_of_isPullback B p f' f g sq
    letI := locallyQuasiFinite_of_isPullback B p f' f g sq
    (∀ M : ModuleSheaf.{u, u + 1, u} B Y Λ,
        HasWeightedTraceStalksMod.{u, u + 1, u} B Λ f (pullbackMod.{u, u + 1, u} B Λ f)
          (pullbackModForgetIso.{u, u + 1, u} B Λ f) w M
          (weightedTraceMod.{u, u + 1, u} B Λ f hw M)) ∧
      (∀ (M : ModuleSheaf.{u, u + 1, u} B Y Λ)
          (σ : (fShriekMod.{u, u + 1, u} B Λ f).obj
            ((pullbackMod.{u, u + 1, u} B Λ f).obj M) ⟶ M),
          HasWeightedTraceStalksMod.{u, u + 1, u} B Λ f (pullbackMod.{u, u + 1, u} B Λ f)
            (pullbackModForgetIso.{u, u + 1, u} B Λ f) w M σ →
            σ = weightedTraceMod.{u, u + 1, u} B Λ f hw M) ∧
      (∀ (K K' : DerivedCategory (ModuleSheaf.{u, u + 1, u} B Y Λ)) (ψ : K ⟶ K'),
          ((pullbackMod.{u, u + 1, u} B Λ f).mapDerivedCategory ⋙
              (fShriekMod.{u, u + 1, u} B Λ f).mapDerivedCategory).map ψ ≫
              (derivedWeightedTraceMod.{u, u + 1, t, u} B Λ f hw).app K' =
            (derivedWeightedTraceMod.{u, u + 1, t, u} B Λ f hw).app K ≫ ψ) ∧
      (derivedWeightedTraceMod.{u, u + 1, t, u} B Λ f hw =
          (Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso
              (pullbackMod.{u, u + 1, u} B Λ f) (fShriekMod.{u, u + 1, u} B Λ f)).inv ≫
            NatTrans.mapDerivedCategory
              (weightedTraceModTrans.{u, u + 1, u} B Λ f hw) ≫
            (Functor.mapDerivedCategoryIdIso _).hom) ∧
      (∀ M : ModuleSheaf.{u, u + 1, u} B Y Λ,
          (weightedTraceModTrans.{u, u + 1, u} B Λ f hw).app M =
            weightedTraceMod.{u, u + 1, u} B Λ f hw M) ∧
      (NatTrans.mapDerivedCategory
            (traceBaseChangeComparison.{u, u + 1, u} B Λ f' f (pullbackMod.{u, u + 1, u} B Λ f)
              (pullbackMod.{u, u + 1, u} B Λ f') (pullbackMod.{u, u + 1, u} B Λ g)
              (pullbackMod.{u, u + 1, u} B Λ p) (fShriekBaseChangeMod.{u} B Λ p f' f g sq)
              (inverseImageSquareMod.{u} B Λ p f' f g sq)).hom ≫
          (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
            (pullbackMod.{u, u + 1, u} B Λ g)
            (pullbackMod.{u, u + 1, u} B Λ f' ⋙ fShriekMod.{u, u + 1, u} B Λ f')).hom ≫
          Functor.whiskerLeft (pullbackMod.{u, u + 1, u} B Λ g).mapDerivedCategory
            (NatTrans.mapDerivedCategory
              (weightedTraceModTrans.{u, u + 1, u} B Λ f'
                (AlgebraicGeometry.IsWeighting.comp_of_isPullback hw (sq.map B.inclusion)))) ≫
          (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
            (pullbackMod.{u, u + 1, u} B Λ g)
            (𝟭 (ModuleSheaf.{u, u + 1, u} B Y' Λ))).inv =
        (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
            (pullbackMod.{u, u + 1, u} B Λ f ⋙ fShriekMod.{u, u + 1, u} B Λ f)
            (pullbackMod.{u, u + 1, u} B Λ g)).hom ≫
          Functor.whiskerRight
            (NatTrans.mapDerivedCategory (weightedTraceModTrans.{u, u + 1, u} B Λ f hw))
            (pullbackMod.{u, u + 1, u} B Λ g).mapDerivedCategory ≫
          (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
            (𝟭 (ModuleSheaf.{u, u + 1, u} B Y Λ))
            (pullbackMod.{u, u + 1, u} B Λ g)).inv) ∧
      AlgebraicGeometry.IsWeighting (B.inclusion.map f') (w ∘ B.inclusion.map p) := by
  let := locallyOfFiniteType_of_isPullback B p f' f g sq
  let := locallyQuasiFinite_of_isPullback B p f' f g sq
  obtain ⟨hnat, heq, happ, hbc, hwt⟩ :=
    derivedWeightedTrace_spec_of_lifts.{u, t} B Λ p f' f g sq
      (pullbackMod.{u, u + 1, u} B Λ f) (pullbackModForgetIso.{u, u + 1, u} B Λ f)
      (pullbackMod.{u, u + 1, u} B Λ f') (pullbackModForgetIso.{u, u + 1, u} B Λ f')
      (pullbackMod.{u, u + 1, u} B Λ g) (pullbackModForgetIso.{u, u + 1, u} B Λ g)
      (pullbackMod.{u, u + 1, u} B Λ p) (pullbackModForgetIso.{u, u + 1, u} B Λ p)
      (fShriekBaseChangeMod.{u} B Λ p f' f g sq) (inverseImageSquareMod.{u} B Λ p f' f g sq)
      (fShriekBaseChangeMod_forget.{u} B Λ p f' f g sq)
      (inverseImageSquareMod_forget.{u} B Λ p f' f g sq) w
      (weightedTraceMod.{u, u + 1, u} B Λ f hw)
      (weightedTraceMod_hasWeightedTraceStalksMod.{u, u + 1, u} B Λ f hw)
      (weightedTraceMod.{u, u + 1, u} B Λ f'
        (AlgebraicGeometry.IsWeighting.comp_of_isPullback hw (sq.map B.inclusion)))
      (weightedTraceMod_hasWeightedTraceStalksMod.{u, u + 1, u} B Λ f'
        (AlgebraicGeometry.IsWeighting.comp_of_isPullback hw (sq.map B.inclusion)))
  exact ⟨weightedTraceMod_hasWeightedTraceStalksMod.{u, u + 1, u} B Λ f hw,
    fun _ _ hσ => eq_weightedTraceMod.{u, u + 1, u} B Λ f hw _ hσ,
    hnat, heq, happ, hbc, hwt hw⟩

end Tagged

end AlgebraicGeometry.SmallEtale

end
