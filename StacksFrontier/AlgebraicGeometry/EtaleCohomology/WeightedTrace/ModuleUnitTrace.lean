module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.IntegralTraceStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.ModuleWeightedTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.TensorUnitConstantSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceProperties

/-!
# The trace on the constant sheaf as a trace on the monoidal unit

Let `f : X ⟶ Y` be a morphism of a big étale site which is locally of finite type and locally
quasi-finite as a morphism of schemes, and let `w` be a weighting of it. The trace map
`Tr : f_!Z ⟶ Z` of [Stacks, Tag 0GKG] on the constant abelian sheaf with value `Z = ULift ℤ`
is built in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.IntegralTracePresheaf`, and its
stalks are computed in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.IntegralTraceStalk`. The
projection formula of [Stacks, Tag 0GKF], from which the trace on an arbitrary sheaf is
obtained, lives in the world of sheaves of `Λ`-modules. At `Λ = ULift ℤ` the two worlds are the
same, by the dictionary of
`StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleIntEquivalence`, and this file carries the
trace across: it produces a morphism `f_!(𝟙_) ⟶ 𝟙_` of sheaves of `ULift ℤ`-modules whose
stalks are the weighted sum over the geometric fibre, which is the hypothesis
`AlgebraicGeometry.SmallEtale.ModHasUnitTraceStalks` that
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.ModuleWeightedTrace` carries.

## Main definitions

* `AlgebraicGeometry.SmallEtale.forgetUnitTrace` — the trace on the abelian sheaf underlying the
  monoidal unit: the trace `AlgebraicGeometry.SmallEtale.integralTrace` on the constant sheaf,
  read through the identification
  `AlgebraicGeometry.SmallEtale.forgetTensorUnitIsoLocallyConstantSheafAb` of the unit with the
  sheaf of locally constant functions and through the comparison
  `AlgebraicGeometry.SmallEtale.fShriekModForget_natIso` of the two `f_!`.
* `AlgebraicGeometry.SmallEtale.modUnitTrace` — **the trace on the monoidal unit**,
  `f_!(𝟙_) ⟶ 𝟙_`: the preimage of `forgetUnitTrace` under the forgetful functor, which is full.

## Main results

* `AlgebraicGeometry.SmallEtale.forgetModuleSheaf_map_modUnitTrace` — the underlying morphism of
  abelian sheaves of the trace on the monoidal unit is `forgetUnitTrace`.
* `AlgebraicGeometry.SmallEtale.modHasUnitTraceStalks_modUnitTrace` — **the stalks of the trace
  on the monoidal unit are the weighted sum over the geometric fibre**, which is the
  characterisation `AlgebraicGeometry.SmallEtale.ModHasUnitTraceStalks` of [Stacks, Tag 0GKG].

## Implementation notes

The whole transport is a computation with abelian sheaves: the equation of
`ModHasUnitTraceStalks` is an equation of morphisms of `Λ`-modules, the forgetful functor to
abelian groups is faithful, and every `Λ`-linear ingredient of the equation forgets to its
abelian counterpart *on the nose* — `AlgebraicGeometry.SmallEtale.moduleFShriekStalkIso_forget₂`
for the stalk decomposition of Stacks 0F5F,
`AlgebraicGeometry.SmallEtale.forget₂_obj_moduleFiberStalks_obj` and
`AlgebraicGeometry.SmallEtale.forget₂_map_moduleFiberStalks_map` for the direct sum of the
stalks over the geometric fibre, and `Stacks.ModuleCatLift.forget₂_map_valueLift_map` for the
stalk functor itself. The two comparisons
`AlgebraicGeometry.SmallEtale.moduleEtaleStalkIso` of the two `Λ`-module structures on a stalk,
which are the only ingredients that do *not* disappear, are kept explicit throughout and
cancelled at the very end, by a private lemma about composites in an abstract category.

The resulting abelian identity, also private, is the content of the file: it is
checked on each summand of the stalk decomposition, where
`AlgebraicGeometry.SmallEtale.integralTrace_stalk` supplies the left-hand side and
`AlgebraicGeometry.SmallEtale.modUnitWeightedSum_modFiberStalkOf` the right-hand side, and the
two are matched by
`AlgebraicGeometry.SmallEtale.etaleStalkLocallyConstantMapsAbIso_tensorUnit_eps`, the
compatibility of the monoidal and the concrete identification of the stalk of the unit with
`Λ`, used once above at the point of the geometric fibre and once below at the geometric point.

Nothing here carries a `stacks` attribute: the trace map and its stalks are the ones already
attributed in `IntegralTracePresheaf` and `IntegralTraceStalk`, and what is added is their
transport along a dictionary between two formalisations of the same coefficients.

## References

* [Stacks Project, Tag 0GKG](https://stacks.math.columbia.edu/tag/0GKG)
* [Stacks Project, Tag 0GKF](https://stacks.math.columbia.edu/tag/0GKF)
* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

/-! ### Three bookkeeping facts about composites -/

/-- Two isomorphisms with the same underlying morphism have the same inverse. -/
private theorem iso_inv_congr {A : Type*} [Category A] {P Q : A} {α β : P ≅ Q}
    (h : α.hom = β.hom) : α.inv = β.inv :=
  congrArg Iso.inv (Iso.ext h)

/-- A composite of four morphisms, the first two of which and the middle two of which are known
in closed form. -/
private theorem comp_four_of_inv_comp {A : Type*} [Category A] {T₀ T₁ S₁ S₂ S₃ S₄ : A}
    (k : T₀ ⟶ S₁) (a : S₁ ⟶ S₂) (b : S₂ ⟶ S₃) (c : S₃ ⟶ S₄) (m : T₀ ⟶ T₁) (k' : T₁ ⟶ S₂)
    (n : T₁ ⟶ S₃) (h₁ : k ≫ a = m ≫ k') (h₂ : k' ≫ b = n) :
    k ≫ a ≫ b ≫ c = m ≫ n ≫ c := by
  rw [← Category.assoc k a, h₁, Category.assoc, ← Category.assoc k' b, h₂]

/-- **The cancellation at the heart of the transport.** A composite of four morphisms whose
middle two are known in closed form after the last one has been commuted past, and whose two
outer factors are cancelled by the identifications they came with. -/
private theorem comp_chain_cancel {A : Type*} [Category A] {T₀ T₁ S₁ S₂ S₃ M : A}
    (d' : T₀ ⟶ T₁) (d : T₁ ⟶ T₀) (p : T₁ ⟶ S₁) (e : S₁ ⟶ S₂) (t : S₂ ⟶ M) (g : S₁ ⟶ S₃)
    (e' : S₃ ⟶ M) (e'' : M ⟶ S₃) (W : T₀ ⟶ M) (hnat : e ≫ t = g ≫ e')
    (hcore : p ≫ g = d ≫ W ≫ e'') (hd : d' ≫ d = 𝟙 T₀) (he : e'' ≫ e' = 𝟙 M) :
    d' ≫ p ≫ e ≫ t = W := by
  rw [hnat, ← Category.assoc p g, hcore, Category.assoc d (W ≫ e'') e', Category.assoc W e'' e',
    he, Category.comp_id, ← Category.assoc d' d W, hd, Category.id_comp]

section UnitTrace

attribute [local instance] moduleSheafMonoidal
attribute [local instance] SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat
attribute [local instance] hasLimitsOfSizeModuleCatSmall
attribute [local instance] preservesFilteredColimitsTensorLeftSmall
attribute [local instance] preservesFilteredColimitsTensorRightSmall
attribute [local instance] modStalkMonoidal

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  {w : X.obj → ℤ} (hw : IsWeighting (B.inclusion.map f) w)

/-! ### The stalk of the monoidal unit -/

/-- **The concrete identification of the stalk of the monoidal unit, from the monoidal one.**
If the germ `z` is carried by the comparison of the two `Λ`-module structures on the stalk to
the unit constraint `ε` at `a`, then the stalk of the identification of the unit with the sheaf
of locally constant functions carries `z` to `a`. -/
private theorem etaleStalkLocallyConstantMapsAbIso_hom_stalkMap_tensorUnit (S : B.Scheme)
    (t : GeometricPoint S.obj)
    (a : ↑(𝟙_ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))))
    (z : ↑(etaleStalk B S.obj S.property t
      ((forgetModuleSheaf.{u, v, max (u + 1) v} B S
          (AddCommGrpCat.ULiftInt.{max (u + 1) v})).obj (𝟙_ _)).obj))
    (hz : (moduleEtaleStalkIso.{u, v, max (u + 1) v} B
          (AddCommGrpCat.ULiftInt.{max (u + 1) v}) S t).hom.app (𝟙_ _) z =
      Functor.LaxMonoidal.ε (modStalkFunctor.{u, v, max (u + 1) v} B
        (AddCommGrpCat.ULiftInt.{max (u + 1) v}) S t) a) :
    (etaleStalkLocallyConstantMapsAbIso.{u, v} B S.obj S.property t
        (AddCommGrpCat.ULiftInt.{max (u + 1) v})).hom
      (colim.map (Functor.whiskerLeft
        (CategoryOfElements.π (geometricPointFiber B S.obj S.property t)).op
        (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B S
          (AddCommGrpCat.ULiftInt.{max (u + 1) v})).hom.hom) z) = a := by
  have hz' : (moduleEtaleStalkIso.{u, v, max (u + 1) v} B
        (AddCommGrpCat.ULiftInt.{max (u + 1) v}) S t).inv.app (𝟙_ _)
      (Functor.LaxMonoidal.ε (modStalkFunctor.{u, v, max (u + 1) v} B
        (AddCommGrpCat.ULiftInt.{max (u + 1) v}) S t) a) = z := by
    rw [← hz]
    exact Iso.hom_inv_id_apply ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B
      (AddCommGrpCat.ULiftInt.{max (u + 1) v}) S t).app (𝟙_ _)) z
  exact Eq.trans
    (congrArg (fun y => (etaleStalkLocallyConstantMapsAbIso.{u, v} B S.obj S.property t
        (AddCommGrpCat.ULiftInt.{max (u + 1) v})).hom
      (colim.map (Functor.whiskerLeft
        (CategoryOfElements.π (geometricPointFiber B S.obj S.property t)).op
        (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B S
          (AddCommGrpCat.ULiftInt.{max (u + 1) v})).hom.hom) y)) hz'.symm)
    (etaleStalkLocallyConstantMapsAbIso_tensorUnit_eps.{u, v} B S
      (AddCommGrpCat.ULiftInt.{max (u + 1) v}) t a)

/-- **The monoidal identification of the stalk of the monoidal unit, read concretely.** The
germ of the unit constraint `ε` at `a` is, through the comparison of the two `Λ`-module
structures on the stalk, the germ of the constant function with value `a`. -/
private theorem moduleEtaleStalkIso_inv_app_eps (S : B.Scheme) (t : GeometricPoint S.obj)
    (a : ↑(𝟙_ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v})))) :
    (moduleEtaleStalkIso.{u, v, max (u + 1) v} B
        (AddCommGrpCat.ULiftInt.{max (u + 1) v}) S t).inv.app (𝟙_ _)
      (Functor.LaxMonoidal.ε (modStalkFunctor.{u, v, max (u + 1) v} B
        (AddCommGrpCat.ULiftInt.{max (u + 1) v}) S t) a) =
      colim.map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B S.obj S.property t)).op
          (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B S
            (AddCommGrpCat.ULiftInt.{max (u + 1) v})).inv.hom)
        ((etaleStalkLocallyConstantMapsAbIso.{u, v} B S.obj S.property t
          (AddCommGrpCat.ULiftInt.{max (u + 1) v})).inv a) := by
  have key := etaleStalkLocallyConstantMapsAbIso_hom_stalkMap_tensorUnit.{u, v} B S t a _
    (Iso.inv_hom_id_apply ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B
      (AddCommGrpCat.ULiftInt.{max (u + 1) v}) S t).app (𝟙_ _)) _)
  exact Eq.trans
    (Iso.hom_inv_id_apply (((geometricPointSitePoint B S.obj S.property t).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).mapIso
      (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B S
        (AddCommGrpCat.ULiftInt.{max (u + 1) v}))) _).symm
    (congrArg (fun y => colim.map (Functor.whiskerLeft
      (CategoryOfElements.π (geometricPointFiber B S.obj S.property t)).op
      (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B S
        (AddCommGrpCat.ULiftInt.{max (u + 1) v})).inv.hom) y)
      ((Iso.hom_inv_id_apply _ _).symm.trans (congrArg (fun y =>
        (etaleStalkLocallyConstantMapsAbIso.{u, v} B S.obj S.property t
          (AddCommGrpCat.ULiftInt.{max (u + 1) v})).inv y) key)))

/-! ### The trace on the abelian sheaf underlying the monoidal unit -/

/-- **The trace on the abelian sheaf underlying the monoidal unit.** The trace
`AlgebraicGeometry.SmallEtale.integralTrace` on the constant sheaf, read at both ends through
the identification of the monoidal unit with the sheaf of locally constant functions and, at the
source, through the comparison of the `ULift ℤ`-linear `f_!` with the `f_!` of Stacks 0F6R. -/
public def forgetUnitTrace :
    (forgetModuleSheaf.{u, v, max (u + 1) v} B Y (AddCommGrpCat.ULiftInt.{max (u + 1) v})).obj
        ((fShriekMod.{u, v, max (u + 1) v} B
          (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj (𝟙_ _)) ⟶
      (forgetModuleSheaf.{u, v, max (u + 1) v} B Y
        (AddCommGrpCat.ULiftInt.{max (u + 1) v})).obj (𝟙_ _) :=
  (fShriekModForget_natIso.{u, v} B f).hom.app (𝟙_ _) ≫
    (fShriekFunctor.{u, v} B f).map
      (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B X
        (AddCommGrpCat.ULiftInt.{max (u + 1) v})).hom ≫
      integralTrace.{u, v} B f hw ≫
        (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B Y
          (AddCommGrpCat.ULiftInt.{max (u + 1) v})).inv

/-- The comparison of the two `f_!` at the monoidal unit is the identity: the `ULift ℤ`-linear
`f_!` is a lift of the `f_!` of Stacks 0F6R, not a transport of it. -/
private theorem fShriekModForget_natIso_hom_app_tensorUnit :
    (fShriekModForget_natIso.{u, v} B f).hom.app
        (𝟙_ (ModuleSheaf.{u, v, max (u + 1) v} B X
          (AddCommGrpCat.ULiftInt.{max (u + 1) v}))) =
      𝟙 ((forgetModuleSheaf.{u, v, max (u + 1) v} B Y
        (AddCommGrpCat.ULiftInt.{max (u + 1) v})).obj
          ((fShriekMod.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj (𝟙_ _))) :=
  rfl

/-- The trace on the abelian sheaf underlying the monoidal unit, with the comparison of the two
`f_!` cancelled. -/
private theorem forgetUnitTrace_eq :
    forgetUnitTrace.{u, v} B f hw =
      (fShriekFunctor.{u, v} B f).map
          (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B X
            (AddCommGrpCat.ULiftInt.{max (u + 1) v})).hom ≫
        integralTrace.{u, v} B f hw ≫
          (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B Y
            (AddCommGrpCat.ULiftInt.{max (u + 1) v})).inv := by
  have h : forgetUnitTrace.{u, v} B f hw =
      (fShriekModForget_natIso.{u, v} B f).hom.app (𝟙_ _) ≫
        (fShriekFunctor.{u, v} B f).map
            (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B X
              (AddCommGrpCat.ULiftInt.{max (u + 1) v})).hom ≫
          integralTrace.{u, v} B f hw ≫
            (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B Y
              (AddCommGrpCat.ULiftInt.{max (u + 1) v})).inv :=
    rfl
  rw [h, fShriekModForget_natIso_hom_app_tensorUnit.{u, v} B f]
  exact Category.id_comp _

/-! ### The trace on the monoidal unit -/

/-- The functor forgetting the `ULift ℤ`-module structure of an étale sheaf of modules is full,
being the functor of the equivalence
`AlgebraicGeometry.SmallEtale.abelianSheafUliftIntEquivalence`. -/
public instance full_forgetModuleSheafUliftInt (S : B.Scheme) :
    (forgetModuleSheaf.{u, v, max (u + 1) v} B S
      (AddCommGrpCat.ULiftInt.{max (u + 1) v})).Full :=
  inferInstanceAs ((abelianSheafUliftIntEquivalence.{u, v} B S).functor.Full)

/-- **The trace on the monoidal unit**, `f_!(𝟙_) ⟶ 𝟙_`: the unique morphism of étale sheaves of
`ULift ℤ`-modules whose underlying morphism of abelian sheaves is
`AlgebraicGeometry.SmallEtale.forgetUnitTrace`. -/
public def modUnitTrace :
    (fShriekMod.{u, v, max (u + 1) v} B
        (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj (𝟙_ _) ⟶ 𝟙_ _ :=
  (forgetModuleSheaf.{u, v, max (u + 1) v} B Y
    (AddCommGrpCat.ULiftInt.{max (u + 1) v})).preimage (forgetUnitTrace.{u, v} B f hw)

/-- **The trace on the monoidal unit lifts the trace on the constant sheaf.** -/
public theorem forgetModuleSheaf_map_modUnitTrace :
    (forgetModuleSheaf.{u, v, max (u + 1) v} B Y
        (AddCommGrpCat.ULiftInt.{max (u + 1) v})).map (modUnitTrace.{u, v} B f hw) =
      forgetUnitTrace.{u, v} B f hw :=
  Functor.map_preimage _ _

/-! ### The stalk of the trace on the monoidal unit -/

/-- The stalk decomposition of `f_!` at the monoidal unit, unfolded into its three factors. -/
private theorem modShriekStalkIso_trans_moduleFiberStalksIso_inv (s : GeometricPoint Y.obj) :
    ((modShriekStalkIso.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s).app (𝟙_ _) ≪≫
        moduleFiberStalksIso.{u, v, max (u + 1) v} B
          (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s (𝟙_ _)).inv =
      (moduleFiberStalksIso.{u, v, max (u + 1) v} B
          (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s (𝟙_ _)).inv ≫
        (moduleFShriekStalkIso.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s (𝟙_ _)).inv ≫
          (moduleEtaleStalkIso.{u, v, max (u + 1) v} B
              (AddCommGrpCat.ULiftInt.{max (u + 1) v}) Y s).hom.app
            ((fShriekMod.{u, v, max (u + 1) v} B
              (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj (𝟙_ _)) :=
  rfl

/-- The `ULift ℤ`-linear stalk decomposition of Stacks 0F5F forgets to the abelian one, in the
backward direction. -/
private theorem forget₂_map_moduleFShriekStalkIso_inv (s : GeometricPoint Y.obj) :
    (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
          AddCommGrpCat.{max (u + 1) v}).map
        (moduleFShriekStalkIso.{u, v, max (u + 1) v} B
          (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s (𝟙_ _)).inv =
      (fShriekStalkIso.{u, v} B f s
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B X
          (AddCommGrpCat.ULiftInt.{max (u + 1) v})).obj (𝟙_ _))).inv := by
  have h : ((forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
          AddCommGrpCat.{max (u + 1) v}).mapIso
        (moduleFShriekStalkIso.{u, v, max (u + 1) v} B
          (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s (𝟙_ _))).hom =
      (fShriekStalkIso.{u, v} B f s
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B X
          (AddCommGrpCat.ULiftInt.{max (u + 1) v})).obj (𝟙_ _))).hom :=
    moduleFShriekStalkIso_forget₂.{u, v, max (u + 1) v} B
      (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s (𝟙_ _)
  exact iso_inv_congr h

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- The identification of the two direct sums of stalks over the geometric fibre, on the summand
indexed by a point of that fibre. -/
private theorem forget₂_map_moduleFiberStalksIso_hom_fiberStalkOf (s : GeometricPoint Y.obj)
    (x : GeometricFiberPoint B f s)
    (z : ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B f s)
      ((forgetModuleSheaf.{u, v, max (u + 1) v} B X
        (AddCommGrpCat.ULiftInt.{max (u + 1) v})).obj (𝟙_ _)).obj)) :
    (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
          AddCommGrpCat.{max (u + 1) v}).map
        (moduleFiberStalksIso.{u, v, max (u + 1) v} B
          (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s (𝟙_ _)).hom
        (fiberStalkOf.{u, v} B f s
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X
            (AddCommGrpCat.ULiftInt.{max (u + 1) v})).obj (𝟙_ _)) x z) =
      modFiberStalkOf.{u, v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s (𝟙_ _) x
        ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B
          (AddCommGrpCat.ULiftInt.{max (u + 1) v}) X
            (x.toGeometricPoint B f s)).hom.app (𝟙_ _) z) := by
  let : DecidableEq (GeometricFiberPoint B f s) := Classical.decEq _
  show DirectSum.congrLinearEquiv
      (fun y : GeometricFiberPoint B f s =>
        ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B
          (AddCommGrpCat.ULiftInt.{max (u + 1) v}) X
            (y.toGeometricPoint B f s)).app (𝟙_ _)).toLinearEquiv)
      (DirectSum.of _ x z) = _
  rw [DirectSum.coe_congrLinearEquiv]
  exact DirectSum.lmap_of
    (fun y : GeometricFiberPoint B f s =>
      ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B
        (AddCommGrpCat.ULiftInt.{max (u + 1) v}) X
          (y.toGeometricPoint B f s)).app (𝟙_ _)).toLinearEquiv.toLinearMap) x z

/-- **The weighted sum on the monoidal unit, on a summand**, read on underlying abelian
groups. -/
private theorem forget₂_map_modUnitWeightedSum_modFiberStalkOf (s : GeometricPoint Y.obj)
    (x : GeometricFiberPoint B f s)
    (a : ↑((modStalkFunctor.{u, v, max (u + 1) v} B
      (AddCommGrpCat.ULiftInt.{max (u + 1) v}) X (x.toGeometricPoint B f s)).obj (𝟙_ _))) :
    (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
          AddCommGrpCat.{max (u + 1) v}).map
        (modUnitWeightedSum.{u, v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f w s)
        (modFiberStalkOf.{u, v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s (𝟙_ _) x a) =
      w (x.1 default) •
        (Functor.Monoidal.εIso (modStalkFunctor.{u, v, max (u + 1) v} B
          (AddCommGrpCat.ULiftInt.{max (u + 1) v}) Y s)).hom
          ((Functor.Monoidal.εIso (modStalkFunctor.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) X (x.toGeometricPoint B f s))).inv a) :=
  Eq.trans
    (modUnitWeightedSum_modFiberStalkOf.{u, v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v})
      f w s x a)
    (modUnitWeightedSumSummand_apply.{u, v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v})
      f w s x a)

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- Two composites of three morphisms out of the direct sum of the stalks over the geometric
fibre agree as soon as they agree on every summand, on elements. -/
private theorem fiberStalks_comp_ext (s : GeometricPoint Y.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    {N₁ N₂ N₃ N₄ M : AddCommGrpCat.{max (u + 1) v}}
    (a₁ : AddCommGrpCat.of (fiberStalks.{u, max (u + 1) v} B f s F) ⟶ N₁) (b₁ : N₁ ⟶ N₂)
    (c₁ : N₂ ⟶ M)
    (a₂ : AddCommGrpCat.of (fiberStalks.{u, max (u + 1) v} B f s F) ⟶ N₃) (b₂ : N₃ ⟶ N₄)
    (c₂ : N₄ ⟶ M)
    (H : ∀ (x : GeometricFiberPoint B f s)
      (z : ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B f s) F.obj)),
      c₁ (b₁ (a₁ (fiberStalkOf.{u, v} B f s F x z))) =
        c₂ (b₂ (a₂ (fiberStalkOf.{u, v} B f s F x z)))) :
    a₁ ≫ b₁ ≫ c₁ = a₂ ≫ b₂ ≫ c₂ :=
  fiberStalks_hom_ext.{u, v} B f s fun x z => by
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply]
    exact H x z

/-- **The stalk of the trace on the abelian sheaf underlying the monoidal unit**, read through
the stalk decomposition of Stacks 0F5F: the weighted sum over the geometric fibre of
`AlgebraicGeometry.SmallEtale.integralTraceStalkMap`, between the two identifications of the
monoidal unit with the sheaf of locally constant functions. -/
private theorem fShriekStalkIso_inv_comp_stalkMap_forgetUnitTrace (s : GeometricPoint Y.obj) :
    (fShriekStalkIso.{u, v} B f s
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X
            (AddCommGrpCat.ULiftInt.{max (u + 1) v})).obj (𝟙_ _))).inv ≫
        colim.map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op
          (forgetUnitTrace.{u, v} B f hw).hom) =
      AddCommGrpCat.ofHom (fiberStalksMap.{u, max (u + 1) v} B f s
          (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B X
            (AddCommGrpCat.ULiftInt.{max (u + 1) v})).hom) ≫
        integralTraceStalkMap.{u, v} B f w s ≫
          colim.map (Functor.whiskerLeft
            (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op
            (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B Y
              (AddCommGrpCat.ULiftInt.{max (u + 1) v})).inv.hom) := by
  have h₁ : (fShriekStalkIso.{u, v} B f s
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X
            (AddCommGrpCat.ULiftInt.{max (u + 1) v})).obj (𝟙_ _))).inv ≫
        colim.map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op
          ((fShriekFunctor.{u, v} B f).map
            (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B X
              (AddCommGrpCat.ULiftInt.{max (u + 1) v})).hom).hom) =
      AddCommGrpCat.ofHom (fiberStalksMap.{u, max (u + 1) v} B f s
          (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B X
            (AddCommGrpCat.ULiftInt.{max (u + 1) v})).hom) ≫
        (fShriekStalkIso.{u, v} B f s
          (locallyConstantSheafAb.{u, v} B X.obj X.property
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}))).inv :=
    iso_inv_comp_of_comp_hom _ _ _ _
      (fShriekStalkIso_natural.{u, v} B f s
        (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B X
          (AddCommGrpCat.ULiftInt.{max (u + 1) v})).hom)
  have h₂ : (fShriekStalkIso.{u, v} B f s
          (locallyConstantSheafAb.{u, v} B X.obj X.property
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}))).inv ≫
        colim.map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op
          (integralTrace.{u, v} B f hw).hom) =
      integralTraceStalkMap.{u, v} B f w s :=
    integralTrace_stalk.{u, v} B f hw s
  have hmap : ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map (forgetUnitTrace.{u, v} B f hw) =
      ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).map
          ((fShriekFunctor.{u, v} B f).map
            (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B X
              (AddCommGrpCat.ULiftInt.{max (u + 1) v})).hom) ≫
        ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
            (A := AddCommGrpCat.{max (u + 1) v})).map (integralTrace.{u, v} B f hw) ≫
          ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
            (A := AddCommGrpCat.{max (u + 1) v})).map
            (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B Y
              (AddCommGrpCat.ULiftInt.{max (u + 1) v})).inv :=
    Eq.trans
      (congrArg (fun φ => ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).map φ) (forgetUnitTrace_eq.{u, v} B f hw))
      (Eq.trans
        (((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
            (A := AddCommGrpCat.{max (u + 1) v})).map_comp _ _)
        (congrArg (fun m => ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
              (A := AddCommGrpCat.{max (u + 1) v})).map
            ((fShriekFunctor.{u, v} B f).map
              (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B X
                (AddCommGrpCat.ULiftInt.{max (u + 1) v})).hom) ≫ m)
          (((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
            (A := AddCommGrpCat.{max (u + 1) v})).map_comp _ _)))
  exact Eq.trans
    (congrArg (fun m => (fShriekStalkIso.{u, v} B f s
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B X
          (AddCommGrpCat.ULiftInt.{max (u + 1) v})).obj (𝟙_ _))).inv ≫ m) hmap)
    (comp_four_of_inv_comp _ _ _ _ _ _ _ h₁ h₂)

/-- **The abelian form of the characterisation of the trace.** The stalk of
`AlgebraicGeometry.SmallEtale.forgetUnitTrace`, read through the stalk decomposition of
Stacks 0F5F, is the weighted sum `AlgebraicGeometry.SmallEtale.modUnitWeightedSum` of the
monoidal unit, read through the two comparisons of the `ULift ℤ`-module structures on a
stalk. -/
private theorem fShriekStalkIso_inv_comp_stalkMap_forgetUnitTrace_eq (s : GeometricPoint Y.obj) :
    (fShriekStalkIso.{u, v} B f s
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X
            (AddCommGrpCat.ULiftInt.{max (u + 1) v})).obj (𝟙_ _))).inv ≫
        colim.map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op
          (forgetUnitTrace.{u, v} B f hw).hom) =
      (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
            AddCommGrpCat.{max (u + 1) v}).map
          (moduleFiberStalksIso.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s (𝟙_ _)).hom ≫
        (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
              AddCommGrpCat.{max (u + 1) v}).map
            (modUnitWeightedSum.{u, v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f w s) ≫
          (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
                AddCommGrpCat.{max (u + 1) v}).map
            ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B
              (AddCommGrpCat.ULiftInt.{max (u + 1) v}) Y s).inv.app (𝟙_ _)) := by
  rw [fShriekStalkIso_inv_comp_stalkMap_forgetUnitTrace.{u, v} B f hw s]
  refine fiberStalks_comp_ext.{u, v} B f s _ _ _ _ _ _ _ fun x z => ?_
  have hleft : colim.map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op
          (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B Y
            (AddCommGrpCat.ULiftInt.{max (u + 1) v})).inv.hom)
        (integralTraceStalkMap.{u, v} B f w s
          (AddCommGrpCat.ofHom (fiberStalksMap.{u, max (u + 1) v} B f s
              (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B X
                (AddCommGrpCat.ULiftInt.{max (u + 1) v})).hom)
            (fiberStalkOf.{u, v} B f s
              ((forgetModuleSheaf.{u, v, max (u + 1) v} B X
                (AddCommGrpCat.ULiftInt.{max (u + 1) v})).obj (𝟙_ _)) x z))) =
      w (x.1 default) •
        colim.map (Functor.whiskerLeft
            (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op
            (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B Y
              (AddCommGrpCat.ULiftInt.{max (u + 1) v})).inv.hom)
          ((etaleStalkLocallyConstantMapsAbIso.{u, v} B Y.obj Y.property s
              (AddCommGrpCat.ULiftInt.{max (u + 1) v})).inv
            ((etaleStalkLocallyConstantMapsAbIso.{u, v} B X.obj X.property
                (x.toGeometricPoint B f s)
                (AddCommGrpCat.ULiftInt.{max (u + 1) v})).hom
              (colim.map (Functor.whiskerLeft
                (CategoryOfElements.π (geometricPointFiber B X.obj X.property
                  (x.toGeometricPoint B f s))).op
                (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B X
                  (AddCommGrpCat.ULiftInt.{max (u + 1) v})).hom.hom) z))) :=
    Eq.trans
      (congrArg (fun y => colim.map (Functor.whiskerLeft
            (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op
            (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B Y
              (AddCommGrpCat.ULiftInt.{max (u + 1) v})).inv.hom)
          (integralTraceStalkMap.{u, v} B f w s y))
        (fiberStalksMap_fiberStalkOf.{u, v} B f s
          (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B X
            (AddCommGrpCat.ULiftInt.{max (u + 1) v})).hom x z))
      (Eq.trans
        (congrArg (fun y => colim.map (Functor.whiskerLeft
            (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op
            (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B Y
              (AddCommGrpCat.ULiftInt.{max (u + 1) v})).inv.hom) y)
          (integralTraceStalkMap_fiberStalkOf.{u, v} B f w s x
            (colim.map (Functor.whiskerLeft
              (CategoryOfElements.π (geometricPointFiber B X.obj X.property
                (x.toGeometricPoint B f s))).op
              (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B X
                (AddCommGrpCat.ULiftInt.{max (u + 1) v})).hom.hom) z)))
        (map_zsmul _ _ _))
  have hright : (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
            AddCommGrpCat.{max (u + 1) v}).map
          ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) Y s).inv.app (𝟙_ _))
        ((forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
              AddCommGrpCat.{max (u + 1) v}).map
            (modUnitWeightedSum.{u, v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f w s)
          ((forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
                AddCommGrpCat.{max (u + 1) v}).map
              (moduleFiberStalksIso.{u, v, max (u + 1) v} B
                (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s (𝟙_ _)).hom
            (fiberStalkOf.{u, v} B f s
              ((forgetModuleSheaf.{u, v, max (u + 1) v} B X
                (AddCommGrpCat.ULiftInt.{max (u + 1) v})).obj (𝟙_ _)) x z))) =
      w (x.1 default) •
        (moduleEtaleStalkIso.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) Y s).inv.app (𝟙_ _)
          ((Functor.Monoidal.εIso (modStalkFunctor.{u, v, max (u + 1) v} B
              (AddCommGrpCat.ULiftInt.{max (u + 1) v}) Y s)).hom
            ((Functor.Monoidal.εIso (modStalkFunctor.{u, v, max (u + 1) v} B
                (AddCommGrpCat.ULiftInt.{max (u + 1) v}) X
                  (x.toGeometricPoint B f s))).inv
              ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B
                (AddCommGrpCat.ULiftInt.{max (u + 1) v}) X
                  (x.toGeometricPoint B f s)).hom.app (𝟙_ _) z))) := by
    rw [forget₂_map_moduleFiberStalksIso_hom_fiberStalkOf.{u, v} B f s x z]
    refine Eq.trans (congrArg (fun y => (moduleEtaleStalkIso.{u, v, max (u + 1) v} B
        (AddCommGrpCat.ULiftInt.{max (u + 1) v}) Y s).inv.app (𝟙_ _) y)
      (forget₂_map_modUnitWeightedSum_modFiberStalkOf.{u, v} B f s x _)) ?_
    exact map_zsmul _ _ _
  have hkey : (etaleStalkLocallyConstantMapsAbIso.{u, v} B X.obj X.property
          (x.toGeometricPoint B f s) (AddCommGrpCat.ULiftInt.{max (u + 1) v})).hom
        (colim.map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B X.obj X.property
            (x.toGeometricPoint B f s))).op
          (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B X
            (AddCommGrpCat.ULiftInt.{max (u + 1) v})).hom.hom) z) =
      (Functor.Monoidal.εIso (modStalkFunctor.{u, v, max (u + 1) v} B
          (AddCommGrpCat.ULiftInt.{max (u + 1) v}) X (x.toGeometricPoint B f s))).inv
        ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B
          (AddCommGrpCat.ULiftInt.{max (u + 1) v}) X
            (x.toGeometricPoint B f s)).hom.app (𝟙_ _) z) :=
    etaleStalkLocallyConstantMapsAbIso_hom_stalkMap_tensorUnit.{u, v} B X
      (x.toGeometricPoint B f s) _ z
      (Iso.inv_hom_id_apply (Functor.Monoidal.εIso (modStalkFunctor.{u, v, max (u + 1) v} B
        (AddCommGrpCat.ULiftInt.{max (u + 1) v}) X (x.toGeometricPoint B f s))) _).symm
  exact Eq.trans hleft (Eq.trans
    (congrArg (fun y => w (x.1 default) •
        colim.map (Functor.whiskerLeft
            (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op
            (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B Y
              (AddCommGrpCat.ULiftInt.{max (u + 1) v})).inv.hom)
          ((etaleStalkLocallyConstantMapsAbIso.{u, v} B Y.obj Y.property s
            (AddCommGrpCat.ULiftInt.{max (u + 1) v})).inv y)) hkey)
    (Eq.trans
      (congrArg (fun y => w (x.1 default) • y)
        (moduleEtaleStalkIso_inv_app_eps.{u, v} B Y s
          ((Functor.Monoidal.εIso (modStalkFunctor.{u, v, max (u + 1) v} B
              (AddCommGrpCat.ULiftInt.{max (u + 1) v}) X (x.toGeometricPoint B f s))).inv
            ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B
              (AddCommGrpCat.ULiftInt.{max (u + 1) v}) X
                (x.toGeometricPoint B f s)).hom.app (𝟙_ _) z))).symm)
      hright.symm))

/-- The stalk of `AlgebraicGeometry.SmallEtale.modUnitTrace` at a geometric point of `Y`, read
through the stalk decomposition of Stacks 0F5F, is the weighted sum over the geometric
fibre. -/
private theorem modShriekStalkIso_inv_comp_modStalkFunctor_map_modUnitTrace
    (s : GeometricPoint Y.obj) :
    ((modShriekStalkIso.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s).app (𝟙_ _) ≪≫
          moduleFiberStalksIso.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s (𝟙_ _)).inv ≫
        (modStalkFunctor.{u, v, max (u + 1) v} B
          (AddCommGrpCat.ULiftInt.{max (u + 1) v}) Y s).map (modUnitTrace.{u, v} B f hw) =
      modUnitWeightedSum.{u, v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f w s := by
  have hstalk : (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
          AddCommGrpCat.{max (u + 1) v}).map
        ((moduleEtaleStalkFunctor.{u, v, max (u + 1) v} B
          (AddCommGrpCat.ULiftInt.{max (u + 1) v}) Y s).map (modUnitTrace.{u, v} B f hw)) =
      colim.map (Functor.whiskerLeft
        (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op
        (forgetUnitTrace.{u, v} B f hw).hom) :=
    congrArg (fun φ : (forgetModuleSheaf.{u, v, max (u + 1) v} B Y
          (AddCommGrpCat.ULiftInt.{max (u + 1) v})).obj
            ((fShriekMod.{u, v, max (u + 1) v} B
              (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj (𝟙_ _)) ⟶
          (forgetModuleSheaf.{u, v, max (u + 1) v} B Y
            (AddCommGrpCat.ULiftInt.{max (u + 1) v})).obj (𝟙_ _) =>
        colim.map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op φ.hom))
      (forgetModuleSheaf_map_modUnitTrace.{u, v} B f hw)
  have hnat : (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
          AddCommGrpCat.{max (u + 1) v}).map
        ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) Y s).hom.app
          ((fShriekMod.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj (𝟙_ _))) ≫
      (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
          AddCommGrpCat.{max (u + 1) v}).map
        ((modStalkFunctor.{u, v, max (u + 1) v} B
          (AddCommGrpCat.ULiftInt.{max (u + 1) v}) Y s).map (modUnitTrace.{u, v} B f hw)) =
      colim.map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op
          (forgetUnitTrace.{u, v} B f hw).hom) ≫
        (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
            AddCommGrpCat.{max (u + 1) v}).map
          ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) Y s).hom.app (𝟙_ _)) := by
    rw [← Functor.map_comp,
      ← (moduleEtaleStalkIso.{u, v, max (u + 1) v} B
        (AddCommGrpCat.ULiftInt.{max (u + 1) v}) Y s).hom.naturality
        (modUnitTrace.{u, v} B f hw),
      Functor.map_comp, hstalk]
    rfl
  refine (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
    AddCommGrpCat.{max (u + 1) v}).map_injective ?_
  rw [modShriekStalkIso_trans_moduleFiberStalksIso_inv.{u, v} B f s, Functor.map_comp,
    Functor.map_comp, Functor.map_comp, Category.assoc,
    forget₂_map_moduleFShriekStalkIso_inv.{u, v} B f s]
  exact comp_chain_cancel _ _ _ _ _ _ _ _ _ hnat
    (fShriekStalkIso_inv_comp_stalkMap_forgetUnitTrace_eq.{u, v} B f hw s)
    (Iso.map_inv_hom_id _ _) (Iso.map_inv_hom_id ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B
      (AddCommGrpCat.ULiftInt.{max (u + 1) v}) Y s).app (𝟙_ _)) _)

/-- **The stalks of the trace on the monoidal unit are the weighted sum over the geometric
fibre.** This is the characterisation [Stacks, Tag 0GKG] asks of the trace on the constant
sheaf, in the world of sheaves of `ULift ℤ`-modules in which the projection formula of
[Stacks, Tag 0GKF] takes place. -/
public theorem modHasUnitTraceStalks_modUnitTrace :
    ModHasUnitTraceStalks.{u, v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f w
      (modUnitTrace.{u, v} B f hw) := by
  intro s
  exact modShriekStalkIso_inv_comp_modStalkFunctor_map_modUnitTrace.{u, v} B f hw s

end UnitTrace

end AlgebraicGeometry.SmallEtale

end
