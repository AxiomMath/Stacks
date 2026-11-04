module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Pullback
import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Limits.HasLimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.ExtensionByZeroLowerShriekModules
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits

/-!
# Comparing lower shriek on modules with lower shriek on abelian sheaves

Let `F : C ⥤ D` be a continuous functor of sites and let `φ : S ⟶ f_* R` be a morphism of
sheaves of rings making the situation a morphism of ringed sites. Both sheaves of `S`-modules
and abelian sheaves on `C` admit a lower-shriek functor, namely the left adjoint of the
corresponding direct image. Forgetting the module structure does not commute with lower shriek,
but there is a canonical comparison transformation between the two composites. It is not an
isomorphism in general, and it is one if and only if it is one at every extension by zero
`j_{U!} O_U` of the structure sheaf.

## Main definitions

* `Stacks.SheafOfModules.lowerShriekForgetComparison`: the canonical natural transformation
  from lower shriek of the underlying abelian sheaf to the underlying abelian sheaf of lower
  shriek on modules.

## Main results

* `Stacks.SheafOfModules.lowerShriekForgetComparison_homEquiv`: the adjoint transpose of the
  comparison under the adjunction for abelian sheaves is the unit of the module lower-shriek
  adjunction, after forgetting the module structure.
* `Stacks.SheafOfModules.lowerShriekForget_not_isomorphic`: there is a morphism of ringed sites
  and a sheaf of modules on the source for which the two abelian sheaves obtained by the two
  lower-shriek functors are not isomorphic.
* `Stacks.SheafOfModules.epi_sigmaDesc_extensionByZeroUnitSections`: the sheaves `j_{U!} O_U`
  generate the category of sheaves of modules.
* `Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_app_of_isColimit`: the comparison is
  invertible at the vertex of a colimit cocone at whose objects it is invertible, provided the
  two forgetful functors preserve colimits of that shape.
* `Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_iff`: the comparison is an
  isomorphism if and only if it is one at every `j_{U!} O_U`.
* `Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_iff_of_isos`: the same criterion at
  any family of sheaves of modules isomorphic, object by object, to the `j_{U!} O_U`.
* `Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_iff_extensionByZeroUnit`: the
  comparison is an isomorphism if and only if `g_!^{Ab} j_{U!} O_U ⟶ j_{u(U)!} O_{u(U)}` is an
  isomorphism for every object `U` of the source site.

## References

* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
* [Stacks Project, Tag 07AE](https://stacks.math.columbia.edu/tag/07AE)
* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
* [Stacks Project, Tag 03DB](https://stacks.math.columbia.edu/tag/03DB)
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

/-- The canonical natural transformation from lower shriek applied to the underlying abelian
sheaf to the underlying abelian sheaf of lower shriek on modules. -/
@[stacks 0798 "comparison_transformation"]
noncomputable def lowerShriekForgetComparison :
    _root_.SheafOfModules.toSheaf.{w} S ⋙
        F.sheafPullback AddCommGrpCat.{w} J K ⟶
      _root_.SheafOfModules.pullback.{w} phi ⋙ _root_.SheafOfModules.toSheaf.{w} R := by
  let adj := F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K
  let moduleAdj := _root_.SheafOfModules.pullbackPushforwardAdjunction.{w} phi
  exact
    { app := fun M =>
        (adj.homEquiv ((_root_.SheafOfModules.toSheaf.{w} S).obj M)
          ((_root_.SheafOfModules.toSheaf.{w} R).obj
            ((_root_.SheafOfModules.pullback.{w} phi).obj M))).symm
          ((_root_.SheafOfModules.toSheaf.{w} S).map (moduleAdj.unit.app M))
      naturality := by
        intro M N f
        simp only [Functor.comp_map]
        let XM := (_root_.SheafOfModules.toSheaf.{w} S).obj M
        let YM := (_root_.SheafOfModules.toSheaf.{w} R).obj
          ((_root_.SheafOfModules.pullback.{w} phi).obj M)
        let YN := (_root_.SheafOfModules.toSheaf.{w} R).obj
          ((_root_.SheafOfModules.pullback.{w} phi).obj N)
        calc
          _ = (adj.homEquiv XM YN).symm
              ((_root_.SheafOfModules.toSheaf.{w} S).map f ≫
                (_root_.SheafOfModules.toSheaf.{w} S).map (moduleAdj.unit.app N)) := by
                  symm
                  exact adj.homEquiv_naturality_left_symm
                    (Y := YN)
                    ((_root_.SheafOfModules.toSheaf.{w} S).map f)
                    ((_root_.SheafOfModules.toSheaf.{w} S).map (moduleAdj.unit.app N))
          _ = (adj.homEquiv XM YN).symm
                  ((_root_.SheafOfModules.toSheaf.{w} S).map (moduleAdj.unit.app M) ≫
                (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map
                  ((_root_.SheafOfModules.toSheaf.{w} R).map
                    ((_root_.SheafOfModules.pullback.{w} phi).map f))) := by
                  congr 1
                  change (_root_.SheafOfModules.toSheaf.{w} S).map f ≫
                      (_root_.SheafOfModules.toSheaf.{w} S).map (moduleAdj.unit.app N) =
                    (_root_.SheafOfModules.toSheaf.{w} S).map (moduleAdj.unit.app M) ≫
                      (_root_.SheafOfModules.toSheaf.{w} S).map
                        ((_root_.SheafOfModules.pullback.{w} phi ⋙
                          _root_.SheafOfModules.pushforward.{w} phi).map f)
                  exact congrArg (_root_.SheafOfModules.toSheaf.{w} S).map
                    (moduleAdj.unit.naturality f)
          _ = _ := adj.homEquiv_naturality_right_symm
            (X := XM) (Y := YM) (Y' := YN)
            ((_root_.SheafOfModules.toSheaf.{w} S).map (moduleAdj.unit.app M))
            ((_root_.SheafOfModules.toSheaf.{w} R).map
              ((_root_.SheafOfModules.pullback.{w} phi).map f)) }

/-- The comparison map is adjoint to the forgotten unit of the module lower-shriek
adjunction. -/
@[stacks 0798 "comparison_transformation"]
theorem lowerShriekForgetComparison_homEquiv (M : _root_.SheafOfModules.{w} S) :
    (F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).homEquiv
        ((_root_.SheafOfModules.toSheaf.{w} S).obj M)
        ((_root_.SheafOfModules.toSheaf.{w} R).obj
          ((_root_.SheafOfModules.pullback.{w} phi).obj M))
        ((lowerShriekForgetComparison F phi).app M) =
      (_root_.SheafOfModules.toSheaf.{w} S).map
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w} phi).unit.app M) := by
  show (F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).homEquiv
      ((_root_.SheafOfModules.toSheaf.{w} S).obj M)
      ((_root_.SheafOfModules.toSheaf.{w} R).obj
        ((_root_.SheafOfModules.pullback.{w} phi).obj M))
      (((F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).homEquiv
        ((_root_.SheafOfModules.toSheaf.{w} S).obj M)
        ((_root_.SheafOfModules.toSheaf.{w} R).obj
          ((_root_.SheafOfModules.pullback.{w} phi).obj M))).symm
        ((_root_.SheafOfModules.toSheaf.{w} S).map
          ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w} phi).unit.app M))) =
    (_root_.SheafOfModules.toSheaf.{w} S).map
      ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w} phi).unit.app M)
  exact Equiv.apply_symm_apply _ _

end Stacks.SheafOfModules

end

/-!
### Lower shriek does not commute with forgetting the module structure

The target site is `Bool` as a poset with the trivial topology, carrying the sheaf of rings with
value `ZMod 2 × ZMod 2` at `false`, `ZMod 2` at `true` and the diagonal as the restriction map;
the source site is a one-object poset mapping to `true`, and the sheaf of rings on it is the
direct image. At `false`, the abelian lower shriek of the structure sheaf of the source has two
elements, since the left Kan extension is computed by a terminal index object, while its module
lower shriek has four.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace Stacks.SheafOfModules

private def siteEquivalence : PUnit.{u + 1} ≌ PUnit.{1} where
  functor := {
    obj := fun _ => PUnit.unit
    map := fun _ => 𝟙 _
    map_id := by intro; subsingleton
    map_comp := by intros; subsingleton }
  inverse := {
    obj := fun _ => PUnit.unit
    map := fun _ => 𝟙 _
    map_id := by intro; subsingleton
    map_comp := by intros; subsingleton }
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; subsingleton)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; subsingleton)
  functor_unitIso_comp := by intro; subsingleton

private def smallSiteFunctor : PUnit.{1} ⥤ Bool where
  obj _ := true
  map _ := 𝟙 true
  map_id := by intro; simp
  map_comp := by intros; simp

private abbrev counterexampleSiteFunctor : PUnit.{u + 1} ⥤ Bool :=
  siteEquivalence.{u}.functor ⋙ smallSiteFunctor

private abbrev Jbig : GrothendieckTopology PUnit.{u + 1} := ⊥
private abbrev Jsmall : GrothendieckTopology PUnit.{1} := ⊥
private abbrev K : GrothendieckTopology Bool := ⊥

private instance smallSiteFunctor_continuous :
    smallSiteFunctor.IsContinuous Jsmall K := ⟨fun _ => Presieve.isSheaf_bot⟩

private instance smallSiteFunctor_final : smallSiteFunctor.Final where
  out d := by
    have : Subsingleton (StructuredArrow d smallSiteFunctor) := by
      refine ⟨?_⟩
      intro X Y
      cases X
      cases Y
      congr <;> subsingleton
    have : Nonempty (StructuredArrow d smallSiteFunctor) := by
      cases d with
      | false =>
        exact ⟨StructuredArrow.mk (Y := PUnit.unit) (homOfLE (show false ≤ true by decide))⟩
      | true => exact ⟨StructuredArrow.mk (Y := PUnit.unit) (𝟙 true)⟩
    exact isConnected_of_nonempty_and_subsingleton

private instance siteEquivalence_functor_continuous :
    siteEquivalence.{u}.functor.IsContinuous Jbig Jsmall := ⟨fun _ => Presieve.isSheaf_bot⟩

private instance siteEquivalence_inverse_continuous :
    siteEquivalence.{u}.inverse.IsContinuous Jsmall Jbig := ⟨fun _ => Presieve.isSheaf_bot⟩

/-- Every functor is cocontinuous for the trivial topologies. -/
private theorem isCocontinuous_bot {C D : Type*} [Category C] [Category D] (G : C ⥤ D) :
    G.IsCocontinuous (⊥ : GrothendieckTopology C) (⊥ : GrothendieckTopology D) := by
  refine ⟨@fun U S hS ↦ ?_⟩
  obtain rfl := (GrothendieckTopology.bot_covering).mp hS
  exact (GrothendieckTopology.bot_covering).mpr (Sieve.functorPullback_top G U)

private instance siteEquivalence_functor_cocontinuous :
    siteEquivalence.{u}.functor.IsCocontinuous Jbig Jsmall := isCocontinuous_bot _

private instance siteEquivalence_inverse_cocontinuous :
    siteEquivalence.{u}.inverse.IsCocontinuous Jsmall Jbig := isCocontinuous_bot _

private instance siteEquivalence_inverse_dense :
    siteEquivalence.{u}.inverse.IsDenseSubsite Jsmall Jbig :=
  Equivalence.isDenseSubsite_inverse_of_isCocontinuous Jbig Jsmall siteEquivalence.{u}

private instance counterexampleSiteFunctor_continuous :
    counterexampleSiteFunctor.{u}.IsContinuous Jbig K :=
  Functor.isContinuous_comp siteEquivalence.{u}.functor smallSiteFunctor Jbig Jsmall K

private instance counterexampleSiteFunctor_final : counterexampleSiteFunctor.{u}.Final :=
  Functor.final_comp siteEquivalence.{u}.functor smallSiteFunctor

private def counterexampleRingPresheaf : Boolᵒᵖ ⥤ RingCat.{0} where
  obj X := match X.unop with
    | false => RingCat.of (ZMod 2 × ZMod 2)
    | true => RingCat.of (ZMod 2)
  map := by
    intro X Y f
    cases X with
    | op x =>
      cases Y with
      | op y =>
        cases x <;> cases y
        · exact 𝟙 _
        · exact False.elim (by
            have h : (true : Bool) ≤ false := f.unop.down.down
            exact (by decide : ¬ ((true : Bool) ≤ false)) h)
        · exact RingCat.ofHom (RingHom.prod (RingHom.id _) (RingHom.id _))
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
            have h : (true : Bool) ≤ false := f.unop.down.down
            exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) h)
          case op.op.op.true.false.true =>
            have h : (true : Bool) ≤ false := g.unop.down.down
            exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) h)
          all_goals simp_all [RingHom.prod]

private def counterexampleRingSheaf : Sheaf (⊥ : GrothendieckTopology Bool) RingCat.{0} :=
  ⟨counterexampleRingPresheaf, Presheaf.isSheaf_bot _⟩

private abbrev smallRingPushforward (R : Sheaf K RingCat.{0}) :
    Sheaf Jsmall RingCat.{0} :=
  (smallSiteFunctor.sheafPushforwardContinuous RingCat.{0} Jsmall K).obj R

private def smallRingMap (R : Sheaf K RingCat.{0}) :
    smallRingPushforward R ⟶
      (smallSiteFunctor.sheafPushforwardContinuous RingCat.{0} Jsmall K).obj R :=
  ObjectProperty.homMk (𝟙 (smallRingPushforward R).obj)

private theorem smallModulePushforward_isRightAdjoint (R : Sheaf K RingCat.{0}) :
    (SheafOfModules.pushforward.{0} (F := smallSiteFunctor) (J := Jsmall) (K := K)
      (R := R) (S := smallRingPushforward R) (smallRingMap R)).IsRightAdjoint := by
  have : HasWeakSheafify K AddCommGrpCat.{0} := inferInstance
  have hbij (P : Boolᵒᵖ ⥤ AddCommGrpCat.{0}) (X : Boolᵒᵖ) :
      Function.Bijective ((CategoryTheory.toSheafify K P).app X) :=
    (ConcreteCategory.isIso_iff_bijective _).mp
      ((NatTrans.isIso_iff_isIso_app _).mp
        (CategoryTheory.isIso_toSheafify _ (Presheaf.isSheaf_bot P)) X)
  have : ∀ P : Boolᵒᵖ ⥤ AddCommGrpCat.{0},
      Presheaf.IsLocallyInjective K (CategoryTheory.toSheafify K P) := fun P =>
    Presheaf.isLocallyInjective_of_injective (J := ⊥) _ fun X => (hbij P X).1
  have : ∀ P : Boolᵒᵖ ⥤ AddCommGrpCat.{0},
      Presheaf.IsLocallySurjective K (CategoryTheory.toSheafify K P) := fun P =>
    Presheaf.isLocallySurjective_of_surjective (J := ⊥) _ fun X => (hbij P X).2
  have : K.WEqualsLocallyBijective AddCommGrpCat.{0} := by
    show (⊥ : GrothendieckTopology Bool).WEqualsLocallyBijective AddCommGrpCat.{0}
    exact (GrothendieckTopology.WEqualsLocallyBijective.mk'
      (J := ⊥) (A := AddCommGrpCat.{0}))
  have hPres : (PresheafOfModules.pushforward.{0} (F := smallSiteFunctor)
      (smallRingMap R).hom).IsRightAdjoint :=
    Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
      (PresheafOfModules.pullbackObjIsDefined_eq_top (F := smallSiteFunctor)
        (smallRingMap R).hom)
  have : (PresheafOfModules.pushforward.{0} (F := smallSiteFunctor)
      (smallRingMap R).hom).IsRightAdjoint := hPres
  exact (SheafOfModules.PullbackConstruction.adjunction
    (F := smallSiteFunctor) (smallRingMap R)).isRightAdjoint

private abbrev bigRingPushforward (T : Sheaf Jsmall RingCat.{0}) :
    Sheaf Jbig RingCat.{0} :=
  (siteEquivalence.{u}.functor.sheafPushforwardContinuous RingCat.{0} Jbig Jsmall).obj T

private def bigRingMap (T : Sheaf Jsmall RingCat.{0}) :
    bigRingPushforward T ⟶
      (siteEquivalence.{u}.functor.sheafPushforwardContinuous RingCat.{0} Jbig Jsmall).obj T :=
  ObjectProperty.homMk (𝟙 (bigRingPushforward T).obj)

private def inverseBigRingMap (T : Sheaf Jsmall RingCat.{0}) :
    T ⟶ (siteEquivalence.{u}.inverse.sheafPushforwardContinuous RingCat.{0} Jsmall Jbig).obj
      (bigRingPushforward T) :=
  (siteEquivalence.{u}.sheafCongr Jbig Jsmall RingCat.{0}).counitIso.inv.app T

private theorem inverseBigRingMap_eq (T : Sheaf Jsmall RingCat.{0}) :
    Functor.whiskerRight (NatTrans.op siteEquivalence.{u}.counit) T.obj =
      (inverseBigRingMap T).hom ≫
        siteEquivalence.{u}.inverse.op.whiskerLeft (bigRingMap T).hom := by
  ext X
  rfl

private theorem bigRingMap_eq (T : Sheaf Jsmall RingCat.{0}) :
    (bigRingMap T).hom ≫ siteEquivalence.{u}.functor.op.whiskerLeft
        (inverseBigRingMap T).hom ≫
      Functor.whiskerRight (NatTrans.op siteEquivalence.{u}.unit) (bigRingPushforward T).obj =
        𝟙 (bigRingPushforward T).obj := by
  ext X x
  have ht : siteEquivalence.{u}.functor.map (siteEquivalence.{u}.unitIso.hom.app (unop X)) ≫
      siteEquivalence.{u}.counitIso.hom.app (siteEquivalence.{u}.functor.obj (unop X)) = 𝟙 _ :=
    siteEquivalence.{u}.functor_unitIso_comp (unop X)
  have hcomp : T.obj.map
      (siteEquivalence.{u}.counitIso.hom.app (siteEquivalence.{u}.functor.obj (unop X))).op ≫
      T.obj.map (siteEquivalence.{u}.functor.map
          (siteEquivalence.{u}.unitIso.hom.app (unop X))).op =
        𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp, ht]
    simp [siteEquivalence]
  show (RingCat.Hom.hom
    (T.obj.map (siteEquivalence.{u}.counitIso.hom.app
        (siteEquivalence.{u}.functor.obj (unop X))).op ≫
      T.obj.map (siteEquivalence.{u}.functor.map
        (siteEquivalence.{u}.unitIso.hom.app (unop X))).op)) x = x
  rw [hcomp]
  rfl

private theorem bigModulePushforward_isRightAdjoint (T : Sheaf Jsmall RingCat.{0}) :
    (SheafOfModules.pushforward.{0} (F := siteEquivalence.{u}.functor)
      (J := Jbig) (K := Jsmall) (R := T) (S := bigRingPushforward T)
      (bigRingMap T)).IsRightAdjoint := by
  let h : SheafOfModules T ≌ SheafOfModules (bigRingPushforward T) :=
    SheafOfModules.pushforwardPushforwardEquivalence.{0} siteEquivalence.{u}
      (bigRingMap T) (inverseBigRingMap T) (inverseBigRingMap_eq T) (bigRingMap_eq T)
  exact h.symm.toAdjunction.isRightAdjoint

private theorem counterexampleModulePushforward_isRightAdjoint :
    (SheafOfModules.pushforward.{0} (F := counterexampleSiteFunctor.{u})
      (J := Jbig) (K := K) (R := counterexampleRingSheaf)
      (S := bigRingPushforward (smallRingPushforward counterexampleRingSheaf))
      (𝟙 (bigRingPushforward (smallRingPushforward counterexampleRingSheaf)))).IsRightAdjoint := by
  let T := smallRingPushforward counterexampleRingSheaf
  let S := bigRingPushforward T
  let ψ := smallRingMap counterexampleRingSheaf
  let φ := bigRingMap T
  have : (SheafOfModules.pushforward.{0} (F := siteEquivalence.{u}.functor)
      (J := Jbig) (K := Jsmall) (R := T) (S := S) φ).IsRightAdjoint :=
    bigModulePushforward_isRightAdjoint T
  have : (SheafOfModules.pushforward.{0} (F := smallSiteFunctor)
      (J := Jsmall) (K := K) (R := counterexampleRingSheaf) (S := T) ψ).IsRightAdjoint :=
    smallModulePushforward_isRightAdjoint counterexampleRingSheaf
  have hcomp := SheafOfModules.pushforwardComp.{0}
    (F := siteEquivalence.{u}.functor) (G := smallSiteFunctor) φ ψ
  have heq : φ ≫
      (siteEquivalence.{u}.functor.sheafPushforwardContinuous RingCat.{0} Jbig Jsmall).map ψ =
        𝟙 S := by
    ext X x
    rfl
  exact Functor.isRightAdjoint_of_iso
    (hcomp ≪≫ SheafOfModules.pushforwardCongr heq)

private abbrev falseLanIndex.{v} :=
  CostructuredArrow counterexampleSiteFunctor.{v}.op (Opposite.op false)

private def falseLanIndexObj : falseLanIndex.{u} :=
  CostructuredArrow.mk (Y := Opposite.op PUnit.unit)
    (show counterexampleSiteFunctor.{u}.op.obj (Opposite.op (PUnit.unit : PUnit.{u + 1})) ⟶
        Opposite.op false from
      (homOfLE (show (false : Bool) ≤ true by decide)).op)

private instance falseLanIndex_subsingleton : Subsingleton falseLanIndex.{u} := by
  refine ⟨?_⟩
  intro X Y
  cases X
  cases Y
  congr <;> subsingleton

private def falseLanIndexObj_terminal : Limits.IsTerminal falseLanIndexObj.{u} :=
  Limits.IsTerminal.ofUniqueHom
    (fun X => eqToHom (Subsingleton.elim X falseLanIndexObj.{u}))
    (fun _ _ => rfl)

private noncomputable def counterexampleLanFalseIso
    (G : PUnit.{u + 1}ᵒᵖ ⥤ AddCommGrpCat.{0}) :
    (counterexampleSiteFunctor.{u}.op.lan.obj G).obj (Opposite.op false) ≅
      G.obj (Opposite.op PUnit.unit) := by
  classical
  let D := CostructuredArrow.proj counterexampleSiteFunctor.{u}.op (Opposite.op false) ⋙ G
  let e := counterexampleSiteFunctor.{u}.op.leftKanExtensionObjIsoColimit G (Opposite.op false)
  change (counterexampleSiteFunctor.{u}.op.leftKanExtension G).obj (Opposite.op false) ≅ _
  exact e ≪≫
    Limits.IsColimit.coconePointUniqueUpToIso (Limits.colimit.isColimit D)
      (Limits.colimitOfDiagramTerminal falseLanIndexObj_terminal.{u} D)

/-- The lower shriek of modules may differ, even as an abelian sheaf, from lower
shriek of the underlying abelian sheaf. -/
@[stacks 0798 "noncommutativity", stacks 07AE "underived noncommutation"]
theorem lowerShriekForget_not_isomorphic :
    ∃ (J : GrothendieckTopology PUnit) (K : GrothendieckTopology Bool)
      (F : PUnit ⥤ Bool) (R : Sheaf K RingCat.{0})
      (hF : F.IsContinuous J K) (_hFc : F.IsCocontinuous J K),
      letI : F.IsContinuous J K := hF
      let S : Sheaf J RingCat.{0} :=
        (F.sheafPushforwardContinuous RingCat.{0} J K).obj R
      let φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{0} J K).obj R := 𝟙 S
      ∃ (hAb : (F.sheafPushforwardContinuous AddCommGrpCat.{0} J K).IsRightAdjoint)
        (hMod : (SheafOfModules.pushforward.{0} φ).IsRightAdjoint),
      letI : (F.sheafPushforwardContinuous AddCommGrpCat.{0} J K).IsRightAdjoint := hAb
      letI : (SheafOfModules.pushforward.{0} φ).IsRightAdjoint := hMod
      ∃ M : SheafOfModules.{0} S,
        ¬ Nonempty
          (((SheafOfModules.toSheaf.{0} S ⋙
              F.sheafPullback AddCommGrpCat.{0} J K).obj M) ≅
            ((SheafOfModules.pullback.{0} φ ⋙
              SheafOfModules.toSheaf.{0} R).obj M)) :=
  by
    let hF : counterexampleSiteFunctor.IsContinuous
        (⊥ : GrothendieckTopology PUnit) (⊥ : GrothendieckTopology Bool) :=
      ⟨fun _ ↦ Presieve.isSheaf_bot⟩
    let hFc : counterexampleSiteFunctor.IsCocontinuous
        (⊥ : GrothendieckTopology PUnit) (⊥ : GrothendieckTopology Bool) :=
      isCocontinuous_bot _
    refine ⟨⊥, ⊥, counterexampleSiteFunctor, counterexampleRingSheaf, hF, hFc, ?_⟩
    have : counterexampleSiteFunctor.IsContinuous (⊥ : GrothendieckTopology PUnit)
        (⊥ : GrothendieckTopology Bool) := hF
    let S := (counterexampleSiteFunctor.sheafPushforwardContinuous RingCat.{0}
      (⊥ : GrothendieckTopology PUnit) (⊥ : GrothendieckTopology Bool)).obj
        counterexampleRingSheaf
    let φ := 𝟙 S
    have : HasWeakSheafify (⊥ : GrothendieckTopology Bool) AddCommGrpCat.{0} :=
      inferInstance
    have : ∀ P : PUnitᵒᵖ ⥤ AddCommGrpCat.{0},
        counterexampleSiteFunctor.op.HasLeftKanExtension P := fun _ ↦ inferInstance
    have hAb : (counterexampleSiteFunctor.sheafPushforwardContinuous AddCommGrpCat.{0}
        (⊥ : GrothendieckTopology PUnit) (⊥ : GrothendieckTopology Bool)).IsRightAdjoint :=
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        counterexampleSiteFunctor AddCommGrpCat.{0} (⊥ : GrothendieckTopology PUnit)
        (⊥ : GrothendieckTopology Bool)).isRightAdjoint
    refine ⟨hAb, ?_⟩
    have hMod : (SheafOfModules.pushforward.{0} φ).IsRightAdjoint :=
      counterexampleModulePushforward_isRightAdjoint
    refine ⟨hMod, ?_⟩
    refine ⟨SheafOfModules.unit S, ?_⟩
    classical
    let M := SheafOfModules.unit S
    let X := ((SheafOfModules.toSheaf S ⋙
      counterexampleSiteFunctor.sheafPullback AddCommGrpCat.{0}
        (⊥ : GrothendieckTopology PUnit) (⊥ : GrothendieckTopology Bool)).obj M)
    let Y := ((SheafOfModules.pullback φ ⋙
      SheafOfModules.toSheaf counterexampleRingSheaf).obj M)
    let sourceAb := (SheafOfModules.toSheaf S).obj M
    let lan := counterexampleSiteFunctor.op.lan.obj sourceAb.obj
    let hlan : Presheaf.IsSheaf (⊥ : GrothendieckTopology Bool) lan :=
      Presheaf.isSheaf_bot _
    let ePull := (Functor.sheafPullbackConstruction.sheafPullbackIso
      counterexampleSiteFunctor AddCommGrpCat.{0}
        (⊥ : GrothendieckTopology PUnit) (⊥ : GrothendieckTopology Bool)).app sourceAb
    let eSheaf := CategoryTheory.sheafificationIso
      (⟨lan, hlan⟩ : Sheaf (⊥ : GrothendieckTopology Bool) AddCommGrpCat.{0})
    let eX := asIso ((ePull ≪≫ eSheaf.symm).hom.hom.app (Opposite.op false))
    let eX' := eX ≪≫ counterexampleLanFalseIso sourceAb.obj
    let eY := (SheafOfModules.toSheaf counterexampleRingSheaf).mapIso
      (asIso (SheafOfModules.pullbackObjUnitToUnit φ))
    let eY' := asIso (eY.hom.hom.app (Opposite.op false))
    let ex : (X.obj.obj (Opposite.op false) : Type 0) ≃ ZMod 2 :=
      Equiv.ofBijective eX'.hom
        (ConcreteCategory.isIso_iff_bijective eX'.hom |>.mp inferInstance)
    let ey : (Y.obj.obj (Opposite.op false) : Type 0) ≃
        (ZMod 2 × ZMod 2) :=
      Equiv.ofBijective eY'.hom
        (ConcreteCategory.isIso_iff_bijective eY'.hom |>.mp inferInstance)
    have : Fintype (X.obj.obj (Opposite.op false) : Type 0) := Fintype.ofEquiv _ ex.symm
    have : Fintype (Y.obj.obj (Opposite.op false) : Type 0) := Fintype.ofEquiv _ ey.symm
    intro h
    let e := h.some
    have hIso : IsIso (e.hom.hom.app (Opposite.op false)) := inferInstance
    have hBij := (ConcreteCategory.isIso_iff_bijective _).mp hIso
    have hcard : Fintype.card (X.obj.obj (Opposite.op false) : Type 0) =
        Fintype.card (Y.obj.obj (Opposite.op false) : Type 0) :=
      Fintype.card_congr
        (Equiv.ofBijective (e.hom.hom.app (Opposite.op false)) hBij)
    rw [Fintype.card_congr ex, Fintype.card_congr ey] at hcard
    norm_num [Fintype.card_prod, ZMod.card] at hcard

end Stacks.SheafOfModules

/-!
### The criterion for the two lower shrieks to agree

The comparison transformation is an isomorphism if and only if it is one at every extension by
zero `j_{U!} O_U` of the structure sheaf. Since `g_! j_{U!} O_U = j_{u(U)!} O_{u(U)}`, this says
that `g_!^{Ab} j_{U!} O_U ⟶ j_{u(U)!} O_{u(U)}` is an isomorphism for every object `U` of the
source site.
-/

open CategoryTheory.Limits

universe w t u₁ u₂ v₁ v₂

namespace Stacks.SheafOfModules

section Devissage

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : Functor C D) [F.IsContinuous J K]
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  (phi : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  [(_root_.SheafOfModules.pushforward.{w} phi).IsRightAdjoint]
  [(F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]

/-- The comparison between the two lower shrieks is an isomorphism at the vertex of a colimit
cocone at whose objects it is an isomorphism, provided both forgetful functors preserve
colimits of that shape. -/
theorem isIso_lowerShriekForgetComparison_app_of_isColimit {I : Type*} [Category I]
    (Z : I ⥤ _root_.SheafOfModules.{w} S) (c : Cocone Z) (hc : IsColimit c)
    (hS : PreservesColimitsOfShape I (_root_.SheafOfModules.toSheaf.{w} S))
    (hR : PreservesColimitsOfShape I (_root_.SheafOfModules.toSheaf.{w} R))
    (h : ∀ i, IsIso ((lowerShriekForgetComparison F phi).app (Z.obj i))) :
    IsIso ((lowerShriekForgetComparison F phi).app c.pt) := by
  let _ := hS
  let _ := hR
  let _ : PreservesColimitsOfShape I (F.sheafPullback AddCommGrpCat.{w} J K) :=
    ((F.sheafAdjunctionContinuous AddCommGrpCat.{w} J
      K).leftAdjoint_preservesColimits).preservesColimitsOfShape
  let _ : PreservesColimitsOfShape I (_root_.SheafOfModules.pullback.{w} phi) :=
    ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
      phi).leftAdjoint_preservesColimits).preservesColimitsOfShape
  let _ : IsIso (Z.whiskerLeft (lowerShriekForgetComparison F phi)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact h
  exact isIso_app_coconePt_of_preservesColimit Z _ c hc

end Devissage

section Generation

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{max u₁ v₁ u t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁ u t}]
  (S : Sheaf J RingCat.{u})

/-- Sheaves of modules over a sheaf of rings form an abelian category. -/
@[instance_reducible]
private noncomputable def abelian_sheafOfModules :
    Abelian (_root_.SheafOfModules.{max u₁ v₁ u t} S) := inferInstance

/-- Forgetting a sheaf of modules to an abelian sheaf preserves colimits indexed by a shape in
the lowest universe. -/
private theorem preservesColimitsOfSize_toSheaf_zero :
    PreservesColimitsOfSize.{0, 0}
      (_root_.SheafOfModules.toSheaf.{max u₁ v₁ u t} S) :=
  @preservesSmallestColimits_of_preservesColimits _ _ _ _
    (_root_.SheafOfModules.toSheaf.{max u₁ v₁ u t} S)
    (inferInstance : PreservesColimitsOfSize.{max u₁ v₁ u t, max u₁ v₁ u t}
      (_root_.SheafOfModules.toSheaf.{max u₁ v₁ u t} S))

/-- The morphism to a sheaf of modules `M` out of the direct sum of one copy of `j_{U!} O_U` for
every pair `(U, s)` of an object and a section of `M` over it, with component at `(U, s)` the
morphism named by `s`, is an epimorphism. -/
theorem epi_sigmaDesc_extensionByZeroUnitSections
    (M : _root_.SheafOfModules.{max u₁ v₁ u t} S) :
    Epi (Sigma.desc (f := fun p : (Σ U : C, ToType (M.val.obj (op U))) =>
        extensionByZeroUnit.{u₁, v₁, u, t} S p.1)
      fun p => (extensionByZeroUnitHomEquiv.{u₁, v₁, u, t} S p.1 M).symm p.2) := by
  constructor
  intro Z h₁ h₂ hyp
  ext U s
  have key : ∀ (g : M ⟶ Z),
      extensionByZeroUnitHomEquiv.{u₁, v₁, u, t} S U.unop Z
        (Sigma.ι (fun p : (Σ U : C, ToType (M.val.obj (op U))) =>
            extensionByZeroUnit.{u₁, v₁, u, t} S p.1) ⟨U.unop, s⟩ ≫
          Sigma.desc (fun p =>
            (extensionByZeroUnitHomEquiv.{u₁, v₁, u, t} S p.1 M).symm p.2) ≫ g) =
        g.val.app U s := by
    intro g
    rw [← Category.assoc, Sigma.ι_desc]
    refine (extensionByZeroUnitHomEquiv_naturality.{u₁, v₁, u, t} S U.unop _ g).trans ?_
    rw [Equiv.apply_symm_apply]
    rfl
  rw [← key h₁, ← key h₂, hyp]

end Generation

section Criterion

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : Functor C D) [F.IsContinuous J K]
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  (phi : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  [(_root_.SheafOfModules.pushforward.{max u₁ v₁ u₂ v₂ u t} phi).IsRightAdjoint]
  [(F.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁ u₂ v₂ u t} J K).IsRightAdjoint]
  [HasWeakSheafify J AddCommGrpCat.{max u₁ v₁ u₂ v₂ u t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁ u₂ v₂ u t}]
  [HasWeakSheafify K AddCommGrpCat.{max u₁ v₁ u₂ v₂ u t}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁ u₂ v₂ u t}]

/-- The canonical comparison between lower shriek on sheaves of modules and lower shriek on the
underlying abelian sheaves is an isomorphism if and only if it is an isomorphism at the extension
by zero `j_{U!} O_U` of the structure sheaf for every object `U` of the source site. -/
@[stacks 0798 "the criterion: agreement iff the comparison is invertible at every j_{U!} O_U"]
theorem isIso_lowerShriekForgetComparison_iff :
    IsIso (lowerShriekForgetComparison F phi) ↔
      ∀ U : C, IsIso ((lowerShriekForgetComparison F phi).app
        (extensionByZeroUnit.{u₁, v₁, u, max u₂ v₂ t} S U)) := by
  refine ⟨fun _ U => inferInstance, fun h => ?_⟩
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  let _ := abelian_sheafOfModules.{u, max u₂ v₂ t, u₁, v₁} S
  let Z (N : _root_.SheafOfModules.{max u₁ v₁ u₂ v₂ u t} S) :
      Discrete (Σ U : C, ToType (N.val.obj (op U))) ⥤
        _root_.SheafOfModules.{max u₁ v₁ u₂ v₂ u t} S :=
    Discrete.functor fun p => extensionByZeroUnit.{u₁, v₁, u, max u₂ v₂ t} S p.1
  have key (N : _root_.SheafOfModules.{max u₁ v₁ u₂ v₂ u t} S) :
      IsIso ((lowerShriekForgetComparison F phi).app (colimit.cocone (Z N)).pt) :=
    have : HasColimit (Z N) := inferInstance
    isIso_lowerShriekForgetComparison_app_of_isColimit F phi (Z N) _ (colimit.isColimit _)
      inferInstance inferInstance fun i => h i.as.1
  let epiMap (N : _root_.SheafOfModules.{max u₁ v₁ u₂ v₂ u t} S) :
      (colimit.cocone (Z N)).pt ⟶ N :=
    Sigma.desc fun p =>
      (extensionByZeroUnitHomEquiv.{u₁, v₁, u, max u₂ v₂ t} S p.1 N).symm p.2
  have hepi (N : _root_.SheafOfModules.{max u₁ v₁ u₂ v₂ u t} S) : Epi (epiMap N) :=
    epi_sigmaDesc_extensionByZeroUnitSections.{u, max u₂ v₂ t, u₁, v₁} S N
  have hpi := hepi M
  have hq := hepi (kernel (epiMap M))
  have hzero : (epiMap (kernel (epiMap M)) ≫ kernel.ι (epiMap M)) ≫ epiMap M = 0 := by
    simp
  have hcok : IsColimit (CokernelCofork.ofπ (epiMap M) hzero) :=
    isCokernelEpiComp (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel (epiMap M)))
      (epiMap (kernel (epiMap M))) rfl
  refine isIso_lowerShriekForgetComparison_app_of_isColimit F phi
    (parallelPair (epiMap (kernel (epiMap M)) ≫ kernel.ι (epiMap M)) 0) _ hcok
    (preservesColimitsOfSize_toSheaf_zero.{u, max u₂ v₂ t, u₁, v₁} S).preservesColimitsOfShape
    (preservesColimitsOfSize_toSheaf_zero.{u, max u₁ v₁ t, u₂, v₂} R).preservesColimitsOfShape
    fun j => ?_
  cases j with
  | zero => exact key _
  | one => exact key _

/-- If a family `G` of sheaves of modules is isomorphic, object by object, to the extensions by
zero of the structure sheaf, then the comparison is an isomorphism exactly when it is an
isomorphism at every `G U`. -/
@[stacks 0798 "the criterion, at any family isomorphic to the extensions by zero of the \
structure sheaf"]
theorem isIso_lowerShriekForgetComparison_iff_of_isos
    (G : C → _root_.SheafOfModules.{max u₁ v₁ u₂ v₂ u t} S)
    (e : ∀ U : C, extensionByZeroUnit.{u₁, v₁, u, max u₂ v₂ t} S U ≅ G U) :
    IsIso (lowerShriekForgetComparison F phi) ↔
      ∀ U : C, IsIso ((lowerShriekForgetComparison F phi).app (G U)) := by
  rw [isIso_lowerShriekForgetComparison_iff.{u, t, u₁, u₂, v₁, v₂} F phi]
  exact forall_congr' fun U => NatTrans.isIso_app_iff_of_iso _ (e U)

end Criterion

section Spelling

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{max u₁ v₁ w})
  [HasWeakSheafify J AddCommGrpCat.{max u₁ v₁ w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁ w}]
  [∀ V : C, (_root_.SheafOfModules.pushforward.{max u₁ v₁ w} (F := Over.forget V)
    (𝟙 (R.over V) : R.over V ⟶ R.over V)).IsRightAdjoint]

/-- The two constructions of the extension by zero `j_{V!} O_V` of the structure sheaf agree: the
sheafified free module on the morphisms to `V`, and the image of the unit sheaf of modules under
extension by zero along the localization morphism `C/V ⥤ C`. -/
noncomputable def extensionByZeroUnitSpellingIso (V : C) :
    extensionByZeroUnit.{u₁, v₁, max u₁ v₁ w, w} R V ≅
      Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnit R V where
  hom := (extensionByZeroUnitHomEquiv.{u₁, v₁, max u₁ v₁ w, w} R V _).symm
    (Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv.{max u₁ v₁ w} J R V _ (𝟙 _))
  inv := (Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv.{max u₁ v₁ w}
    J R V _).symm (extensionByZeroUnitHomEquiv.{u₁, v₁, max u₁ v₁ w, w} R V _ (𝟙 _))
  hom_inv_id := by
    apply (extensionByZeroUnitHomEquiv.{u₁, v₁, max u₁ v₁ w, w} R V _).injective
    rw [extensionByZeroUnitHomEquiv_naturality, Equiv.apply_symm_apply,
      ← Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv_naturality,
      Category.id_comp, Equiv.apply_symm_apply]
  inv_hom_id := by
    apply (Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv.{max u₁ v₁ w}
      J R V _).injective
    rw [Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv_naturality,
      Equiv.apply_symm_apply, ← extensionByZeroUnitHomEquiv_naturality,
      Category.id_comp, Equiv.apply_symm_apply]

end Spelling

section SourceForm

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (u : C ⥤ D) [u.IsContinuous J K] [u.IsCocontinuous J K]
  (O : Sheaf K RingCat.{max u₁ v₁ u₂ v₂ t})
  [HasWeakSheafify J AddCommGrpCat.{max u₁ v₁ u₂ v₂ t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁ u₂ v₂ t}]
  [HasWeakSheafify K AddCommGrpCat.{max u₁ v₁ u₂ v₂ t}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁ u₂ v₂ t}]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁ u₂ v₂ t} J K).IsRightAdjoint]
  [∀ V : C, (_root_.SheafOfModules.pushforward.{max u₁ v₁ u₂ v₂ t} (F := Over.forget V)
    (𝟙 ((inverseImageRing J K u O).over V) :
      (inverseImageRing J K u O).over V ⟶ (inverseImageRing J K u O).over V)).IsRightAdjoint]
  [∀ W : D, (_root_.SheafOfModules.pushforward.{max u₁ v₁ u₂ v₂ t} (F := Over.forget W)
    (𝟙 (O.over W) : O.over W ⟶ O.over W)).IsRightAdjoint]

/-- The identification `g_! j_{U!} O_U = j_{u(U)!} O_{u(U)}`, for the lower shriek given by the
left adjoint `SheafOfModules.pullback`. -/
noncomputable def pullbackExtensionByZeroUnitIso (V : C) :
    (_root_.SheafOfModules.pullback.{max u₁ v₁ u₂ v₂ t} (structureMap J K u O)).obj
        (extensionByZeroUnit (inverseImageRing J K u O) V) ≅
      Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnit O (u.obj V) :=
  (_root_.SheafOfModules.pullback.{max u₁ v₁ u₂ v₂ t} (structureMap J K u O)).mapIso
      (extensionByZeroUnitSpellingIso (inverseImageRing J K u O) V) ≪≫
    ((lowerShriekIsoPullback.{max u₁ v₁ u₂ v₂ t} J K u O).app _).symm ≪≫
    Stacks.Cohomology.DerivedLowerShriek.lowerShriekExtensionByZeroUnitIso J K u O V

/-- The canonical comparison between lower shriek on sheaves of modules and lower shriek on the
underlying abelian sheaves is an isomorphism if and only if, for every object `U` of the source
site, the canonical map

`g_!^{Ab} j_{U!} O_U ⟶ j_{u(U)!} O_{u(U)}`

is an isomorphism. -/
@[stacks 0798 "the criterion in the source's form: the comparison is an isomorphism iff \
`g_!^{Ab} j_{U!} O_U ⟶ j_{u(U)!} O_{u(U)}` is one for every `U`, the target being identified by \
Stacks 07AC"]
theorem isIso_lowerShriekForgetComparison_iff_extensionByZeroUnit :
    IsIso (lowerShriekForgetComparison u (structureMap J K u O)) ↔
      ∀ V : C, IsIso ((lowerShriekForgetComparison u (structureMap J K u O)).app
            (extensionByZeroUnit (inverseImageRing J K u O) V) ≫
          (_root_.SheafOfModules.toSheaf O).map
            (pullbackExtensionByZeroUnitIso.{t, u₁, u₂, v₁, v₂} J K u O V).hom) := by
  rw [isIso_lowerShriekForgetComparison_iff]
  exact forall_congr' fun V =>
    (isIso_comp_right_iff _ ((_root_.SheafOfModules.toSheaf O).map
      (pullbackExtensionByZeroUnitIso.{t, u₁, u₂, v₁, v₂} J K u O V).hom)).symm

end SourceForm

end Stacks.SheafOfModules
