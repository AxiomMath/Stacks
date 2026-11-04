module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalkModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicFiniteEtaleDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.StalkPointChange

/-!
# The stalks of the direct image of an ℓ-adic sheaf along a finite étale morphism

Let `π : X ⟶ Y` be a finite étale morphism of a big étale site and `F` an ℓ-adic sheaf on `X`
whose levels are locally constant of finite type, so that `π_* F` is the ℓ-adic sheaf
`AlgebraicGeometry.SmallEtale.LAdicSheaf.directImage`. At a geometric point `ȳ` of `Y`, the
level-`n` stalk of `π_* F` is the product of the level-`n` stalks of `F` at the lifts `x̄` of `ȳ`
(Tag 03QP for sheaves of modules, `AlgebraicGeometry.bijective_finitePushforwardStalkLiftHom`),
compatibly with the transitions; hence

  `(π_* F)_ȳ ≅ ∏_{x̄ ↦ ȳ} F_x̄`

as `ℤ_ℓ`-modules, and after extending scalars to `ℚ_ℓ` the rational stalk of `π_* F` is the
direct sum of the rational stalks of `F` at the lifts, with projections `pr_x̄` and inclusions
`inc_x̄`.

An endomorphism `a` of `ȳ` (for instance the geometric Frobenius at a closed point) acts on the
lifts by `x̄ ↦ a ≫ x̄`, a permutation `σ_a` when `a` is an epimorphism, and its action on
`(π_* F)_ȳ` carries the summand of `x̄` into the summand of `σ_a x̄`
(`AlgebraicGeometry.geometricPointStalkMap_comp_finitePushforwardStalkLiftHom`). If `a` fixes
`x̄`, then on the summand of `x̄` it acts as the endomorphism `a` of the geometric point `x̄`.
These are the hypotheses of
`Stacks.EtaleCohomology.norm_eq_of_permutedBlocks` and
`Stacks.EtaleCohomology.trace_pow_eq_sum_of_permutedBlocks`.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.directImageStalkLift`: the component at a lift.
* `Stacks.EtaleCohomology.LAdicSheaf.directImageStalkEquiv`: `(π_* F)_ȳ ≅ ∏_{x̄} F_x̄`.
* `Stacks.EtaleCohomology.LAdicSheaf.directImageRationalPr`,
  `Stacks.EtaleCohomology.LAdicSheaf.directImageRationalInc`: the rational projections and
  inclusions.
* `Stacks.EtaleCohomology.geometricLiftsPerm`: the permutation of the lifts.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.bijective_directImageStalkLift`.
* `Stacks.EtaleCohomology.LAdicSheaf.directImageRational_sum`,
  `…_pr_inc_self`, `…_pr_inc_of_ne`: the direct sum decomposition.
* `Stacks.EtaleCohomology.LAdicSheaf.rationalStalkEnd_directImage_comp_inc_comp_pr`: the action
  of `a` permutes the summands along `σ_a`.
* `Stacks.EtaleCohomology.LAdicSheaf.directImageRationalPr_comp_rationalStalkEnd_comp_inc`: on a
  fixed summand, the action of `a` is the action of `a` read at the lift.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale Opposite

universe u

namespace Stacks.EtaleCohomology

section Perm

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme} (π : X ⟶ Y) [IsFinite (B.inclusion.map π)]
  {y : GeometricPoint Y.1} (a : GeometricPoint.Hom y y) [Epi a.hom]

/-- An endomorphism of `ȳ` with epimorphic underlying morphism acts on the lifts of `ȳ`
by `x̄ ↦ a ≫ x̄`, a permutation: injective as `a` is an epimorphism, and the lifts are finite. -/
public def geometricLiftsPerm : Equiv.Perm (GeometricLifts B π y) :=
  haveI := finite_geometricLifts B π y
  Equiv.ofBijective (GeometricLifts.comap B π a)
    (Finite.injective_iff_bijective.1 fun _ _ h =>
      Subtype.ext ((cancel_epi a.hom).1 (congrArg Subtype.val h)))

/-- `geometricLiftsPerm π a` sends a lift `x̄` to `a ≫ x̄` (`GeometricLifts.comap`). -/
public theorem geometricLiftsPerm_apply (x : GeometricLifts B π y) :
    geometricLiftsPerm π a x = GeometricLifts.comap B π a x :=
  rfl

end Perm

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme} (π : X ⟶ Y) [IsFinite (B.inclusion.map π)]
  [AlgebraicGeometry.Etale (B.inclusion.map π)] {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.obj] [IsNoetherian Y.obj]
  (F : LAdicSheaf.{u, u + 1} B X ℓ)
  (hF : ∀ n, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1)))
    (SmallEtale.topology B X.1 X.property) (F.level n))

/-! ### Finite levels -/

/-- The level-`n` component at a lift `x̄` of the stalk of `π_* F` at `ȳ`. -/
public abbrev directImageLevelStalkLift (y : GeometricPoint Y.1) (n : ℕ)
    (x : GeometricLifts B π y) :
    finiteLevelStalk B Y ℓ (SmallEtale.LAdicSheaf.directImage π F hF) y n ⟶
      finiteLevelStalk B X ℓ F (geometricPointLift (B.inclusion.map π) y x) n :=
  finitePushforwardStalkLiftHom B π y (ZMod (ℓ ^ (n + 1))) (F.level n) x

/-- A functor preserving colimits carries the inclusion into the colimit of a natural
transformation, followed by the comparison isomorphism, to the componentwise image. -/
private theorem ι_colimMap_preservesColimitIso_inv {C D J : Type*} [Category C] [Category D]
    [Category J] [HasColimitsOfShape J C] [HasColimitsOfShape J D] (R : C ⥤ D)
    [PreservesColimitsOfShape J R] {E : J ⥤ C} {E' : J ⥤ D} (w : E' ⟶ E ⋙ R) (j : J) :
    colimit.ι E' j ≫ colim.map w ≫ (preservesColimitIso R E).inv =
      w.app j ≫ R.map (colimit.ι E j) := by
  rw [colimit.ι_map_assoc, ι_preservesColimitIso_inv]

/-- The level components commute with the transitions. -/
public theorem directImageLevelStalkLift_comp_transition (y : GeometricPoint Y.1) (n : ℕ)
    (x : GeometricLifts B π y) :
    directImageLevelStalkLift π F hF y (n + 1) x ≫
        finiteLevelStalkTransition B X ℓ F (geometricPointLift (B.inclusion.map π) y x) n =
      finiteLevelStalkTransition B Y ℓ (SmallEtale.LAdicSheaf.directImage π F hF) y n ≫
        (ModuleCat.restrictScalars (finiteLevelRingHom ℓ n)).map
          (directImageLevelStalkLift π F hF y n x) := by
  apply colimit.hom_ext
  intro U
  let R := ModuleCat.restrictScalars (finiteLevelRingHom ℓ n)
  let L := op (liftedEtaleNeighborhood B π y x U.unop)
  let E := (CategoryOfElements.π (geometricPointFiber B X.1 X.property
    (geometricPointLift (B.inclusion.map π) y x))).op ⋙ (F.level n).obj
  let E' := (CategoryOfElements.π (geometricPointFiber B X.1 X.property
    (geometricPointLift (B.inclusion.map π) y x))).op ⋙ (F.level (n + 1)).obj
  let D := (CategoryOfElements.π (geometricPointFiber B Y.1 Y.property y)).op ⋙
    ((SmallEtale.LAdicSheaf.directImage π F hF).level n).obj
  let D' := (CategoryOfElements.π (geometricPointFiber B Y.1 Y.property y)).op ⋙
    ((SmallEtale.LAdicSheaf.directImage π F hF).level (n + 1)).obj
  let w := Functor.whiskerLeft (CategoryOfElements.π (geometricPointFiber B X.1 X.property
    (geometricPointLift (B.inclusion.map π) y x))).op (F.transition n).hom
  let wP := Functor.whiskerLeft (CategoryOfElements.π (geometricPointFiber B Y.1 Y.property y)).op
    ((SmallEtale.LAdicSheaf.directImage π F hF).transition n).hom
  have hl : colimit.ι D' U ≫ directImageLevelStalkLift π F hF y (n + 1) x = colimit.ι E' L :=
    ι_finitePushforwardStalkLiftHom B π y (ZMod (ℓ ^ (n + 1 + 1))) (F.level (n + 1)) x U
  have hl' : colimit.ι D U ≫ directImageLevelStalkLift π F hF y n x = colimit.ι E L :=
    ι_finitePushforwardStalkLiftHom B π y (ZMod (ℓ ^ (n + 1))) (F.level n) x U
  have hX := ι_colimMap_preservesColimitIso_inv R (E := E) w L
  have hY := ι_colimMap_preservesColimitIso_inv R (E := D) wP U
  have h3 : w.app L ≫ R.map (colimit.ι E L) =
      wP.app U ≫ R.map (colimit.ι D U ≫ directImageLevelStalkLift π F hF y n x) := by
    rw [hl']
    rfl
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hl)).trans ?_
  refine hX.trans (h3.trans ?_)
  refine ((congrArg (wP.app U ≫ ·) (R.map_comp _ _)).trans (Category.assoc _ _ _).symm).trans ?_
  exact (congrArg (· ≫ R.map (directImageLevelStalkLift π F hF y n x)) hY.symm).trans
    ((Category.assoc _ _ _).trans (congrArg (colimit.ι D' U ≫ ·) rfl))

/-- The level components commute with the transitions, on elements. -/
public theorem stalkTransition_directImageLevelStalkLift (y : GeometricPoint Y.1) (n : ℕ)
    (x : GeometricLifts B π y)
    (v : finiteLevelStalk B Y ℓ (SmallEtale.LAdicSheaf.directImage π F hF) y (n + 1)) :
    LAdicSheaf.stalkTransition B X ℓ F _ n ((directImageLevelStalkLift π F hF y (n + 1) x).hom v) =
      (directImageLevelStalkLift π F hF y n x).hom
        (LAdicSheaf.stalkTransition B Y ℓ (SmallEtale.LAdicSheaf.directImage π F hF) y n v) :=
  congrArg (fun g => g.hom v) (directImageLevelStalkLift_comp_transition π F hF y n x)

/-! ### The ℓ-adic stalk -/

/-- **The component at a lift of the stalk of `π_* F`**: the `ℤ_ℓ`-linear map
`(π_* F)_ȳ ⟶ F_x̄`, level by level. -/
public def LAdicSheaf.directImageStalkLift (y : GeometricPoint Y.1) (x : GeometricLifts B π y) :
    LAdicSheaf.stalk B Y ℓ (SmallEtale.LAdicSheaf.directImage π F hF) y →ₗ[PadicInt ℓ]
      LAdicSheaf.stalk B X ℓ F (geometricPointLift (B.inclusion.map π) y x) where
  toFun v := ⟨fun n => (directImageLevelStalkLift π F hF y n x).hom (v.1 n), fun n => by
    rw [stalkTransition_directImageLevelStalkLift π F hF y n x (v.1 (n + 1)), v.2 n]⟩
  map_add' v w := Subtype.ext (funext fun n => map_add _ _ _)
  map_smul' c v := Subtype.ext (funext fun n =>
    map_smul (directImageLevelStalkLift π F hF y n x).hom (PadicInt.toZModPow (n + 1) c) (v.1 n))

/-- Level `n` of the component of `v` at the lift `x̄` is the level-`n` stalk map applied to
level `n` of `v`. -/
public theorem LAdicSheaf.directImageStalkLift_apply_coe (y : GeometricPoint Y.1)
    (x : GeometricLifts B π y)
    (v : LAdicSheaf.stalk B Y ℓ (SmallEtale.LAdicSheaf.directImage π F hF) y) (n : ℕ) :
    (LAdicSheaf.directImageStalkLift π F hF y x v).1 n =
      (directImageLevelStalkLift π F hF y n x).hom (v.1 n) :=
  rfl

/-- **Tag 03QP for the ℓ-adic stalk of `π_* F`**: the components at the lifts are jointly
bijective, since they are at every level and commute with the transitions. -/
public theorem LAdicSheaf.bijective_directImageStalkLift (y : GeometricPoint Y.1) :
    Function.Bijective (fun (v : LAdicSheaf.stalk B Y ℓ
        (SmallEtale.LAdicSheaf.directImage π F hF) y)
      (x : GeometricLifts B π y) => LAdicSheaf.directImageStalkLift π F hF y x v) := by
  have hb := fun n => bijective_finitePushforwardStalkLiftHom B π y (ZMod (ℓ ^ (n + 1)))
    (F.level n)
  refine ⟨fun v w hvw => Subtype.ext (funext fun n => (hb n).1 (funext fun x => ?_)), fun t => ?_⟩
  · exact congrArg (fun z : LAdicSheaf.stalk B X ℓ F _ => z.1 n) (congrFun hvw x)
  · choose v hv using fun n => (hb n).2 (fun x => (t x).1 n)
    refine ⟨⟨v, fun n => (hb n).1 (funext fun x => ?_)⟩, funext fun x => Subtype.ext
      (funext fun n => congrFun (hv n) x)⟩
    show (directImageLevelStalkLift π F hF y n x).hom
        (LAdicSheaf.stalkTransition B Y ℓ _ y n (v (n + 1))) =
      (directImageLevelStalkLift π F hF y n x).hom (v n)
    refine (stalkTransition_directImageLevelStalkLift π F hF y n x (v (n + 1))).symm.trans ?_
    have h1 := congrFun (hv (n + 1)) x
    have h2 := congrFun (hv n) x
    change (directImageLevelStalkLift π F hF y (n + 1) x).hom (v (n + 1)) = (t x).1 (n + 1) at h1
    change (directImageLevelStalkLift π F hF y n x).hom (v n) = (t x).1 n at h2
    rw [h1, h2]
    exact (t x).2 n

/-- **The stalk of `π_* F` at `ȳ` is the product of the stalks of `F` at the lifts of `ȳ`.** -/
public def LAdicSheaf.directImageStalkEquiv (y : GeometricPoint Y.1) :
    LAdicSheaf.stalk B Y ℓ (SmallEtale.LAdicSheaf.directImage π F hF) y ≃ₗ[PadicInt ℓ]
      (∀ x : GeometricLifts B π y,
        LAdicSheaf.stalk B X ℓ F (geometricPointLift (B.inclusion.map π) y x)) :=
  LinearEquiv.ofBijective (LinearMap.pi fun x => LAdicSheaf.directImageStalkLift π F hF y x)
    (LAdicSheaf.bijective_directImageStalkLift π F hF y)

/-- The component at `x̄` of the image of `v` under `directImageStalkEquiv` is
`directImageStalkLift` at `x̄` applied to `v`. -/
public theorem LAdicSheaf.directImageStalkEquiv_apply (y : GeometricPoint Y.1)
    (v : LAdicSheaf.stalk B Y ℓ (SmallEtale.LAdicSheaf.directImage π F hF) y)
    (x : GeometricLifts B π y) :
    LAdicSheaf.directImageStalkEquiv π F hF y v x = LAdicSheaf.directImageStalkLift π F hF y x v :=
  rfl

/-! ### The action of an endomorphism of the geometric point -/

section Action

variable {y : GeometricPoint Y.1} (a : GeometricPoint.Hom y y)

/-- The action of `a` on `(π_* F)_ȳ` followed by the component at `a ≫ x̄` vanishes on the
kernel of the component at `x̄`. -/
public theorem LAdicSheaf.directImageStalkLift_comap_stalkEnd_eq_zero (x : GeometricLifts B π y)
    (v : LAdicSheaf.stalk B Y ℓ (SmallEtale.LAdicSheaf.directImage π F hF) y)
    (hv : LAdicSheaf.directImageStalkLift π F hF y x v = 0) :
    LAdicSheaf.directImageStalkLift π F hF y (GeometricLifts.comap B π a x)
      (LAdicSheaf.stalkEnd B Y ℓ (SmallEtale.LAdicSheaf.directImage π F hF) a v) = 0 := by
  refine Subtype.ext (funext fun n => ?_)
  have h := congrArg (fun g => g.hom (v.1 n))
    (geometricPointStalkMap_comp_finitePushforwardStalkLiftHom B π a (ZMod (ℓ ^ (n + 1)))
      (F.level n) x)
  have hv' : (directImageLevelStalkLift π F hF y n x).hom (v.1 n) = 0 :=
    congrArg (fun z : LAdicSheaf.stalk B X ℓ F _ => z.1 n) hv
  show (directImageLevelStalkLift π F hF y n (GeometricLifts.comap B π a x)).hom
      ((finiteLevelStalkEnd B Y ℓ (SmallEtale.LAdicSheaf.directImage π F hF) a n).hom (v.1 n)) = 0
  refine h.trans ?_
  show ((geometricPointStalkMap B X.1 X.property (GeometricLifts.liftHom B π a x)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).app (F.level n).obj).hom
      ((directImageLevelStalkLift π F hF y n x).hom (v.1 n)) = 0
  rw [hv']
  exact map_zero _

/-- **On a summand fixed by `a`, the action of `a` is the action of `a` at the lift**: if
`a ≫ x̄ = x̄` and `b` is the endomorphism of the geometric point `x̄` with underlying morphism
that of `a`, then the component at `x̄` intertwines the actions of `a` and `b`. -/
public theorem LAdicSheaf.directImageStalkLift_stalkEnd_of_fixed (x : GeometricLifts B π y)
    (hx : a.hom ≫ x.1 = x.1)
    (b : GeometricPoint.Hom (geometricPointLift (B.inclusion.map π) y x)
      (geometricPointLift (B.inclusion.map π) y x)) (hb : b.hom = a.hom)
    (v : LAdicSheaf.stalk B Y ℓ (SmallEtale.LAdicSheaf.directImage π F hF) y) :
    LAdicSheaf.directImageStalkLift π F hF y x
        (LAdicSheaf.stalkEnd B Y ℓ (SmallEtale.LAdicSheaf.directImage π F hF) a v) =
      LAdicSheaf.stalkEnd B X ℓ F b (LAdicSheaf.directImageStalkLift π F hF y x v) := by
  refine Subtype.ext (funext fun n => ?_)
  exact congrArg (fun g => g.hom (v.1 n))
    (geometricPointStalkMap_comp_finitePushforwardStalkLiftHom_of_eq B π a (ZMod (ℓ ^ (n + 1)))
      (F.level n) x x hx.symm b hb)

end Action

/-! ### The rational stalk -/

section Rational

variable (y : GeometricPoint Y.1)

/-- The rational projection onto the summand of a lift. -/
public def LAdicSheaf.directImageRationalPr (x : GeometricLifts B π y) :
    LAdicSheaf.rationalStalkLeft B Y ℓ (SmallEtale.LAdicSheaf.directImage π F hF) y →ₗ[Padic ℓ]
      LAdicSheaf.rationalStalkLeft B X ℓ F (geometricPointLift (B.inclusion.map π) y x) :=
  (LAdicSheaf.directImageStalkLift π F hF y x).baseChange (Padic ℓ)

/-- The integral inclusion of the summand of a lift. -/
public def LAdicSheaf.directImageStalkInc [DecidableEq (GeometricLifts B π y)]
    (x : GeometricLifts B π y) :
    LAdicSheaf.stalk B X ℓ F (geometricPointLift (B.inclusion.map π) y x) →ₗ[PadicInt ℓ]
      LAdicSheaf.stalk B Y ℓ (SmallEtale.LAdicSheaf.directImage π F hF) y :=
  (LAdicSheaf.directImageStalkEquiv π F hF y).symm.toLinearMap ∘ₗ
    LinearMap.single (PadicInt ℓ)
      (fun x : GeometricLifts B π y =>
        LAdicSheaf.stalk B X ℓ F (geometricPointLift (B.inclusion.map π) y x)) x

/-- The rational inclusion of the summand of a lift. -/
public def LAdicSheaf.directImageRationalInc [DecidableEq (GeometricLifts B π y)]
    (x : GeometricLifts B π y) :
    LAdicSheaf.rationalStalkLeft B X ℓ F (geometricPointLift (B.inclusion.map π) y x) →ₗ[Padic ℓ]
      LAdicSheaf.rationalStalkLeft B Y ℓ (SmallEtale.LAdicSheaf.directImage π F hF) y :=
  (LAdicSheaf.directImageStalkInc π F hF y x).baseChange (Padic ℓ)

variable [DecidableEq (GeometricLifts B π y)]

/-- The component at `x̄'` of the inclusion of `w` at the summand `x̄` is `Pi.single x̄ w x̄'`. -/
theorem LAdicSheaf.directImageStalkLift_inc (x x' : GeometricLifts B π y)
    (w : LAdicSheaf.stalk B X ℓ F (geometricPointLift (B.inclusion.map π) y x)) :
    LAdicSheaf.directImageStalkLift π F hF y x' (LAdicSheaf.directImageStalkInc π F hF y x w) =
      Pi.single (M := fun x : GeometricLifts B π y =>
        LAdicSheaf.stalk B X ℓ F (geometricPointLift (B.inclusion.map π) y x)) x w x' := by
  rw [← LAdicSheaf.directImageStalkEquiv_apply, LAdicSheaf.directImageStalkInc,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rfl

/-- The component at a lift composed with the inclusion of its own summand is the identity. -/
theorem LAdicSheaf.directImageStalkLift_comp_inc_self (x : GeometricLifts B π y) :
    LAdicSheaf.directImageStalkLift π F hF y x ∘ₗ LAdicSheaf.directImageStalkInc π F hF y x =
      LinearMap.id :=
  LinearMap.ext fun w => by
    rw [LinearMap.comp_apply, LAdicSheaf.directImageStalkLift_inc, Pi.single_eq_same]
    rfl

/-- The component at `x̄'` composed with the inclusion of the summand of a different lift `x̄` is
zero. -/
theorem LAdicSheaf.directImageStalkLift_comp_inc_of_ne {x x' : GeometricLifts B π y}
    (h : x' ≠ x) :
    LAdicSheaf.directImageStalkLift π F hF y x' ∘ₗ LAdicSheaf.directImageStalkInc π F hF y x =
      0 :=
  LinearMap.ext fun w => by
    rw [LinearMap.comp_apply, LAdicSheaf.directImageStalkLift_inc, Pi.single_eq_of_ne h]
    rfl

/-- The integral inclusions and components decompose the stalk of `π_* F`:
`∑ x̄, inc x̄ ∘ lift x̄ = id`. -/
theorem LAdicSheaf.sum_directImageStalkInc_comp_lift [Fintype (GeometricLifts B π y)] :
    ∑ x, LAdicSheaf.directImageStalkInc π F hF y x ∘ₗ LAdicSheaf.directImageStalkLift π F hF y x =
      LinearMap.id := by
  refine LinearMap.ext fun v => (LAdicSheaf.directImageStalkEquiv π F hF y).injective
    (funext fun x' => ?_)
  rw [LinearMap.sum_apply, map_sum, Finset.sum_apply, LinearMap.id_apply,
    LAdicSheaf.directImageStalkEquiv_apply]
  rw [Finset.sum_eq_single x' (fun x _ hx => ?_) (fun h => absurd (Finset.mem_univ x') h)]
  · rw [LinearMap.comp_apply, LAdicSheaf.directImageStalkEquiv_apply,
      LAdicSheaf.directImageStalkLift_inc, Pi.single_eq_same]
  · rw [LinearMap.comp_apply, LAdicSheaf.directImageStalkEquiv_apply,
      LAdicSheaf.directImageStalkLift_inc, Pi.single_eq_of_ne' hx]

/-- The rational projections and inclusions decompose the rational stalk of `π_* F`. -/
public theorem LAdicSheaf.directImageRational_sum [Fintype (GeometricLifts B π y)] :
    ∑ x, LAdicSheaf.directImageRationalInc π F hF y x ∘ₗ
        LAdicSheaf.directImageRationalPr π F hF y x = LinearMap.id := by
  simp only [LAdicSheaf.directImageRationalInc, LAdicSheaf.directImageRationalPr,
    ← LinearMap.baseChange_comp]
  refine (map_sum (LinearMap.baseChangeHom (PadicInt ℓ) (Padic ℓ) _ _)
    (fun x => LAdicSheaf.directImageStalkInc π F hF y x ∘ₗ
      LAdicSheaf.directImageStalkLift π F hF y x) Finset.univ).symm.trans ?_
  show (∑ x, LAdicSheaf.directImageStalkInc π F hF y x ∘ₗ
    LAdicSheaf.directImageStalkLift π F hF y x).baseChange (Padic ℓ) = _
  rw [LAdicSheaf.sum_directImageStalkInc_comp_lift]
  exact LinearMap.baseChange_id

/-- The rational projection onto the summand of a lift, composed with its inclusion, is the
identity. -/
public theorem LAdicSheaf.directImageRational_pr_inc_self (x : GeometricLifts B π y) :
    LAdicSheaf.directImageRationalPr π F hF y x ∘ₗ LAdicSheaf.directImageRationalInc π F hF y x =
      LinearMap.id := by
  rw [LAdicSheaf.directImageRationalInc, LAdicSheaf.directImageRationalPr,
    ← LinearMap.baseChange_comp, LAdicSheaf.directImageStalkLift_comp_inc_self]
  exact LinearMap.baseChange_id

/-- The rational projection onto the summand of `x̄'`, composed with the inclusion of the summand
of a different lift `x̄`, is zero. -/
public theorem LAdicSheaf.directImageRational_pr_inc_of_ne (x x' : GeometricLifts B π y)
    (h : x' ≠ x) :
    LAdicSheaf.directImageRationalPr π F hF y x' ∘ₗ LAdicSheaf.directImageRationalInc π F hF y x =
      0 := by
  rw [LAdicSheaf.directImageRationalInc, LAdicSheaf.directImageRationalPr,
    ← LinearMap.baseChange_comp, LAdicSheaf.directImageStalkLift_comp_inc_of_ne π F hF y h]
  exact LinearMap.baseChange_zero

end Rational

/-! ### The action of an endomorphism of the geometric point on the rational stalk -/

section RationalAction

variable {y : GeometricPoint Y.1} (a : GeometricPoint.Hom y y) [Epi a.hom]
  [DecidableEq (GeometricLifts B π y)]

omit [AlgebraicGeometry.Etale (B.inclusion.map π)] [AlgebraicGeometry.IsNoetherian X.obj]
  [AlgebraicGeometry.IsNoetherian Y.obj] [DecidableEq (GeometricLifts B π y)] in
/-- The powers of the permutation of the lifts are the actions of the iterates. -/
public theorem geometricLiftsPerm_pow_succ_apply (e : ℕ) (x : GeometricLifts B π y) :
    ((geometricLiftsPerm π a) ^ (e + 1)) x = GeometricLifts.comap B π (a.iterate e) x := by
  induction e generalizing x with
  | zero => rw [zero_add, pow_one]; rfl
  | succ e ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih]
    exact Subtype.ext (Category.assoc _ _ _).symm

/-- **The action of `a` permutes the summands** of the integral stalk of `π_* F` along `σ_a`. -/
public theorem LAdicSheaf.stalkEnd_directImage_comp_inc_comp_lift (x : GeometricLifts B π y) :
    LAdicSheaf.stalkEnd B Y ℓ (SmallEtale.LAdicSheaf.directImage π F hF) a ∘ₗ
        LAdicSheaf.directImageStalkInc π F hF y x ∘ₗ LAdicSheaf.directImageStalkLift π F hF y x =
      LAdicSheaf.directImageStalkInc π F hF y (geometricLiftsPerm π a x) ∘ₗ
        LAdicSheaf.directImageStalkLift π F hF y (geometricLiftsPerm π a x) ∘ₗ
          LAdicSheaf.stalkEnd B Y ℓ (SmallEtale.LAdicSheaf.directImage π F hF) a := by
  refine LinearMap.ext fun v => (LAdicSheaf.directImageStalkEquiv π F hF y).injective
    (funext fun μ => ?_)
  simp only [LinearMap.comp_apply, LAdicSheaf.directImageStalkEquiv_apply]
  rw [LAdicSheaf.directImageStalkLift_inc]
  obtain ⟨x', rfl⟩ := (geometricLiftsPerm π a).surjective μ
  by_cases hx : x' = x
  · subst hx
    rw [Pi.single_eq_same]
    have h0 : LAdicSheaf.directImageStalkLift π F hF y x'
        (v - LAdicSheaf.directImageStalkInc π F hF y x'
          (LAdicSheaf.directImageStalkLift π F hF y x' v)) = 0 := by
      rw [map_sub, LAdicSheaf.directImageStalkLift_inc, Pi.single_eq_same, sub_self]
    have := LAdicSheaf.directImageStalkLift_comap_stalkEnd_eq_zero π F hF a x' _ h0
    rw [map_sub, map_sub, sub_eq_zero] at this
    exact this.symm
  · rw [Pi.single_eq_of_ne ((geometricLiftsPerm π a).injective.ne hx)]
    refine LAdicSheaf.directImageStalkLift_comap_stalkEnd_eq_zero π F hF a x' _ ?_
    rw [LAdicSheaf.directImageStalkLift_inc, Pi.single_eq_of_ne hx]

/-- **The action of `a` on the rational stalk of `π_* F` permutes the summands along `σ_a`**:
the hypothesis of `Stacks.EtaleCohomology.norm_eq_of_permutedBlocks`. -/
public theorem LAdicSheaf.rationalStalkEnd_directImage_comp_inc_comp_pr
    (x : GeometricLifts B π y) :
    LAdicSheaf.rationalStalkEnd B Y ℓ (SmallEtale.LAdicSheaf.directImage π F hF) a ∘ₗ
        LAdicSheaf.directImageRationalInc π F hF y x ∘ₗ
          LAdicSheaf.directImageRationalPr π F hF y x =
      LAdicSheaf.directImageRationalInc π F hF y (geometricLiftsPerm π a x) ∘ₗ
        LAdicSheaf.directImageRationalPr π F hF y (geometricLiftsPerm π a x) ∘ₗ
          LAdicSheaf.rationalStalkEnd B Y ℓ (SmallEtale.LAdicSheaf.directImage π F hF) a := by
  simp only [LAdicSheaf.rationalStalkEnd, LAdicSheaf.directImageRationalInc,
    LAdicSheaf.directImageRationalPr, ← LinearMap.baseChange_comp]
  rw [LAdicSheaf.stalkEnd_directImage_comp_inc_comp_lift]

/-- **On a summand fixed by a power of `a`, that power acts as an endomorphism of the geometric
point at the lift**: if `σ_a ^ (e + 1)` fixes `x̄` and `b` is an endomorphism of the geometric
point `x̄` with the underlying morphism of `a ^ (e + 1)`, then the diagonal block of the action of
`a ^ (e + 1)` at `x̄` is the action of `b` on the rational stalk of `F` at `x̄`. -/
public theorem LAdicSheaf.directImageRationalPr_comp_rationalStalkEnd_pow_comp_inc
    (x : GeometricLifts B π y) (e : ℕ) (hx : ((geometricLiftsPerm π a) ^ (e + 1)) x = x)
    (b : GeometricPoint.Hom (geometricPointLift (B.inclusion.map π) y x)
      (geometricPointLift (B.inclusion.map π) y x)) (hb : b.hom = (a.iterate e).hom) :
    LAdicSheaf.directImageRationalPr π F hF y x ∘ₗ
        (LAdicSheaf.rationalStalkEnd B Y ℓ (SmallEtale.LAdicSheaf.directImage π F hF) a ^
          (e + 1)) ∘ₗ
          LAdicSheaf.directImageRationalInc π F hF y x =
      LAdicSheaf.rationalStalkEnd B X ℓ F b := by
  have hfix : (a.iterate e).hom ≫ x.1 = x.1 := by
    have := congrArg Subtype.val hx
    rwa [geometricLiftsPerm_pow_succ_apply] at this
  have hZ : LAdicSheaf.directImageStalkLift π F hF y x ∘ₗ
      LAdicSheaf.stalkEnd B Y ℓ (SmallEtale.LAdicSheaf.directImage π F hF) (a.iterate e) ∘ₗ
        LAdicSheaf.directImageStalkInc π F hF y x = LAdicSheaf.stalkEnd B X ℓ F b := by
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      LAdicSheaf.directImageStalkLift_stalkEnd_of_fixed π F hF (a.iterate e) x hfix b hb,
      LAdicSheaf.directImageStalkLift_inc, Pi.single_eq_same]
  rw [← LAdicSheaf.rationalStalkEnd_iterate, LAdicSheaf.rationalStalkEnd,
    LAdicSheaf.directImageRationalInc, LAdicSheaf.directImageRationalPr,
    ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hZ]
  rfl

end RationalAction

end Stacks.EtaleCohomology

end
