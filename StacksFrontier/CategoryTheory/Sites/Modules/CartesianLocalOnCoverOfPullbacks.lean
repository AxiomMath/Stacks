module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianComposition
public import StacksFrontier.CategoryTheory.Sites.Modules.CartesianLocalOnCover

/-!
# Locality of the cartesian condition, with only the pullbacks it uses

`Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_cover` says that a presheaf of modules
is cartesian over a flat `f : U ⟶ V` as soon as it is cartesian on the base changes of a finite
cover `W i ⟶ V` and satisfies the sheaf axiom for that cover and for its base change. It is
stated for a category with all pullbacks. Its proof forms only the fibre products of the cover
with itself and with `f`, and those of the base-changed cover with itself; this file states the
same result with exactly those pullbacks as hypotheses, so that it applies on a site, such as the
lisse-étale site of an algebraic stack, which has fibre products along its covering morphisms but
not in general.

## Main results

* `Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_cover_of_hasPullback`: locality of
  the cartesian condition over a flat morphism, on a finite cover.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u v r m w

namespace Stacks.PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{r}}
  (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))

/-- **Being cartesian over `f` is local on a finite flat cover of the target.**  The base-change
comparison along `f : U ⟶ V` is an isomorphism as soon as the ring map along `f` is flat, `M`
satisfies the sheaf axiom for a finite family `W i ⟶ V` and for its base change to `U`, the
attached squares of rings are pushouts, and `M` is cartesian over the projections of those base
changes. -/
theorem isIso_restrictionBaseChange_of_cover_of_hasPullback
    {U V : C} (f : U ⟶ V)
    {I : Type w} [Finite I]
    (W : I → C) (g : ∀ i, W i ⟶ V)
    [∀ i, HasPullback f (g i)] [∀ i j, HasPullback (g i) (g j)]
    [∀ c : I × I, HasPullback f (pullback.fst (g c.1) (g c.2) ≫ g c.1)]
    [∀ i j, HasPullback (pullback.fst f (g i)) (pullback.fst f (g j))]
    (hflat : (R.map f.op).hom.Flat)
    (hsfV : Presieve.IsSheafFor (M.presheaf ⋙ forget AddCommGrpCat) (Presieve.ofArrows W g))
    (hsfU : Presieve.IsSheafFor (M.presheaf ⋙ forget AddCommGrpCat)
      (Presieve.ofArrows (fun i => pullback f (g i)) (fun i => pullback.fst f (g i))))
    (hpo : ∀ i, IsPushout (R.map f.op) (R.map (g i).op)
      (R.map (pullback.fst f (g i)).op) (R.map (pullback.snd f (g i)).op))
    (hpo' : ∀ c : I × I,
      IsPushout (R.map f.op) (R.map (pullback.fst (g c.1) (g c.2) ≫ g c.1).op)
        (R.map (pullback.fst f (pullback.fst (g c.1) (g c.2) ≫ g c.1)).op)
        (R.map (pullback.snd f (pullback.fst (g c.1) (g c.2) ≫ g c.1)).op))
    (hcart : ∀ i, IsIso (restrictionBaseChange M (pullback.snd f (g i)).op))
    (hcart' : ∀ c : I × I, IsIso (restrictionBaseChange M
      (pullback.snd f (pullback.fst (g c.1) (g c.2) ≫ g c.1)).op)) :
    IsIso (restrictionBaseChange M f.op) := by
  have _ : (Presieve.ofArrows W g).HasPairwisePullbacks := by
    constructor
    rintro _ _ _ ⟨⟩ _ ⟨⟩
    infer_instance
  let algB := algebraOfRingHom (R := R) (R.map f.op)
  have : Module.Flat (R.obj (.op V)) (R.obj (.op U)) := hflat
  let T : I → C := fun i => pullback f (g i)
  let q : ∀ i, T i ⟶ U := fun i => pullback.fst f (g i)
  let pr : ∀ i, T i ⟶ W i := fun i => pullback.snd f (g i)
  let w1 : ∀ c : I × I, pullback (g c.1) (g c.2) ⟶ W c.1 := fun c => pullback.fst (g c.1) (g c.2)
  let w2 : ∀ c : I × I, pullback (g c.1) (g c.2) ⟶ W c.2 := fun c => pullback.snd (g c.1) (g c.2)
  let Wp : I × I → C := fun c => pullback (g c.1) (g c.2)
  let gp : ∀ c : I × I, Wp c ⟶ V := fun c => w1 c ≫ g c.1
  let Tp : I × I → C := fun c => pullback f (gp c)
  let qp : ∀ c : I × I, Tp c ⟶ U := fun c => pullback.fst f (gp c)
  let pp : ∀ c : I × I, Tp c ⟶ Wp c := fun c => pullback.snd f (gp c)
  have hw : ∀ c : I × I, w1 c ≫ g c.1 = w2 c ≫ g c.2 := fun c => pullback.condition
  let mc : ∀ c : I × I, Tp c ⟶ T c.1 := fun c =>
    pullback.lift (qp c) (pp c ≫ w1 c) (by rw [Category.assoc]; exact pullback.condition)
  let mc' : ∀ c : I × I, Tp c ⟶ T c.2 := fun c =>
    pullback.lift (qp c) (pp c ≫ w2 c)
      (by rw [Category.assoc, ← hw c]; exact pullback.condition)
  have hmc1 : ∀ c : I × I, mc c ≫ q c.1 = qp c := fun c => pullback.lift_fst _ _ _
  have hmc2 : ∀ c : I × I, mc c ≫ pr c.1 = pp c ≫ w1 c := fun c => pullback.lift_snd _ _ _
  have hmc1' : ∀ c : I × I, mc' c ≫ q c.2 = qp c := fun c => pullback.lift_fst _ _ _
  have hmc2' : ∀ c : I × I, mc' c ≫ pr c.2 = pp c ≫ w2 c := fun c => pullback.lift_snd _ _ _
  let instMi : ∀ i, Module (R.obj (.op V)) (M.obj (.op (W i))) :=
    fun i => moduleOfRingHom M (R.map (g i).op)
  let instMp : ∀ c : I × I, Module (R.obj (.op V)) (M.obj (.op (Wp c))) :=
    fun c => moduleOfRingHom M (R.map (gp c).op)
  let instMUi : ∀ i, Module (R.obj (.op V)) (M.obj (.op (T i))) :=
    fun i => moduleOfRingHom M (R.map f.op ≫ R.map (q i).op)
  let instMUp : ∀ c : I × I, Module (R.obj (.op V)) (M.obj (.op (Tp c))) :=
    fun c => moduleOfRingHom M (R.map f.op ≫ R.map (qp c).op)
  let instMU : Module (R.obj (.op V)) (M.obj (.op U)) := moduleOfRingHom M (R.map f.op)
  let towU : IsScalarTower (R.obj (.op V)) (R.obj (.op U)) (M.obj (.op U)) :=
    ⟨fun x y z => mul_smul _ _ _⟩
  let ε : M.obj (.op V) →ₗ[R.obj (.op V)] ∀ i, M.obj (.op (W i)) :=
    LinearMap.pi (fun i => restrictionLinear M (g i))
  let εU : M.obj (.op U) →ₗ[R.obj (.op V)] ∀ i, M.obj (.op (T i)) :=
    LinearMap.pi (fun i =>
      restrictionLinearOf M (R.map f.op ≫ R.map (q i).op) (R.map f.op) (q i) rfl)
  let δ : ∀ c : I × I, M.obj (.op (W c.1)) →ₗ[R.obj (.op V)] M.obj (.op (Wp c)) := fun c =>
    restrictionLinearOf M (R.map (gp c).op) (R.map (g c.1).op) (w1 c) (by
      change R.map (w1 c ≫ g c.1).op = _
      rw [op_comp, R.map_comp])
  let δ' : ∀ c : I × I, M.obj (.op (W c.2)) →ₗ[R.obj (.op V)] M.obj (.op (Wp c)) := fun c =>
    restrictionLinearOf M (R.map (gp c).op) (R.map (g c.2).op) (w2 c) (by
      change R.map (w1 c ≫ g c.1).op = _
      rw [hw c, op_comp, R.map_comp])
  let ρ : ∀ c : I × I, M.obj (.op (T c.1)) →ₗ[R.obj (.op V)] M.obj (.op (Tp c)) := fun c =>
    restrictionLinearOf M (R.map f.op ≫ R.map (qp c).op)
      (R.map f.op ≫ R.map (q c.1).op) (mc c) (by
        rw [Category.assoc]
        congr 1
        rw [← R.map_comp, ← op_comp, hmc1 c])
  let ρ' : ∀ c : I × I, M.obj (.op (T c.2)) →ₗ[R.obj (.op V)] M.obj (.op (Tp c)) := fun c =>
    restrictionLinearOf M (R.map f.op ≫ R.map (qp c).op)
      (R.map f.op ≫ R.map (q c.2).op) (mc' c) (by
        rw [Category.assoc]
        congr 1
        rw [← R.map_comp, ← op_comp, hmc1' c])
  let Φ : (∀ i, M.obj (.op (W i))) →ₗ[R.obj (.op V)] (∀ c : I × I, M.obj (.op (Wp c))) :=
    LinearMap.pi (fun c => δ c ∘ₗ LinearMap.proj c.1 - δ' c ∘ₗ LinearMap.proj c.2)
  let ψ : ∀ i, (R.obj (.op U)) ⊗[R.obj (.op V)] (M.obj (.op (W i)))
      ≃ₗ[R.obj (.op V)] M.obj (.op (T i)) := fun i =>
    LinearEquiv.ofBijective (restrictionBaseChangeOfSquare M f (g i) (q i) (pr i) (hpo i).w)
      (bijective_restrictionBaseChangeOfSquare M f (g i) (q i) (pr i) (hpo i).w
        (hpo i) (hcart i))
  let ψ' : ∀ c : I × I, (R.obj (.op U)) ⊗[R.obj (.op V)] (M.obj (.op (Wp c)))
      ≃ₗ[R.obj (.op V)] M.obj (.op (Tp c)) := fun c =>
    LinearEquiv.ofBijective (restrictionBaseChangeOfSquare M f (gp c) (qp c) (pp c) (hpo' c).w)
      (bijective_restrictionBaseChangeOfSquare M f (gp c) (qp c) (pp c) (hpo' c).w
        (hpo' c) (hcart' c))
  let θ : (R.obj (.op U)) ⊗[R.obj (.op V)] (M.obj (.op V)) →ₗ[R.obj (.op V)] M.obj (.op U) :=
    { toFun := fun z => restrictionBaseChange M f.op z
      map_add' := fun z z' => map_add (restrictionBaseChange M f.op).hom z z'
      map_smul' := fun c z => by
        have h := (restrictionBaseChange M f.op).hom.map_smul
          (algebraMap (R.obj (.op V)) (R.obj (.op U)) c) z
        rw [algebraMap_smul] at h
        exact h }
  have hψgen : ∀ (c : I × I) (j : I) (m : Tp c ⟶ T j) (w : Wp c ⟶ W j),
      m ≫ q j = qp c → m ≫ pr j = pp c ≫ w → ∀ (b : R.obj (.op U)) (x : M.obj (.op (W j))),
      (R.map (qp c).op).hom b • (M.map (pp c).op (M.map w.op x) : M.obj (.op (Tp c))) =
        M.map m.op ((R.map (q j).op).hom b • (M.map (pr j).op x : M.obj (.op (T j)))) := by
    intro c j m w hq hp b x
    have hm : (M.map m.op (M.map (pr j).op x) : M.obj (.op (Tp c)))
        = M.map (pp c).op (M.map w.op x) := by
      rw [← M.map_comp_apply, ← M.map_comp_apply, ← op_comp, ← op_comp, hp]
    have hsc : ((R ⋙ forget₂ CommRingCat RingCat).map m.op) ((R.map (q j).op).hom b)
        = (R.map (qp c).op).hom b := by
      change ((R.map (q j).op) ≫ (R.map m.op)).hom b = (R.map (qp c).op).hom b
      rw [← R.map_comp, ← op_comp, hq]
    have key : ((R ⋙ forget₂ CommRingCat RingCat).map m.op) ((R.map (q j).op).hom b) •
          (M.map m.op (M.map (pr j).op x) : M.obj (.op (Tp c)))
        = (R.map (qp c).op).hom b • (M.map (pp c).op (M.map w.op x) : M.obj (.op (Tp c))) := by
      rw [hsc, hm]
      rfl
    exact key.symm.trans (M.map_smul m.op _ _).symm
  have hV := (Presieve.isSheafFor_arrows_iff_pullbacks _ _).mp hsfV
  have hbij : Function.Bijective θ := by
    refine Module.Descent.bijective_of_flat_descent ε ?_ δ δ' Φ ?_ ?_ εU ?_ ρ ρ' ?_ ψ ψ' ?_ ?_
      θ ?_
    · exact fun x y hxy => hsfV.isSeparatedFor.ext (by rintro _ _ ⟨i⟩; exact congrFun hxy i)
    · exact fun _ _ => rfl
    · intro mm
      constructor
      · intro h0
        have hcompat : Presieve.Arrows.PullbackCompatible
            (M.presheaf ⋙ forget AddCommGrpCat) g mm := fun i j =>
          sub_eq_zero.mp (congrFun h0 (i, j) : δ (i, j) (mm i) - δ' (i, j) (mm j) = 0)
        obtain ⟨t, ht, _⟩ := hV _ hcompat
        exact ⟨t, funext ht⟩
      · rintro ⟨t, rfl⟩
        funext c
        have e : ∀ (j : I) (w : Wp c ⟶ W j),
            (M.map w.op (M.map (g j).op t) : M.obj (.op (Wp c))) = M.map (w ≫ g j).op t := by
          intro j w
          rw [← M.map_comp_apply, ← op_comp]
        change δ c (ε t c.1) - δ' c (ε t c.2) = 0
        rw [show δ c (ε t c.1) = _ from e c.1 (w1 c), show δ' c (ε t c.2) = _ from e c.2 (w2 c),
          hw c]
        exact sub_self _
    · exact fun x y hxy => hsfU.isSeparatedFor.ext (by rintro _ _ ⟨i⟩; exact congrFun hxy i)
    · intro t c
      change M.map (mc c).op (M.map (q c.1).op t) = M.map (mc' c).op (M.map (q c.2).op t)
      rw [← M.map_comp_apply, ← M.map_comp_apply, ← op_comp, ← op_comp, hmc1 c, hmc1' c]
    · intro c b x
      exact hψgen c c.1 (mc c) (w1 c) (hmc1 c) (hmc2 c) b x
    · intro c b y
      exact hψgen c c.2 (mc' c) (w2 c) (hmc1' c) (hmc2' c) b y
    · intro b n i
      have hθt : (θ (b ⊗ₜ n) : M.obj (.op U)) = b • (M.map f.op n : M.obj (.op U)) :=
        restrictionBaseChange_tmul M f.op b n
      have hmv : (M.map (q i).op (M.map f.op n) : M.obj (.op (T i)))
          = M.map (pr i).op (M.map (g i).op n) := by
        rw [← M.map_comp_apply, ← M.map_comp_apply, ← op_comp, ← op_comp, pullback.condition]
      have key : ((R ⋙ forget₂ CommRingCat RingCat).map (q i).op) b •
            (M.map (q i).op (M.map f.op n) : M.obj (.op (T i)))
          = (R.map (q i).op).hom b •
            (M.map (pr i).op (M.map (g i).op n) : M.obj (.op (T i))) := by
        rw [hmv]
        rfl
      exact ((congrArg (fun z => (M.map (q i).op z : M.obj (.op (T i)))) hθt).trans
        (M.map_smul (q i).op b (M.map f.op n))).trans key
  exact (ConcreteCategory.isIso_iff_bijective _).2 hbij

end Stacks.PresheafOfModules

end
