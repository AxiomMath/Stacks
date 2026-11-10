module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.TangentChartBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.StageFactorization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFormallyEtale
public import StacksFrontier.Deformation.Artin.SliceTangentSpace
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissibleAdic

/-!
# Ring-valued charts of the first-order deformations of a point of a formal algebraic space

Let `P` be a locally Noetherian formal algebraic space over `S` and `p₀ ∈ P(T₀)` a point over
`Spec k`, where `Spec k ⟶ S` factors through an affine open `Spec Λ ⊆ S` with `Λ → k` finite. This
file attaches to every first-order deformation of `p₀` — a section of `P` over a test datum
`T = Spec k[V]` restricting to `p₀` — a ring map `R → k[V] ⊗_k l`, for a fixed finite extension
`l/k` and a fixed Noetherian `Λ`-algebra `R`, so that the hypotheses of
`Deformation.finiteDimensional_artinianTangentSpace_of_ringValue` hold.

The construction: an étale chart `X ⟶ P` by a Noetherian affine formal algebraic space receives
the restriction of `p₀` to `Spec l` for a finite extension `l/k`
(`AlgebraicGeometry.FormalSpace.exists_finite_extension_lift_of_isLocallySurjective_sigmaDesc`).
A deformation, restricted to `Spec (k[V] ⊗_k l)`, lifts uniquely along the chart because the
chart is formally étale and `Spec l ⟶ Spec (k[V] ⊗_k l)` is a square-zero thickening. The lift
factors uniquely through the stage `Spec (A ⧸ I²)` of the chart, `A` being its Noetherian adic
ring and `I` an ideal of definition, because the nilpotent elements of `k[V] ⊗_k l` multiply to
zero. Finally an affine open `Spec R` of that stage around the image of the closed point and over
`Spec Λ` turns the point into a ring map out of `R`.

## Main results

* `AlgebraicGeometry.FormalSpace.TangentChart.exists_ringChart`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace AlgebraicGeometry.FormalSpace.TangentChart

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The right `k`-module structure on `V` given by its left one through `MulOpposite.unop`. -/
local instance (V : FGModuleCat.{u} k) : Module kᵐᵒᵖ V :=
  Module.compHom V {
    toFun := MulOpposite.unop
    map_one' := rfl
    map_mul' := by simp [mul_comm]
    map_zero' := rfl
    map_add' _ _ := rfl }

/-- The left and right actions of `k` on `V` agree. -/
local instance (V : FGModuleCat.{u} k) : IsCentralScalar k V where
  op_smul_eq_smul _ _ := rfl

/-! ### Killing the square of an ideal of definition -/

section Kill

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] {I : Ideal A} (hI : _root_.IsAdic I)

/-- The weak ideal of definition `I²`. -/
abbrev sqIdeal : WeakIdeals A :=
  OrderDual.toDual ⟨I ^ (1 + 1), TopologicalRing.isWeakIdealOfDefinition_pow_of_isAdic hI 1⟩

omit [IsLinearTopology A A] in
/-- A ring map out of a quotient of `A` by an open ideal, into a ring whose nilpotent elements
multiply to zero, kills `I²`. -/
theorem map_eq_zero_of_mem_sqIdeal {C : Type u} [CommRing C]
    (hC : ∀ a b : C, IsNilpotent a → IsNilpotent b → a * b = 0) (M : WeakIdeals A)
    (ρ : A ⧸ M.1 →+* C) (x : A) (hx : x ∈ (sqIdeal hI).1) : ρ (Ideal.Quotient.mk M.1 x) = 0 := by
  have hnil : ∀ a ∈ I, IsNilpotent (ρ (Ideal.Quotient.mk M.1 a)) := by
    intro a ha
    have hM : (M.1 : Set A) ∈ nhds (0 : A) := M.2.1.mem_nhds M.1.zero_mem
    obtain ⟨n, hn⟩ := (isAdic_iff.mp hI).2 _ hM
    refine ⟨n, ?_⟩
    rw [← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.mpr (hn (Ideal.pow_mem_pow ha n)),
      map_zero]
  change x ∈ I ^ (1 + 1) at hx
  rw [show I ^ (1 + 1) = I * I by rw [pow_two]] at hx
  refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · simpa only [map_mul] using hC _ _ (hnil a ha) (hnil b hb)
  · rw [map_add, map_add, ha, hb, add_zero]

end Kill

/-! ### The stage of a point -/

section Stage

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : FppfSheaf B S hS} {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] (hA : TopologicalRing.IsWeaklyAdmissible A)
  (pres : WeakIdealColimitPresentation B S hS A X) {I : Ideal A} (hI : _root_.IsAdic I)

/-- The stage `Spec (A ⧸ I²)` of the presentation, as an object of the site. -/
abbrev sqStage : BigFppfOver B S hS :=
  (BigAffineFppf.inclusion B S hS).obj (pres.diagram.obj (sqIdeal hI))

/-- The factorization through the stage `Spec (A ⧸ I²)` of a point of `X` over an object of the
site whose underlying scheme is `Spec C`, for `C` whose nilpotent elements multiply to zero. -/
def stageOf {C : CommRingCat.{u}} (hC : ∀ a b : C, IsNilpotent a → IsNilpotent b → a * b = 0)
    {W : BigFppfOver B S hS} (eW : (BigFppfOver.toScheme B S hS).obj W = Spec C)
    (x : X.obj.obj (op W)) : W ⟶ sqStage pres hI :=
  (pres.existsUnique_stage_factor hA (sqIdeal hI) C W eW
    (map_eq_zero_of_mem_sqIdeal hI hC) ((Sheaf.sectionEquiv _).symm x)).exists.choose

/-- The point factors through its stage: composing the stage with the quotient map recovers the
point. -/
theorem stageOf_spec {C : CommRingCat.{u}}
    (hC : ∀ a b : C, IsNilpotent a → IsNilpotent b → a * b = 0)
    {W : BigFppfOver B S hS} (eW : (BigFppfOver.toScheme B S hS).obj W = Spec C)
    (x : X.obj.obj (op W)) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (stageOf hA pres hI hC eW x) ≫
      quotientMap B S hS A X pres (sqIdeal hI) = (Sheaf.sectionEquiv _).symm x :=
  (pres.existsUnique_stage_factor hA (sqIdeal hI) C W eW
    (map_eq_zero_of_mem_sqIdeal hI hC) ((Sheaf.sectionEquiv _).symm x)).exists.choose_spec

/-- The stage is the unique factorization of the point through `Spec (A ⧸ I²)`. -/
theorem stageOf_unique {C : CommRingCat.{u}}
    (hC : ∀ a b : C, IsNilpotent a → IsNilpotent b → a * b = 0)
    {W : BigFppfOver B S hS} (eW : (BigFppfOver.toScheme B S hS).obj W = Spec C)
    (x : X.obj.obj (op W)) (σ : W ⟶ sqStage pres hI)
    (hσ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map σ ≫
      quotientMap B S hS A X pres (sqIdeal hI) = (Sheaf.sectionEquiv _).symm x) :
    σ = stageOf hA pres hI hC eW x :=
  (pres.existsUnique_stage_factor hA (sqIdeal hI) C W eW
    (map_eq_zero_of_mem_sqIdeal hI hC) ((Sheaf.sectionEquiv _).symm x)).unique hσ
    (stageOf_spec hA pres hI hC eW x)

/-- The stage of a restricted point is the restricted stage. -/
theorem stageOf_map {C C' : CommRingCat.{u}}
    (hC : ∀ a b : C, IsNilpotent a → IsNilpotent b → a * b = 0)
    (hC' : ∀ a b : C', IsNilpotent a → IsNilpotent b → a * b = 0)
    {W W' : BigFppfOver B S hS} (eW : (BigFppfOver.toScheme B S hS).obj W = Spec C)
    (eW' : (BigFppfOver.toScheme B S hS).obj W' = Spec C') (g : W' ⟶ W)
    (x : X.obj.obj (op W)) :
    stageOf hA pres hI hC' eW' (X.obj.map g.op x) = g ≫ stageOf hA pres hI hC eW x := by
  symm
  apply stageOf_unique
  rw [Functor.map_comp, Category.assoc, stageOf_spec]
  apply (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).injective
  rw [Equiv.apply_symm_apply, Sheaf.sectionEquiv_map_comp, Equiv.apply_symm_apply]

/-- A point is determined by its stage. -/
theorem eq_of_stageOf_eq {C : CommRingCat.{u}}
    (hC : ∀ a b : C, IsNilpotent a → IsNilpotent b → a * b = 0)
    {W : BigFppfOver B S hS} (eW : (BigFppfOver.toScheme B S hS).obj W = Spec C)
    {x y : X.obj.obj (op W)} (h : stageOf hA pres hI hC eW x = stageOf hA pres hI hC eW y) :
    x = y := by
  apply (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm.injective
  rw [← stageOf_spec hA pres hI hC eW x, ← stageOf_spec hA pres hI hC eW y, h]

end Stage

/-! ### `Spec (k[V] ⊗_k l)` has one point -/

/-- The spectrum of `k[V] ⊗_k l` has exactly one point. -/
theorem subsingleton_spec_baseChange (l : Type u) [Field l] [Algebra k l]
    (V : FGModuleCat.{u} k) : Subsingleton (Spec (.of (TrivSqZeroExt k V ⊗[k] l))) := by
  have key : ∀ p : PrimeSpectrum (TrivSqZeroExt k V ⊗[k] l),
      p.asIdeal = RingHom.ker (residueHom l V).toRingHom := by
    intro p
    have hmax : (RingHom.ker (residueHom l V).toRingHom).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ (residueHom_surjective l V)
    refine (hmax.eq_of_le p.2.ne_top fun x hx => ?_).symm
    have hsq : x * x = 0 := mul_eq_zero_of_residueHom l V hx hx
    exact (p.2.mem_or_mem (hsq ▸ p.asIdeal.zero_mem)).elim id id
  exact ⟨fun p q => PrimeSpectrum.ext ((key p).trans (key q).symm)⟩

/-- In a field the nilpotent elements multiply to zero. -/
theorem field_mul_eq_zero_of_isNilpotent (l : Type u) [Field l] :
    ∀ a b : CommRingCat.of l, IsNilpotent a → IsNilpotent b → a * b = 0 :=
  fun a _ ha _ => by rw [ha.eq_zero, zero_mul]

/-- The ring map of a chart is compatible with precomposing the morphism with a spectrum map. -/
private theorem ringMap_eq_comp {S Y : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S} [IsOpenImmersion iΛ]
    {s : Y ⟶ S} {y : Y} (c : Deformation.Artin.SliceTangent.AffineChart iΛ s y)
    {A A' : CommRingCat.{u}} (β : A ⟶ A')
    (g : Spec A ⟶ Y) (g' : Spec A' ⟶ Y) (hg : Set.range g.base ⊆ c.U)
    (hg' : Set.range g'.base ⊆ c.U) (h : Spec.map β ≫ g = g') :
    c.ringMap g' hg' = c.ringMap g hg ≫ β := by
  subst h
  exact c.ringMap_comp β g hg hg'

/-! ### The ring-valued chart -/

section Value

open Deformation.Artin.SliceTangent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {iΛ : Spec (.of Λ) ⟶ S} {T₀ : BigFppfOver B S hS}
  {e₀ : (BigFppfOver.toScheme B S hS).obj T₀ = Spec (.of k)}
  (h₀ : B.inclusion.map T₀.hom = eqToHom e₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
  {P : FppfSheaf B S hS} (p₀ : P.obj.obj (op T₀))
  (l : Type u) [Field l] [Algebra k l] (hl : B.Contains (Spec (.of l)))
  {X : FppfSheaf B S hS} (f : X ⟶ P) (hf : Space.FormallyEtale f.hom)
  {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  (hA : TopologicalRing.IsWeaklyAdmissible A) (pres : WeakIdealColimitPresentation B S hS A X)
  {I : Ideal A} (hI : _root_.IsAdic I)
  (z : X.obj.obj (op (fieldExtensionObject T₀ e₀ l hl)))
  (hz : f.hom.app _ z = P.obj.map (fieldExtensionMap T₀ e₀ l hl).op p₀)

/-- The stage of the chart point over `Spec l`. -/
abbrev pointStage : fieldExtensionObject T₀ e₀ l hl ⟶ sqStage pres hI :=
  stageOf hA pres hI (field_mul_eq_zero_of_isNilpotent l) rfl z

include hl in
/-- The containment of the base change of a test datum. -/
theorem TestDatum.baseChange_contains {V : FGModuleCat.{u} k} (d : TestDatum iΛ T₀ e₀ V) :
    B.Contains (Spec (.of (TrivSqZeroExt k V ⊗[k] l))) :=
  BigFppfSite.contains_spec_tensorProduct B d.contains hl

include hz in
/-- The restriction of a deformation `p` of `p₀` to `Spec (k[V] ⊗_k l)` restricts along the closed
point `Spec l` to the image of the chart point `z`. -/
theorem TestDatum.lift_condition {V : FGModuleCat.{u} k} (d : TestDatum iΛ T₀ e₀ V)
    (p : P.obj.obj (op d.T)) (hp : P.obj.map d.j.op p = p₀) :
    f.hom.app _ z = P.obj.map (closedPointMap iΛ T₀ e₀ l h₀ V (d.baseChange_contains l hl) hl).op
      (P.obj.map (d.baseChangeMap l (d.baseChange_contains l hl)).op p) := by
  rw [hz, ← types_comp_apply (P.obj.map _) (P.obj.map _), ← Functor.map_comp, ← op_comp,
    d.closedPointMap_baseChangeMap l h₀ _ hl, op_comp, Functor.map_comp, types_comp_apply, hp]

/-- The lift along the chart of a deformation restricted to `Spec (k[V] ⊗_k l)`. -/
def TestDatum.liftOf {V : FGModuleCat.{u} k} (d : TestDatum iΛ T₀ e₀ V)
    (p : P.obj.obj (op d.T)) (hp : P.obj.map d.j.op p = p₀) :
    X.obj.obj (op (baseChange iΛ l V (d.baseChange_contains l hl))) :=
  (hf _ _ (inferInstanceAs (IsAffine (Spec (.of l))))
    (inferInstanceAs (IsAffine (Spec (.of (TrivSqZeroExt k V ⊗[k] l)))))
    (closedPointMap iΛ T₀ e₀ l h₀ V (d.baseChange_contains l hl) hl)
    (isSquareZeroClosedImmersion_closedPointMap l h₀ V _ hl) z _
    (d.lift_condition h₀ p₀ l hl f z hz p hp)).exists.choose

/-- The lift along the chart exists uniquely. -/
private theorem TestDatum.existsUnique_lift {V : FGModuleCat.{u} k} (d : TestDatum iΛ T₀ e₀ V)
    (hf : Space.FormallyEtale f.hom) (hz : f.hom.app _ z = P.obj.map
      (fieldExtensionMap T₀ e₀ l hl).op p₀) (p : P.obj.obj (op d.T))
    (hp : P.obj.map d.j.op p = p₀) :
    ∃! y : X.obj.obj (op (baseChange iΛ l V (d.baseChange_contains l hl))),
      X.obj.map (closedPointMap iΛ T₀ e₀ l h₀ V (d.baseChange_contains l hl) hl).op y = z ∧
        f.hom.app _ y = P.obj.map (d.baseChangeMap l (d.baseChange_contains l hl)).op p :=
  (hf _ _ (inferInstanceAs (IsAffine (Spec (.of l))))
    (inferInstanceAs (IsAffine (Spec (.of (TrivSqZeroExt k V ⊗[k] l)))))
    (closedPointMap iΛ T₀ e₀ l h₀ V (d.baseChange_contains l hl) hl)
    (isSquareZeroClosedImmersion_closedPointMap l h₀ V _ hl) z _
    (d.lift_condition h₀ p₀ l hl f z hz p hp))

/-- The lift restricts to the chart point `z` along the closed point and maps under the chart to
the restriction of the deformation. -/
theorem TestDatum.liftOf_spec {V : FGModuleCat.{u} k} (d : TestDatum iΛ T₀ e₀ V)
    (p : P.obj.obj (op d.T)) (hp : P.obj.map d.j.op p = p₀) :
    X.obj.map (closedPointMap iΛ T₀ e₀ l h₀ V (d.baseChange_contains l hl) hl).op
        (d.liftOf h₀ p₀ l hl f hf z hz p hp) = z ∧
      f.hom.app _ (d.liftOf h₀ p₀ l hl f hf z hz p hp) =
        P.obj.map (d.baseChangeMap l (d.baseChange_contains l hl)).op p :=
  (d.existsUnique_lift h₀ p₀ l hl f z hf hz p hp).exists.choose_spec

/-- The lift is the unique section of `X` over `Spec (k[V] ⊗_k l)` restricting to `z` and mapping
to the restriction of the deformation. -/
theorem TestDatum.liftOf_unique {V : FGModuleCat.{u} k} (d : TestDatum iΛ T₀ e₀ V)
    (p : P.obj.obj (op d.T)) (hp : P.obj.map d.j.op p = p₀)
    (y : X.obj.obj (op (baseChange iΛ l V (d.baseChange_contains l hl))))
    (hy₁ : X.obj.map (closedPointMap iΛ T₀ e₀ l h₀ V (d.baseChange_contains l hl) hl).op y = z)
    (hy₂ : f.hom.app _ y = P.obj.map (d.baseChangeMap l (d.baseChange_contains l hl)).op p) :
    y = d.liftOf h₀ p₀ l hl f hf z hz p hp :=
  (d.existsUnique_lift h₀ p₀ l hl f z hf hz p hp).unique ⟨hy₁, hy₂⟩
    (d.liftOf_spec h₀ p₀ l hl f hf z hz p hp)

/-- The stage of the lift of a deformation. -/
abbrev TestDatum.stage {V : FGModuleCat.{u} k} (d : TestDatum iΛ T₀ e₀ V)
    (p : P.obj.obj (op d.T)) (hp : P.obj.map d.j.op p = p₀) :
    baseChange iΛ l V (d.baseChange_contains l hl) ⟶ sqStage pres hI :=
  stageOf hA pres hI (fun _ _ ha hb => mul_eq_zero_of_isNilpotent l V ha hb) rfl
    (d.liftOf h₀ p₀ l hl f hf z hz p hp)

/-- The stage of the lift restricts along the closed point to the stage of the chart point. -/
theorem TestDatum.closedPointMap_stage {V : FGModuleCat.{u} k} (d : TestDatum iΛ T₀ e₀ V)
    (p : P.obj.obj (op d.T)) (hp : P.obj.map d.j.op p = p₀) :
    closedPointMap iΛ T₀ e₀ l h₀ V (d.baseChange_contains l hl) hl ≫
      d.stage h₀ p₀ l hl f hf hA pres hI z hz p hp = pointStage l hl hA pres hI z := by
  rw [← stageOf_map hA pres hI _ (field_mul_eq_zero_of_isNilpotent l) rfl rfl,
    (d.liftOf_spec h₀ p₀ l hl f hf z hz p hp).1]

include h₀ in
/-- The chart point lies over `Spec l ⟶ Spec Λ ⟶ S`. -/
theorem pointStage_comp : B.inclusion.map (pointStage l hl hA pres hI z).left ≫
    B.inclusion.map (sqStage pres hI).hom =
      Spec.map (CommRingCat.ofHom ((algebraMap k l).comp (algebraMap Λ k))) ≫ iΛ := by
  rw [← Functor.map_comp, Over.w]
  change B.inclusion.map (_ ≫ T₀.hom) = _
  rw [Functor.map_comp, Functor.map_preimage, Category.assoc, h₀, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp, ← Category.assoc, ← Spec.map_comp]
  rfl

section Chart

variable [IsOpenImmersion iΛ]
  (c : AffineChart iΛ (B.inclusion.map (sqStage pres hI).hom)
    ((B.inclusion.map (pointStage l hl hA pres hI z).left).base (closedPt (.of l))))

omit [IsOpenImmersion iΛ] in
/-- The stage of the lift, composed with `Spec l ⟶ Spec (k[V] ⊗_k l)`, is the stage of the chart
point. -/
theorem TestDatum.specMap_residueHom_stage {V : FGModuleCat.{u} k} (d : TestDatum iΛ T₀ e₀ V)
    (p : P.obj.obj (op d.T)) (hp : P.obj.map d.j.op p = p₀) :
    Spec.map (CommRingCat.ofHom (residueHom l V).toRingHom) ≫
      B.inclusion.map (d.stage h₀ p₀ l hl f hf hA pres hI z hz p hp).left =
        B.inclusion.map (pointStage l hl hA pres hI z).left := by
  rw [← toScheme_closedPointMap l h₀ V (d.baseChange_contains l hl) hl, ← Functor.map_comp,
    ← Over.comp_left, d.closedPointMap_stage h₀ p₀ l hl f hf hA pres hI z hz p hp]

omit [Algebra Λ k] [IsOpenImmersion iΛ] in
/-- The stage of the chart point lands in the affine open of the chart. -/
theorem range_pointStage : Set.range (B.inclusion.map (pointStage l hl hA pres hI z).left).base ⊆
    c.U := by
  rintro _ ⟨x, rfl⟩
  obtain rfl : x = closedPt (.of l) := @Subsingleton.elim (Spec (.of l)) inferInstance x _
  exact c.mem

omit [IsOpenImmersion iΛ] in
/-- The stage of the lift of a deformation lands in the affine open of the chart. -/
theorem TestDatum.range_stage {V : FGModuleCat.{u} k} (d : TestDatum iΛ T₀ e₀ V)
    (p : P.obj.obj (op d.T)) (hp : P.obj.map d.j.op p = p₀) :
    Set.range (B.inclusion.map (d.stage h₀ p₀ l hl f hf hA pres hI z hz p hp).left).base ⊆
      c.U := by
  rintro _ ⟨x, rfl⟩
  obtain rfl : x = (Spec.map (CommRingCat.ofHom (residueHom l V).toRingHom)).base
      (closedPt (.of l)) :=
    @Subsingleton.elim (Spec (.of (TrivSqZeroExt k V ⊗[k] l))) (subsingleton_spec_baseChange l V)
      x _
  rw [← Scheme.Hom.comp_apply, d.specMap_residueHom_stage h₀ p₀ l hl f hf hA pres hI z hz p hp]
  exact range_pointStage l hl hA pres hI z c ⟨_, rfl⟩

/-- The ring map out of the chart ring attached to a first-order deformation. -/
def TestDatum.ringValue {V : FGModuleCat.{u} k} (d : TestDatum iΛ T₀ e₀ V)
    (p : P.obj.obj (op d.T)) (hp : P.obj.map d.j.op p = p₀) :
    c.ring ⟶ CommRingCat.of (TrivSqZeroExt k V ⊗[k] l) :=
  c.ringMap (A := CommRingCat.of (TrivSqZeroExt k V ⊗[k] l))
    (B.inclusion.map (d.stage h₀ p₀ l hl f hf hA pres hI z hz p hp).left)
    (d.range_stage h₀ p₀ l hl f hf hA pres hI z hz c p hp)

/-- The ring map out of the chart ring attached to the chart point. -/
def pointValue : c.ring ⟶ CommRingCat.of l :=
  c.ringMap (A := CommRingCat.of l) (B.inclusion.map (pointStage l hl hA pres hI z).left)
    (range_pointStage l hl hA pres hI z c)

/-- The ring map attached to a deformation reduces to the ring map attached to the chart point. -/
theorem TestDatum.ringValue_residueHom {V : FGModuleCat.{u} k} (d : TestDatum iΛ T₀ e₀ V)
    (p : P.obj.obj (op d.T)) (hp : P.obj.map d.j.op p = p₀) :
    d.ringValue h₀ p₀ l hl f hf hA pres hI z hz c p hp ≫
      CommRingCat.ofHom (residueHom l V).toRingHom = pointValue l hl hA pres hI z c := by
  exact (ringMap_eq_comp c _ _ _ _ _
    (d.specMap_residueHom_stage h₀ p₀ l hl f hf hA pres hI z hz p hp)).symm

/-- The ring map attached to a deformation is compatible with the structure maps from `Λ`. -/
theorem TestDatum.structureMap_ringValue {V : FGModuleCat.{u} k} (d : TestDatum iΛ T₀ e₀ V)
    (p : P.obj.obj (op d.T)) (hp : P.obj.map d.j.op p = p₀) :
    c.structureMap ≫ d.ringValue h₀ p₀ l hl f hf hA pres hI z hz c p hp =
      CommRingCat.ofHom (structureHom l V) := by
  apply c.structureMap_ringMap
  have := congrArg B.inclusion.map (Over.w (d.stage h₀ p₀ l hl f hf hA pres hI z hz p hp))
  rwa [Functor.map_comp] at this

include h₀ in
/-- The ring map attached to the chart point is compatible with the structure maps from `Λ`. -/
theorem structureMap_pointValue :
    c.structureMap ≫ pointValue l hl hA pres hI z c =
      CommRingCat.ofHom ((algebraMap k l).comp (algebraMap Λ k)) :=
  c.structureMap_ringMap _ _ _ (pointStage_comp h₀ l hl hA pres hI z)

omit [IsOpenImmersion iΛ] in
/-- The lift of a deformation is compatible with morphisms of test data. -/
theorem TestDatum.Hom.liftOf_eq {V V' : FGModuleCat.{u} k} {g : V ⟶ V'}
    {d : TestDatum iΛ T₀ e₀ V} {d' : TestDatum iΛ T₀ e₀ V'} (φ : TestDatum.Hom g d d')
    (p : P.obj.obj (op d.T)) (hp : P.obj.map d.j.op p = p₀)
    (p' : P.obj.obj (op d'.T)) (hp' : P.obj.map d'.j.op p' = p₀)
    (hpp : p' = P.obj.map φ.m.op p) :
    d'.liftOf h₀ p₀ l hl f hf z hz p' hp' = X.obj.map (baseChangeMorph l g
      (d.baseChange_contains l hl) (d'.baseChange_contains l hl)).op
        (d.liftOf h₀ p₀ l hl f hf z hz p hp) := by
  symm
  refine d'.liftOf_unique h₀ p₀ l hl f hf z hz p' hp' _ ?_ ?_
  · rw [← types_comp_apply (X.obj.map _) (X.obj.map _), ← Functor.map_comp, ← op_comp,
      closedPointMap_baseChangeMorph h₀ l g _ _ hl]
    exact (d.liftOf_spec h₀ p₀ l hl f hf z hz p hp).1
  · rw [NatTrans.naturality_apply, (d.liftOf_spec h₀ p₀ l hl f hf z hz p hp).2,
      ← types_comp_apply (P.obj.map _) (P.obj.map _), ← Functor.map_comp, ← op_comp,
      ← φ.baseChangeMap_comp l _ _, op_comp, Functor.map_comp, types_comp_apply, hpp]

omit [IsOpenImmersion iΛ] in
/-- The stage of the lift of a deformation is compatible with morphisms of test data. -/
theorem TestDatum.Hom.stage_eq {V V' : FGModuleCat.{u} k} {g : V ⟶ V'}
    {d : TestDatum iΛ T₀ e₀ V} {d' : TestDatum iΛ T₀ e₀ V'} (φ : TestDatum.Hom g d d')
    (p : P.obj.obj (op d.T)) (hp : P.obj.map d.j.op p = p₀)
    (p' : P.obj.obj (op d'.T)) (hp' : P.obj.map d'.j.op p' = p₀)
    (hpp : p' = P.obj.map φ.m.op p) :
    d'.stage h₀ p₀ l hl f hf hA pres hI z hz p' hp' =
      baseChangeMorph l g (d.baseChange_contains l hl) (d'.baseChange_contains l hl) ≫
        d.stage h₀ p₀ l hl f hf hA pres hI z hz p hp := by
  rw [TestDatum.stage, φ.liftOf_eq h₀ p₀ l hl f hf z hz p hp p' hp' hpp]
  exact stageOf_map hA pres hI _ _ rfl rfl _ _

/-- The ring map attached to a deformation is compatible with morphisms of test data. -/
theorem TestDatum.Hom.ringValue_eq {V V' : FGModuleCat.{u} k} {g : V ⟶ V'}
    {d : TestDatum iΛ T₀ e₀ V} {d' : TestDatum iΛ T₀ e₀ V'} (φ : TestDatum.Hom g d d')
    (p : P.obj.obj (op d.T)) (hp : P.obj.map d.j.op p = p₀)
    (p' : P.obj.obj (op d'.T)) (hp' : P.obj.map d'.j.op p' = p₀)
    (hpp : p' = P.obj.map φ.m.op p) :
    d'.ringValue h₀ p₀ l hl f hf hA pres hI z hz c p' hp' =
      d.ringValue h₀ p₀ l hl f hf hA pres hI z hz c p hp ≫ CommRingCat.ofHom
        (Algebra.TensorProduct.map (TrivSqZeroExt.map g.hom.hom) (AlgHom.id k l)).toRingHom := by
  have e : Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (TrivSqZeroExt.map g.hom.hom) (AlgHom.id k l)).toRingHom) ≫
        B.inclusion.map (d.stage h₀ p₀ l hl f hf hA pres hI z hz p hp).left =
      B.inclusion.map (d'.stage h₀ p₀ l hl f hf hA pres hI z hz p' hp').left := by
    rw [φ.stage_eq h₀ p₀ l hl f hf hA pres hI z hz p hp p' hp' hpp, Over.comp_left,
      Functor.map_comp, toScheme_baseChangeMorph]
  exact ringMap_eq_comp c _ _ _ _ _ e

omit [IsOpenImmersion iΛ] in
/-- A deformation of `p₀` over a test datum is determined by its ring map. -/
theorem TestDatum.ringValue_injective [Module.Finite k l] {V : FGModuleCat.{u} k}
    (d : TestDatum iΛ T₀ e₀ V) (p : P.obj.obj (op d.T)) (hp : P.obj.map d.j.op p = p₀)
    (p' : P.obj.obj (op d.T)) (hp' : P.obj.map d.j.op p' = p₀)
    (h : d.ringValue h₀ p₀ l hl f hf hA pres hI z hz c p hp =
      d.ringValue h₀ p₀ l hl f hf hA pres hI z hz c p' hp') : p = p' := by
  have h₁ : d.stage h₀ p₀ l hl f hf hA pres hI z hz p hp =
      d.stage h₀ p₀ l hl f hf hA pres hI z hz p' hp' :=
    Over.OverMorphism.ext (B.inclusion.map_injective (c.ringMap_injective _ _ h))
  refine d.injective_map_baseChangeMap l P.property (d.baseChange_contains l hl) ?_
  rw [← (d.liftOf_spec h₀ p₀ l hl f hf z hz p hp).2,
    ← (d.liftOf_spec h₀ p₀ l hl f hf z hz p' hp').2, eq_of_stageOf_eq hA pres hI _ rfl h₁]

end Chart

end Value

/-! ### Existence of a ring-valued chart -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {iΛ : Spec (.of Λ) ⟶ S} {T₀ : BigFppfOver B S hS}
  {e₀ : (BigFppfOver.toScheme B S hS).obj T₀ = Spec (.of k)}

/-- **Ring-valued charts of the first-order deformations of a point of a locally Noetherian
formal algebraic space.** Let `P` be a locally Noetherian formal algebraic space over `S` and
`p₀ ∈ P(T₀)` a point over `Spec k ⟶ Spec Λ ⟶ S`, with `Spec Λ ⊆ S` open, `Λ` Noetherian and
`Λ → k` finite. Then there are a finite extension `l/k`, a Noetherian `Λ`-algebra `R`, a map
`φ₀ : R → l` compatible with `Λ`, and for every first-order deformation `p` of `p₀` over a test
datum `Spec k[V]` a `Λ`-algebra map `R → k[V] ⊗_k l` reducing to `φ₀`, compatible with the
morphisms of test data, and determining `p`. -/
theorem exists_ringChart [IsNoetherianRing Λ] [IsOpenImmersion iΛ]
    (h₀ : B.inclusion.map T₀.hom = eqToHom e₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
    {P : FppfSheaf B S hS} (hP : IsLocallyNoetherian B S hS P) (p₀ : P.obj.obj (op T₀)) :
    ∃ (l : Type u) (_ : Field l) (_ : Algebra k l) (_ : Module.Finite k l) (_ : Algebra Λ l)
      (_ : IsScalarTower Λ k l) (R : Type u) (_ : CommRing R) (_ : Algebra Λ R)
      (_ : IsNoetherianRing R) (φ₀ : R →+* l)
      (value : ∀ (V : FGModuleCat.{u} k) (d : TestDatum iΛ T₀ e₀ V) (p : P.obj.obj (op d.T)),
        P.obj.map d.j.op p = p₀ → (R →+* TrivSqZeroExt k V ⊗[k] l)),
      (∀ r : Λ, φ₀ (algebraMap Λ R r) = algebraMap Λ l r) ∧
      (∀ V d p hp (r : Λ), value V d p hp (algebraMap Λ R r) =
        algebraMap k (TrivSqZeroExt k V ⊗[k] l) (algebraMap Λ k r)) ∧
      (∀ V d p hp (r : R), Deformation.tensorFst l V (value V d p hp r) = 1 ⊗ₜ φ₀ r) ∧
      (∀ {V V' : FGModuleCat.{u} k} (g : V ⟶ V') (d : TestDatum iΛ T₀ e₀ V)
        (d' : TestDatum iΛ T₀ e₀ V') (φ : TestDatum.Hom g d d') (p : P.obj.obj (op d.T)) hp
        (p' : P.obj.obj (op d'.T)) hp', p' = P.obj.map φ.m.op p →
          value V' d' p' hp' = (Algebra.TensorProduct.map (TrivSqZeroExt.map g.hom.hom)
            (AlgHom.id k l)).toRingHom.comp (value V d p hp)) ∧
      (∀ V d (p : P.obj.obj (op d.T)) hp p' hp', value V d p hp = value V d p' hp' → p = p') := by
  classical
  obtain ⟨-, Ix, Xi, fi, -, hXet, hcov, hXN⟩ := hP
  obtain ⟨l, _, _, hfin, hl, i, z, hz⟩ :=
    exists_finite_extension_lift_of_isLocallySurjective_sigmaDesc fi hcov T₀ e₀ p₀
  obtain ⟨-, A, _, _, _, _, ⟨hwa, ⟨pres⟩⟩, hNoeth, hAdic⟩ := hXN i
  obtain ⟨⟨I, -, hI⟩, -⟩ := hAdic
  have hf := formallyEtale_hom_of_isRepresentableEtale (fi i) (hXet i)
  let algΛl : Algebra Λ l := ((algebraMap k l).comp (algebraMap Λ k)).toAlgebra
  have : IsScalarTower Λ k l := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hy₀ : (B.inclusion.map (sqStage pres hI).hom).base
      ((B.inclusion.map (pointStage l hl hwa pres hI z).left).base
        (Deformation.Artin.SliceTangent.closedPt (.of l))) ∈ Set.range iΛ.base := by
    rw [← Scheme.Hom.comp_apply, pointStage_comp h₀ l hl hwa pres hI z, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  obtain ⟨c⟩ := Deformation.Artin.SliceTangent.nonempty_affineChart hy₀
  let algΛR : Algebra Λ c.ring := c.structureMap.hom.toAlgebra
  have : _root_.AlgebraicGeometry.IsLocallyNoetherian
      (B.inclusion.obj (sqStage pres hI).left) :=
    isLocallyNoetherian_of_isOpenImmersion (pres.quotientIso (sqIdeal hI)).hom
  have : IsNoetherianRing c.ring :=
    _root_.AlgebraicGeometry.IsLocallyNoetherian.component_noetherian ⟨c.U, c.isAffineOpen⟩
  refine ⟨l, inferInstance, inferInstance, hfin, algΛl, inferInstance, c.ring, inferInstance,
    algΛR, inferInstance, (pointValue l hl hwa pres hI z c).hom,
    fun V d p hp => (d.ringValue h₀ p₀ l hl (fi i) hf hwa pres hI z hz c p hp).hom,
    fun r => ?_, fun V d p hp r => ?_, fun V d p hp r => ?_,
    fun g d d' φ p hp p' hp' hpp => ?_, fun V d p hp p' hp' h => ?_⟩
  · exact congrArg (fun χ => χ.hom r) (structureMap_pointValue h₀ l hl hwa pres hI z c)
  · exact congrArg (fun χ => χ.hom r)
      (d.structureMap_ringValue h₀ p₀ l hl (fi i) hf hwa pres hI z hz c p hp)
  · rw [tensorFst_eq]
    congr 1
    exact congrArg (fun χ => χ.hom r)
      (d.ringValue_residueHom h₀ p₀ l hl (fi i) hf hwa pres hI z hz c p hp)
  · exact congrArg (·.hom)
      (φ.ringValue_eq h₀ p₀ l hl (fi i) hf hwa pres hI z hz c p hp p' hp' hpp)
  · exact d.ringValue_injective h₀ p₀ l hl (fi i) hf hwa pres hI z hz c p hp p' hp'
      (CommRingCat.hom_ext h)

end AlgebraicGeometry.FormalSpace.TangentChart

end
