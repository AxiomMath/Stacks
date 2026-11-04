module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.Descent.Module.Pushforward
public import StacksFrontier.AlgebraicGeometry.Descent.Module.SplitEqualizer
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.TensorEqualizer
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.CechCosimplicialModule
public import StacksCore.Tactic.StacksAttribute

/-!
# Recognising effective descent data for modules

For a faithfully flat ring map, a module descent datum is effective precisely when extension of
scalars from its module of descent-invariant elements recovers its underlying module.

## Main definitions

* `ModuleCat.DescentData.cosimplicialH0` is the coface equaliser of the cosimplicial module of
  Tag 023H.
* `ModuleCat.DescentData.pushforwardEquivCosimplicialH0` identifies it with the pushforward
  module of Tag 08X5.
* `ModuleCat.DescentData.canonicalMap` is the canonical base-change map
  `A ⊗[R] H⁰(s(N_•)) → N`.

## Main results

* `ModuleCat.DescentData.isEffective_iff_canonicalMap_bijective`: along a faithfully flat ring
  map, a descent datum is effective if and only if its canonical map is bijective.
* `ModuleCat.DescentData.canonicalMap_tmul` computes the canonical map on a pure tensor.

## Implementation notes

Degree-zero cohomology is `ModuleCat.pushforward`, the functorial equaliser of the two cofaces
of the cosimplicial module of Tag 023H; this is also the inverse functor of the equivalence of
Tag 023N. Its underlying module is `ModuleCat.invariantSubmodule`, whose elements satisfy
`φ(n ⊗ 1) = 1 ⊗ n`. The canonical map sends `a ⊗ n` to `a • n`; being an isomorphism of
`A`-modules is equivalent to being bijective, which is the form the statement takes.

Bijectivity for a faithfully flat map is obtained by comparing two equaliser presentations of
the same parallel pair — the split equaliser of Tag 08WZ and the tensor equaliser of Tag 08X7 —
rather than through the invariants equivalence of
`StacksFrontier/AlgebraicGeometry/Descent/Modules/InvariantsEffective.lean`: the latter is stated
with `R` and `A` in a single universe, while everything here keeps them independent.

## References

* [Stacks Project, Tag 039W](https://stacks.math.columbia.edu/tag/039W)
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct

universe u v w

namespace ModuleCat.DescentData


variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
variable (D : DescentData.{u, v, w} R A)

/-- Degree-zero cohomology of the cosimplicial module of Tag 023H, as the equalizer of
its two degree-zero cofaces. -/
public def cosimplicialH0 : Type _ :=
  {x : ((ModuleCat.descentCosimplicialModuleFunctor R A).obj D).obj (op (op ⟨0⟩)) //
    HEq
      ((((ModuleCat.descentCosimplicialModuleFunctor R A).obj D).map
        (SimplexCategory.δ (0 : Fin 2)).op.op).hom x)
      ((((ModuleCat.descentCosimplicialModuleFunctor R A).obj D).map
        (SimplexCategory.δ (1 : Fin 2)).op.op).hom x)}

open CategoryTheory.Limits
open scoped ChangeOfRings
section

/-- An element of an extension of scalars which is the generator `1 ⊗ m` scales to the pure
tensor `t ⊗ m`.  The generator is passed as a hypothesis rather than written into the
statement, so that the module structure in the left-hand side is the one instance search
finds on `(extendScalars f).obj M`. -/
private theorem extendScalars_smul_one_tmul {S T : Type*} [CommRing S] [CommRing T]
    (f : S →+* T) {M : ModuleCat S} (t : T) (m : M)
    (x : (ModuleCat.extendScalars f).obj M) (hx : x = (1 : T) ⊗ₜ[S,f] m) :
    t • x = t ⊗ₜ[S,f] m := by
  subst hx
  exact (ModuleCat.ExtendScalars.smul_tmul f t 1 m).trans
    (congrArg (fun s : T => s ⊗ₜ[S,f] m) (mul_one t))

private noncomputable def scalarExtensionEval
    {K : Type*} {S : Type*} {T : Type*}
    [CommRing K] [CommRing S] [CommRing T]
    (f : K →+* S) (g : S →+* T) (N : ModuleCat K)
    {P : Type*} [AddCommGroup P] [Module T P]
    (j : N →+ P) (hj : ∀ k n, j (k • n) = g (f k) • j n) :
    (ModuleCat.extendScalars f).obj N →+ P :=
  TensorProduct.liftAddHom
    { toFun := fun s =>
        { toFun := fun n => g (show S from s) • j n
          map_zero' := by with_unfolding_all simp
          map_add' := by intros; with_unfolding_all simp [smul_add] }
      map_zero' := by
        ext n
        change g (0 : S) • j n = 0
        rw [map_zero, zero_smul]
      map_add' := by
        intro s t
        ext n
        change g (s + t) • j n = g s • j n + g t • j n
        rw [show g (s + t) = g s + g t from map_add g s t, add_smul] }
    (by
      intro k s n
      change g (f k * (show S from s)) • j n = g s • j (k • n)
      rw [map_mul, hj, mul_smul, smul_comm])

private noncomputable def cechAugmentation (n : SimplexCategory) :
    (ModuleCat.cechCosimplicialAlgebra R A).obj n →+* A :=
  ULift.ringEquiv.toRingHom.comp
    (WidePushout.desc (AlgebraicTopology.algebraMapArrow R A).hom
      (fun _ => 𝟙 _) (fun _ => Category.comp_id _)).hom.toRingHom

private theorem cechAugmentation_leg (n : SimplexCategory)
    (i : Fin (n.len + 1)) (a : A) :
    cechAugmentation R A n (ModuleCat.cechLeg R A n i (ULift.up a)) = a :=
  congrArg (fun f => (f.hom (ULift.up a)).down)
    (WidePushout.ι_desc (fun _ : Fin (n.len + 1) => (AlgebraicTopology.algebraMapArrow R A).hom)
      (AlgebraicTopology.algebraMapArrow R A).hom (fun _ => 𝟙 _)
      (fun _ => Category.comp_id _) i)

/-- The retraction of the degree-`n` part of the Čech conerve of `R → A` which descends the
identity of `A` along every leg. -/
private noncomputable def cechLegRetraction (n : SimplexCategory) :
    (AlgebraicTopology.algebraMapArrow R A).cechConerve.obj n ⟶
      (AlgebraicTopology.algebraMapArrow R A).right :=
  WidePushout.desc (arrows := Arrow.cechLegs (AlgebraicTopology.algebraMapArrow R A) n)
    (AlgebraicTopology.algebraMapArrow R A).hom (fun _ => 𝟙 _) (fun _ => Category.comp_id _)

private theorem cechι_comp_cechLegRetraction (n : SimplexCategory) (i : Fin (n.len + 1)) :
    Arrow.cechι (f := AlgebraicTopology.algebraMapArrow R A) n i ≫ cechLegRetraction R A n =
      𝟙 _ :=
  WidePushout.ι_desc (Arrow.cechLegs (AlgebraicTopology.algebraMapArrow R A) n) _ _ _ i

private theorem cechLeg_zero_surjective :
    Function.Surjective (ModuleCat.cechLeg R A ⟨0⟩ (Fin.last 0)) := by
  have h : cechLegRetraction R A ⟨0⟩ ≫
      Arrow.cechι (f := AlgebraicTopology.algebraMapArrow R A) ⟨0⟩ (Fin.last 0) = 𝟙 _ := by
    apply Arrow.cech_hom_ext
    intro i
    have hi : i = Fin.last 0 := by
      show i = (0 : Fin 1)
      exact @Subsingleton.elim (Fin 1) (inferInstance : Subsingleton (Fin 1)) i 0
    subst hi
    rw [← Category.assoc, cechι_comp_cechLegRetraction, Category.id_comp, Category.comp_id]
  intro x
  exact ⟨(cechLegRetraction R A ⟨0⟩).hom x, congrArg (fun k => k.hom x) h⟩

private noncomputable def cechGeneratorRetraction (N : ModuleCat.{w} A)
    (n : SimplexCategory) (i : Fin (n.len + 1)) :
    ModuleCat.cechDegreeObj R A N n i →+ N :=
  scalarExtensionEval (ModuleCat.cechLeg R A n i) (cechAugmentation R A n)
    (ModuleCat.liftedModule A N)
    { toFun := fun x => x.down
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
    (by
      intro k x
      change k.down • x.down = _
      rw [cechAugmentation_leg]
      rfl)

private theorem cechGeneratorRetraction_generator (N : ModuleCat.{w} A)
    (n : SimplexCategory) (i : Fin (n.len + 1))
    (x : ModuleCat.restrictModule R A N) :
    cechGeneratorRetraction R A N n i (ModuleCat.cechGenerator R A N n i x) = x := by
  show cechAugmentation R A n 1 • (x : N) = x
  simp

private theorem cechGenerator_zero_bijective (N : ModuleCat.{w} A) :
    Function.Bijective (ModuleCat.cechGenerator R A N ⟨0⟩ (Fin.last 0)) := by
  refine ⟨fun x y h => ?_, fun x => ?_⟩
  · have := congrArg (cechGeneratorRetraction R A N ⟨0⟩ (Fin.last 0)) h
    show (x : N) = (y : N)
    exact (cechGeneratorRetraction_generator R A N ⟨0⟩ (Fin.last 0) x).symm.trans
      (this.trans (cechGeneratorRetraction_generator R A N ⟨0⟩ (Fin.last 0) y))
  · induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩
    | tmul s n =>
      obtain ⟨a, rfl⟩ := cechLeg_zero_surjective R A s
      change ULift.{max u v} N at n
      refine ⟨a.down • (n.down : ModuleCat.restrictModule R A N), ?_⟩
      refine (ModuleCat.cechGenerator_smul R A N ⟨0⟩ (Fin.last 0) a.down
        (n.down : ModuleCat.restrictModule R A N)).trans ?_
      exact extendScalars_smul_one_tmul (ModuleCat.cechLeg R A ⟨0⟩ (Fin.last 0))
        (M := ModuleCat.liftedModule A N)
        (ModuleCat.cechLeg R A ⟨0⟩ (Fin.last 0) (ULift.up a.down))
        (ULift.up (n.down : N)) _
        (ModuleCat.cechGenerator_eq_tmul R A N ⟨0⟩ (Fin.last 0)
          (n.down : ModuleCat.restrictModule R A N))

private def cechTensorAlgebra : CommAlgCat.{max u v} (ULift.{v} R) := by
  let := ULift.algebra' R (ULift.{u} (A ⊗[R] A))
  exact CommAlgCat.of (ULift.{v} R) (ULift.{u} (A ⊗[R] A))

private noncomputable def cechTensorLeg
    (i : Fin ((⟨1⟩ : SimplexCategory).len + 1)) :
    (AlgebraicTopology.algebraMapArrow R A).right ⟶ cechTensorAlgebra R A := by
  let := ULift.algebra' R (ULift.{u} A)
  let := ULift.algebra' R (ULift.{u} (A ⊗[R] A))
  exact CommAlgCat.ofHom {
    toRingHom := ULift.ringEquiv.symm.toRingHom.comp
      ((if i = 0 then Algebra.TensorProduct.includeLeftRingHom
        else Algebra.TensorProduct.includeRight.toRingHom).comp
          ULift.ringEquiv.toRingHom)
    commutes' := by
      intro r
      change ULift.up ((if i = 0 then Algebra.TensorProduct.includeLeftRingHom
        else Algebra.TensorProduct.includeRight.toRingHom) (algebraMap R A r.down)) = _
      split_ifs <;> apply ULift.ext
      · exact (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).commutes r.down
      · exact Algebra.TensorProduct.includeRight.commutes r.down }

private noncomputable def cechTensorMapHom :
    (ModuleCat.cechCosimplicialAlgebra R A).obj ⟨1⟩ ⟶ cechTensorAlgebra R A := by
  let := ULift.algebra' R (ULift.{u} (A ⊗[R] A))
  exact WidePushout.desc (CommAlgCat.ofHom (Algebra.ofId (ULift.{v} R) (cechTensorAlgebra R A)))
    (cechTensorLeg R A)
    (fun i => CommAlgCat.hom_ext (AlgHom.ext fun r => (cechTensorLeg R A i).hom.commutes r))

private noncomputable def cechTensorRingMap :
    (ModuleCat.cechCosimplicialAlgebra R A).obj ⟨1⟩ →+* (A ⊗[R] A) :=
  ULift.ringEquiv.toRingHom.comp (cechTensorMapHom R A).hom.toRingHom

private theorem cechTensorRingMap_leg (i : Fin 2) (a : A) :
    cechTensorRingMap R A (ModuleCat.cechLeg R A ⟨1⟩ i (ULift.up a)) =
      if i = 0 then a ⊗ₜ[R] (1 : A) else (1 : A) ⊗ₜ[R] a := by
  have h : ModuleCat.cechLegHom R A ⟨1⟩ i ≫ cechTensorMapHom R A =
      cechTensorLeg R A i := WidePushout.ι_desc _ _ _ _ i
  have hx := congrArg (fun f => (f.hom (ULift.up a)).down) h
  change cechTensorRingMap R A (ModuleCat.cechLeg R A ⟨1⟩ i (ULift.up a)) =
    ((cechTensorLeg R A i).hom (ULift.up a)).down at hx
  rw [hx]
  dsimp [cechTensorLeg]
  split_ifs <;> rfl

private noncomputable def cechDegreeOneRetraction :
    ModuleCat.cechDegreeObj R A D.module ⟨1⟩ (Fin.last 1) →+
      (A ⊗[R] ModuleCat.restrictModule R A D.module) :=
  scalarExtensionEval (ModuleCat.cechLeg R A ⟨1⟩ (Fin.last 1))
    (cechTensorRingMap R A) (ModuleCat.liftedModule A D.module)
    { toFun := fun x => (1 : A) ⊗ₜ[R]
        (x.down : ModuleCat.restrictModule R A D.module)
      map_zero' := by
        change (1 : A) ⊗ₜ[R] (0 : ModuleCat.restrictModule R A D.module) = 0
        exact TensorProduct.tmul_zero _ _
      map_add' := fun _ _ => TensorProduct.tmul_add _ _ _ }
    (by
      intro k x
      let : Module R D.module := Module.compHom D.module (algebraMap R A)
      rw [cechTensorRingMap_leg]
      simp only [show (Fin.last 1 : Fin 2) ≠ 0 by decide, ite_false]
      change (1 : A) ⊗ₜ[R] (k.down • (x.down : ModuleCat.restrictModule R A D.module)) =
        ((1 : A) ⊗ₜ[R] k.down : A ⊗[R] A) •
          (show A ⊗[R] ModuleCat.restrictModule R A D.module from
            (1 : A) ⊗ₜ[R] (x.down : ModuleCat.restrictModule R A D.module))
      rw [show ((1 : A) ⊗ₜ[R] k.down : A ⊗[R] A) •
            (show A ⊗[R] ModuleCat.restrictModule R A D.module from
              (1 : A) ⊗ₜ[R] (x.down : ModuleCat.restrictModule R A D.module)) =
            ((1 : A) * 1) ⊗ₜ[R]
              (ModuleCat.restrictedScalarAction R A D.module k.down x.down) from
          ModuleCat.targetTensor_smul_tmul R A D.module 1 k.down 1 x.down, one_mul]
      rfl)

private theorem cechDegreeOneRetraction_transitionGen
    (z : A ⊗[R] ModuleCat.restrictModule R A D.module) :
    cechDegreeOneRetraction R A D (ModuleCat.transitionGen D ⟨1⟩ 0 (Fin.last 1) z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a n =>
    rw [ModuleCat.transitionGen_tmul]
    refine (congrArg (cechDegreeOneRetraction R A D)
      (extendScalars_smul_one_tmul (ModuleCat.cechLeg R A ⟨1⟩ (Fin.last 1))
        (M := ModuleCat.liftedModule A D.module)
        (ModuleCat.cechLeg R A ⟨1⟩ 0 (ULift.up a)) (ULift.up (n : D.module)) _
        (ModuleCat.cechGenerator_eq_tmul R A D.module ⟨1⟩ (Fin.last 1) n))).trans ?_
    show cechTensorRingMap R A (ModuleCat.cechLeg R A ⟨1⟩ 0 (ULift.up a)) •
      ((1 : A) ⊗ₜ[R] n) = _
    rw [cechTensorRingMap_leg]
    simp only [ite_true, ModuleCat.targetTensor_smul_tmul, mul_one]
    rw [map_one]
    rfl

private theorem transitionGen_degreeOne_injective :
    Function.Injective (ModuleCat.transitionGen D ⟨1⟩ 0 (Fin.last 1)) := by
  intro x y h
  simpa only [cechDegreeOneRetraction_transitionGen] using
    congrArg (cechDegreeOneRetraction R A D) h

private theorem module_eqToHom_heq {S : Type*} [Ring S]
    {X Y : ModuleCat S} (h : X = Y) (x : X) :
    HEq ((eqToHom h).hom x) x := by
  subst h
  rfl

private theorem cosimplicialMap_heq {n m : SimplexCategory} (β : n ⟶ m)
    (x : ModuleCat.cechDegreeObj R A D.module n (Fin.last n.len)) :
    HEq
      ((((ModuleCat.descentCosimplicialModuleFunctor R A).obj D).map β.op.op).hom
        ((eqToHom (ModuleCat.descentCosimplicialModuleFunctor_obj R A D n).symm).hom x))
      ((ModuleCat.cechStructureMap D β).hom x) := by
  have hn := ModuleCat.descentCosimplicialModuleFunctor_obj R A D n
  have hm := congrArg ((ModuleCat.restrictScalars (ModuleCat.cechRingMap R A β)).obj)
    (ModuleCat.descentCosimplicialModuleFunctor_obj R A D m).symm
  have hy : (((ModuleCat.descentCosimplicialModuleFunctor R A).obj D).map β.op.op).hom
        ((eqToHom hn.symm).hom x) =
      (eqToHom hm).hom
        ((ModuleCat.cechStructureMap D β).hom ((eqToHom hn).hom ((eqToHom hn.symm).hom x))) :=
    congrArg (fun k => k.hom ((eqToHom hn.symm).hom x))
      (ModuleCat.descentCosimplicialModuleFunctor_map R A D β)
  have hc : (eqToHom hn).hom ((eqToHom hn.symm).hom x) = x :=
    (eqToIso hn).toLinearEquiv.apply_symm_apply x
  refine (heq_of_eq hy).trans ?_
  rw [hc]
  exact module_eqToHom_heq _ _

private theorem transitionBase_self (n : SimplexCategory)
    (x : ModuleCat.restrictModule R A D.module) :
    ModuleCat.transitionBase D n (Fin.last n.len) (Fin.last n.len) x =
      ModuleCat.cechGenerator R A D.module n (Fin.last n.len) x := by
  have h := cosimplicialMap_heq R A D (𝟙 n)
    (ModuleCat.cechGenerator R A D.module n (Fin.last n.len) x)
  rw [cechStructureMap_generator] at h
  change HEq
    ((((ModuleCat.descentCosimplicialModuleFunctor R A).obj D).map (𝟙 (op (op n)))).hom _)
    (ModuleCat.transitionBase D n (Fin.last n.len) (Fin.last n.len) x) at h
  dsimp only [PresheafOfModulesOfCommRing.map] at h
  rw [PresheafOfModules.map_id] at h
  simp only [ModuleCat.restrictScalarsId'_inv_app] at h
  have hc := module_eqToHom_heq
    (ModuleCat.descentCosimplicialModuleFunctor_obj R A D n).symm
    (ModuleCat.cechGenerator R A D.module n (Fin.last n.len) x)
  exact eq_of_heq (h.symm.trans hc)

private theorem coface_equalizer_iff (x : ModuleCat.restrictModule R A D.module) :
    HEq
      ((((ModuleCat.descentCosimplicialModuleFunctor R A).obj D).map
        (SimplexCategory.δ (0 : Fin 2)).op.op).hom
        ((eqToHom (ModuleCat.descentCosimplicialModuleFunctor_obj R A D ⟨0⟩).symm).hom
          (ModuleCat.cechGenerator R A D.module ⟨0⟩ (Fin.last 0) x)))
      ((((ModuleCat.descentCosimplicialModuleFunctor R A).obj D).map
        (SimplexCategory.δ (1 : Fin 2)).op.op).hom
        ((eqToHom (ModuleCat.descentCosimplicialModuleFunctor_obj R A D ⟨0⟩).symm).hom
          (ModuleCat.cechGenerator R A D.module ⟨0⟩ (Fin.last 0) x))) ↔
      x ∈ ModuleCat.invariantSubmodule R A D := by
  have h₀ := cosimplicialMap_heq R A D (SimplexCategory.δ (0 : Fin 2))
    (ModuleCat.cechGenerator R A D.module ⟨0⟩ (Fin.last 0) x)
  have h₁ := cosimplicialMap_heq R A D (SimplexCategory.δ (1 : Fin 2))
    (ModuleCat.cechGenerator R A D.module ⟨0⟩ (Fin.last 0) x)
  rw [cechStructureMap_generator] at h₀ h₁
  change HEq _ (ModuleCat.transitionBase D ⟨1⟩ (Fin.last 1) (Fin.last 1) x) at h₀
  change HEq _ (ModuleCat.transitionBase D ⟨1⟩ 0 (Fin.last 1) x) at h₁
  rw [transitionBase_self] at h₀
  have he : ModuleCat.transitionGen D ⟨1⟩ 0 (Fin.last 1) ((1 : A) ⊗ₜ[R] x) =
      ModuleCat.cechGenerator R A D.module ⟨1⟩ (Fin.last 1) x := by
    rw [ModuleCat.transitionGen_tmul]
    show ModuleCat.cechLeg R A ⟨1⟩ 0 1 • _ = _
    rw [map_one, one_smul]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hh := eq_of_heq (h₀.symm.trans (h.trans h₁))
    change _ = ModuleCat.transitionGen D ⟨1⟩ 0 (Fin.last 1)
      (D.transitionRestrictScalars R A (x ⊗ₜ[R] (1 : A))) at hh
    rw [← he] at hh
    exact (transitionGen_degreeOne_injective R A D hh).symm
  · change D.transitionRestrictScalars R A (x ⊗ₜ[R] (1 : A)) = (1 : A) ⊗ₜ[R] x at h
    have hh : ModuleCat.transitionBase D ⟨1⟩ 0 (Fin.last 1) x =
        ModuleCat.cechGenerator R A D.module ⟨1⟩ (Fin.last 1) x := by
      show ModuleCat.transitionGen D ⟨1⟩ 0 (Fin.last 1)
        (D.transitionRestrictScalars R A (x ⊗ₜ[R] (1 : A))) = _
      rw [h, he]
    exact h₀.trans ((heq_of_eq hh.symm).trans h₁.symm)

end

/-- The functorial invariant module of Tag 08X5 is canonically the degree-zero
cohomology of the cosimplicial module of Tag 023H. The specified equivalence
sends an invariant section to its degree-zero Čech generator. -/
public noncomputable def pushforwardEquivCosimplicialH0 :
    {e : ((ModuleCat.pushforward R A).obj D) ≃ cosimplicialH0 R A D //
      ∀ n, (e n).val =
        (eqToHom (ModuleCat.descentCosimplicialModuleFunctor_obj R A D ⟨0⟩).symm).hom
          (ModuleCat.cechGenerator R A D.module ⟨0⟩ (Fin.last 0)
            (show ModuleCat.restrictModule R A D.module from n.val))} := by
  let e₀ := Equiv.ofBijective
    (ModuleCat.cechGenerator R A D.module ⟨0⟩ (Fin.last 0))
    (by exact cechGenerator_zero_bijective R A D.module)
  let e₁ := (eqToIso (ModuleCat.descentCosimplicialModuleFunctor_obj R A D ⟨0⟩)).symm
    |>.toLinearEquiv.toEquiv
  exact ⟨(e₀.trans e₁).subtypeEquiv (by intro x; exact (coface_equalizer_iff R A D x).symm),
    fun _ => rfl⟩

/-- The canonical map `A ⊗[R] H⁰(s(Nₙ)) → N` associated to a descent datum. -/
public noncomputable def canonicalMap :
    A ⊗[R] (ModuleCat.pushforward R A).obj D →ₗ[A] D.module := by
  let : Module R D.module := Module.compHom D.module (algebraMap R A)
  let : IsScalarTower R A D.module := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact TensorProduct.AlgebraTensorModule.lift {
    toFun := fun a => {
      toFun := fun n => a • (show D.module from n.val)
      map_add' := by
        intro n m
        change a • ((show D.module from n.val) + (show D.module from m.val)) =
          a • (show D.module from n.val) + a • (show D.module from m.val)
        exact smul_add a _ _
      map_smul' := by
        intro r n
        change a • (r • (show D.module from n.val)) =
          r • (a • (show D.module from n.val))
        exact (smul_comm r a _).symm }
    map_add' := by
      intro a b
      ext n
      change (a + b) • (show D.module from n.val) =
        a • (show D.module from n.val) + b • (show D.module from n.val)
      exact add_smul a b _
    map_smul' := by
      intro r a
      ext n
      change (r * a) • (show D.module from n.val) =
        r • (a • (show D.module from n.val))
      exact mul_smul r a _
  }

/-- The canonical map sends `a ⊗ n` to `a • n`. -/
@[simp] public theorem canonicalMap_tmul (a : A)
    (n : (ModuleCat.pushforward R A).obj D) :
    canonicalMap R A D (a ⊗ₜ[R] n) = a • (show D.module from n.val) := rfl

private noncomputable def descentComparisonLinearIso
    (h : Stacks.UniversalInjectivity.LocalizationCriteria.UniversallyInjective.{u}
      (Algebra.linearMap R A))
    (D : DescentData.{u, v, w} R A) :
    ModuleCat.of A (A ⊗[R] ModuleCat.invariantSubmodule R A D) ≅
      ModuleCat.of A (ULift.{v} D.module) :=
  (ModuleCat.tensorPushforward_isEqualizer R A h D).conePointUniqueUpToIso
    (Classical.choice (ModuleCat.DescentData.isSplitEqualizer_descentComparison R A D)).isEqualizer

private noncomputable def descentCounitLinearEquiv
    (h : Stacks.UniversalInjectivity.LocalizationCriteria.UniversallyInjective.{u}
      (Algebra.linearMap R A))
    (D : DescentData.{u, v, w} R A) :
    (A ⊗[R] ModuleCat.invariantSubmodule R A D) ≃ₗ[A] D.module :=
  (descentComparisonLinearIso R A h D).toLinearEquiv.trans
    (ULift.moduleEquiv.{v, w, v} (R := A) (M := D.module))

private theorem descentComparisonLinearIso_spec
    (h : Stacks.UniversalInjectivity.LocalizationCriteria.UniversallyInjective.{u}
      (Algebra.linearMap R A))
    (D : DescentData.{u, v, w} R A)
    (x : A ⊗[R] ModuleCat.invariantSubmodule R A D) :
    ModuleCat.DescentData.descentComparisonHom R A D
        (ULift.up ((descentCounitLinearEquiv R A h D x) : D.module)) =
      ModuleCat.tensorPushforwardComparison R A D x := by
  have he : (descentComparisonLinearIso R A h D).hom ≫
      ModuleCat.ofHom (ModuleCat.DescentData.descentComparisonHom R A D) =
      ModuleCat.ofHom (ModuleCat.tensorPushforwardComparison R A D) :=
    ModuleCat.hom_ext (congrArg ModuleCat.Hom.hom
      (IsLimit.conePointUniqueUpToIso_hom_comp (ModuleCat.tensorPushforward_isEqualizer R A h D)
        (Classical.choice
          (ModuleCat.DescentData.isSplitEqualizer_descentComparison R A D)).isEqualizer
        WalkingParallelPair.zero))
  have hx := congrArg (fun f : ModuleCat.of A
      (A ⊗[R] ModuleCat.invariantSubmodule R A D) ⟶
      ModuleCat.of A (A ⊗[R] ModuleCat.restrictModule R A D.module) => f.hom x) he
  have hval : ULift.up (descentCounitLinearEquiv R A h D x) =
      (descentComparisonLinearIso R A h D).hom.hom x := rfl
  rw [hval]
  exact hx

/-- For an invariant section `m`, the descent transition sends `(a • m) ⊗ b` to `a ⊗ (b • m)`. -/
private theorem transition_smul_tmul_invariant (a b : A)
    (m : ModuleCat.invariantSubmodule R A D) :
    D.transitionRestrictScalars R A
      (((a • (m.1 : D.module) : D.module) :
        ModuleCat.restrictModule R A D.module) ⊗ₜ[R] b) =
    a ⊗ₜ[R] ((b • (m.1 : D.module) : D.module) :
      ModuleCat.restrictModule R A D.module) := by
  have hsource :
      (((a • (m.1 : D.module) : D.module) :
        ModuleCat.restrictModule R A D.module) ⊗ₜ[R] b) =
        (a ⊗ₜ[R] b : A ⊗[R] A) •
          ((m.1 : ModuleCat.restrictModule R A D.module) ⊗ₜ[R] (1 : A)) := by
    rw [ModuleCat.sourceTensor_smul_tmul, mul_one]
    congr 1
  have hinv₀ := m.2
  change D.transitionRestrictScalars R A
      (m.1 ⊗ₜ[R] (1 : A)) = (1 : A) ⊗ₜ[R] m.1 at hinv₀
  have hinv : D.transition (m.1 ⊗ₜ[R] (1 : A)) =
      (1 : A) ⊗ₜ[R] m.1 := by
    simpa only [DescentData.transitionRestrictScalars_apply] using hinv₀
  rw [hsource]
  show D.transition ((a ⊗ₜ[R] b : A ⊗[R] A) •
      ((m.1 : ModuleCat.restrictModule R A D.module) ⊗ₜ[R] (1 : A))) = _
  rw [D.transition.map_smul, hinv, ModuleCat.targetTensor_smul_tmul, mul_one]
  congr 1

private theorem descentCounitLinearEquiv_tmul
    (h : Stacks.UniversalInjectivity.LocalizationCriteria.UniversallyInjective.{u}
      (Algebra.linearMap R A))
    (D : DescentData.{u, v, w} R A)
    (a : A) (m : ModuleCat.invariantSubmodule R A D) :
    descentCounitLinearEquiv R A h D (a ⊗ₜ[R] m) = a • (m.1 : D.module) := by
  have hcmp₁ : ModuleCat.DescentData.descentComparisonHom R A D
      (ULift.up (descentCounitLinearEquiv R A h D (a ⊗ₜ[R] m))) =
      a ⊗ₜ[R] (m.1 : ModuleCat.restrictModule R A D.module) :=
    descentComparisonLinearIso_spec R A h D (a ⊗ₜ[R] m)
  have hcmp₂ : ModuleCat.DescentData.descentComparisonHom R A D
      (ULift.up (a • (m.1 : D.module))) =
      a ⊗ₜ[R] (m.1 : ModuleCat.restrictModule R A D.module) := by
    rw [ModuleCat.DescentData.descentComparisonHom_apply R A D (a • (m.1 : D.module))]
    exact (transition_smul_tmul_invariant R A D a 1 m).trans (by rw [one_smul])
  exact congrArg ULift.down (descentComparisonHom_injective R A D (hcmp₁.trans hcmp₂.symm))

@[sga "1 VIII 1.6"]
private theorem canonicalMap_bijective_of_faithfullyFlat
    [Module.FaithfullyFlat R A] :
    Function.Bijective (canonicalMap R A D) := by
  have h : Stacks.UniversalInjectivity.LocalizationCriteria.UniversallyInjective.{u}
      (Algebra.linearMap R A) := by
    intro Q hQ hM
    exact (Module.FaithfullyFlat.lTensor_injective_iff_injective R A
      (LinearMap.rTensor Q (Algebra.linearMap R A))).mp lTensor_rTensor_algebraMap_injective
  have heq : canonicalMap R A D =
      (descentCounitLinearEquiv R A h D).toLinearMap := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [map_add, hx, hy]
    | tmul a m =>
      show a • (show D.module from m.val) =
        descentCounitLinearEquiv R A h D (a ⊗ₜ[R] m)
      exact (descentCounitLinearEquiv_tmul R A h D a
        (show ModuleCat.invariantSubmodule R A D from m)).symm
  rw [heq]
  exact (descentCounitLinearEquiv R A h D).bijective

private theorem isEffective_of_canonicalMap_bijective
    (h : Function.Bijective (canonicalMap R A D)) :
    IsEffective R A D := by
  let e : (A ⊗[R] (ModuleCat.pushforward R A).obj D) ≃ₗ[A] D.module :=
    LinearEquiv.ofBijective (canonicalMap R A D) h
  refine ⟨(ModuleCat.pushforward R A).obj D, e, ?_⟩
  intro a b m
  exact transition_smul_tmul_invariant R A D a b m

/-- A module descent datum is effective if and only if its canonical map from the base change
of its zeroth cohomology is an isomorphism. -/
@[stacks 039W] public theorem isEffective_iff_canonicalMap_bijective
    [Module.FaithfullyFlat R A] :
    IsEffective R A D ↔
      Function.Bijective (canonicalMap R A D) :=
  ⟨fun _ => canonicalMap_bijective_of_faithfullyFlat R A D,
    isEffective_of_canonicalMap_bijective R A D⟩


end ModuleCat.DescentData

end
