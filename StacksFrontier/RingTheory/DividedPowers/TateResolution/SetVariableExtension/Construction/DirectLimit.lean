module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.Construction.OneVariableLift
import all StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.Construction.OneVariableLift
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.Construction.FiniteVariable
import all StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.Construction.FiniteVariable
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Basic
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariable
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariableDividedPowers
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.OddVariable
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.FiniteStage

/-!
# Direct limits of graded divided power algebras

This file constructs the colimit `gradedDirectLimit` of a diagram of graded divided power
algebras indexed by a nonempty directed preorder, with its structure maps and universal
property, and applies it to the finite-variable stages: the set-variable algebra is their direct
limit, each of its elements lies in a finite stage, and each stage is identified with the
corresponding finite-variable subring of the limit.
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w z

attribute [local instance] prodGradedAlgebra prodStrictlyGradedComm

attribute [local instance] GradedDPAlgebra.ring GradedDPAlgebra.algebra
  GradedDPAlgebra.graded GradedDPAlgebra.strict

section GradedDirectLimit
open scoped DirectSum
/-- The carrier of the colimit of a directed diagram of graded divided power algebras. -/
public abbrev gradedLimitCarrier
    {R : Type u} [CommRing R] {I : Type w}
    [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (B : I → GradedDPAlgebra.{u, v} R)
    (f : ∀ S T : I, S ≤ T → GradedDPHom (B S) (B T))
    [DirectedSystem (fun S => (B S).carrier) (fun S T h => (f S T h).hom)] :=
  DirectLimit (fun S => (B S).carrier) (fun S T h => (f S T h).hom)

/-- The structure map of a stage into the colimit. -/
public noncomputable abbrev gradedLimitInclusion
    {R : Type u} [CommRing R] {I : Type w}
    [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (B : I → GradedDPAlgebra.{u, v} R)
    (f : ∀ S T : I, S ≤ T → GradedDPHom (B S) (B T))
    [DirectedSystem (fun S => (B S).carrier) (fun S T h => (f S T h).hom)] (S : I) :
    (B S).carrier →ₐ[R] gradedLimitCarrier B f :=
  DirectLimit.Algebra.of _ (fun S T h => (f S T h).hom) S

/-- The structure maps into the colimit are compatible with the transition maps. -/
public theorem gradedLimitInclusion_map
    {R : Type u} [CommRing R] {I : Type w}
    [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (B : I → GradedDPAlgebra.{u, v} R)
    (f : ∀ S T : I, S ≤ T → GradedDPHom (B S) (B T))
    [DirectedSystem (fun S => (B S).carrier) (fun S T h => (f S T h).hom)]
    {S T : I} (h : S ≤ T) (x : (B S).carrier) :
    gradedLimitInclusion B f T ((f S T h).hom x) = gradedLimitInclusion B f S x :=
  DirectLimit.Algebra.of_f (f := fun S T h => (f S T h).hom) h x

/-- The grading of the colimit: an element is homogeneous of degree `m` when it comes from a
homogeneous element of that degree at some stage. -/
public noncomputable def gradedLimitGrade
    {R : Type u} [CommRing R] {I : Type w}
    [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (B : I → GradedDPAlgebra.{u, v} R)
    (f : ∀ S T : I, S ≤ T → GradedDPHom (B S) (B T))
    [DirectedSystem (fun S => (B S).carrier) (fun S T h => (f S T h).hom)] (m : ℕ) :
    Submodule R (gradedLimitCarrier B f) where
  carrier := {x | ∃ S y, y ∈ (B S).grade m ∧ gradedLimitInclusion B f S y = x}
  zero_mem' := ⟨Classical.arbitrary I, 0, Submodule.zero_mem _, map_zero _⟩
  add_mem' := by
    rintro x y ⟨S, a, ha, rfl⟩ ⟨T, b, hb, rfl⟩
    classical
    obtain ⟨U, hSU, hTU⟩ := exists_ge_ge S T
    refine ⟨U, (f S U hSU).hom a + (f T U hTU).hom b,
      Submodule.add_mem _ ((f ..).map_grade m a ha) ((f ..).map_grade m b hb), ?_⟩
    rw [map_add, gradedLimitInclusion_map, gradedLimitInclusion_map]
  smul_mem' := by
    rintro r x ⟨S, a, ha, rfl⟩
    exact ⟨S, r • a, Submodule.smul_mem _ r ha, map_smul _ r a⟩

/-- The structure maps into the colimit preserve homogeneous degrees. -/
public theorem gradedLimitInclusion_mem
    {R : Type u} [CommRing R] {I : Type w}
    [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (B : I → GradedDPAlgebra.{u, v} R)
    (f : ∀ S T : I, S ≤ T → GradedDPHom (B S) (B T))
    [DirectedSystem (fun S => (B S).carrier) (fun S T h => (f S T h).hom)]
    (S : I) (m : ℕ) (x : (B S).carrier)
    (hx : x ∈ (B S).grade m) : gradedLimitInclusion B f S x ∈ gradedLimitGrade B f m :=
  ⟨S, x, hx, rfl⟩

/-- The colimit of a directed diagram of graded divided power algebras is a graded algebra. -/
@[instance_reducible] public noncomputable def gradedLimitGradedAlgebra
    {R : Type u} [CommRing R] {I : Type w}
    [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (B : I → GradedDPAlgebra.{u, v} R)
    (f : ∀ S T : I, S ≤ T → GradedDPHom (B S) (B T))
    [DirectedSystem (fun S => (B S).carrier) (fun S T h => (f S T h).hom)] :
    GradedAlgebra (gradedLimitGrade B f) := by
  classical
  let Cᵢ := gradedLimitGrade B f
  let l (S : I) (m : ℕ) : (B S).grade m →+ Cᵢ m :=
    { toFun := fun x =>
        ⟨gradedLimitInclusion B f S x, gradedLimitInclusion_mem B f S m x x.property⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }
  let ds (S : I) : (B S).carrier →+ ⨁ m, Cᵢ m :=
    (DirectSum.toAddMonoid fun m => (DirectSum.of _ m).comp (l S m)).comp
      (DirectSum.decomposeAddEquiv (B S).grade).toAddMonoidHom
  have hs (S : I) {m : ℕ} {x : (B S).carrier} (hx : x ∈ (B S).grade m) :
      ds S x = DirectSum.of _ m (l S m ⟨x,hx⟩) := by
    change DirectSum.toAddMonoid _ (DirectSum.decompose (B S).grade x) = _
    rw [DirectSum.decompose_of_mem _ hx, DirectSum.toAddMonoid_of]; rfl
  have hc (S T : I) (h : S ≤ T) (x : (B S).carrier) :
      ds S x = ds T ((f S T h).hom x) := by
    induction x using DirectSum.Decomposition.inductionOn (B S).grade with
    | zero => simp only [map_zero]
    | @homogeneous m x =>
      rw [hs S x.property, hs T ((f S T h).map_grade m x x.property)]
      congr 1
      exact Subtype.ext (gradedLimitInclusion_map B f h x).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  let dc : gradedLimitCarrier B f →+ ⨁ m, Cᵢ m :=
    { toFun := DirectLimit.lift (fun S T h => (f S T h).hom) (fun S x => ds S x) hc
      map_zero' := DirectLimit.lift_zero ds hc
      map_add' := DirectLimit.lift_add ds hc }
  have hdc (S : I) (x : (B S).carrier) : dc (gradedLimitInclusion B f S x) = ds S x := rfl
  let dec : DirectSum.Decomposition Cᵢ := DirectSum.Decomposition.ofAddHom Cᵢ dc
    (by
      apply AddMonoidHom.ext
      intro x
      induction x using DirectLimit.induction (fun S T h => (f S T h).hom) with
      | ih S x =>
        change DirectSum.coeAddMonoidHom Cᵢ (dc (gradedLimitInclusion B f S x)) =
          gradedLimitInclusion B f S x
        rw [hdc]
        induction x using DirectSum.Decomposition.inductionOn (B S).grade with
        | zero =>
          simp only [map_zero]
        | homogeneous x => rw [hs S x.property, DirectSum.coeAddMonoidHom_of]; rfl
        | add x y hx hy => simp only [map_add, hx, hy])
    (by
      apply DirectSum.addHom_ext
      intro m x
      simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of, AddMonoidHom.id_apply]
      obtain ⟨S, a, ha, heq⟩ := x.property
      have he : x = l S m ⟨a,ha⟩ := Subtype.ext heq.symm
      rw [he]
      exact hs S ha)
  exact
    { dec with
      one_mem := ⟨Classical.arbitrary I, 1, SetLike.GradedOne.one_mem, map_one _⟩
      mul_mem := by
        rintro m n x y ⟨S,a,ha,rfl⟩ ⟨T,b,hb,rfl⟩
        obtain ⟨U, hSU, hTU⟩ := exists_ge_ge S T
        refine ⟨U, (f S U hSU).hom a * (f T U hTU).hom b,
          SetLike.mul_mem_graded ((f ..).map_grade m a ha) ((f ..).map_grade n b hb), ?_⟩
        rw [map_mul, gradedLimitInclusion_map, gradedLimitInclusion_map] }

attribute [local instance] gradedLimitGradedAlgebra

/-- The colimit of a directed diagram of graded divided power algebras is strictly graded
commutative. -/
public theorem gradedLimitStrictlyGradedComm
    {R : Type u} [CommRing R] {I : Type w}
    [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (B : I → GradedDPAlgebra.{u, v} R)
    (f : ∀ S T : I, S ≤ T → GradedDPHom (B S) (B T))
    [DirectedSystem (fun S => (B S).carrier) (fun S T h => (f S T h).hom)] :
    IsStrictlyGradedComm (gradedLimitGrade B f) := by
  classical
  constructor
  · rintro m n x y ⟨S,a,ha,rfl⟩ ⟨T,b,hb,rfl⟩
    obtain ⟨U, hSU, hTU⟩ := exists_ge_ge S T
    rw [← gradedLimitInclusion_map B f hSU a, ← gradedLimitInclusion_map B f hTU b,
      ← map_mul]
    rw [IsStrictlyGradedComm.graded_comm ((f S U hSU).map_grade m a ha)
      ((f T U hTU).map_grade n b hb), map_smul, map_mul]
  · rintro d x ⟨S,a,ha,rfl⟩
    rw [← map_pow, IsStrictlyGradedComm.odd_sq_zero ha, map_zero]

attribute [local instance] gradedLimitStrictlyGradedComm

/-- The colimit carries a unique divided power structure compatible with those of the stages. -/
public theorem gradedLimit_existsUnique_dividedPowers
    {R : Type u} [CommRing R] {I : Type w}
    [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (B : I → GradedDPAlgebra.{u, v} R)
    (f : ∀ S T : I, S ≤ T → GradedDPHom (B S) (B T))
    [DirectedSystem (fun S => (B S).carrier) (fun S T h => (f S T h).hom)] :
    ∃! δ : DividedPowerStructure (gradedLimitGrade B f),
      ∀ S n x, x ∈ positiveEvenPart (B S).grade →
        δ.dpow n (gradedLimitInclusion B f S x) =
          gradedLimitInclusion B f S ((B S).gamma.dpow n x) :=
  existsUnique_dividedPowerStructure_of_finiteStages (fun S => (B S).carrier)
    (fun S => (B S).grade) (fun S => (B S).gamma) (gradedLimitGrade B f)
    (fun {S T} h => (f S T h).hom) (gradedLimitInclusion B f)
    (fun h x => gradedLimitInclusion_map B f h x) (gradedLimitInclusion_mem B f)
    (fun _ _ hx => hx) (fun _ _ _ _ heq => Quotient.exact heq)
    (fun {S T} h => (f S T h).map_grade)
    (fun {S T} h n x hx => ((f S T h).map_dpow n x hx).symm)

/-- The colimit of a directed diagram of graded divided power algebras, as a graded divided power
algebra. -/
@[reducible] public noncomputable def gradedDirectLimit
    {R : Type u} [CommRing R] {I : Type w}
    [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (B : I → GradedDPAlgebra.{u, v} R)
    (f : ∀ S T : I, S ≤ T → GradedDPHom (B S) (B T))
    [DirectedSystem (fun S => (B S).carrier) (fun S T h => (f S T h).hom)] :
    GradedDPAlgebra.{u, max v w} R where
  carrier := gradedLimitCarrier B f
  ring := inferInstance
  algebra := inferInstance
  grade := gradedLimitGrade B f
  graded := inferInstance
  strict := inferInstance
  gamma := (gradedLimit_existsUnique_dividedPowers B f).choose

/-- The structure map of a stage into the colimit, as a morphism of graded divided power
algebras. -/
public noncomputable def gradedDirectLimitInclusion
    {R : Type u} [CommRing R] {I : Type w}
    [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (B : I → GradedDPAlgebra.{u, v} R)
    (f : ∀ S T : I, S ≤ T → GradedDPHom (B S) (B T))
    [DirectedSystem (fun S => (B S).carrier) (fun S T h => (f S T h).hom)] (S : I) :
    GradedDPHom (B S) (gradedDirectLimit B f) where
  hom := gradedLimitInclusion B f S
  map_grade := gradedLimitInclusion_mem B f S
  map_dpow := (gradedLimit_existsUnique_dividedPowers B f).choose_spec.1 S

/-- The universal property of the colimit: a compatible family of morphisms out of the stages
extends uniquely to a morphism out of the colimit. -/
public theorem gradedDirectLimit_existsUnique_lift
    {R : Type u} [CommRing R] {I : Type w}
    [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (B : I → GradedDPAlgebra.{u, v} R)
    (f : ∀ S T : I, S ≤ T → GradedDPHom (B S) (B T))
    [DirectedSystem (fun S => (B S).carrier) (fun S T h => (f S T h).hom)]
    (D : GradedDPAlgebra.{u,z} R) (g : ∀ S, GradedDPHom (B S) D)
    (hg : ∀ S T h x, (g T).hom ((f S T h).hom x) = (g S).hom x) :
    ∃! F : GradedDPHom (gradedDirectLimit B f) D,
      ∀ S x, F.hom ((gradedDirectLimitInclusion B f S).hom x) = (g S).hom x := by
  let l : (gradedDirectLimit B f).carrier →ₐ[R] D.carrier :=
    DirectLimit.Algebra.lift _ (fun S T h => (f S T h).hom) D.carrier (fun S => (g S).hom) hg
  have hl (S : I) (x : (B S).carrier) :
      l (gradedLimitInclusion B f S x) = (g S).hom x := rfl
  let F : GradedDPHom (gradedDirectLimit B f) D :=
    { hom := l
      map_grade := by
        rintro m x ⟨S,y,hy,rfl⟩
        rw [hl]
        exact (g S).map_grade m y hy
      map_dpow := by
        intro n x hx
        obtain ⟨S,y,hy,heq⟩ := exists_lift_positiveEvenPart (fun S => (B S).carrier)
          (fun S => (B S).grade) (gradedLimitGrade B f)
          (fun {S T} h => (f S T h).hom) (gradedLimitInclusion B f)
          (fun h x => gradedLimitInclusion_map B f h x)
          (fun {S T} h => (f S T h).map_grade) (fun m x hx => hx) hx
        rw [← heq, hl, (gradedLimit_existsUnique_dividedPowers B f).choose_spec.1 S n y hy, hl]
        exact (g S).map_dpow n y hy }
  refine ⟨F, hl, ?_⟩
  intro k hk
  apply GradedDPHom.ext
  apply DirectLimit.Algebra.hom_ext
  intro S
  ext x
  exact hk S x

attribute [local instance] gradedLimitGradedAlgebra gradedLimitStrictlyGradedComm

universe y

/-- The colimit of a directed system of strictly graded-commutative nonnegatively graded
algebras with divided powers on their positive even parts, indexed by an arbitrary nonempty
directed preorder.

The colimit is graded by the elements coming from a homogeneous element of some stage, carries
the unique divided power structure for which every stage map preserves divided powers, and has
both the algebra and the module universal property: the first produces maps of graded algebras
with divided powers, the second — which is what a colimit of differentials needs, a differential
being linear and not multiplicative — produces `R`-linear maps.  Every element of the colimit,
homogeneous or not, comes from a stage, and two stage elements with the same image in the
colimit already agree at a later stage. -/
@[stacks 0F4I "directed colimit of graded algebras with divided powers"]
public theorem exists_gradedDividedPowerColimit
    {R : Type u} [CommRing R] {I : Type w}
    [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (B : I → Type v) [stageRing : ∀ S, Ring (B S)] [stageAlgebra : ∀ S, Algebra R (B S)]
    (Bᵢ : (S : I) → ℕ → Submodule R (B S))
    [stageGraded : ∀ S, GradedAlgebra (Bᵢ S)]
    [stageComm : ∀ S, IsStrictlyGradedComm (Bᵢ S)]
    (γ : (S : I) → DividedPowerStructure (Bᵢ S))
    (transition : ∀ {S T : I}, S ≤ T → B S →ₐ[R] B T)
    (htransition_self : ∀ (S : I) (x : B S), transition (le_refl S) x = x)
    (htransition_comp : ∀ {S T U : I} (h : S ≤ T) (h' : T ≤ U) (x : B S),
      transition h' (transition h x) = transition (h.trans h') x)
    (htransition_grade : ∀ {S T : I} (h : S ≤ T) (m : ℕ) (x : B S),
      x ∈ Bᵢ S m → transition h x ∈ Bᵢ T m)
    (htransition_dpow : ∀ {S T : I} (h : S ≤ T) (n : ℕ) (x : B S),
      x ∈ positiveEvenPart (Bᵢ S) →
        transition h ((γ S).dpow n x) = (γ T).dpow n (transition h x)) :
    ∃ (C : Type (max v w)) (ringC : Ring C),
      letI : Ring C := ringC
      ∃ algebraC : Algebra R C,
        letI : Algebra R C := algebraC
        ∃ (Cᵢ : ℕ → Submodule R C) (gradedC : GradedAlgebra Cᵢ),
          letI : GradedAlgebra Cᵢ := gradedC
          ∃ strictC : IsStrictlyGradedComm Cᵢ,
            letI : IsStrictlyGradedComm Cᵢ := strictC
            ∃ (δ : DividedPowerStructure Cᵢ) (incl : (S : I) → B S →ₐ[R] C),
              (∀ {S T : I} (h : S ≤ T) (x : B S), incl T (transition h x) = incl S x) ∧
              (∀ (S : I) (m : ℕ) (x : B S), x ∈ Bᵢ S m → incl S x ∈ Cᵢ m) ∧
              (∀ (m : ℕ) (x : C), x ∈ Cᵢ m →
                ∃ (S : I) (y : B S), y ∈ Bᵢ S m ∧ incl S y = x) ∧
              (∀ x : C, ∃ (S : I) (y : B S), incl S y = x) ∧
              (∀ (S : I) (n : ℕ) (x : B S), x ∈ positiveEvenPart (Bᵢ S) →
                δ.dpow n (incl S x) = incl S ((γ S).dpow n x)) ∧
              (∀ (S T : I) (x : B S) (y : B T), incl S x = incl T y →
                ∃ U : I, ∃ (hS : S ≤ U) (hT : T ≤ U),
                  transition hS x = transition hT y) ∧
              (∀ {D : Type z} [Ring D] [Algebra R D] (Dᵢ : ℕ → Submodule R D)
                  [GradedAlgebra Dᵢ] [IsStrictlyGradedComm Dᵢ]
                  (ε : DividedPowerStructure Dᵢ) (g : (S : I) → B S →ₐ[R] D),
                  (∀ {S T : I} (h : S ≤ T) (x : B S), g T (transition h x) = g S x) →
                  (∀ (S : I) (m : ℕ) (x : B S), x ∈ Bᵢ S m → g S x ∈ Dᵢ m) →
                  (∀ (S : I) (n : ℕ) (x : B S), x ∈ positiveEvenPart (Bᵢ S) →
                    ε.dpow n (g S x) = g S ((γ S).dpow n x)) →
                  ∃! F : C →ₐ[R] D,
                    (∀ (S : I) (x : B S), F (incl S x) = g S x) ∧
                    (∀ (m : ℕ) (x : C), x ∈ Cᵢ m → F x ∈ Dᵢ m) ∧
                    (∀ (n : ℕ) (x : C), x ∈ positiveEvenPart Cᵢ →
                      ε.dpow n (F x) = F (δ.dpow n x))) ∧
              ∀ {M : Type y} [AddCommGroup M] [Module R M] (g : (S : I) → B S →ₗ[R] M),
                  (∀ {S T : I} (h : S ≤ T) (x : B S), g T (transition h x) = g S x) →
                  ∃! F : C →ₗ[R] M, ∀ (S : I) (x : B S), F (incl S x) = g S x := by
  classical
  let Bb : I → GradedDPAlgebra.{u, v} R := fun S =>
    { carrier := B S
      ring := stageRing S
      algebra := stageAlgebra S
      grade := Bᵢ S
      graded := stageGraded S
      strict := stageComm S
      gamma := γ S }
  let fb : ∀ S T : I, S ≤ T → GradedDPHom (Bb S) (Bb T) := fun _ _ h =>
    { hom := transition h
      map_grade := fun m a ha => htransition_grade h m a ha
      map_dpow := fun n a ha => (htransition_dpow h n a ha).symm }
  have hds : DirectedSystem (fun S => (Bb S).carrier) (fun S T h => (fb S T h).hom) :=
    { map_self := fun {S} x => htransition_self S x
      map_map := fun {_ _ _} h h' x => htransition_comp h h' x }
  let := hds
  let Cb := gradedDirectLimit Bb fb
  refine ⟨Cb.carrier, Cb.ring, Cb.algebra, Cb.grade, Cb.graded, Cb.strict, Cb.gamma,
    fun S => (gradedDirectLimitInclusion Bb fb S).hom,
    fun h x => gradedLimitInclusion_map Bb fb h x,
    fun S m x hx => (gradedDirectLimitInclusion Bb fb S).map_grade m x hx,
    fun _ _ hx => hx, ?_,
    fun S n x hx => (gradedDirectLimitInclusion Bb fb S).map_dpow n x hx,
    fun _ _ _ _ heq => Quotient.exact heq, ?_, ?_⟩
  · intro x
    induction x using DirectLimit.induction (fun S T h => (fb S T h).hom) with
    | ih S y => exact ⟨S, y, rfl⟩
  · intro D ringD algebraD Dᵢ gradedD strictD ε g hg hggrade hgdpow
    let Db : GradedDPAlgebra.{u, z} R :=
      { carrier := D
        ring := ringD
        algebra := algebraD
        grade := Dᵢ
        graded := gradedD
        strict := strictD
        gamma := ε }
    let gb : ∀ S, GradedDPHom (Bb S) Db := fun S =>
      { hom := g S
        map_grade := fun m a ha => hggrade S m a ha
        map_dpow := fun n a ha => hgdpow S n a ha }
    obtain ⟨F, hF, hFu⟩ :=
      gradedDirectLimit_existsUnique_lift Bb fb Db gb (fun _ _ h x => hg h x)
    refine ⟨F.hom, ⟨hF, F.map_grade, F.map_dpow⟩, ?_⟩
    intro k hk
    exact congrArg GradedDPHom.hom
      (hFu { hom := k, map_grade := hk.2.1, map_dpow := hk.2.2 } hk.1)
  · intro M _ _ g hg
    refine ⟨{ toFun := DirectLimit.lift (fun S T h => (fb S T h).hom) (fun S x => g S x)
                (fun _ _ h x => (hg h x).symm)
              map_add' := DirectLimit.lift_add _ _
              map_smul' := DirectLimit.lift_smul _ _ }, fun _ _ => rfl, ?_⟩
    intro k hk
    apply LinearMap.ext
    intro x
    induction x using DirectLimit.induction (fun S T h => (fb S T h).hom) with
    | ih S y => exact hk S y

end GradedDirectLimit

attribute [local instance] gradedLimitGradedAlgebra gradedLimitStrictlyGradedComm

private theorem finiteVariable_directedSystem {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j) :
    DirectedSystem (fun S : Finset J => (finiteVariableAlgebra A deg hdeg S).carrier)
      (fun _ _ h => (finiteVariableMap A deg hdeg h).hom) where
  map_self := fun {S} x => congrArg (fun k => k.hom x) (finiteVariableMap_self A deg hdeg S)
  map_map := fun {_ _ _} h k x =>
    congrArg (fun l => l.hom x) (finiteVariableMap_comp A deg hdeg h k)

attribute [local instance] finiteVariable_directedSystem

@[reducible] private noncomputable def setVariableAlgebra {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j) :
    GradedDPAlgebra.{u,max v w} R :=
  gradedDirectLimit (fun S : Finset J => finiteVariableAlgebra A deg hdeg S)
    (fun _ _ h => finiteVariableMap A deg hdeg h)

private noncomputable abbrev setVariableStageInclusion {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j)
    (S : Finset J) :
    GradedDPHom (finiteVariableAlgebra A deg hdeg S) (setVariableAlgebra A deg hdeg) :=
  gradedDirectLimitInclusion (fun S : Finset J => finiteVariableAlgebra A deg hdeg S)
    (fun _ _ h => finiteVariableMap A deg hdeg h) S

private theorem setVariableStageInclusion_map {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j)
    {S T : Finset J} (h : S ⊆ T) (x : (finiteVariableAlgebra A deg hdeg S).carrier) :
    (setVariableStageInclusion A deg hdeg T).hom ((finiteVariableMap A deg hdeg h).hom x) =
      (setVariableStageInclusion A deg hdeg S).hom x :=
  gradedLimitInclusion_map (fun S : Finset J => finiteVariableAlgebra A deg hdeg S)
    (fun _ _ h => finiteVariableMap A deg hdeg h) h x

private theorem setVariableStageInclusion_injective {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j)
    (S : Finset J) :
    Function.Injective (setVariableStageInclusion A deg hdeg S).hom :=
  DirectLimit.mk_injective (fun _ _ h => (finiteVariableMap A deg hdeg h).hom)
    (fun _ _ h => finiteVariableMap_injective A deg hdeg h) S

private noncomputable def setVariableCoefficient {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j) :
    GradedDPHom A (setVariableAlgebra A deg hdeg) :=
  (setVariableStageInclusion A deg hdeg (∅ : Finset J)).comp
    (finiteVariableCoefficient A deg hdeg ∅)

private theorem setVariableStageInclusion_coefficient {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j) (S : Finset J)
    (a : A.carrier) :
    (setVariableStageInclusion A deg hdeg S).hom ((finiteVariableCoefficient A deg hdeg S).hom a) =
      (setVariableCoefficient A deg hdeg).hom a := by
  rw [← finiteVariableMap_coefficient A deg hdeg (Finset.empty_subset S) a,
    setVariableStageInclusion_map]
  rfl

private noncomputable def setVariableGenerator {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j) (j : J) :
    (setVariableAlgebra A deg hdeg).carrier :=
  (setVariableStageInclusion A deg hdeg {j}).hom
    (finiteVariableGenerator A deg hdeg {j} ⟨j, by simp⟩)

private theorem setVariableStageInclusion_generator {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j)
    (S : Finset J) (j : S) :
    (setVariableStageInclusion A deg hdeg S).hom (finiteVariableGenerator A deg hdeg S j) =
      setVariableGenerator A deg hdeg j.val := by
  have h : {j.val} ⊆ S := Finset.singleton_subset_iff.mpr j.property
  change (setVariableStageInclusion A deg hdeg S).hom (finiteVariableGenerator A deg hdeg S j) =
    (setVariableStageInclusion A deg hdeg {j.val}).hom
      (finiteVariableGenerator A deg hdeg {j.val} ⟨j.val, by simp⟩)
  rw [← setVariableStageInclusion_map A deg hdeg h, finiteVariableMap_generator]

private theorem setVariableCoefficient_injective {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j) :
    Function.Injective (setVariableCoefficient A deg hdeg).hom :=
  setVariableStageInclusion_injective A deg hdeg (∅ : Finset J)

private theorem setVariableGenerator_mem {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j) (j : J) :
    setVariableGenerator A deg hdeg j ∈ (setVariableAlgebra A deg hdeg).grade (deg j) :=
  (setVariableStageInclusion A deg hdeg {j}).map_grade (deg j) _
    (finiteVariableGenerator_mem A deg hdeg {j} ⟨j, Finset.mem_singleton_self j⟩)

/-- Two maps out of a finite stage agree after precomposing with a stage map when they agree on the
coefficients and the generators. -/
private theorem finiteVariableMap_comp_eq {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j)
    {S T : Finset J} (h : S ⊆ T) {D : GradedDPAlgebra.{u, z} R}
    (p : GradedDPHom (finiteVariableAlgebra A deg hdeg T) D)
    (q : GradedDPHom (finiteVariableAlgebra A deg hdeg S) D)
    (hc : ∀ a, p.hom ((finiteVariableCoefficient A deg hdeg T).hom a) =
      q.hom ((finiteVariableCoefficient A deg hdeg S).hom a))
    (hg : ∀ j : S, p.hom (finiteVariableGenerator A deg hdeg T ⟨j, h j.property⟩) =
      q.hom (finiteVariableGenerator A deg hdeg S j)) :
    p.comp (finiteVariableMap A deg hdeg h) = q := by
  apply finiteVariableAlgebra_hom_ext A deg hdeg S
  · intro a
    change p.hom ((finiteVariableMap A deg hdeg h).hom _) = _
    rw [finiteVariableMap_coefficient, hc]
  · intro j
    change p.hom ((finiteVariableMap A deg hdeg h).hom _) = _
    rw [finiteVariableMap_generator, hg]

/-- Two maps out of the set-variable algebra agree after precomposing with a stage inclusion when
they agree on the coefficients and the generators of that stage. -/
private theorem setVariableStageInclusion_comp_eq {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j)
    (S : Finset J) {D : GradedDPAlgebra.{u, z} R}
    (k : GradedDPHom (setVariableAlgebra A deg hdeg) D)
    (g : GradedDPHom (finiteVariableAlgebra A deg hdeg S) D)
    (hc : ∀ a, k.hom ((setVariableCoefficient A deg hdeg).hom a) =
      g.hom ((finiteVariableCoefficient A deg hdeg S).hom a))
    (hg : ∀ j : S, k.hom (setVariableGenerator A deg hdeg j) =
      g.hom (finiteVariableGenerator A deg hdeg S j)) :
    k.comp (setVariableStageInclusion A deg hdeg S) = g := by
  apply finiteVariableAlgebra_hom_ext A deg hdeg S
  · intro a
    change k.hom ((setVariableStageInclusion A deg hdeg S).hom _) = _
    rw [setVariableStageInclusion_coefficient, hc]
  · intro j
    change k.hom ((setVariableStageInclusion A deg hdeg S).hom _) = _
    rw [setVariableStageInclusion_generator, hg]

private theorem setVariableAlgebra_existsUnique_lift {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j)
    (D : GradedDPAlgebra.{u, z} R) (f : GradedDPHom A D)
    (t : J → D.carrier) (ht : ∀ j, t j ∈ D.grade (deg j)) :
    ∃! g : GradedDPHom (setVariableAlgebra A deg hdeg) D,
      (∀ a, g.hom ((setVariableCoefficient A deg hdeg).hom a) = f.hom a) ∧
      (∀ j, g.hom (setVariableGenerator A deg hdeg j) = t j) := by
  classical
  let g (S : Finset J) := (finiteVariableAlgebra_existsUnique_lift A deg hdeg S D f
    (fun j : S => t j.val) (fun j : S => ht j.val)).choose
  have hg (S : Finset J) := (finiteVariableAlgebra_existsUnique_lift A deg hdeg S D f
    (fun j : S => t j.val) (fun j : S => ht j.val)).choose_spec
  have hc (S T : Finset J) (h : S ⊆ T) :
      (g T).comp (finiteVariableMap A deg hdeg h) = g S := by
    apply finiteVariableMap_comp_eq
    · exact fun a => ((hg T).1.1 a).trans ((hg S).1.1 a).symm
    · exact fun j => ((hg T).1.2 _).trans ((hg S).1.2 j).symm
  obtain ⟨F,hF,hu⟩ := gradedDirectLimit_existsUnique_lift
    (fun S : Finset J => finiteVariableAlgebra A deg hdeg S)
    (fun S T h => finiteVariableMap A deg hdeg h) D g
    (fun S T h x => congrArg (fun k => k.hom x) (hc S T h))
  refine ⟨F, ⟨?_, ?_⟩, ?_⟩
  · intro a
    change F.hom ((setVariableStageInclusion A deg hdeg ∅).hom
      ((finiteVariableCoefficient A deg hdeg (∅ : Finset J)).hom a)) = _
    rw [hF, (hg ∅).1.1]
  · intro j
    change F.hom ((setVariableStageInclusion A deg hdeg {j}).hom
      (finiteVariableGenerator A deg hdeg {j} ⟨j, by simp⟩)) = _
    rw [hF, (hg {j}).1.2]
  · intro k hk
    apply hu k
    intro S x
    have heq : k.comp (setVariableStageInclusion A deg hdeg S) = g S := by
      apply setVariableStageInclusion_comp_eq
      · exact fun a => (hk.1 a).trans ((hg S).1.1 a).symm
      · exact fun j => (hk.2 j).trans ((hg S).1.2 j).symm
    exact congrArg (fun l => l.hom x) heq

private theorem finiteVariableAlgebra_generated {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j) (S : Finset J)
    (x : (finiteVariableAlgebra A deg hdeg S).carrier) :
    x ∈ finiteVariableStage (finiteVariableAlgebra A deg hdeg S).gamma
      (finiteVariableCoefficient A deg hdeg S).hom (finiteVariableGenerator A deg hdeg S)
      Finset.univ := by
  classical
  apply Subring.closure_mono (t := Set.range (finiteVariableCoefficient A deg hdeg S).hom ∪
    {x | ∃ j : S, j ∈ (Finset.univ : Finset S) ∧
      (x = finiteVariableGenerator A deg hdeg S j ∨
        ∃ n, x = (finiteVariableAlgebra A deg hdeg S).gamma.dpow n
          (finiteVariableGenerator A deg hdeg S j))})
    (s := Set.range (finiteVariableCoefficient A deg hdeg S).hom ∪
      {x | ∃ j : Fin (Fintype.card S), j ∈ (Finset.univ : Finset (Fin (Fintype.card S))) ∧
        (x = iteratedVariableGenerator A (Fintype.card S) (stageDeg deg S)
            (stageDeg_pos deg hdeg S) j ∨
          ∃ n, x = (finiteVariableAlgebra A deg hdeg S).gamma.dpow n
            (iteratedVariableGenerator A (Fintype.card S) (stageDeg deg S)
              (stageDeg_pos deg hdeg S) j))}) ?_
    (iteratedVariableAlgebra_generated A (Fintype.card S) (stageDeg deg S)
      (stageDeg_pos deg hdeg S) x)
  rintro y (hy | ⟨j,hj,hy⟩)
  · exact Or.inl hy
  · refine Or.inr ⟨(Fintype.equivFin S).symm j, by simp, ?_⟩
    simpa only [finiteVariableGenerator, Equiv.apply_symm_apply] using hy

private theorem setVariableStageInclusion_mem_finiteStage {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j) (S : Finset J)
    (x : (finiteVariableAlgebra A deg hdeg S).carrier) :
    (setVariableStageInclusion A deg hdeg S).hom x ∈
      finiteVariableStage (setVariableAlgebra A deg hdeg).gamma
        (setVariableCoefficient A deg hdeg).hom (setVariableGenerator A deg hdeg) S := by
  classical
  let Q := finiteVariableStage (setVariableAlgebra A deg hdeg).gamma
    (setVariableCoefficient A deg hdeg).hom (setVariableGenerator A deg hdeg) S
  have hx := finiteVariableAlgebra_generated A deg hdeg S x
  induction hx using Subring.closure_induction with
  | mem y hy =>
    rcases hy with ⟨a,rfl⟩ | ⟨j,hj,rfl | ⟨n,rfl⟩⟩
    · rw [setVariableStageInclusion_coefficient]
      exact Subring.subset_closure (Or.inl ⟨a,rfl⟩)
    · rw [setVariableStageInclusion_generator]
      exact Subring.subset_closure (Or.inr ⟨j.val,j.property,Or.inl rfl⟩)
    · by_cases hp : finiteVariableGenerator A deg hdeg S j ∈
          positiveEvenPart (finiteVariableAlgebra A deg hdeg S).grade
      · rw [← (setVariableStageInclusion A deg hdeg S).map_dpow n _ hp,
          setVariableStageInclusion_generator]
        exact Subring.subset_closure (Or.inr ⟨j.val,j.property,Or.inr ⟨n,rfl⟩⟩)
      · rw [(finiteVariableAlgebra A deg hdeg S).gamma.dpow_null hp, map_zero]
        exact Q.zero_mem
  | zero => rw [map_zero]; exact Q.zero_mem
  | one => rw [map_one]; exact Q.one_mem
  | add a b ha hb ha' hb' => rw [map_add]; exact Q.add_mem ha' hb'
  | neg a ha ha' => rw [map_neg]; exact Q.neg_mem ha'
  | mul a b ha hb ha' hb' => rw [map_mul]; exact Q.mul_mem ha' hb'

private theorem setVariableAlgebra_finite_support {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j)
    (x : (setVariableAlgebra A deg hdeg).carrier) :
    ∃ S : Finset J, x ∈ finiteVariableStage (setVariableAlgebra A deg hdeg).gamma
      (setVariableCoefficient A deg hdeg).hom (setVariableGenerator A deg hdeg) S := by
  obtain ⟨S,y,rfl⟩ := DirectLimit.exists_eq_mk
    (fun S T h => (finiteVariableMap A deg hdeg h).hom) x
  exact ⟨S, setVariableStageInclusion_mem_finiteStage A deg hdeg S y⟩

private theorem setVariableStageInclusion_exists_retraction {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j)
    (S : Finset J) :
    ∃ r : GradedDPHom (setVariableAlgebra A deg hdeg) (finiteVariableAlgebra A deg hdeg S),
      ∀ x, r.hom ((setVariableStageInclusion A deg hdeg S).hom x) = x := by
  classical
  let t (j : J) := if hj : j ∈ S then finiteVariableGenerator A deg hdeg S ⟨j,hj⟩ else 0
  obtain ⟨r,hr,_⟩ := setVariableAlgebra_existsUnique_lift A deg hdeg
    (finiteVariableAlgebra A deg hdeg S) (finiteVariableCoefficient A deg hdeg S) t
    (fun j => by
      dsimp only [t]
      split_ifs with hj
      · exact finiteVariableGenerator_mem A deg hdeg S ⟨j, hj⟩
      · exact Submodule.zero_mem _)
  have heq : r.comp (setVariableStageInclusion A deg hdeg S) =
      GradedDPHom.id (finiteVariableAlgebra A deg hdeg S) := by
    apply setVariableStageInclusion_comp_eq
    · exact hr.1
    · intro j
      rw [hr.2]
      simp only [t, dite_eq_left j.property]
      rfl
  exact ⟨r, fun x => congrArg (fun k => k.hom x) heq⟩

private theorem setVariableStageInclusion_range {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j)
    (S : Finset J) :
    (setVariableStageInclusion A deg hdeg S).hom.toRingHom.range =
      finiteVariableStage (setVariableAlgebra A deg hdeg).gamma
        (setVariableCoefficient A deg hdeg).hom (setVariableGenerator A deg hdeg) S := by
  classical
  apply le_antisymm
  · rintro x ⟨y,rfl⟩
    exact setVariableStageInclusion_mem_finiteStage A deg hdeg S y
  · apply Subring.closure_le.mpr
    obtain ⟨r,hr⟩ := setVariableStageInclusion_exists_retraction A deg hdeg S
    rintro x (⟨a,rfl⟩ | ⟨j,hj,rfl | ⟨n,rfl⟩⟩)
    · exact ⟨(finiteVariableCoefficient A deg hdeg S).hom a,
        setVariableStageInclusion_coefficient A deg hdeg S a⟩
    · exact ⟨finiteVariableGenerator A deg hdeg S ⟨j,hj⟩,
        setVariableStageInclusion_generator A deg hdeg S ⟨j,hj⟩⟩
    · by_cases hp : setVariableGenerator A deg hdeg j ∈
          positiveEvenPart (setVariableAlgebra A deg hdeg).grade
      · have hp' := algHom_mem_positiveEvenPart (setVariableAlgebra A deg hdeg).grade
          (finiteVariableAlgebra A deg hdeg S).grade r.hom r.map_grade hp
        rw [← setVariableStageInclusion_generator A deg hdeg S ⟨j,hj⟩, hr] at hp'
        refine ⟨(finiteVariableAlgebra A deg hdeg S).gamma.dpow n
          (finiteVariableGenerator A deg hdeg S ⟨j,hj⟩), ?_⟩
        change (setVariableStageInclusion A deg hdeg S).hom
          ((finiteVariableAlgebra A deg hdeg S).gamma.dpow n
            (finiteVariableGenerator A deg hdeg S ⟨j,hj⟩)) = _
        rw [← (setVariableStageInclusion A deg hdeg S).map_dpow n _ hp',
          setVariableStageInclusion_generator]
      · rw [(setVariableAlgebra A deg hdeg).gamma.dpow_null hp]
        exact Subring.zero_mem _

private noncomputable def finiteVariableStageRingEquiv {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j)
    (S : Finset J) :
    (finiteVariableAlgebra A deg hdeg S).carrier ≃+*
      finiteVariableStage (setVariableAlgebra A deg hdeg).gamma
        (setVariableCoefficient A deg hdeg).hom (setVariableGenerator A deg hdeg) S := by
  let Q := finiteVariableStage (setVariableAlgebra A deg hdeg).gamma
    (setVariableCoefficient A deg hdeg).hom (setVariableGenerator A deg hdeg) S
  let k : (finiteVariableAlgebra A deg hdeg S).carrier →+* Q :=
    (setVariableStageInclusion A deg hdeg S).hom.toRingHom.codRestrict Q
      (setVariableStageInclusion_mem_finiteStage A deg hdeg S)
  apply RingEquiv.ofBijective k
  constructor
  · intro x y h
    exact setVariableStageInclusion_injective A deg hdeg S (congrArg Subtype.val h)
  · intro x
    have hx := (setVariableStageInclusion_range A deg hdeg S).ge x.property
    obtain ⟨y,hy⟩ := hx
    exact ⟨y,Subtype.ext hy⟩

private theorem finiteVariableStageRingEquiv_apply {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j) (S : Finset J)
    (x : (finiteVariableAlgebra A deg hdeg S).carrier) :
    (finiteVariableStageRingEquiv A deg hdeg S x : (setVariableAlgebra A deg hdeg).carrier) =
      (setVariableStageInclusion A deg hdeg S).hom x := rfl

private theorem finiteVariable_insert_inverse_lifts {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j)
    [DecidableEq J] (S : Finset J) (j : J) (hj : j ∉ S) :
    let E := oneVariableExtension (finiteVariableAlgebra A deg hdeg S) (deg j) (hdeg j)
    ∃ g : GradedDPHom E.algebra (finiteVariableAlgebra A deg hdeg (insert j S)),
    ∃ r : GradedDPHom (finiteVariableAlgebra A deg hdeg (insert j S)) E.algebra,
      (∀ x, g.hom (E.coefficient.hom x) =
        (finiteVariableMap A deg hdeg (Finset.subset_insert j S)).hom x) ∧
      g.hom E.generator = finiteVariableGenerator A deg hdeg (insert j S) ⟨j, by simp⟩ ∧
      r.comp g = GradedDPHom.id E.algebra ∧
      g.comp r = GradedDPHom.id (finiteVariableAlgebra A deg hdeg (insert j S)) := by
  classical
  dsimp only
  let E := oneVariableExtension (finiteVariableAlgebra A deg hdeg S) (deg j) (hdeg j)
  let F := finiteVariableAlgebra A deg hdeg (insert j S)
  let i := finiteVariableMap A deg hdeg (Finset.subset_insert j S)
  obtain ⟨g,hg,_⟩ := oneVariableExtension_existsUnique_lift
    (finiteVariableAlgebra A deg hdeg S) (deg j) (hdeg j) F i
    (finiteVariableGenerator A deg hdeg (insert j S) ⟨j,by simp⟩)
    (finiteVariableGenerator_mem A deg hdeg (insert j S) ⟨j, by simp⟩)
  have hmem (x : ↥(insert j S)) (h : x.val ≠ j) : x.val ∈ S :=
    (Finset.mem_insert.mp x.property).resolve_left h
  let t (x : ↥(insert j S)) := if h : x.val = j then E.generator else
    E.coefficient.hom (finiteVariableGenerator A deg hdeg S ⟨x.val,hmem x h⟩)
  obtain ⟨r,hr,_⟩ := finiteVariableAlgebra_existsUnique_lift A deg hdeg (insert j S) E.algebra
    (E.coefficient.comp (finiteVariableCoefficient A deg hdeg S)) t
    (fun x : ↥(insert j S) => by
      dsimp only [t]
      split_ifs with hx
      · rw [hx]
        exact E.generator_mem
      · exact E.coefficient.map_grade (deg x.val) _
          (finiteVariableGenerator_mem A deg hdeg S ⟨x.val, hmem x hx⟩))
  have hri : r.comp i = E.coefficient := by
    apply finiteVariableMap_comp_eq
    · exact hr.1
    · intro x
      rw [hr.2]
      have hxj : x.val ≠ j := fun h => hj (h ▸ x.property)
      simp only [t, dite_eq_right hxj]
  have hrg : r.comp g = GradedDPHom.id E.algebra := by
    obtain ⟨k,hk,hu⟩ := oneVariableExtension_existsUnique_lift
      (finiteVariableAlgebra A deg hdeg S) (deg j) (hdeg j) E.algebra E.coefficient E.generator
      E.generator_mem
    apply (hu (r.comp g) ?_).trans (hu (GradedDPHom.id E.algebra) ⟨fun _ => rfl,rfl⟩).symm
    constructor
    · intro x
      change r.hom (g.hom (E.coefficient.hom x)) = E.coefficient.hom x
      rw [hg.1]
      exact congrArg (fun f => f.hom x) hri
    · change r.hom (g.hom E.generator) = E.generator
      rw [hg.2, hr.2]
      simp only [t, dite_eq_left rfl]
  have hgr : g.comp r = GradedDPHom.id F := by
    apply finiteVariableAlgebra_hom_ext A deg hdeg (insert j S)
    · intro a
      change g.hom (r.hom ((finiteVariableCoefficient A deg hdeg (insert j S)).hom a)) = _
      rw [hr.1]
      change g.hom (E.coefficient.hom ((finiteVariableCoefficient A deg hdeg S).hom a)) = _
      rw [hg.1, finiteVariableMap_coefficient]
      rfl
    · intro x
      change g.hom (r.hom (finiteVariableGenerator A deg hdeg (insert j S) x)) = _
      rw [hr.2]
      dsimp only [t]
      split_ifs with hx
      · rw [hg.2]
        congr 1
        exact Subtype.ext hx.symm
      · rw [hg.1, finiteVariableMap_generator]
        rfl
  exact ⟨g,r,hg.1,hg.2,hrg,hgr⟩

end DividedPowers.TateResolution
