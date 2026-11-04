module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.Coinduction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ExtAlongAnExactFunctor

/-!
# Shapiro's lemma for discrete modules over a profinite group

Let `G` be a profinite group and `H` a closed subgroup. Group cohomology of a discrete module is
computed by `Ext` out of the trivial module `ℤ`. *Shapiro's lemma* identifies the cohomology of
`H` with coefficients in a discrete `H`-module `N` with the cohomology of `G` with coefficients in
the coinduced module:

`Extⁿ_H(ℤ, N) ≅ Extⁿ_G(ℤ, Coind_H^G N)`.

Coinduction is exact and right adjoint to restriction, which is exact, so it carries injective
modules to injective modules; the identification in degree zero is the adjunction, since the
restriction of the trivial `G`-module `ℤ` is the trivial `H`-module `ℤ`.

## Main definitions

* `Stacks.GroupCohomology.trivialGModule`: an abelian group with the trivial action of `G`.
* `Stacks.GroupCohomology.shapiroIso`: Shapiro's lemma, as an isomorphism of functors
  `Extⁿ_H(ℤ, -) ≅ Coind_H^G ⋙ Extⁿ_G(ℤ, -)`.

## References

* [Stacks Project, Tag 0DV8](https://stacks.math.columbia.edu/tag/0DV8)
* [J.-P. Serre, *Galois cohomology*, I.2.5][serre1997galois]
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe v v' w

namespace Stacks.GroupCohomology

section Trivial

variable (G : Type v) [Group G] [TopologicalSpace G]

section

open scoped Stacks.DiscreteModuleTopology

/-- The trivial action of `G` on an abelian group is continuous for the discrete topology. -/
lemma isContinuous_trivial (A : ModuleCat.{w} ℤ) : (Action.trivial G A).IsContinuous := by
  rw [Action.isContinuous_def, continuous_prod_of_discrete_right]
  exact fun _ ↦ continuous_const

end

/-- An abelian group with the trivial action of `G`, as a discrete `G`-module. -/
def trivialGModule (A : Type w) [AddCommGroup A] : ContinuousGModule.{v, w} G :=
  ⟨⟨Action.trivial G (ModuleCat.of ℤ A), isContinuous_trivial G _⟩, ⟨rfl⟩⟩

/-- Every element of `G` acts as the identity on `trivialGModule G A`. -/
@[simp]
lemma trivialGModule_ρ (A : Type w) [AddCommGroup A] (g : G) (a : A) :
    ((trivialGModule G A).obj.obj.ρ g).hom a = a := rfl

variable {G} {G' : Type v'} [Group G'] [TopologicalSpace G']

/-- The restriction of a trivial module is the trivial module. -/
def restrictionTrivialIso (φ : G' →* G) (hφ : Continuous φ) (A : Type w) [AddCommGroup A] :
    (restriction φ hφ).obj (trivialGModule G A) ≅ trivialGModule G' A where
  hom := (gModuleHomEquiv G' _ _).symm ⟨AddMonoidHom.id _, fun _ _ ↦ rfl⟩
  inv := (gModuleHomEquiv G' _ _).symm ⟨AddMonoidHom.id _, fun _ _ ↦ rfl⟩
  hom_inv_id := hom_ext fun _ ↦ rfl
  inv_hom_id := hom_ext fun _ ↦ rfl

variable (G) in
/-- The functor sending an abelian group to the discrete `G`-module with trivial action. -/
def trivialFunctor : AddCommGrpCat.{w} ⥤ ContinuousGModule.{v, w} G where
  obj A := trivialGModule G A
  map f := (gModuleHomEquiv G _ _).symm ⟨f.hom, fun _ _ ↦ rfl⟩
  map_id _ := hom_ext fun _ ↦ rfl
  map_comp _ _ := hom_ext fun _ ↦ rfl

variable (G) in
/-- **The trivial module functor is left adjoint to taking invariants.** -/
def trivialFunctorAdjunction : trivialFunctor.{v, w} G ⊣ continuousGModuleInvariants.{v, w} G :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ :=
        { toFun φ := AddCommGrpCat.ofHom
            { toFun a := ⟨φ.hom.hom.hom.hom a, fun g ↦ (hom_comm φ g a).symm⟩
              map_zero' := Subtype.ext (map_zero φ.hom.hom.hom.hom)
              map_add' a b := Subtype.ext (map_add φ.hom.hom.hom.hom a b) }
          invFun ψ := (gModuleHomEquiv G _ _).symm
            ⟨{ toFun a := (ψ.hom a).1
               map_zero' := congrArg Subtype.val (map_zero ψ.hom)
               map_add' a b := congrArg Subtype.val (map_add ψ.hom a b) },
              fun g a ↦ ((ψ.hom a).2 g).symm⟩
          left_inv _ := hom_ext fun _ ↦ rfl
          right_inv _ := rfl }
      homEquiv_naturality_left_symm _ _ := hom_ext fun _ ↦ rfl
      homEquiv_naturality_right _ _ := rfl }

end Trivial

section Shapiro

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] (H : Subgroup G)

variable [HasExt.{max v w} (ContinuousGModule.{v, max v w} G)]
  [HasExt.{max v w} (ContinuousGModule.{v, max v w} H)]

/-- **Shapiro's lemma.** For a closed subgroup `H` of a profinite group `G`, the cohomology of `H`
with coefficients in a discrete `H`-module is the cohomology of `G` with coefficients in the
coinduced module, naturally and in every degree. -/
def shapiroIso (n : ℕ) :
    Abelian.extFunctorObj (trivialGModule.{v, max v w} H (ULift.{max v w} ℤ)) n ≅
      coinduction.{v, w} H ⋙
        Abelian.extFunctorObj (trivialGModule.{v, max v w} G (ULift.{max v w} ℤ)) n :=
  letI := restriction_additive.{v, v, max v w} H.subtype continuous_subtype_val
  Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso
    (restrictionCoinductionAdjunction.{v, w} H)
    (restrictionTrivialIso H.subtype continuous_subtype_val (ULift.{max v w} ℤ)) n

/-- Shapiro's lemma on a single module, as an equivalence of `Ext` groups. -/
def shapiroAddEquiv (N : ContinuousGModule.{v, max v w} H) (n : ℕ) :
    Abelian.Ext (trivialGModule.{v, max v w} H (ULift.{max v w} ℤ)) N n ≃+
      Abelian.Ext (trivialGModule.{v, max v w} G (ULift.{max v w} ℤ))
        ((coinduction.{v, w} H).obj N) n :=
  ((shapiroIso.{v, w} H n).app N).addCommGroupIsoToAddEquiv

end Shapiro

end Stacks.GroupCohomology

end
