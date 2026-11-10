module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FlatDeformation.Surjectivity
public import StacksFrontier.Deformation.ToposThickening.SquareZeroExtensionNaiveExt
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flat deformations across a first order thickening form a torsor

Let `S ⊂ S'` be a first order thickening of schemes and `f : X ⟶ S` flat. This file proves part
(1) of [Stacks Project, Tag 0D14]: if a flat `f' : X' ⟶ S'` with `X ≅ X' ×_{S'} S` over `S`
exists, the isomorphism classes of such pairs are principal homogeneous under
`Ext¹_{𝒪_X}(NL_{X/S}, f^*𝒞_{S/S'})`. Part (2) is
`Stacks.Thickenings.flatThickeningAutEquiv`.

## Main definitions

* `Stacks.Thickenings.FlatDeformation.solutionOf`: the solution of the square-zero extension
  problem `problem` attached to a flat deformation.
* `Stacks.Thickenings.FlatDeformation.classesEquiv`: the bijection between isomorphism classes
  of flat deformations and isomorphism classes of solutions.
* `Stacks.Thickenings.FlatDeformation.addTorsor`: the torsor of [Stacks Project, Tag 08UK]
  carried over along `classesEquiv` and `extIso`.

## Main results

* `Stacks.Thickenings.FlatDeformation.exists_addTorsor_classes`: the isomorphism classes of flat
  deformations of `f` along `S ⊂ S'` are principal homogeneous under
  `Ext¹_{𝒪_X}(NL_{X/S}, f^*𝒞_{S/S'})`, with `ξ` sending one class to another exactly when the
  obstruction class separating the corresponding solutions is `ξ`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite
open Deformation.ToposThickening.RingedToposExtensionProblem

universe u

namespace Stacks.Thickenings.FlatDeformation

variable {X S S' : Scheme.{u}} {t : S ⟶ S'} {f : X ⟶ S} [IsClosedImmersion t]
  (hst : t.ker ^ 2 = ⊥)

/-- The map from the ideal of the thickened base to `f^*𝒞_{S/S'}` read off a flat deformation;
it does not depend on the deformation (`idealMap_eq`). -/
abbrev refIdeal (D₀ : FlatDeformation t f) :
    ideal t f hst ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (structureHom f).fSharpInverseImage)).obj (conormalModule t f) :=
  have := D₀.isIso_base hst
  idealMap hst D₀

/-- The map `refIdeal hst D₀` equals the map `idealMap hst D` read off any flat deformation
`D`. -/
theorem refIdeal_eq (D₀ D : FlatDeformation t f) [IsIso D.i.base] :
    refIdeal hst D₀ = idealMap hst D :=
  have := D₀.isIso_base hst
  idealMap_eq hst D₀ D

/-- **The solution of the deformation problem attached to a flat deformation `D`**, for the
problem whose kernel map is read off a reference deformation `D₀`. -/
def solutionOf (D₀ D : FlatDeformation t f) :
    (problem t f hst (refIdeal hst D₀)).CompatibleFirstOrderThickening :=
  haveI := D.isIso_base hst
  toSolution hst D _ (refIdeal_eq hst D₀ D)

/-- The map `refIdeal hst D₀` sends the section `idealSection hst W j hj` defined by a local
section `j` of the ideal of `S` in `S'` to the corresponding section `canonicalSection W j hj` of
`f^*𝒞_{S/S'}`. -/
theorem refIdeal_idealSection (D₀ : FlatDeformation t f) (W : S'.Opens) (j : Γ(S', W))
    (hj : (t.app W).hom j = 0) :
    ((refIdeal hst D₀).val.app (op ((Opens.map (f.base ≫ t.base)).obj W))).hom
        (idealSection hst W j hj) = canonicalSection W j hj :=
  have := D₀.isIso_base hst
  idealMap_idealSection hst D₀ W j hj

/-- **The flat deformation realizing a solution**, [Stacks Project, Tag 05YV] and
[Stacks Project, Tag 063Y]. -/
abbrev deformationOfRef [Flat f] (D₀ : FlatDeformation t f)
    (P : (problem t f hst (refIdeal hst D₀)).CompatibleFirstOrderThickening) :
    FlatDeformation t f :=
  deformationOf P (refIdeal_idealSection hst D₀)

/-- **The isomorphism classes of flat deformations are the isomorphism classes of solutions of
the deformation problem.** -/
def classesEquiv [Flat f] (D₀ : FlatDeformation t f) :
    Classes t f ≃
      CompatibleFirstOrderThickening.IsomorphismClasses.{u, u, u, u, u, u}
        (problem t f hst (refIdeal hst D₀)) where
  toFun := Quotient.map (sa := setoid t f)
    (sb := CompatibleFirstOrderThickening.isomorphicSetoid (problem t f hst (refIdeal hst D₀)))
    (solutionOf hst D₀)
    fun D₁ D₂ ⟨φ⟩ =>
      have := D₁.isIso_base hst
      have := D₂.isIso_base hst
      ⟨solutionIso hst φ _ (refIdeal_eq hst D₀ D₁) (refIdeal_eq hst D₀ D₂)⟩
  invFun := Quotient.map
    (sa := CompatibleFirstOrderThickening.isomorphicSetoid (problem t f hst (refIdeal hst D₀)))
    (sb := setoid t f) (deformationOfRef hst D₀)
    fun P Q ⟨e⟩ => ⟨isoOfSolutionIso (deformationOfRef hst D₀ P) (deformationOfRef hst D₀ Q)
      (idealMap_deformationOf P (refIdeal_idealSection hst D₀))
      (idealMap_deformationOf Q (refIdeal_idealSection hst D₀))
      (((solutionIsoDeformationOf P (refIdeal_idealSection hst D₀)).trans e).trans
        (solutionIsoDeformationOf Q (refIdeal_idealSection hst D₀)).symm)⟩
  left_inv := by
    rintro ⟨D⟩
    have := D.isIso_base hst
    exact Quotient.sound ⟨isoOfSolutionIso (deformationOfRef hst D₀ (solutionOf hst D₀ D)) D
      (idealMap_deformationOf _ (refIdeal_idealSection hst D₀)) (refIdeal_eq hst D₀ D)
      (solutionIsoDeformationOf (solutionOf hst D₀ D) (refIdeal_idealSection hst D₀))⟩
  right_inv := by
    rintro ⟨P⟩
    exact Quotient.sound ⟨solutionIsoDeformationOf P (refIdeal_idealSection hst D₀)⟩

/-- `classesEquiv hst D₀` sends the class of a flat deformation `D` to the class of the solution
`solutionOf hst D₀ D`. -/
theorem classesEquiv_mk [Flat f] (D₀ D : FlatDeformation t f) :
    classesEquiv hst D₀ (Quotient.mk (setoid t f) D) =
      Quotient.mk (CompatibleFirstOrderThickening.isomorphicSetoid
        (problem t f hst (refIdeal hst D₀))) (solutionOf hst D₀ D) :=
  rfl

include hst

/-- **The principal homogeneous structure** on the isomorphism classes of flat deformations,
carried over from the one of [Stacks Project, Tag 08UK] on the isomorphism classes of solutions
of the deformation problem along `classesEquiv`, and from `Ext¹` of the topos-level naive
cotangent complex to `Ext¹_{𝒪_X}(NL_{X/S}, f^*𝒞_{S/S'})` along `extIso`. -/
@[instance_reducible, sga "7 VI 4.16" "(b), special case"]
def addTorsor [Flat f] (D₀ : FlatDeformation t f) :
    AddTorsor (Scheme.naiveCotangentExt f (pullbackConormalModule f t) 1) (Classes t f) :=
  have : Nonempty (problem t f hst (refIdeal hst D₀)).CompatibleFirstOrderThickening :=
    ⟨solutionOf hst D₀ D₀⟩
  let := CompatibleFirstOrderThickening.addTorsorOfObstruction
    (CompatibleFirstOrderThickening.pairObstructionData (problem t f hst (refIdeal hst D₀)))
    (fun P Q => CompatibleFirstOrderThickening.pairObstruction_eq_zero_iff
      (S := problem t f hst (refIdeal hst D₀)) P Q)
    (extIso f (pullbackConormalModule f t) 1)
  Deformation.ToposThickening.addTorsorCongr (AddEquiv.refl _) (classesEquiv hst D₀)

/-- Under `addTorsor hst D₀`, `ξ` sends the class of `D₁` to the class of `D₂` if and only if
the obstruction class separating `solutionOf hst D₀ D₁` and `solutionOf hst D₀ D₂` is the image
of `ξ` under `extIso`. -/
theorem addTorsor_vadd_iff [Flat f] (D₀ : FlatDeformation t f)
    (ξ : Scheme.naiveCotangentExt f (pullbackConormalModule f t) 1)
    (D₁ D₂ : FlatDeformation t f) :
    (addTorsor hst D₀).vadd ξ (Quotient.mk (setoid t f) D₁) = Quotient.mk (setoid t f) D₂ ↔
      CompatibleFirstOrderThickening.pairObstruction (solutionOf hst D₀ D₁) (solutionOf hst D₀ D₂) =
        extIso f (pullbackConormalModule f t) 1 ξ := by
  have : Nonempty (problem t f hst (refIdeal hst D₀)).CompatibleFirstOrderThickening :=
    ⟨solutionOf hst D₀ D₀⟩
  let := CompatibleFirstOrderThickening.addTorsorOfObstruction
    (CompatibleFirstOrderThickening.pairObstructionData (problem t f hst (refIdeal hst D₀)))
    (fun P Q => CompatibleFirstOrderThickening.pairObstruction_eq_zero_iff
      (S := problem t f hst (refIdeal hst D₀)) P Q)
    (extIso f (pullbackConormalModule f t) 1)
  change (classesEquiv hst D₀).symm (ξ +ᵥ classesEquiv hst D₀ (Quotient.mk (setoid t f) D₁)) =
    Quotient.mk (setoid t f) D₂ ↔ _
  rw [Equiv.symm_apply_eq, eq_comm, eq_vadd_iff_vsub_eq]
  refine (Iff.of_eq (congrArg (· = ξ)
    (CompatibleFirstOrderThickening.addTorsorOfObstruction_vsub _ _ _
      (solutionOf hst D₀ D₂) (solutionOf hst D₀ D₁)))).trans ?_
  exact (extIso f (pullbackConormalModule f t) 1).symm_apply_eq

/-- The obstruction class separating the solutions `toSolution hst D₁ c hc₁` and
`toSolution hst D₂ c hc₂` equals the image of `ξ` under `extIso` if and only if the same holds
for an equal kernel map `c'`. -/
theorem pairObstruction_toSolution_congr {c c' : ideal t f hst ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (structureHom f).fSharpInverseImage)).obj (conormalModule t f)}
    (h : c = c') (D₁ D₂ : FlatDeformation t f) [IsIso D₁.i.base] [IsIso D₂.i.base]
    (hc₁ : c = idealMap hst D₁) (hc₂ : c = idealMap hst D₂) (hc₁' : c' = idealMap hst D₁)
    (hc₂' : c' = idealMap hst D₂)
    (ξ : Scheme.naiveCotangentExt f (pullbackConormalModule f t) 1) :
    CompatibleFirstOrderThickening.pairObstruction (toSolution hst D₁ c hc₁)
          (toSolution hst D₂ c hc₂) =
        extIso f (pullbackConormalModule f t) 1 ξ ↔
      CompatibleFirstOrderThickening.pairObstruction (toSolution hst D₁ c' hc₁')
          (toSolution hst D₂ c' hc₂') =
        extIso f (pullbackConormalModule f t) 1 ξ := by
  subst h
  rfl

/-- The relation defining the action does not depend on the reference deformation used to read
off the kernel map of the deformation problem. -/
theorem pairObstruction_solutionOf_congr (D₀ D₀' D₁ D₂ : FlatDeformation t f)
    (ξ : Scheme.naiveCotangentExt f (pullbackConormalModule f t) 1) :
    CompatibleFirstOrderThickening.pairObstruction (solutionOf hst D₀ D₁) (solutionOf hst D₀ D₂) =
        extIso f (pullbackConormalModule f t) 1 ξ ↔
      CompatibleFirstOrderThickening.pairObstruction (solutionOf hst D₀' D₁)
          (solutionOf hst D₀' D₂) =
        extIso f (pullbackConormalModule f t) 1 ξ :=
  have := D₀'.isIso_base hst
  have := D₁.isIso_base hst
  have := D₂.isIso_base hst
  pairObstruction_toSolution_congr hst (refIdeal_eq hst D₀ D₀') D₁ D₂ _ _ _ _ ξ

/-- Let `S ⊂ S'` be a first order thickening of schemes (`t : S ⟶ S'` a closed immersion whose
ideal sheaf squares to zero) and let `f : X ⟶ S` be flat. Suppose there exist a flat morphism
`f' : X' ⟶ S'` and an isomorphism `a : X ≅ X' ×_{S'} S` over `S` (a `FlatDeformation t f`,
recording `a` through `i = pr₁ ∘ a` and the cartesian square `IsPullback i f f' t`;
`FlatDeformation.ofPair` and `FlatDeformation.a` pass between the two). Then the set of isomorphism
classes of such pairs (`FlatDeformation.Classes t f`; by `FlatDeformation.nonempty_iso_iff` two
pairs are isomorphic exactly when there is `e : X'₁ ≅ X'₂` over `S'` with `(e ×_{S'} S) ∘ a₁ = a₂`)
is principal homogeneous under `Ext¹_{𝒪_X}(NL_{X/S}, f^*𝒞_{S/S'})`
(`Scheme.naiveCotangentExt f _ 1`, with `pullbackConormalModule f t = f^*𝒞_{S/S'}`).

The action is as follows: a pair is the same thing as a solution of the square-zero extension
problem
`0 ⟶ f^*𝒞_{S/S'} ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` over `0 ⟶ 𝒞_{S/S'} ⟶ 𝒪_{S'} ⟶ 𝒪_S ⟶ 0`
(`solutionOf`, with the ideal of `X` in `X'` identified with `f^*𝒞_{S/S'}` by
[Stacks Project, Tag 063Y]), and `ξ` sends the class of `(f'₁, a₁)` to the class of `(f'₂, a₂)`
exactly when the obstruction class of [Stacks Project, Tag 08UG] separating the two solutions is
`ξ`, which is the action of [Stacks Project, Tag 08UK]. The relation is independent of the
reference pair `D₀` used to write down the extension problem. -/
@[stacks 0D14, sga "7 VI 4.16" "(b), special case"]
theorem exists_addTorsor_classes [Flat f]
    (hne : Nonempty (FlatDeformation t f)) :
    ∃ T : AddTorsor (Scheme.naiveCotangentExt f (pullbackConormalModule f t) 1)
        (Classes t f),
      ∀ (ξ : Scheme.naiveCotangentExt f (pullbackConormalModule f t) 1)
        (D₀ D₁ D₂ : FlatDeformation t f),
        T.vadd ξ (Quotient.mk (setoid t f) D₁) = Quotient.mk (setoid t f) D₂ ↔
          CompatibleFirstOrderThickening.pairObstruction (solutionOf hst D₀ D₁)
              (solutionOf hst D₀ D₂) =
            extIso f (pullbackConormalModule f t) 1 ξ :=
  ⟨addTorsor hst hne.some, fun ξ D₀ D₁ D₂ =>
    (addTorsor_vadd_iff hst hne.some ξ D₁ D₂).trans
      (pairObstruction_solutionOf_congr hst hne.some D₀ D₁ D₂ ξ)⟩

end Stacks.Thickenings.FlatDeformation
