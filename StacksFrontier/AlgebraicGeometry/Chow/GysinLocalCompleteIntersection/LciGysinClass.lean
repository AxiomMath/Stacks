module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.RegularImmersionGysinComposition
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.FactorizationIndependence
public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.SubbundleCompleted
public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.Statement
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.LocalCompleteIntersectionAffine
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.NoetherianRegularKoszul
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.SmoothConnectedComponents
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Gysin map `f^! = i^! ∘ g^*` of a local complete intersection morphism

Let `(S, δ)` be as in Situation 02QL and let `f : X ⟶ Y` be a local complete intersection
morphism of schemes locally of finite type over `S` which factors as `f = g ∘ i` with
`i : X ⟶ P` an immersion and `g : P ⟶ Y` smooth. The Gysin map of `f` is

  `f^! = i^! ∘ g^* ∈ A^*(X ⟶ Y)^∧`,

where `g^* ∈ A^*(P ⟶ Y)^∧` is flat pullback, taken on each connected component of `P`, and
`i^! = c(X ⟶ U, 𝒩_{X/U})` is the class attached to the normal sheaf of the regular closed
immersion `i' : X ⟶ U` into the open `U = P ∖ (closure(i(X)) ∖ i(X))` in which `i` is closed.

## Main definitions

* `Stacks.Chow.smoothPullbackCompletedClass` — `g^* ∈ A^*(P ⟶ Y)^∧` for a smooth `g`.
* `Stacks.Chow.SmoothFactorization.closedAmbient`, `Stacks.Chow.SmoothFactorization.closedImm`,
  `Stacks.Chow.SmoothFactorization.closedProj` — the closed-immersion form `f = i' ≫ g'` of a
  factorization.
* `Stacks.Chow.SmoothFactorization.normalBundle` — the normal sheaf of `i'`, a virtual normal
  sheaf.
* `Stacks.Chow.SmoothFactorization.immersionGysinClass` — `i^! ∈ A^*(X ⟶ U)^∧`.
* `Stacks.Chow.SmoothFactorization.smoothPullbackClass` — `(g|_U)^* ∈ A^*(U ⟶ Y)^∧`.
* `Stacks.Chow.lciGysinClass` — `f^! = i^! ∘ g^* ∈ A^*(X ⟶ Y)^∧`.

## References

* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 069G](https://stacks.math.columbia.edu/tag/069G)
* [Stacks Project, Tag 063L](https://stacks.math.columbia.edu/tag/063L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Flat pullback along a smooth morphism, in the completed group -/

section SmoothPullback

variable (C : ChowSituation.{u}) {P Y : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (g : P ⟶ Y) [Smooth g] [LocallyOfFiniteType g]
  (hg : g ≫ sY = sP)

/-- The restriction of a smooth morphism to a connected component of its source is smooth. -/
instance smooth_resConnectedComponent [IsLocallyNoetherian P] [IsLocallyNoetherian Y]
    (k : _root_.ConnectedComponents P) : Smooth (g.resConnectedComponent k) := by
  unfold Scheme.Hom.resConnectedComponent
  infer_instance

/-- The flat pullback class `g^* ∈ A^*(P ⟶ Y)^∧` of a smooth morphism `g`: on a connected
component `P_k` of `P`, on which `g` has constant relative dimension `d_k`, it is the flat pullback
class `(g|_{P_k})^* ∈ A^{-d_k}(P_k ⟶ Y_{a(k)})`, placed in degree `-d_k`. -/
def smoothPullbackCompletedClass :
    completedBivariantGroup C (gysinSystemOfInvertible C) sP sY g hg :=
  letI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian sP
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  fun k ↦ DirectSum.of _ (-(g.smoothComponentDimension k : ℤ))
    (flatPullbackBivariantClassOfInvertible C ((P.connectedComponentOpens k).ι ≫ sP)
      ((Y.connectedComponentOpens (g.continuous.connectedComponentsMap k)).ι ≫ sY)
      (g.resConnectedComponent k) (g.resConnectedComponent_comp_ι_comp hg k)
      (g.smoothComponentDimension k) (g.relativeDimension_resConnectedComponent_of_smooth k))

end SmoothPullback

/-! ### The closed-immersion form of a factorization -/

namespace SmoothFactorization

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (F : SmoothFactorization f)

/-- The open `U ⊆ P` in which the immersion `i : X ⟶ P` is closed. -/
abbrev closedAmbient : Scheme.{u} := F.imm.coborderRange.toScheme

/-- The closed immersion `i' : X ⟶ U`. -/
abbrev closedImm : X ⟶ F.closedAmbient := F.imm.liftCoborder

/-- The smooth morphism `g' = g|_U : U ⟶ Y`. -/
abbrev closedProj : F.closedAmbient ⟶ Y := F.imm.coborderRange.ι ≫ F.proj

/-- The composite `i' ≫ g' : X ⟶ Y` is `f`. -/
theorem closedImm_closedProj : F.closedImm ≫ F.closedProj = f := by
  rw [← Category.assoc, Scheme.Hom.liftCoborder_ι, F.imm_proj]

/-- The immersion `i' : X ⟶ U` of a factorization of a local complete intersection morphism is
regular, for `U` locally Noetherian. -/
@[sga "6 0 3.2" "special case", sga "6 VIII 1.1" "special case"]
theorem isRegularImmersion_closedImm [IsLocallyNoetherian F.closedAmbient]
    (hf : IsLocalCompleteIntersectionMorphism f) :
    Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion F.closedImm :=
  (Stacks.AlgebraicGeometry.RegularIdealSheaf.isRegularImmersion_iff_isKoszulRegularImmersion
    F.closedImm).2 (isKoszulRegularImmersion_of_koszul_comp_smooth F.closedImm F.closedProj
      (by rwa [F.closedImm_closedProj]))

/-- The normal sheaf `𝒩_{X/U} = 𝒞_{X/U}^∨` of the regular immersion `i' : X ⟶ U`, as a virtual
normal sheaf. -/
def normalBundle [IsLocallyNoetherian X] [IsLocallyNoetherian F.closedAmbient]
    (hf : IsLocalCompleteIntersectionMorphism f) : VirtualNormalBundle F.closedImm :=
  VirtualNormalBundle.ofIsRegularImmersion F.closedImm (F.isRegularImmersion_closedImm hf)

variable (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
  [LocallyOfFiniteType sY]

/-- The structure morphism of `U` over the base. -/
abbrev closedAmbientStructure : F.closedAmbient ⟶ C.S := F.closedProj ≫ sY

/-- The structure morphism `U ⟶ S` of `U` over the base is locally of finite type. -/
instance locallyOfFiniteType_closedAmbientStructure :
    LocallyOfFiniteType (F.closedAmbientStructure C sY) :=
  inferInstance

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] in
/-- If `f ≫ sY = sX`, then the composite of `i' : X ⟶ U` with the structure morphism `U ⟶ S` is
`sX`. -/
theorem closedImm_comp_closedAmbientStructure (hfs : f ≫ sY = sX) :
    F.closedImm ≫ F.closedAmbientStructure C sY = sX := by
  rw [closedAmbientStructure, ← Category.assoc, F.closedImm_closedProj, hfs]

/-- The class `i^! = c(X ⟶ U, 𝒩_{X/U}) ∈ A^*(X ⟶ U)^∧` of the normal sheaf of the regular
immersion `i' : X ⟶ U`. -/
def immersionGysinClass (hfs : f ≫ sY = sX) (hf : IsLocalCompleteIntersectionMorphism f) :
    completedBivariantGroup C (gysinSystemOfInvertible C) sX (F.closedAmbientStructure C sY)
      F.closedImm (F.closedImm_comp_closedAmbientStructure C sX sY hfs) :=
  letI := LocallyOfFiniteType.isLocallyNoetherian sX
  letI := LocallyOfFiniteType.isLocallyNoetherian (F.closedAmbientStructure C sY)
  (F.normalBundle hf).completedClass C (F.closedAmbientStructure C sY) sX
    (F.closedImm_comp_closedAmbientStructure C sX sY hfs)

/-- The flat pullback class `(g|_U)^* ∈ A^*(U ⟶ Y)^∧` of the smooth morphism `g' : U ⟶ Y`. -/
def smoothPullbackClass :
    completedBivariantGroup C (gysinSystemOfInvertible C) (F.closedAmbientStructure C sY) sY
      F.closedProj rfl :=
  smoothPullbackCompletedClass C (F.closedAmbientStructure C sY) sY F.closedProj rfl

end SmoothFactorization

/-! ### The Gysin map -/

section Gysin

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (hfs : f ≫ sY = sX)
  (hf : IsLocalCompleteIntersectionMorphism f) (F : SmoothFactorization f)

/-- The Gysin map `f^! = i^! ∘ g^* ∈ A^*(X ⟶ Y)^∧` of a local complete intersection morphism
`f : X ⟶ Y` of schemes locally of finite type over `S`, for a factorization `F` of `f` as an
immersion `i : X ⟶ P` followed by a smooth morphism `g : P ⟶ Y`: the composite in the completed
groups of the class `i^! = c(X ⟶ U, 𝒩_{X/U})` of the normal sheaf of the regular closed immersion
`i' : X ⟶ U` into the open `U ⊆ P` in which `i` is closed, and of the flat pullback `(g|_U)^*`
along the smooth morphism `g|_U`. -/
@[stacks 0FF3 "the Gysin map f^! = i^! ∘ g^* in A^*(X → Y)^∧ of a local complete intersection \
morphism f = g ∘ i, g smooth, i an immersion: i^! = c(X → U, N_{X/U}) of Tag 0FBK for the regular \
closed immersion of X into the open U ⊆ P where i is closed, g^* the flat pullback of Tag 0B78 on \
each connected component, ∘ the completed composition of Tag 0FE0"]
def lciGysinClass :
    completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hfs :=
  letI := LocallyOfFiniteType.isLocallyNoetherian sX
  letI := LocallyOfFiniteType.isLocallyNoetherian sY
  letI := LocallyOfFiniteType.isLocallyNoetherian (F.closedAmbientStructure C sY)
  completedBivariantGroupCongr C (gysinSystemOfInvertible C) sX sY F.closedImm_closedProj
    (comp_comp_structureMorphism_eq (F.closedImm_comp_closedAmbientStructure C sX sY hfs) rfl) hfs
    (completedBivariantCompositeOfInvertible C sX (F.closedAmbientStructure C sY) sY F.closedImm
      F.closedProj (F.closedImm_comp_closedAmbientStructure C sX sY hfs) rfl
      (F.immersionGysinClass C sX sY hfs hf) (F.smoothPullbackClass C sY))

end Gysin

end Stacks.Chow

end
