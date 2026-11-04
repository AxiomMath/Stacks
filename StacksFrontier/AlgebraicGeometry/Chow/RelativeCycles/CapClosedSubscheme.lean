module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CapTensorPullback
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedSubschemeFamily
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.GermSourceAndTarget.Flat
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaLocal
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.Sections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.AffinePushforward
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaMap.Consequence
public import StacksCore.Tactic.StacksAttribute

/-!
# The action on cycles of the family attached to a flat closed subscheme

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `Y` be locally of
finite type over `S` and let `f : X ⟶ Y` be locally of finite type. Let `Z ⊆ X` be a closed
subscheme whose scheme-theoretic fibres over `Y` have dimension at most `r` and set
`α = [Z/X/Y]_r`; let `W ⊆ Y` be a closed subscheme of delta-dimension at most `e` and set
`β = [W]_e`. This file proves that when `Z` is flat over `Y` the action `α ∩ β` is the cycle
`[Z ×_Y W]_{r + e}` of the closed subscheme `Z ×_Y W ⊆ X`.

## Main results

* `Stacks.Chow.cap_familyAssociatedToClosedSubscheme` — Stacks 0H6A, the equality
  `α ∩ β = [Z ×_Y W]_{r + e}`.
* `Stacks.Chow.familyAssociatedToModule_pushforwardStructureSheaf` — the family `[Z/X/Y]_r` of
  Example 0H4S is the family `[i_* 𝒪_Z / X / Y]_r` of Example 0H4Q, which is what lets Stacks
  0H69 be applied to it.
* `Stacks.Chow.tensorPullbackStructureSheavesIso` — the identification
  `i_* 𝒪_Z ⊗_{𝒪_X} f^* j_* 𝒪_W ≅ (Z ×_Y W ⟶ X)_* 𝒪_{Z ×_Y W}` that turns the right-hand side of
  Stacks 0H69 into the cycle of the closed subscheme `Z ×_Y W`.
* `Stacks.Chow.isFlatOver_pushforwardStructureSheaf` — flatness of `Z` over `Y` is flatness of
  `i_* 𝒪_Z` over `Y`, which is where the flatness hypothesis of the tag is consumed.
* `Stacks.Chow.cycleAssociatedToCoherentSheaf_eq_of_iso` — isomorphic coherent modules have the
  same associated cycle.

## Implementation notes

The dimension hypothesis is the one of Example 0H4S, `dim (Z_y) ≤ r` for every point `y` of the
base, with `Z_y` the closed subscheme `Z ×_X X_y` of `X_y`; this is equivalent to `Z ⟶ Y` having
relative dimension at most `r` in the sense of Definition 02NJ, since the dimension of a space
is the supremum of its local dimensions, and it is the bound under which `α` is defined at all.

Both sides of the main equality lie in `Stacks.Chow.CycleGroup C (f ≫ sY) ((r : ℤ) + e)`, so no
cast appears, and `e : ℤ` is unrestricted as in the source. Local Noetherianness of `X` and `Y`
and local finite type of `f ≫ sY` are produced from the hypotheses rather than assumed.

## References

* [Stacks Project, Tag 0H6A](https://stacks.math.columbia.edu/tag/0H6A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Cycles of isomorphic modules -/

/-- Isomorphic coherent modules have the same associated cycle: the coefficient at a point is
the multiplicity there, and isomorphic modules have the same multiplicity. -/
theorem cycleAssociatedToCoherentSheaf_eq_of_iso (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] {M N : X.Modules} [M.IsCoherent] [N.IsCoherent]
    (e : M ≅ N) (k : ℤ)
    (hM : schemeDeltaDimension C ((reducedSupport M).subschemeι ≫ f) ≤ (k : EInt))
    (hN : schemeDeltaDimension C ((reducedSupport N).subschemeι ≫ f) ≤ (k : EInt)) :
    cycleAssociatedToCoherentSheaf C f M k hM = cycleAssociatedToCoherentSheaf C f N k hN := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x => ?_)
  by_cases hx : relativeDimension C.dimensionFunction f x = k
  · rw [cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq C f M k hM hx,
      cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq C f N k hN hx,
      sheafMultiplicity_eq_of_iso e x]
  · rw [cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne C f M k hM hx,
      cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne C f N k hN hx]

/-! ### The structure sheaf of a flat closed subscheme -/

/-- The structure sheaf of `A` is flat over `B` for a flat morphism `q : A ⟶ B`: its stalk at a
point is the local ring of `A` there, and flatness of `q` is flatness of that local ring over
the local ring of `B`. -/
@[ega "0 6.7.1" "partial", ega "IV 2.1.1" "partial"]
theorem isFlatOver_unitModule {A B : Scheme.{u}} (q : A ⟶ B) [Flat q] :
    IsFlatOver q.toLRSHom.toShHom (Ample.unitModule A) := fun x =>
  (MorphismOfGerms.flat_stalkMap_iff_isFlatOverAt_unit q x).mp
    ((Flat.iff_flat_stalkMap q).mp inferInstance x)

/-- The direct image of the structure sheaf of a closed subscheme `i : Z ⟶ X` is flat over `Y`
as soon as `Z` is flat over `Y`: the closed immersion is affine, so flatness over `Y` passes
between `𝒪_Z` and `i_* 𝒪_Z` by Stacks 0FLM. -/
theorem isFlatOver_pushforwardStructureSheaf {X Y Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (f : X ⟶ Y) [Flat (i ≫ f)] :
    IsFlatOver f.toLRSHom.toShHom ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z)) :=
  (isFlatOver_pushforward_iff i f (Ample.unitModule Z)).mp (isFlatOver_unitModule (i ≫ f))

/-! ### Base change of the structure sheaf of a closed subscheme -/

/-- **Base change of `i_* 𝒪_Z`.** For a cartesian square `p ≫ i = q ≫ g` with `i : Z ⟶ X` a
closed immersion, the inverse image along `g` of `i_* 𝒪_Z` is the direct image along the base
change `q` of the structure sheaf of the fibre product: the base-change morphism of Stacks 02KG
is invertible because a closed immersion is affine and `𝒪_Z` is quasi-coherent, and the inverse
image of a structure sheaf is a structure sheaf. -/
@[ega "I 10.14.6" "special case",
  sga "3 VIB 11.1" "(1), special case",
  sga "6 III 1.1.3" "special case"]
def pullbackPushforwardStructureSheafIso {X Z T P : Scheme.{u}} {i : Z ⟶ X} {g : T ⟶ X}
    {p : P ⟶ Z} {q : P ⟶ T} [IsClosedImmersion i] (hsq : IsPullback p q i g) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z)) ≅
      (Scheme.Modules.pushforward q).obj (Ample.unitModule P) :=
  haveI : IsAffineHom i := inferInstance
  haveI := Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom
    hsq (Ample.unitModule Z)
  asIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hsq.w).app
      (Ample.unitModule Z)) ≪≫
    (Scheme.Modules.pushforward q).mapIso
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso p)

/-! ### The structure sheaf of a fibre product of closed subschemes -/

/-- **`i_* 𝒪_Z ⊗_{𝒪_X} f^* j_* 𝒪_W ≅ 𝒪_{Z ×_Y W}`**, pushed forward to `X`. Both closed
immersions are affine, so the projection formula of Stacks 0FZE moves `i_*` out of the tensor
product, the left unitor cancels `𝒪_Z`, and the base-change isomorphism of Stacks 02KG
identifies `(i ≫ f)^* j_* 𝒪_W` with the direct image of the structure sheaf of `Z ×_Y W`. -/
def tensorPullbackStructureSheavesIso {X Y Z W : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ Y) (j : W ⟶ Y) [IsClosedImmersion j] :
    tensorPullback f ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z))
        ((Scheme.Modules.pushforward j).obj (Ample.unitModule W)) ≅
      (Scheme.Modules.pushforward (pullback.fst (i ≫ f) j ≫ i)).obj
        (Ample.unitModule (pullback (i ≫ f) j)) :=
  haveI : IsAffineHom i := inferInstance
  haveI : IsAffineHom j := inferInstance
  let G : Y.Modules := (Scheme.Modules.pushforward j).obj (Ample.unitModule W)
  let H : X.Modules := (Scheme.Modules.pullback f).obj G
  Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaIsoOfQuasicoherent i
      (Ample.unitModule Z) H inferInstance inferInstance ≪≫
    (Scheme.Modules.pushforward i).mapIso
      (Stacks.ProjectionFormula.unitTensorIso Z.toRingedSpace
          ((Scheme.Modules.pullback i).obj H) ≪≫
        (Scheme.Modules.pullbackComp i f).app G ≪≫
        pullbackPushforwardStructureSheafIso ((IsPullback.of_hasPullback (i ≫ f) j).flip)) ≪≫
    (Scheme.Modules.pushforwardComp (pullback.fst (i ≫ f) j) i).app
      (Ample.unitModule (pullback (i ≫ f) j))

/-- A module isomorphic to `m_* 𝒪_P` for a closed immersion `m` has support the image of `m`. -/
private theorem supp_eq_range_of_iso_pushforwardStructureSheaf {X P : Scheme.{u}} (m : P ⟶ X)
    [IsClosedImmersion m] {M : X.Modules}
    (e : M ≅ (Scheme.Modules.pushforward m).obj (Ample.unitModule P)) :
    SheafOfModules.supp M = Set.range (ConcreteCategory.hom m.base) := by
  rw [SheafOfModules.supp_eq_of_iso e]
  exact supp_pushforwardStructureSheaf m

/-! ### The fibres of a closed subscheme -/

section Fibre

variable {X Y Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ Y)

/-- The support of `i_* 𝒪_Z` restricted to the scheme-theoretic fibre `X_y` is the image of
`Z_y = Z ×_X X_y` in `X_y`: the restriction is the direct image of the structure sheaf of `Z_y`
by base change, and the support of such a direct image is the image of the immersion. -/
theorem supp_pullback_fiberι_pushforwardStructureSheaf (y : Y) :
    SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι y)).obj
        ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z))) =
      Set.range (ConcreteCategory.hom (pullback.snd i (f.fiberι y)).base) := by
  exact supp_eq_range_of_iso_pushforwardStructureSheaf _
    (pullbackPushforwardStructureSheafIso (IsPullback.of_hasPullback i (f.fiberι y)))

/-- The hypothesis `dim (Z_y) ≤ r` of Example 0H4S supplies the dimension bound on the fibrewise
supports of `i_* 𝒪_Z` that the associated family of cycles requires: that support is the image of
`Z_y`, which is homeomorphic to `Z_y` because `Z_y ⟶ X_y` is a closed immersion. -/
theorem topologicalKrullDim_supp_pullback_fiberι_le {r : ℕ}
    (hZ : ∀ y : Y,
      topologicalKrullDim (pullback i (f.fiberι y) : Scheme.{u}) ≤ (r : WithBot ℕ∞)) (y : Y) :
    topologicalKrullDim (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι y)).obj
        ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z)))) ≤ (r : WithBot ℕ∞) := by
  rw [supp_pullback_fiberι_pushforwardStructureSheaf i f y]
  exact le_of_eq_of_le (IsHomeomorph.topologicalKrullDim_eq _
    (IsClosedImmersion.isClosedEmbedding
      (pullback.snd i (f.fiberι y))).isEmbedding.toHomeomorph.isHomeomorph).symm (hZ y)

variable [IsLocallyNoetherian X] [LocallyOfFiniteType f]

/-- The delta-dimension of `Z_y` over the residue field of `y` is at most `r`: every point of
`Z_y` lies in the support of `i_* 𝒪_Z` on the fibre, where the relative dimension is bounded by
the dimension of that support. -/
theorem schemeDeltaDimension_fiber_closedSubscheme_le {r : ℕ}
    (hZ : ∀ y : Y,
      topologicalKrullDim (pullback i (f.fiberι y) : Scheme.{u}) ≤ (r : WithBot ℕ∞)) (y : Y) :
    schemeDeltaDimension (fieldChowSituation (Y.residueField y))
        (pullback.snd i (f.fiberι y) ≫ f.fiberToSpecResidueField y) ≤ ((r : ℤ) : EInt) := by
  have : IsLocallyNoetherian (f.fiber y) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField y)
  let F : X.Modules := (Scheme.Modules.pushforward i).obj (Ample.unitModule Z)
  let : F.IsFiniteType := isFiniteType_of_isCoherent F
  let : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  refine schemeDeltaDimension_le_of_forall_relativeDimension_le _ _ _ fun w => ?_
  refine relativeDimension_le_of_mem_supp (fieldChowSituation (Y.residueField y))
    (f.fiberToSpecResidueField y) _
    (fiberModule_schemeDeltaDimension_le f F r
      (topologicalKrullDim_supp_pullback_fiberι_le i f hZ) y) ?_
  rw [supp_pullback_fiberι_pushforwardStructureSheaf i f y]
  exact ⟨w, rfl⟩

/-- **The fibrewise formula for `[i_* 𝒪_Z / X / Y]_r`.** The member over `y` of the family of
cycles attached to `i_* 𝒪_Z` is the cycle `[Z_y]_r` of the closed subscheme `Z_y ⊆ X_y`, which is
Example 0H4S's description of `[Z/X/Y]_r`. On the fibre this is Stacks 02QY together with the
base change identifying the restriction of `i_* 𝒪_Z` with the direct image of `𝒪_{Z_y}`. -/
theorem familyAssociatedToModule_pushforwardStructureSheaf_apply (r : ℕ)
    (hZ : ∀ y : Y,
      topologicalKrullDim (pullback i (f.fiberι y) : Scheme.{u}) ≤ (r : WithBot ℕ∞)) (y : Y) :
    letI F : X.Modules := (Scheme.Modules.pushforward i).obj (Ample.unitModule Z)
    letI : F.IsFiniteType := isFiniteType_of_isCoherent F
    letI : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
    familyAssociatedToModule f F r (topologicalKrullDim_supp_pullback_fiberι_le i f hZ) y =
      cycleAssociatedToClosedSubscheme (fieldChowSituation (Y.residueField y))
        (f.fiberToSpecResidueField y) (pullback.snd i (f.fiberι y)) (r : ℤ) := by
  have : IsLocallyNoetherian (f.fiber y) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField y)
  let F : X.Modules := (Scheme.Modules.pushforward i).obj (Ample.unitModule Z)
  let : F.IsFiniteType := isFiniteType_of_isCoherent F
  let : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  rw [familyAssociatedToModule_apply,
    cycleAssociatedToClosedSubscheme_eq_cycleAssociatedToCoherentSheaf
      (fieldChowSituation (Y.residueField y)) (f.fiberToSpecResidueField y)
      (pullback.snd i (f.fiberι y)) (r : ℤ)
      (schemeDeltaDimension_fiber_closedSubscheme_le i f hZ y)]
  exact cycleAssociatedToCoherentSheaf_eq_of_iso _ _
    (pullbackPushforwardStructureSheafIso (IsPullback.of_hasPullback i (f.fiberι y))) _ _ _

/-- **`[i_* 𝒪_Z / X / Y]_r = [Z/X/Y]_r`.** The family of cycles attached to the coherent module
`i_* 𝒪_Z` by Example 0H4Q is the family attached to the closed subscheme `Z` by Example 0H4S:
fibrewise this is `familyAssociatedToModule_pushforwardStructureSheaf_apply`. -/
theorem familyAssociatedToModule_pushforwardStructureSheaf (r : ℕ)
    (hZ : ∀ y : Y,
      topologicalKrullDim (pullback i (f.fiberι y) : Scheme.{u}) ≤ (r : WithBot ℕ∞)) :
    letI F : X.Modules := (Scheme.Modules.pushforward i).obj (Ample.unitModule Z)
    letI : F.IsFiniteType := isFiniteType_of_isCoherent F
    letI : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
    familyAssociatedToModule f F r (topologicalKrullDim_supp_pullback_fiberι_le i f hZ) =
      familyAssociatedToClosedSubscheme f i r :=
  funext fun y =>
    (familyAssociatedToModule_pushforwardStructureSheaf_apply i f r hZ y).trans
      (familyAssociatedToClosedSubscheme_apply f i r y).symm

end Fibre

/-! ### Stacks 0H6A -/

/-- **Stacks Project, Tag 0H6A.** Let `(S, δ)` and `f : X ⟶ Y` be as in Section 0H65. Let
`Z ⊆ X` be a closed subscheme of relative dimension at most `r` over `Y`, so that the fibres
`Z_y = Z ×_X X_y` have dimension at most `r`, and set `α = [Z/X/Y]_r` (Example 0H4S). Let
`W ⊆ Y` be a closed subscheme of `δ`-dimension at most `e` and set `β = [W]_e` (Chow Homology,
Definition 02QU). If `Z` is flat over `Y`, then `α ∩ β = [Z ×_Y W]_{r + e}`.

The proof is the special case `F = 𝒪_Z`, `G = 𝒪_W` of Stacks 0H69: the family `α` is the family
of cycles attached to the coherent module `i_* 𝒪_Z` of Example 0H4Q, by
`Stacks.Chow.familyAssociatedToModule_pushforwardStructureSheaf`; the cycle of a closed
subscheme is the cycle of its structure sheaf (Stacks 02QY) on both sides; flatness of `Z` over
`Y` is flatness of `i_* 𝒪_Z` over `Y` because a closed immersion is affine; and the projection
formula together with base change identifies `i_* 𝒪_Z ⊗_{𝒪_X} f^* j_* 𝒪_W` with the structure
sheaf of `Z ×_Y W` pushed forward to `X`. -/
@[stacks 0H6A]
theorem cap_familyAssociatedToClosedSubscheme (C : ChowSituation.{u}) {X Y Z W : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (r : ℕ) (e : ℤ)
    (i : Z ⟶ X) [IsClosedImmersion i] [Flat (i ≫ f)]
    (hZ : ∀ y : Y, topologicalKrullDim (pullback i (f.fiberι y) : Scheme.{u}) ≤ (r : WithBot ℕ∞))
    (j : W ⟶ Y) [IsClosedImmersion j]
    (hWe : schemeDeltaDimension C (j ≫ sY) ≤ (e : EInt)) :
    cap C sY f (familyAssociatedToClosedSubscheme f i r)
        (cycleAssociatedToClosedSubscheme C sY j e) =
      cycleAssociatedToClosedSubscheme C (f ≫ sY) (pullback.fst (i ≫ f) j ≫ i)
        ((r : ℤ) + e) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sY)
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  let F : X.Modules := (Scheme.Modules.pushforward i).obj (Ample.unitModule Z)
  let G : Y.Modules := (Scheme.Modules.pushforward j).obj (Ample.unitModule W)
  let : F.IsFiniteType := isFiniteType_of_isCoherent F
  let : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  let m : pullback (i ≫ f) j ⟶ X := pullback.fst (i ≫ f) j ≫ i
  have hdim := topologicalKrullDim_supp_pullback_fiberι_le i f hZ
  have hGe : schemeDeltaDimension C ((reducedSupport G).subschemeι ≫ sY) ≤ (e : EInt) :=
    schemeDeltaDimension_reducedSupport_pushforwardStructureSheaf_le C sY j hWe
  have hsupp : SheafOfModules.supp (tensorPullback f F G) =
      Set.range (ConcreteCategory.hom m.base) :=
    supp_eq_range_of_iso_pushforwardStructureSheaf m (tensorPullbackStructureSheavesIso i f j)
  have hmdim : schemeDeltaDimension C (m ≫ (f ≫ sY)) ≤ (((r : ℤ) + e : ℤ) : EInt) :=
    schemeDeltaDimension_le_of_forall_relativeDimension_le C (f ≫ sY) m fun p =>
      relativeDimension_le_of_mem_supp C (f ≫ sY) (tensorPullback f F G)
        (schemeDeltaDimension_tensorPullback_le C sY f r e F hdim G hGe) (hsupp ▸ ⟨p, rfl⟩)
  rw [← familyAssociatedToModule_pushforwardStructureSheaf i f r hZ,
    cycleAssociatedToClosedSubscheme_eq_cycleAssociatedToCoherentSheaf C sY j e hWe,
    cap_familyAssociatedToModule C sY f r e F hdim
      (isFlatOver_pushforwardStructureSheaf i f) G hGe,
    cycleAssociatedToClosedSubscheme_eq_cycleAssociatedToCoherentSheaf C (f ≫ sY) m
      ((r : ℤ) + e) hmdim]
  exact cycleAssociatedToCoherentSheaf_eq_of_iso C (f ≫ sY)
    (tensorPullbackStructureSheavesIso i f j) ((r : ℤ) + e) _ _

end Stacks.Chow

end
