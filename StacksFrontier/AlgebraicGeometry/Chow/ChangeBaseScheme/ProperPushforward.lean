module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.ChowPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.Dimension
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.ProperDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre
public import StacksCore.Tactic.StacksAttribute

/-!
# Proper pushforward under a change of the base scheme

Let `B` be a flat base change of Chow situations, that is a flat morphism `g : S' ⟶ S` of the
two bases whose dimension functions differ by a constant `c` on the generic points of the fibres
of `g`, and let `Y → X → S` be morphisms with `X ⟶ S` locally of finite type. Writing
`X' = X ×_S S'` and `Y' = Y ×_S S'` for the base changes, the morphism `f : Y ⟶ X` induces a
morphism `f' : Y' ⟶ X'` over `S'`, and the square formed by `f`, `f'` and the two projections to
`Y` and `X` is cartesian. Consequently every property of morphisms stable under base change
passes from `f` to `f'`; in particular `f'` is proper as soon as `f` is.

This file proves Stacks 0FVL: for `f` proper, `f'` is proper and proper pushforward commutes
with the base-change map, both on cycle groups and on Chow groups.

## Main definitions

* `Stacks.Chow.baseChangeMorphism` — the induced morphism `Y ×_S S' ⟶ X ×_S S'`.

## Main results

* `Stacks.Chow.isPullback_baseChangeMorphism` — the square relating `f` and `f'` to the two
  projections is cartesian, so `Y ×_S S'` is also the fibre product `Y ×_X X'`.
* `Stacks.Chow.isProper_baseChangeMorphism` — **Stacks 0FVL, properness of the base change**.
* `Stacks.Chow.properPushforward_baseChangeCyclePullback` — **Stacks 0FVL, the cycle square**,
  `f'_* ∘ g^* = g^* ∘ f_*` on cycle groups.
* `Stacks.Chow.properChowPushforward_baseChangeChowPullback` — **Stacks 0FVL, the Chow square**,
  `f'_* ∘ g^* = g^* ∘ f_*` on Chow groups.
* `Stacks.Chow.properChowPushforward_baseChangeChowPullback_of_baseChangeChowPullback` —
  **Stacks 0FVL, the Chow square for the base-change map of Stacks 0FVJ**, the same square with
  the horizontal maps taken to be `Stacks.Chow.baseChangeChowPullback` instead of an arbitrary
  homomorphism with that property.

## Implementation notes

The base change of `X` is the chosen categorical pullback `pullback sX B.g`, with structure
morphism `CategoryTheory.Limits.pullback.snd` over the new base and projection
`CategoryTheory.Limits.pullback.fst` to `X`, as everywhere in this section; the base change of
`Y` is formed along the composite `Y ⟶ X ⟶ S`. The induced morphism is then the canonical map
between the two pullbacks, and the cartesian square is obtained from
`CategoryTheory.Limits.pullbackRightPullbackFstIso`, which identifies `Y ×_S S'` with
`Y ×_X (X ×_S S')`.

Coherence of the direct image of a coherent module under a proper morphism to a locally
Noetherian scheme is what the squares rest on: it enters through Stacks 02R6, which reads a
proper pushforward of cycles as the cycle of a direct image, and which is stated in this library
with the coherence of that direct image as an instance hypothesis. That coherence is the first
assertion of Stacks 02O5 and is proved, as
`Stacks.Chow.forall_properDirectImageIsCoherent`; neither square assumes it.

The Chow square is stated for an arbitrary base-change homomorphism `gChow` on Chow groups
characterized by `hgChow` as the homomorphism induced by `Stacks.Chow.baseChangeCyclePullback`
on classes of cycles, which is more general than the source's statement rather than less. It is
met by `Stacks.Chow.baseChangeChowPullback`, the base-change map of Stacks 0FVJ, whose defining
property `Stacks.Chow.baseChangeChowPullback_mk` is exactly that characterization; so the Chow
square also holds in the unconditional form
`Stacks.Chow.properChowPushforward_baseChangeChowPullback_of_baseChangeChowPullback`.

## References

* [Stacks Project, Tag 0FVG](https://stacks.math.columbia.edu/tag/0FVG)
* [Stacks Project, Tag 0FVI](https://stacks.math.columbia.edu/tag/0FVI)
* [Stacks Project, Tag 0FVJ](https://stacks.math.columbia.edu/tag/0FVJ)
* [Stacks Project, Tag 0FVL](https://stacks.math.columbia.edu/tag/0FVL)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 02R6](https://stacks.math.columbia.edu/tag/02R6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (B : FlatBaseChangeSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ B.base.S) (f : Y ⟶ X)

/-- The morphism `Y ×_S S' ⟶ X ×_S S'` induced by a morphism `f : Y ⟶ X` over the base `S` of a
flat base change of Chow situations. -/
def baseChangeMorphism :
    (pullback (f ≫ sX) B.g : Scheme.{u}) ⟶ (pullback sX B.g : Scheme.{u}) :=
  pullback.map (f ≫ sX) B.g sX B.g f (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- The induced morphism `Y ×_S S' ⟶ X ×_S S'` followed by the first projection to `X` equals the
first projection to `Y` followed by `f`. -/
@[simp]
theorem baseChangeMorphism_comp_fst :
    baseChangeMorphism B sX f ≫ pullback.fst sX B.g = pullback.fst (f ≫ sX) B.g ≫ f := by
  simp only [baseChangeMorphism, pullback.map, Category.comp_id]
  exact pullback.lift_fst _ _ _

/-- The induced morphism `Y ×_S S' ⟶ X ×_S S'` commutes with the second projections to `S'`. -/
@[simp]
theorem baseChangeMorphism_comp_snd :
    baseChangeMorphism B sX f ≫ pullback.snd sX B.g = pullback.snd (f ≫ sX) B.g := by
  simp only [baseChangeMorphism, pullback.map, Category.comp_id]
  exact pullback.lift_snd _ _ _

/-- The square formed by `f : Y ⟶ X`, the induced morphism `f' : Y ×_S S' ⟶ X ×_S S'` and the two
projections to `Y` and `X` is cartesian: both `Y ×_S S'` and `Y ×_X (X ×_S S')` are the fibre
product of `Y ⟶ X ⟵ X ×_S S'`. -/
theorem isPullback_baseChangeMorphism :
    IsPullback (pullback.fst (f ≫ sX) B.g) (baseChangeMorphism B sX f) f
      (pullback.fst sX B.g) := by
  set e := pullbackRightPullbackFstIso sX B.g f with he
  have hfst : e.hom ≫ pullback.fst (f ≫ sX) B.g = pullback.fst f (pullback.fst sX B.g) := by
    simp [he]
  have hsnd : e.hom ≫ baseChangeMorphism B sX f = pullback.snd f (pullback.fst sX B.g) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, baseChangeMorphism_comp_fst, ← Category.assoc, hfst]
      exact pullback.condition
    · rw [Category.assoc, baseChangeMorphism_comp_snd]
      simp [he]
  exact (IsPullback.of_hasPullback f (pullback.fst sX B.g)).of_iso e (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (by simp [hfst]) (by simp [hsnd]) (by simp) (by simp)

/-- **Stacks Project, Tag 0FVL, properness of the base change.** In a flat base change of Chow
situations, the morphism `f' : Y ×_S S' ⟶ X ×_S S'` induced by a proper morphism `f : Y ⟶ X` is
proper, because it is a base change of `f` and properness is stable under base change. -/
@[stacks 0FVL "properness of the base change"]
theorem isProper_baseChangeMorphism [IsProper f] : IsProper (baseChangeMorphism B sX f) :=
  IsProper.isStableUnderBaseChange.of_isPullback (isPullback_baseChangeMorphism B sX f)
    inferInstance


/-! ### The cycle square of Stacks 0FVL -/

/-- The cycle square for the cycle of a closed subscheme `Z ⊆ Y` of delta-dimension at most `k`.

The two routes around the square are compared through cycles of coherent sheaves. Going up and
then across, `g^*[Z]_k = [Z']_{k+c}` by Stacks 0FVI and `f'_*[Z']_{k+c} = [f'_* 𝒪_{Z'}]_{k+c}` by
Stacks 02R6; going across and then up, `f_*[Z]_k = [f_* 𝒪_Z]_k` by Stacks 02R6 and
`g^*[f_* 𝒪_Z]_k = [g^*f_* 𝒪_Z]_{k+c}` by Stacks 0FVI. The two coherent sheaves so reached agree:
`g^* f_* 𝒪_Z` is `f'_* g^* 𝒪_Z` by flat base change for direct images in degree zero, and
`g^* 𝒪_Z` is `𝒪_{Z'}`. -/
private theorem properPushforward_baseChangeCyclePullback_closedSubscheme
    {Z : Scheme.{u}} [LocallyOfFiniteType sX] [IsProper f] (i : Z ⟶ Y) [IsClosedImmersion i]
    (k : ℤ) (hZ : schemeDeltaDimension B.base (i ≫ f ≫ sX) ≤ (k : EInt))
    (hcoh : ∀ {W V : Scheme.{u}} (p : W ⟶ V) [IsProper p] [IsLocallyNoetherian V]
      (G : W.Modules) [G.IsCoherent], ((Scheme.Modules.pushforward p).obj G).IsCoherent) :
    letI : IsProper (baseChangeMorphism B sX f) := isProper_baseChangeMorphism B sX f
    properPushforward B.baseChange (pullback.snd (f ≫ sX) B.g) (pullback.snd sX B.g)
        (baseChangeMorphism B sX f) (baseChangeMorphism_comp_snd B sX f) (k + B.c)
        (baseChangeCyclePullback B (f ≫ sX) k
          (cycleAssociatedToClosedSubscheme B.base (f ≫ sX) i k)) =
      baseChangeCyclePullback B sX k
        (properPushforward B.base (f ≫ sX) sX f rfl k
          (cycleAssociatedToClosedSubscheme B.base (f ≫ sX) i k)) := by
  let _ : IsProper (baseChangeMorphism B sX f) := isProper_baseChangeMorphism B sX f
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  let _ : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  let _ : IsLocallyNoetherian (pullback sX B.g : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd sX B.g)
  let _ : IsLocallyNoetherian (pullback (f ≫ sX) B.g : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd (f ≫ sX) B.g)
  set pX := pullback.fst sX B.g with hpX
  set pY := pullback.fst (f ≫ sX) B.g with hpY
  set f' := baseChangeMorphism B sX f with hf'def
  set i' := pullback.snd i pY with hi'
  -- the coherent sheaf `f_* 𝒪_Z` on `X` and its counterpart `f'_* 𝒪_{Z'}` on `X'`
  set F : Y.Modules := (Scheme.Modules.pushforward i).obj (Ample.unitModule Z) with hF
  set G : X.Modules := (Scheme.Modules.pushforward f).obj F with hG
  let _ : G.IsCoherent := hcoh f F
  set F' : (pullback (f ≫ sX) B.g : Scheme.{u}).Modules :=
    (Scheme.Modules.pushforward i').obj (Ample.unitModule (pullback i pY : Scheme.{u})) with hF'
  set G' : (pullback sX B.g : Scheme.{u}).Modules :=
    (Scheme.Modules.pushforward f').obj F' with hG'
  let _ : G'.IsCoherent := hcoh f' F'
  let _ : ((Scheme.Modules.pullback pX).obj G).IsCoherent :=
    AlgebraicGeometry.isCoherent_pullback pX G
  -- the dimension bounds making every cycle below well formed
  have hZ' : schemeDeltaDimension B.baseChange (i' ≫ pullback.snd (f ≫ sX) B.g) ≤
      ((k + B.c : ℤ) : EInt) :=
    schemeDeltaDimension_baseChange_closedSubscheme_le B (f ≫ sX) i hZ
  have hFk : schemeDeltaDimension B.base ((reducedSupport F).subschemeι ≫ (f ≫ sX)) ≤
      (k : EInt) :=
    schemeDeltaDimension_reducedSupport_pushforwardStructureSheaf_le B.base (f ≫ sX) i hZ
  have hGk : schemeDeltaDimension B.base ((reducedSupport G).subschemeι ≫ sX) ≤ (k : EInt) :=
    schemeDeltaDimension_reducedSupport_pushforward_le B.base (f ≫ sX) sX f rfl F hFk
  have hF'k : schemeDeltaDimension B.baseChange
      ((reducedSupport F').subschemeι ≫ pullback.snd (f ≫ sX) B.g) ≤ ((k + B.c : ℤ) : EInt) :=
    schemeDeltaDimension_reducedSupport_pushforwardStructureSheaf_le B.baseChange
      (pullback.snd (f ≫ sX) B.g) i' hZ'
  have hG'k : schemeDeltaDimension B.baseChange
      ((reducedSupport G').subschemeι ≫ pullback.snd sX B.g) ≤ ((k + B.c : ℤ) : EInt) :=
    schemeDeltaDimension_reducedSupport_pushforward_le B.baseChange
      (pullback.snd (f ≫ sX) B.g) (pullback.snd sX B.g) f'
      (baseChangeMorphism_comp_snd B sX f) F' hF'k
  have hpullGk : schemeDeltaDimension B.baseChange
      ((reducedSupport ((Scheme.Modules.pullback pX).obj G)).subschemeι ≫
        pullback.snd sX B.g) ≤ ((k + B.c : ℤ) : EInt) :=
    schemeDeltaDimension_baseChange_support_le B sX G hGk
  -- the flat base change of `f_* 𝒪_Z` is `f'_* 𝒪_{Z'}`
  let _ : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have hbc : IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
      (isPullback_baseChangeMorphism B sX f).w).app F) :=
    Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat
      (isPullback_baseChangeMorphism B sX f) F
  have e : (Scheme.Modules.pullback pX).obj G ≅ G' :=
    asIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
        (isPullback_baseChangeMorphism B sX f).w).app F) ≪≫
      (Scheme.Modules.pushforward f').mapIso (pullbackPushforwardStructureSheafIso_of_flat pY i)
  -- the four identifications, and the comparison of the two coherent sheaves
  have hup : baseChangeCyclePullback B (f ≫ sX) k
      (cycleAssociatedToClosedSubscheme B.base (f ≫ sX) i k) =
        cycleAssociatedToClosedSubscheme B.baseChange (pullback.snd (f ≫ sX) B.g) i'
          (k + B.c) :=
    baseChangeCyclePullback_cycleAssociatedToClosedSubscheme B (f ≫ sX) i k hZ
  have hacross' : properPushforward B.baseChange (pullback.snd (f ≫ sX) B.g)
        (pullback.snd sX B.g) f' (baseChangeMorphism_comp_snd B sX f) (k + B.c)
        (cycleAssociatedToClosedSubscheme B.baseChange (pullback.snd (f ≫ sX) B.g) i'
          (k + B.c)) =
      cycleAssociatedToCoherentSheaf B.baseChange (pullback.snd sX B.g) G' (k + B.c) hG'k :=
    properPushforward_cycleAssociatedToClosedSubscheme B.baseChange
      (pullback.snd (f ≫ sX) B.g) (pullback.snd sX B.g) f'
      (baseChangeMorphism_comp_snd B sX f) i' (k + B.c) hZ'
  have hacross : properPushforward B.base (f ≫ sX) sX f rfl k
        (cycleAssociatedToClosedSubscheme B.base (f ≫ sX) i k) =
      cycleAssociatedToCoherentSheaf B.base sX G k hGk :=
    properPushforward_cycleAssociatedToClosedSubscheme B.base (f ≫ sX) sX f rfl i k hZ
  have hup' : baseChangeCyclePullback B sX k
        (cycleAssociatedToCoherentSheaf B.base sX G k hGk) =
      cycleAssociatedToCoherentSheaf B.baseChange (pullback.snd sX B.g)
        ((Scheme.Modules.pullback pX).obj G) (k + B.c) hpullGk :=
    baseChangeCyclePullback_cycleAssociatedToCoherentSheaf B sX G k hGk
  calc properPushforward B.baseChange (pullback.snd (f ≫ sX) B.g) (pullback.snd sX B.g) f'
        (baseChangeMorphism_comp_snd B sX f) (k + B.c)
        (baseChangeCyclePullback B (f ≫ sX) k
          (cycleAssociatedToClosedSubscheme B.base (f ≫ sX) i k))
      = cycleAssociatedToCoherentSheaf B.baseChange (pullback.snd sX B.g) G' (k + B.c) hG'k := by
        rw [hup]; exact hacross'
    _ = cycleAssociatedToCoherentSheaf B.baseChange (pullback.snd sX B.g)
          ((Scheme.Modules.pullback pX).obj G) (k + B.c) hpullGk :=
        cycleAssociatedToCoherentSheaf_eq_of_iso' B.baseChange (pullback.snd sX B.g) G'
          ((Scheme.Modules.pullback pX).obj G) (k + B.c) hG'k hpullGk e.symm
    _ = baseChangeCyclePullback B sX k
          (properPushforward B.base (f ≫ sX) sX f rfl k
            (cycleAssociatedToClosedSubscheme B.base (f ≫ sX) i k)) := by
        rw [hacross]; exact hup'.symm

/-- The fundamental cycle of the reduced closure of a point `y` of relative dimension `k` takes
the value one at `y`. -/
private theorem cycleAssociatedToIntegralComponentAt_self (C : ChowSituation.{u})
    {W : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (k : ℤ) (y : W)
    (hy : relativeDimension C.dimensionFunction sW y = k) :
    (cycleAssociatedToClosedSubscheme C sW (integralComponentAt y).subschemeι k).1 y = 1 := by
  have hdim : schemeDeltaDimension C ((integralComponentAt y).subschemeι ≫ sW) = (k : EInt) := by
    rw [schemeDeltaDimension_integralComponentAt C sW y, hy]
  have h := cycleAssociatedToClosedSubscheme_integral_apply C sW (integralComponentAt y)
    (isIntegral_integralComponentAt y) hdim
  rwa [genericPointOf_integralComponentAt] at h

/-- The fundamental cycle of the reduced closure of a point `y` vanishes away from `y`: an
integral scheme has exactly one generic point. -/
private theorem cycleAssociatedToIntegralComponentAt_of_ne (C : ChowSituation.{u})
    {W : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (k : ℤ) (y : W) {w : W}
    (hw : w ≠ y) :
    (cycleAssociatedToClosedSubscheme C sW (integralComponentAt y).subschemeι k).1 w = 0 :=
  cycleAssociatedToClosedSubscheme_integral_apply_of_ne C sW (integralComponentAt y)
    (isIntegral_integralComponentAt y) k (by rwa [genericPointOf_integralComponentAt])

/-- The cycle square for the prime cycle of a point of relative dimension `k`: the reduced
closure of such a point is a closed subscheme of delta-dimension `k`. -/
private theorem properPushforward_baseChangeCyclePullback_point
    [LocallyOfFiniteType sX] [IsProper f] (k : ℤ) (y : Y)
    (hy : relativeDimension B.base.dimensionFunction (f ≫ sX) y = k)
    (hcoh : ∀ {W V : Scheme.{u}} (p : W ⟶ V) [IsProper p] [IsLocallyNoetherian V]
      (G : W.Modules) [G.IsCoherent], ((Scheme.Modules.pushforward p).obj G).IsCoherent) :
    letI : IsProper (baseChangeMorphism B sX f) := isProper_baseChangeMorphism B sX f
    properPushforward B.baseChange (pullback.snd (f ≫ sX) B.g) (pullback.snd sX B.g)
        (baseChangeMorphism B sX f) (baseChangeMorphism_comp_snd B sX f) (k + B.c)
        (baseChangeCyclePullback B (f ≫ sX) k
          (cycleAssociatedToClosedSubscheme B.base (f ≫ sX)
            (integralComponentAt y).subschemeι k)) =
      baseChangeCyclePullback B sX k
        (properPushforward B.base (f ≫ sX) sX f rfl k
          (cycleAssociatedToClosedSubscheme B.base (f ≫ sX)
            (integralComponentAt y).subschemeι k)) :=
  properPushforward_baseChangeCyclePullback_closedSubscheme B sX f
    (integralComponentAt y).subschemeι k
    (le_of_eq (by rw [schemeDeltaDimension_integralComponentAt B.base (f ≫ sX) y, hy])) hcoh

/-- **Stacks Project, Tag 0FVL, the cycle square.** In a flat base change of Chow situations,
proper pushforward commutes with the base-change map on cycle groups: for `f : Y ⟶ X` proper
over the base `S`, the square whose horizontal maps are `g^* : Z_k(Y) ⟶ Z_{k+c}(Y')` and
`g^* : Z_k(X) ⟶ Z_{k+c}(X')` and whose vertical maps are `f_*` and `f'_*` commutes.

Both routes are additive, and a cycle agrees, on the part of its support lying over a single
point `x` of `X'`, with a finite sum of prime cycles: that part is the intersection of the
support with the fibre of the proper morphism `f` over the image of `x`, hence finite, and both
routes read the coefficient at `x` only off that part. So it suffices to treat a prime cycle,
which is the fundamental cycle of the reduced closure of a point and so is covered by the case
of a closed subscheme.

Coherence of the direct image of a coherent module under a proper morphism to a locally
Noetherian scheme is `Stacks.Chow.forall_properDirectImageIsCoherent`, the first assertion of
Stacks 02O5. -/
@[stacks 0FVL "the cycle square"]
theorem properPushforward_baseChangeCyclePullback
    [LocallyOfFiniteType sX] [IsProper f] (k : ℤ)
    (z : CycleGroup B.base (f ≫ sX) k) :
    letI : IsProper (baseChangeMorphism B sX f) := isProper_baseChangeMorphism B sX f
    properPushforward B.baseChange (pullback.snd (f ≫ sX) B.g) (pullback.snd sX B.g)
        (baseChangeMorphism B sX f) (baseChangeMorphism_comp_snd B sX f) (k + B.c)
        (baseChangeCyclePullback B (f ≫ sX) k z) =
      baseChangeCyclePullback B sX k (properPushforward B.base (f ≫ sX) sX f rfl k z) := by
  classical
  let _ : IsProper (baseChangeMorphism B sX f) := isProper_baseChangeMorphism B sX f
  -- the two routes around the square, as homomorphisms of cycle groups
  let P := properPushforwardHom B.base (f ≫ sX) sX f rfl k
  let P' := properPushforwardHom B.baseChange (pullback.snd (f ≫ sX) B.g)
    (pullback.snd sX B.g) (baseChangeMorphism B sX f) (baseChangeMorphism_comp_snd B sX f)
    (k + B.c)
  let L := (baseChangeCyclePullback B sX k).comp P
  let R := P'.comp (baseChangeCyclePullback B (f ≫ sX) k)
  change R z = L z
  refine Eq.symm (Subtype.ext (Function.locallyFinsuppWithin.ext fun x => ?_))
  -- the part of the support of `z` lying over the image of `x`
  set J : Set Y := f.base ⁻¹' {(pullback.fst sX B.g).base x} ∩ z.1.support with hJ
  have hJfin : J.Finite := by
    simpa [hJ, Set.inter_comm] using
      (z.1.locallyFiniteSupport.finite_inter_support_of_isCompact
        (f.isProperMap.isCompact_preimage isCompact_singleton))
  let _ : Fintype J := hJfin.fintype
  set pointTerm : J → CycleGroup B.base (f ≫ sX) k := fun a =>
    cycleAssociatedToClosedSubscheme B.base (f ≫ sX) (integralComponentAt a.1).subschemeι k
    with hpointTerm
  set β : CycleGroup B.base (f ≫ sX) k := ∑ a ∈ Finset.univ, (z.1 a.1) • pointTerm a with hβdef
  have hrel : ∀ a : J, relativeDimension B.base.dimensionFunction (f ≫ sX) a.1 = k := fun a =>
    (mem_cyclesOfDimension_iff_forall_point B.base (f ≫ sX) k z.1).mp z.2 a.1 a.2.2
  have hself : ∀ a : J, (pointTerm a).1 a.1 = 1 := fun a =>
    cycleAssociatedToIntegralComponentAt_self B.base (f ≫ sX) k a.1 (hrel a)
  have hne : ∀ (a : J) (w : Y), w ≠ a.1 → (pointTerm a).1 w = 0 := fun a w hw =>
    cycleAssociatedToIntegralComponentAt_of_ne B.base (f ≫ sX) k a.1 hw
  -- `β` agrees with `z` over the image of `x`
  have hβeval : ∀ w : Y, f.base w = (pullback.fst sX B.g).base x → β.1 w = z.1 w := by
    intro w hw
    let evalAt : CycleGroup B.base (f ≫ sX) k →+ ℤ :=
      { toFun := fun c => c.1 w
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hsum : evalAt β = ∑ a ∈ Finset.univ, z.1 a.1 * (pointTerm a).1 w := by
      rw [hβdef, map_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [map_zsmul]; rfl
    change evalAt β = z.1 w
    rw [hsum]
    by_cases hz : z.1 w = 0
    · refine (Finset.sum_eq_zero fun a _ => ?_).trans hz.symm
      rcases eq_or_ne w (a.1 : Y) with rfl | hwa
      · exact absurd hz a.2.2
      · rw [hne a w hwa, mul_zero]
    · refine (Finset.sum_eq_single (⟨w, hw, hz⟩ : J) (fun a _ hane => ?_) (fun h => ?_)).trans ?_
      · rw [hne a w (fun hwa => hane (Subtype.ext hwa.symm)), mul_zero]
      · exact absurd (Finset.mem_univ (⟨w, hw, hz⟩ : J)) h
      · rw [hself ⟨w, hw, hz⟩, mul_one]
  -- the two routes agree on `β`, since they agree on each prime cycle
  have hβ : L β = R β := by
    rw [hβdef, map_sum, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_zsmul, map_zsmul]
    exact congrArg (fun c => (z.1 a.1) • c)
      (properPushforward_baseChangeCyclePullback_point B sX f k a.1 (hrel a)
        forall_properDirectImageIsCoherent).symm
  -- both routes read the coefficient at `x` only off the part of the support over its image
  have hL : (L z).1 x = (L β).1 x := by
    simp only [L, P, AddMonoidHom.comp_apply, properPushforwardHom_apply]
    rw [baseChangeCyclePullback_apply, baseChangeCyclePullback_apply]
    refine congrArg (fun m : ℤ => m * _) ?_
    rw [properPushforward_apply, properPushforward_apply]
    refine finsum_congr fun w => finsum_congr fun hw => ?_
    rw [hβeval w (by simpa using hw)]
  have hR : (R z).1 x = (R β).1 x := by
    simp only [R, P', AddMonoidHom.comp_apply, properPushforwardHom_apply]
    rw [properPushforward_apply, properPushforward_apply]
    refine finsum_congr fun w => finsum_congr fun hw => ?_
    have hfw : (baseChangeMorphism B sX f).base w = x := by simpa using hw
    have hcomm : f.base ((pullback.fst (f ≫ sX) B.g).base w) =
        (pullback.fst sX B.g).base ((baseChangeMorphism B sX f).base w) := by
      simpa only [Scheme.Hom.comp_apply] using
        congrArg (fun m : (pullback (f ≫ sX) B.g : Scheme.{u}) ⟶ X => m.base w)
          (isPullback_baseChangeMorphism B sX f).w
    rw [baseChangeCyclePullback_apply, baseChangeCyclePullback_apply,
      hβeval _ (hcomm.trans (congrArg (pullback.fst sX B.g).base hfw))]
  rw [hL, hR, hβ]

/-! ### The Chow square of Stacks 0FVL -/

/-- **Stacks Project, Tag 0FVL, the Chow square.** In a flat base change of Chow situations,
proper pushforward commutes with the base-change map on Chow groups: for `f : Y ⟶ X` proper over
the base `S`, the square whose horizontal maps are `g^* : CH_k(Y) ⟶ CH_{k+c}(Y')` and
`g^* : CH_k(X) ⟶ CH_{k+c}(X')` and whose vertical maps are `f_*` and `f'_*` commutes.

Every class is the class of a cycle, and on classes of cycles both routes are the class of the
corresponding route on cycles, so this follows from the cycle square.

The base-change map on Chow groups is a parameter `gChow` of this statement rather than a fixed
map, constrained by `hgChow` to be induced by the base-change map on cycle groups. This is a
generality, not an assumption: quantifying over every such map is stronger than the source's
statement, and the map itself exists, so
`Stacks.Chow.properChowPushforward_baseChangeChowPullback_of_baseChangeChowPullback` below
instantiates this at the base-change map of Stacks 0FVJ and is unconditional. Coherence of the
direct image of a
coherent module under a proper morphism to a locally Noetherian scheme is
`Stacks.Chow.forall_properDirectImageIsCoherent`, the first assertion of Stacks 02O5. -/
@[stacks 0FVL "the Chow square, in the generality of every Chow base-change map induced by the \
cycle-level one of Tag 0FVJ; instantiated at that map, with nothing left to supply, by \
properChowPushforward_baseChangeChowPullback_of_baseChangeChowPullback below"]
theorem properChowPushforward_baseChangeChowPullback
    [LocallyOfFiniteType sX] [IsProper f] (k : ℤ)
    (gChow : ∀ {W : Scheme.{u}} (sW : W ⟶ B.base.S) [LocallyOfFiniteType sW] (j : ℤ),
      chowGroup B.base sW j →+ chowGroup B.baseChange (pullback.snd sW B.g) (j + B.c))
    (hgChow : ∀ {W : Scheme.{u}} (sW : W ⟶ B.base.S) [LocallyOfFiniteType sW] (j : ℤ)
      (a : CycleGroup B.base sW j),
      gChow sW j (QuotientAddGroup.mk' (rationalEquivalences B.base sW j) a) =
        QuotientAddGroup.mk' (rationalEquivalences B.baseChange (pullback.snd sW B.g) (j + B.c))
          (baseChangeCyclePullback B sW j a))
    (w : chowGroup B.base (f ≫ sX) k) :
    letI : IsProper (baseChangeMorphism B sX f) := isProper_baseChangeMorphism B sX f
    properChowPushforward B.baseChange (pullback.snd (f ≫ sX) B.g) (pullback.snd sX B.g)
        (baseChangeMorphism B sX f) (baseChangeMorphism_comp_snd B sX f) (k + B.c)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper B.baseChange
          (pullback.snd (f ≫ sX) B.g) (pullback.snd sX B.g) (baseChangeMorphism B sX f)
          (baseChangeMorphism_comp_snd B sX f) (k + B.c))
        (gChow (f ≫ sX) k w) =
      gChow sX k (properChowPushforward B.base (f ≫ sX) sX f rfl k
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper B.base (f ≫ sX) sX f rfl
          k) w) := by
  let _ : IsProper (baseChangeMorphism B sX f) := isProper_baseChangeMorphism B sX f
  induction w using QuotientAddGroup.induction_on with
  | H a =>
    rw [show (QuotientAddGroup.mk a : chowGroup B.base (f ≫ sX) k) =
          QuotientAddGroup.mk' (rationalEquivalences B.base (f ≫ sX) k) a from rfl,
      hgChow (f ≫ sX) k a, properChowPushforward_mk, properChowPushforward_mk, hgChow sX k]
    exact congrArg (QuotientAddGroup.mk' _)
      (properPushforward_baseChangeCyclePullback B sX f k a)

/-- **Stacks Project, Tag 0FVL, the Chow square for the base-change map of Stacks 0FVJ.** In a
flat base change of Chow situations, proper pushforward commutes with the base-change map
`g^* : CH_k(X) ⟶ CH_{k+c}(X ×_S S')` of Stacks 0FVJ: for `f : Y ⟶ X` proper over the base `S`,
the square whose horizontal maps are those base-change maps for `Y` and for `X` and whose
vertical maps are `f_*` and `f'_*` commutes.

This is the Chow square with its Chow base-change map supplied rather than assumed: the map is
`Stacks.Chow.baseChangeChowPullback`, and it meets the characterization of the general statement
because `Stacks.Chow.baseChangeChowPullback_mk` says it sends the class of a cycle to the class
of the base change of that cycle. Coherence of the direct image of a coherent module under a
proper morphism to a locally Noetherian scheme is
`Stacks.Chow.forall_properDirectImageIsCoherent`, the first assertion of Stacks 02O5. -/
@[stacks 0FVL "the Chow square for the base-change map of Tag 0FVJ"]
theorem properChowPushforward_baseChangeChowPullback_of_baseChangeChowPullback
    [LocallyOfFiniteType sX] [IsProper f] (k : ℤ)
    (w : chowGroup B.base (f ≫ sX) k) :
    letI : IsProper (baseChangeMorphism B sX f) := isProper_baseChangeMorphism B sX f
    properChowPushforward B.baseChange (pullback.snd (f ≫ sX) B.g) (pullback.snd sX B.g)
        (baseChangeMorphism B sX f) (baseChangeMorphism_comp_snd B sX f) (k + B.c)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper B.baseChange
          (pullback.snd (f ≫ sX) B.g) (pullback.snd sX B.g) (baseChangeMorphism B sX f)
          (baseChangeMorphism_comp_snd B sX f) (k + B.c))
        (baseChangeChowPullback B (f ≫ sX) k w) =
      baseChangeChowPullback B sX k (properChowPushforward B.base (f ≫ sX) sX f rfl k
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper B.base (f ≫ sX) sX f rfl
          k) w) :=
  properChowPushforward_baseChangeChowPullback B sX f k
    (fun sW _ j ↦ baseChangeChowPullback B sW j)
    (fun sW _ j a ↦ baseChangeChowPullback_mk B sW j a) w

end Stacks.Chow

end
