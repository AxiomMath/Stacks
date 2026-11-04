module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeExtension
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreDifferencePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CapClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.HilbertCycleClass
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleComposition
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCoherentImage.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Composing the families of cycles attached to two closed subschemes

Let `X --f--> Y --g--> S` be morphisms of schemes, both locally of finite type, let `r, e ≥ 0`,
let `Z ⊆ X` be a closed subscheme whose scheme-theoretic fibres over `Y` have dimension at most
`r` and let `W ⊆ Y` be a closed subscheme whose scheme-theoretic fibres over `S` have dimension
at most `e`. This file proves that when `Z` is flat over `Y` the composition
`[Z/X/Y]_r ∘ [W/Y/S]_e` of the two associated families of cycles on fibres is the family
`[Z ×_Y W/X/S]_{r + e}` of the closed subscheme `Z ×_Y W ⊆ X`.

This is the case `F = 𝒪_Z`, `G = 𝒪_W` of the same statement for modules: the family `[Z/X/Y]_r`
of Example 0H4S is the family `[i_* 𝒪_Z/X/Y]_r` of Example 0H4Q, flatness of `Z` over `Y` is
flatness of `i_* 𝒪_Z` over `Y`, and the projection formula together with base change identifies
`i_* 𝒪_Z ⊗_{𝒪_X} f^* j_* 𝒪_W` with the structure sheaf of `Z ×_Y W` pushed forward to `X`.

## Main results

* `Stacks.Chow.isFiniteType_pushforwardStructureSheaf` — `i_* 𝒪_Z` is of finite type.
* `Stacks.Chow.familyAssociatedToModule_eq_of_iso` — isomorphic modules have the same associated
  family of cycles on fibres.
* `Stacks.Chow.familyAssociatedToClosedSubscheme_eq_familyAssociatedToModule` —
  `[Z/X/S]_r = [i_* 𝒪_Z/X/S]_r` over an arbitrary base scheme `S`.
* `Stacks.Chow.fibreDim_pullbackClosedSubschemes_le` — the fibres of `Z ×_Y W` over `S` have
  dimension at most `r + e`, so the right-hand side of the main result is the family of a closed
  subscheme of the expected relative dimension.
* `Stacks.Chow.compFamily_familyAssociatedToClosedSubscheme` — Stacks 0H6M, the equality of
  families.
* `Stacks.Chow.familyAssociatedToClosedSubscheme_eq_of_iso` — isomorphic closed subschemes of `X`
  have the same associated family of cycles on the fibres of `X/S`.
* `Stacks.Chow.compFamily_familyAssociatedToSelf` — Stacks 0H6S, the case `Z = X` and `W = Y` of
  the equality of families, for `f` and `g` flat of relative dimension `r` resp. `e`.

## Implementation notes

The dimension hypotheses are the ones of Example 0H4S: `dim (Z_y) ≤ r` for every point `y` of
`Y` and `dim (W_s) ≤ e` for every point `s` of `S`, where `Z_y = Z ×_X X_y` and `W_s = W ×_Y Y_s`.
These are the bounds under which the two families are defined at all, and they say that `Z ⟶ Y`
and `W ⟶ S` have relative dimension at most `r` resp. `e` in the sense of Definition 02NJ, the
dimension of a space being the supremum of its local dimensions.

The base of a family of cycles on fibres is an arbitrary scheme, so `i_* 𝒪_Z` cannot be assumed
coherent and its finiteness properties are obtained directly: it is quasi-coherent because a
closed immersion is affine, and of finite type because `𝒪_X ⟶ i_* 𝒪_Z` is an epimorphism and
`𝒪_X` is of finite type over itself. Only on the fibres, which are locally of finite type over a
residue field and hence locally Noetherian, is coherence used.

The bound on the fibres of `Z ×_Y W` over `S` is read off the module statement: the support of
`i_* 𝒪_{Z ×_Y W}` is the image of `Z ×_Y W`, that image is homeomorphic to `Z ×_Y W` because a
closed immersion is a homeomorphism onto its image, and restriction to a fibre commutes with
both operations.

## References

* [Stacks Project, Tag 02QY](https://stacks.math.columbia.edu/tag/02QY)
* [Stacks Project, Tag 0H4Q](https://stacks.math.columbia.edu/tag/0H4Q)
* [Stacks Project, Tag 0H4S](https://stacks.math.columbia.edu/tag/0H4S)
* [Stacks Project, Tag 0H6L](https://stacks.math.columbia.edu/tag/0H6L)
* [Stacks Project, Tag 0H6M](https://stacks.math.columbia.edu/tag/0H6M)
* [Stacks Project, Tag 0H6S](https://stacks.math.columbia.edu/tag/0H6S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Finiteness of the structure sheaf of a closed subscheme -/

/-- **`i_* 𝒪_Z` is of finite type.** The canonical map `𝒪_X ⟶ i_* 𝒪_Z` is an epimorphism for a
closed immersion `i : Z ⟶ X`, and `𝒪_X` is of finite type over itself. Registered as an instance
because `AlgebraicGeometry.Scheme.Modules` is a `def`, through which instance search does not
unfold the pushforward of the monoidal unit. -/
instance isFiniteType_pushforwardStructureSheaf {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z)).IsFiniteType :=
  have : Epi (AlgebraicGeometry.ClosedImmersionCoherentImage.unitToPushforwardUnit i) :=
    AlgebraicGeometry.ClosedImmersionCoherentImage.epi_unitToPushforwardUnit i
  Stacks.SheafOfModules.isFiniteType_of_epi
    (M := SheafOfModules.unit X.ringCatSheaf)
    (N := (Scheme.Modules.pushforward i).obj (Ample.unitModule Z))
    (AlgebraicGeometry.ClosedImmersionCoherentImage.unitToPushforwardUnit i) inferInstance

/-! ### Families of cycles attached to isomorphic modules -/

/-- Isomorphic quasi-coherent modules of finite type have the same associated family of cycles on
fibres: on each fibre the two restrictions are isomorphic coherent modules, so their cycles
agree. -/
theorem familyAssociatedToModule_eq_of_iso {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {M N : X.Modules} [M.IsFiniteType] [M.IsQuasicoherent]
    [N.IsFiniteType] [N.IsQuasicoherent] (eMN : M ≅ N) (r : ℕ)
    (hM : ∀ s : S, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj M)) ≤ (r : WithBot ℕ∞))
    (hN : ∀ s : S, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj N)) ≤ (r : WithBot ℕ∞)) :
    familyAssociatedToModule f M r hM = familyAssociatedToModule f N r hN := by
  funext s
  have : IsLocallyNoetherian (f.fiber s) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)
  rw [familyAssociatedToModule_apply, familyAssociatedToModule_apply]
  exact cycleAssociatedToCoherentSheaf_eq_of_iso _ _
    ((Scheme.Modules.pullback (f.fiberι s)).mapIso eMN) _ _ _

/-- **`[Z/X/S]_r = [i_* 𝒪_Z/X/S]_r`.** The family of cycles on the fibres of `X/S` attached to a
closed subscheme `i : Z ⟶ X` by Example 0H4S is the family attached to the coherent module
`i_* 𝒪_Z` by Example 0H4Q, for an arbitrary base scheme `S`. On the fibre over `s` this is
Stacks 02QY together with the base change identifying the restriction of `i_* 𝒪_Z` with the
direct image of `𝒪_{Z_s}`. -/
theorem familyAssociatedToClosedSubscheme_eq_familyAssociatedToModule {X S Z : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (i : Z ⟶ X) [IsClosedImmersion i] (r : ℕ)
    (hZ : ∀ s : S,
      topologicalKrullDim (pullback i (f.fiberι s) : Scheme.{u}) ≤ (r : WithBot ℕ∞)) :
    familyAssociatedToClosedSubscheme f i r =
      familyAssociatedToModule f ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z)) r
        (topologicalKrullDim_supp_pullback_fiberι_le i f hZ) := by
  funext s
  have : IsLocallyNoetherian (f.fiber s) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)
  rw [familyAssociatedToClosedSubscheme_apply, familyAssociatedToModule_apply,
    cycleAssociatedToClosedSubscheme_eq_cycleAssociatedToCoherentSheaf
      (fieldChowSituation (S.residueField s)) (f.fiberToSpecResidueField s)
      (fiberClosedImmersion f i s) (r : ℤ)
      (fiberClosedSubscheme_schemeDeltaDimension_le f i r hZ s)]
  exact (cycleAssociatedToCoherentSheaf_eq_of_iso _ _
    (pullbackPushforwardStructureSheafIso (IsPullback.of_hasPullback i (f.fiberι s))) _ _ _).symm

/-! ### The dimension of the fibres of the fibre product -/

/-- The fibres of `Z ×_Y W` over `S` have dimension at most `r + e`, so `[Z ×_Y W/X/S]_{r + e}`
is the family of a closed subscheme of `X` of relative dimension at most `r + e` over `S`. The
image of `(Z ×_Y W)_s` in the fibre `X_s` is the support there of
`i_* 𝒪_Z ⊗_{𝒪_X} f^* j_* 𝒪_W`, which is bounded by `r + e`. Flatness of `Z` over `Y` is not
used. -/
theorem fibreDim_pullbackClosedSubschemes_le {X Y S Z W : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (g : Y ⟶ S) [LocallyOfFiniteType g] (r e : ℕ) (i : Z ⟶ X)
    [IsClosedImmersion i]
    (hZ : ∀ y : Y, topologicalKrullDim (pullback i (f.fiberι y) : Scheme.{u}) ≤ (r : WithBot ℕ∞))
    (j : W ⟶ Y) [IsClosedImmersion j]
    (hW : ∀ t : S, topologicalKrullDim (pullback j (g.fiberι t) : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    (t : S) :
    topologicalKrullDim
        (pullback (pullback.fst (i ≫ f) j ≫ i) ((f ≫ g).fiberι t) : Scheme.{u}) ≤
      ((r + e : ℕ) : WithBot ℕ∞) := by
  have hdim : topologicalKrullDim
      (pullback (pullback.fst (i ≫ f) j ≫ i) ((f ≫ g).fiberι t) : Scheme.{u}) =
      topologicalKrullDim (SheafOfModules.supp
        ((Scheme.Modules.pullback ((f ≫ g).fiberι t)).obj
          ((Scheme.Modules.pushforward (pullback.fst (i ≫ f) j ≫ i)).obj
            (Ample.unitModule (pullback (i ≫ f) j))))) := by
    rw [supp_pullback_fiberι_pushforwardStructureSheaf
      (pullback.fst (i ≫ f) j ≫ i) (f ≫ g) t]
    exact IsHomeomorph.topologicalKrullDim_eq _
      (IsClosedImmersion.isClosedEmbedding (pullback.snd (pullback.fst (i ≫ f) j ≫ i)
        ((f ≫ g).fiberι t))).isEmbedding.toHomeomorph.isHomeomorph
  rw [hdim, ← SheafOfModules.supp_eq_of_iso ((Scheme.Modules.pullback ((f ≫ g).fiberι t)).mapIso
    (tensorPullbackStructureSheavesIso i f j))]
  exact fibreDim_tensorPullback_le f g r e _
    (topologicalKrullDim_supp_pullback_fiberι_le i f hZ) _
    (topologicalKrullDim_supp_pullback_fiberι_le j g hW) t

/-! ### Stacks 0H6M -/

/-- **Stacks Project, Tag 0H6M.** Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes, both
locally of finite type, and let `r, e ≥ 0`. Let `Z ⊆ X` be a closed subscheme of relative
dimension at most `r` over `Y`, so that the fibres `Z_y = Z ×_X X_y` have dimension at most `r`,
and let `W ⊆ Y` be a closed subscheme of relative dimension at most `e` over `S`. Set
`α = [Z/X/Y]_r` and `β = [W/Y/S]_e` (Example 0H4S). If `Z` is flat over `Y` then
`α ∘ β = [Z ×_Y W/X/S]_{r + e}`. -/
@[stacks 0H6M]
theorem compFamily_familyAssociatedToClosedSubscheme {X Y S Z W : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (g : Y ⟶ S) [LocallyOfFiniteType g] (r e : ℕ) (i : Z ⟶ X)
    [IsClosedImmersion i] [Flat (i ≫ f)]
    (hZ : ∀ y : Y, topologicalKrullDim (pullback i (f.fiberι y) : Scheme.{u}) ≤ (r : WithBot ℕ∞))
    (j : W ⟶ Y) [IsClosedImmersion j]
    (hW : ∀ t : S,
      topologicalKrullDim (pullback j (g.fiberι t) : Scheme.{u}) ≤ (e : WithBot ℕ∞)) :
    compFamily f g r e (familyAssociatedToClosedSubscheme f i r)
        (familyAssociatedToClosedSubscheme g j e) =
      familyAssociatedToClosedSubscheme (f ≫ g) (pullback.fst (i ≫ f) j ≫ i) (r + e) := by
  have hF := topologicalKrullDim_supp_pullback_fiberι_le i f hZ
  have hG := topologicalKrullDim_supp_pullback_fiberι_le j g hW
  rw [familyAssociatedToClosedSubscheme_eq_familyAssociatedToModule f i r hZ,
    familyAssociatedToClosedSubscheme_eq_familyAssociatedToModule g j e hW,
    compFamily_familyAssociatedToModule f g r e _ hF
      (isFlatOver_pushforwardStructureSheaf i f) _ hG,
    familyAssociatedToClosedSubscheme_eq_familyAssociatedToModule (f ≫ g)
      (pullback.fst (i ≫ f) j ≫ i) (r + e)
      (fibreDim_pullbackClosedSubschemes_le f g r e i hZ j hW)]
  exact familyAssociatedToModule_eq_of_iso (f ≫ g)
    (tensorPullbackStructureSheavesIso i f j) (r + e) _ _

/-! ### Stacks 0H6S -/

/-- A morphism all of whose nonempty fibres are equidimensional of dimension `d` has the fibres of
the closed subscheme `X ⊆ X` of dimension at most `d`: the fibre through a point is nonempty, hence
of dimension `d`, a local dimension is bounded by the dimension of the whole space, and the fibre
of `𝟙 X` is homeomorphic to the fibre of `f`. -/
private theorem topologicalKrullDim_pullback_id_fiberι_le {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (d : ℕ) (hf : AlgebraicGeometry.RelativeDimension f d) (s : S) :
    topologicalKrullDim (pullback (𝟙 X) (f.fiberι s) : Scheme.{u}) ≤ (d : WithBot ℕ∞) := by
  rw [IsHomeomorph.topologicalKrullDim_eq _
    (Scheme.Hom.homeomorph (pullback.snd (𝟙 X) (f.fiberι s))).isHomeomorph]
  exact topologicalKrullDim_fiber_le_of_relativeDimensionLE f
    (fun x => (topologicalKrullDimAt_le_topologicalKrullDim (f.asFiber x)).trans_eq
      (hf (f x) ⟨f.asFiber x⟩).2) s

/-- Isomorphic closed subschemes of `X` have the same associated family of cycles on the fibres
of `X/S`: on each fibre the two inverse images are isomorphic closed subschemes, so their cycles
agree. -/
theorem familyAssociatedToClosedSubscheme_eq_of_iso {X S Z Z' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ X)
    [IsClosedImmersion i'] (e : Z ≅ Z') (h : e.hom ≫ i' = i) (r : ℕ) :
    familyAssociatedToClosedSubscheme f i r = familyAssociatedToClosedSubscheme f i' r := by
  funext s
  rw [familyAssociatedToClosedSubscheme_apply, familyAssociatedToClosedSubscheme_apply]
  exact cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ _
    (asIso (pullback.map i (f.fiberι s) i' (f.fiberι s) e.hom (𝟙 _) (𝟙 _)
      (by simp [h]) (by simp)))
    ((pullback.lift_snd _ _ _).trans (Category.comp_id _)) _

/-- **Stacks Project, Tag 0H6S.** Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes, both
locally of finite type and flat, of relative dimension `r` resp. `e`. Then the composition
`[X/X/Y]_r ∘ [Y/Y/S]_e` of the families of cycles on fibres attached to the closed subschemes
`X ⊆ X` and `Y ⊆ Y` (Example 0H4S) is the family `[X/X/S]_{r + e}`. The equality is one of
families of cycles on fibres, so the local Noetherian hypothesis on `S`, needed only to speak of
the group `z(X/S, r + e)` containing them, is not used. -/
@[stacks 0H6S]
theorem compFamily_familyAssociatedToSelf {X Y S : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Flat f] (g : Y ⟶ S) [LocallyOfFiniteType g] [Flat g] (r e : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r)
    (hg : AlgebraicGeometry.RelativeDimension g e) :
    compFamily f g r e (familyAssociatedToClosedSubscheme f (𝟙 X) r)
        (familyAssociatedToClosedSubscheme g (𝟙 Y) e) =
      familyAssociatedToClosedSubscheme (f ≫ g) (𝟙 X) (r + e) := by
  have : Flat (𝟙 X ≫ f) := by rw [Category.id_comp]; infer_instance
  rw [compFamily_familyAssociatedToClosedSubscheme f g r e (𝟙 X)
    (topologicalKrullDim_pullback_id_fiberι_le f r hf) (𝟙 Y)
    (topologicalKrullDim_pullback_id_fiberι_le g e hg)]
  exact familyAssociatedToClosedSubscheme_eq_of_iso (f ≫ g)
    (pullback.fst (𝟙 X ≫ f) (𝟙 Y) ≫ 𝟙 X) (𝟙 X)
    (asIso (pullback.fst (𝟙 X ≫ f) (𝟙 Y) ≫ 𝟙 X)) (by simp) (r + e)

end Stacks.Chow

end
