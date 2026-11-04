module

public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Multiplicity
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.ClosedImmersionStalkVanishing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.MaximalDeltaDimension

/-!
# The cycle of a closed subscheme is the cycle of its structure sheaf

Let `X` be locally of finite type over the base scheme `S` of chapter 42 of the Stacks Project
and let `i : Z ⟶ X` be a closed subscheme with `dim_δ(Z) ≤ k`. The direct image `i_* 𝒪_Z` is a
coherent `𝒪_X`-module supported on `Z`, so it has a `k`-cycle `[𝒪_Z]_k`, and that cycle is the
cycle `[Z]_k` of the closed subscheme.

Both cycles are supported on the generic points of the `k`-dimensional irreducible components
of `Z`, and the comparison is coefficientwise. At the generic point `ξ` of a component the
coefficient of `[Z]_k` is the length of `𝒪_{Z,ξ}` and the coefficient of `[𝒪_Z]_k` is the
length of the stalk `(i_* 𝒪_Z)_{i ξ}`; those stalks agree, since the stalk of a direct image
along a closed immersion is the stalk of the original sheaf. At a point of `X` off the image of
`i` the stalk of `i_* 𝒪_Z` vanishes, and at a point of the image of delta-dimension `k` the
bound `dim_δ(Z) ≤ k` forces the point to be the generic point of a component; so no other
coefficient is nonzero on either side.

## Main results

* `Stacks.Chow.supp_pushforwardStructureSheaf` — the support of `i_* 𝒪_Z` is the image of `i`.
* `Stacks.Chow.length_stalk_pushforwardStructureSheaf` — the length of the stalk of `i_* 𝒪_Z`
  at `i z` is the length of `𝒪_{Z,z}` over the local ring of `X`.
* `Stacks.Chow.sheafMultiplicity_pushforwardStructureSheaf` — hence the multiplicity of
  `i_* 𝒪_Z` at the generic point of a component of `Z` is that component's multiplicity.
* `Stacks.Chow.cycleAssociatedToClosedSubscheme_eq_cycleAssociatedToCoherentSheaf` —
  Stacks 02QY, `[Z]_k = [𝒪_Z]_k`.

## Implementation notes

`i_* 𝒪_Z` is the pushforward along `i` of the monoidal unit of `Z.Modules`, written here with
`Stacks.Ample.unitModule` for that unit. Its coherence on a locally Noetherian `X` is
`AlgebraicGeometry.ClosedImmersionCoherentImage.isCoherent_pushforward_unit`, registered below as
an instance because `AlgebraicGeometry.Scheme.Modules` is a `def` and instance search does not
see through it.

The stalk comparison is stated for the `CommRingCat`-valued stalk `X.presheaf.stalk x` and the
stalk map `AlgebraicGeometry.Scheme.Hom.stalkMap`, over which `Stacks.Chow.sheafMultiplicity` and
`Stacks.Chow.componentMultiplicity` read lengths, rather than for the `RingCat`-valued stalk of
`Stacks.ClosedImmersion.stalkPushforwardModuleIso`. It is the comparison map of
`TopCat.Presheaf.stalkPushforward`, invertible by
`TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing`, followed by
`Stacks.Ample.unitStalkIso`, which identifies the stalk of `𝒪_Z` read as a module with the stalk
of `𝒪_Z` read as a ring.

## References

* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
* [Stacks Project, Tag 02QY](https://stacks.math.columbia.edu/tag/02QY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable {X Z : Scheme.{u}} (i : Z ⟶ X) (M : Z.Modules) (z : Z)

/-! ### The stalk of a direct image on the image -/

/-- The canonical map from the stalk of `i_* M` at `i z` to the stalk of `M` at `z`, as a map of
abelian groups: the comparison map of `TopCat.Presheaf.stalkPushforward`. -/
def stalkPushforwardComparison :
    ((Scheme.Modules.pushforward i).obj M).presheaf.stalk (i z) → M.presheaf.stalk z :=
  fun s => (TopCat.Presheaf.stalkPushforward Ab.{u} i.base M.val.presheaf z).hom s

/-- The comparison map sends the germ at `i z` of a section of `i_* M` over `U` to the germ at
`z` of the same section, read over `i⁻¹ U`. -/
theorem stalkPushforwardComparison_germ (U : X.Opens) (hU : i z ∈ U)
    (t : Γ((Scheme.Modules.pushforward i).obj M, U)) :
    stalkPushforwardComparison i M z
        ((((Scheme.Modules.pushforward i).obj M).presheaf.germ U (i z) hU).hom t) =
      (M.presheaf.germ (i ⁻¹ᵁ U) z hU).hom t :=
  TopCat.Presheaf.stalkPushforward_germ_apply Ab.{u} i.base M.val.presheaf U z hU t

/-- The comparison map is additive. -/
theorem stalkPushforwardComparison_add (a b) :
    stalkPushforwardComparison i M z (a + b) =
      stalkPushforwardComparison i M z a + stalkPushforwardComparison i M z b :=
  map_add _ a b

/-- The comparison map is semilinear over the stalk map of `i`: a scalar from `𝒪_{X, i z}` acts
on the target through `AlgebraicGeometry.Scheme.Hom.stalkMap`. -/
theorem stalkPushforwardComparison_smul (r : X.presheaf.stalk (i z))
    (s : ((Scheme.Modules.pushforward i).obj M).presheaf.stalk (i z)) :
    stalkPushforwardComparison i M z (r • s) =
      i.stalkMap z r • stalkPushforwardComparison i M z s := by
  obtain ⟨V, hV, a, ha⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf r
  obtain ⟨W, hW, t, ht⟩ :=
    TopCat.Presheaf.exists_germ_eq ((Scheme.Modules.pushforward i).obj M).presheaf s
  let U : X.Opens := V ⊓ W
  have hU : i z ∈ U := ⟨hV, hW⟩
  obtain ⟨a', hga⟩ : ∃ a' : Γ(X, U), (X.presheaf.germ U (i z) hU).hom a' = r :=
    ⟨(X.presheaf.map (homOfLE (inf_le_left : U ≤ V)).op).hom a, by
      rw [TopCat.Presheaf.germ_res_apply]; exact ha⟩
  obtain ⟨t', hgt⟩ : ∃ t' : Γ((Scheme.Modules.pushforward i).obj M, U),
      (((Scheme.Modules.pushforward i).obj M).presheaf.germ U (i z) hU).hom t' = s :=
    ⟨(((Scheme.Modules.pushforward i).obj M).presheaf.map
      (homOfLE (inf_le_right : U ≤ W)).op).hom t, by
      rw [TopCat.Presheaf.germ_res_apply]; exact ht⟩
  have keyX : (((Scheme.Modules.pushforward i).obj M).presheaf.germ U (i z) hU).hom (a' • t') =
      (X.presheaf.germ U (i z) hU).hom a' •
        (((Scheme.Modules.pushforward i).obj M).presheaf.germ U (i z) hU).hom t' :=
    PresheafOfModules.germ_smul ((Scheme.Modules.pushforward i).obj M).val (i z) U hU a' t'
  have keyZ : (M.presheaf.germ (i ⁻¹ᵁ U) z hU).hom
        ((i.app U a') • (show Γ(M, i ⁻¹ᵁ U) from t')) =
      (Z.presheaf.germ (i ⁻¹ᵁ U) z hU).hom (i.app U a') •
        (M.presheaf.germ (i ⁻¹ᵁ U) z hU).hom (show Γ(M, i ⁻¹ᵁ U) from t') :=
    PresheafOfModules.germ_smul M.val z (i ⁻¹ᵁ U) hU (i.app U a') t'
  have hstalk : (Z.presheaf.germ (i ⁻¹ᵁ U) z hU).hom (i.app U a') = i.stalkMap z r :=
    hga ▸ (Scheme.Hom.germ_stalkMap_apply i U z hU a').symm
  calc stalkPushforwardComparison i M z (r • s)
      = stalkPushforwardComparison i M z
          ((((Scheme.Modules.pushforward i).obj M).presheaf.germ U (i z) hU).hom (a' • t')) := by
        rw [keyX, hga, hgt]
    _ = (M.presheaf.germ (i ⁻¹ᵁ U) z hU).hom (a' • t') :=
        stalkPushforwardComparison_germ i M z U hU _
    _ = (Z.presheaf.germ (i ⁻¹ᵁ U) z hU).hom (i.app U a') •
          (M.presheaf.germ (i ⁻¹ᵁ U) z hU).hom (show Γ(M, i ⁻¹ᵁ U) from t') := keyZ
    _ = i.stalkMap z r • stalkPushforwardComparison i M z s := by
        rw [hstalk, ← stalkPushforwardComparison_germ i M z U hU t', hgt]

/-- The comparison map is bijective as soon as the underlying map of `i` is inducing, a closed
immersion for instance. -/
theorem bijective_stalkPushforwardComparison
    (hi : Topology.IsInducing (ConcreteCategory.hom i.base)) :
    Function.Bijective (stalkPushforwardComparison i M z) := by
  have := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing Ab.{u} hi
    M.val.presheaf z
  exact ConcreteCategory.bijective_of_isIso
    (TopCat.Presheaf.stalkPushforward Ab.{u} i.base M.val.presheaf z)

/-- Reading the stalk of `𝒪_Y` as a module and as a ring gives the same abelian group. -/
theorem bijective_unitStalkFun (Y : Scheme.{u}) (y : Y) :
    Function.Bijective (Stacks.Ample.unitStalkFun Y y) :=
  ConcreteCategory.bijective_of_isIso (Stacks.Ample.unitStalkIso Y y).hom

/-! ### The stalk of `i_* 𝒪_Z` on the image -/

/-- The comparison from the stalk of `i_* 𝒪_Z` at `i z` to the local ring `𝒪_{Z,z}`: the stalk
comparison of the direct image, followed by the identification of the stalk of `𝒪_Z` read as a
module with the stalk of `𝒪_Z` read as a ring. -/
def structureSheafStalkComparison (i : Z ⟶ X) (z : Z) :
    ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z)).presheaf.stalk (i z) →
      Z.presheaf.stalk z :=
  fun s => Stacks.Ample.unitStalkFun Z z
    (stalkPushforwardComparison i (Stacks.Ample.unitModule Z) z s)

/-- The comparison to `𝒪_{Z,z}` turns the action of `𝒪_{X, i z}` into multiplication by the
image of the scalar under the stalk map of `i`. -/
theorem structureSheafStalkComparison_smul (r : X.presheaf.stalk (i z))
    (s : ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z)).presheaf.stalk (i z)) :
    structureSheafStalkComparison i z (r • s) =
      i.stalkMap z r * structureSheafStalkComparison i z s := by
  rw [structureSheafStalkComparison, stalkPushforwardComparison_smul]
  exact Stacks.Ample.unitStalkFun_smul Z z _ _

/-- The comparison to `𝒪_{Z,z}` is bijective when the underlying map of `i` is inducing: both
of its two factors are. -/
theorem bijective_structureSheafStalkComparison
    (hi : Topology.IsInducing (ConcreteCategory.hom i.base)) :
    Function.Bijective (structureSheafStalkComparison i z) :=
  (bijective_unitStalkFun Z z).comp (bijective_stalkPushforwardComparison i _ z hi)

/-- **The stalk of `i_* 𝒪_Z` on the image.** For a closed immersion `i : Z ⟶ X` the stalk of
`i_* 𝒪_Z` at `i z` is the local ring `𝒪_{Z,z}`, as a module over `𝒪_{X, i z}` by restriction of
scalars along the stalk map of `i`. -/
def stalkPushforwardStructureSheafLinearEquiv (i : Z ⟶ X) (z : Z)
    (hi : Topology.IsInducing (ConcreteCategory.hom i.base)) :
    letI : Module (X.presheaf.stalk (i z)) (Z.presheaf.stalk z) :=
      Module.compHom (Z.presheaf.stalk z) (i.stalkMap z).hom
    ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z)).presheaf.stalk (i z)
      ≃ₗ[X.presheaf.stalk (i z)] Z.presheaf.stalk z :=
  letI : Module (X.presheaf.stalk (i z)) (Z.presheaf.stalk z) :=
    Module.compHom (Z.presheaf.stalk z) (i.stalkMap z).hom
  { toFun := structureSheafStalkComparison i z
    map_add' := fun a b => by
      simp only [structureSheafStalkComparison, stalkPushforwardComparison_add,
        Stacks.Ample.unitStalkFun_add]
    map_smul' := fun r s => structureSheafStalkComparison_smul i z r s
    invFun := Function.surjInv (bijective_structureSheafStalkComparison i z hi).2
    left_inv := Function.leftInverse_surjInv (bijective_structureSheafStalkComparison i z hi)
    right_inv := Function.rightInverse_surjInv (bijective_structureSheafStalkComparison i z hi).2 }

/-- The length of the stalk of `i_* 𝒪_Z` at `i z` over the local ring of `X` is the length of
`𝒪_{Z,z}` over that same local ring. -/
theorem length_stalk_pushforwardStructureSheaf (i : Z ⟶ X) (z : Z)
    (hi : Topology.IsInducing (ConcreteCategory.hom i.base)) :
    letI : Module (X.presheaf.stalk (i z)) (Z.presheaf.stalk z) :=
      Module.compHom (Z.presheaf.stalk z) (i.stalkMap z).hom
    Module.length (X.presheaf.stalk (i z))
        (((Scheme.Modules.pushforward i).obj (Ample.unitModule Z)).presheaf.stalk (i z)) =
      Module.length (X.presheaf.stalk (i z)) (Z.presheaf.stalk z) :=
  let : Module (X.presheaf.stalk (i z)) (Z.presheaf.stalk z) :=
    Module.compHom (Z.presheaf.stalk z) (i.stalkMap z).hom
  (stalkPushforwardStructureSheafLinearEquiv i z hi).length_eq

/-- The stalk of `i_* 𝒪_Z` at a point of the image is nonzero: it is a local ring. -/
theorem nontrivial_stalk_pushforwardStructureSheaf (i : Z ⟶ X) [IsClosedImmersion i] (z : Z) :
    Nontrivial (((Scheme.Modules.pushforward i).obj (Ample.unitModule Z)).presheaf.stalk (i z)) :=
  (Equiv.ofBijective _ (bijective_structureSheafStalkComparison i z
    (IsClosedImmersion.isClosedEmbedding i).isInducing)).nontrivial

/-- **The support of `i_* 𝒪_Z` is `Z`.** Off the image of a closed immersion the stalk of a
direct image vanishes, and on the image it is a local ring. -/
theorem supp_pushforwardStructureSheaf (i : Z ⟶ X) [IsClosedImmersion i] :
    SheafOfModules.supp ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z)) =
      Set.range (ConcreteCategory.hom i.base) := by
  ext x
  refine ⟨fun hx => ?_, fun ⟨z, hz⟩ => ?_⟩
  · by_contra hrange
    have := AlgebraicGeometry.subsingleton_stalk_pushforward_of_notMemRange' i
      (Stacks.Ample.unitModule Z) x hrange
    obtain ⟨a, ha⟩ := hx
    exact ha (Subsingleton.elim _ _)
  · subst hz
    exact (SheafOfModules.mem_supp_iff_nontrivial_stalk _ _).mpr
      (nontrivial_stalk_pushforwardStructureSheaf i z)

/-- **`i_* 𝒪_Z` is coherent** when `X` is locally Noetherian: the structure sheaf of `X`
surjects onto it, so this is Stacks 01Y1. -/
instance isCoherent_pushforwardStructureSheaf (i : Z ⟶ X) [IsClosedImmersion i]
    [IsLocallyNoetherian X] :
    ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z)).IsCoherent :=
  AlgebraicGeometry.ClosedImmersionCoherentImage.isCoherent_pushforward_unit i

/-! ### The multiplicities agree -/

/-- The multiplicity of `i_* 𝒪_Z` at the generic point of an irreducible component of `Z` is the
multiplicity of that component in `Z`. -/
theorem sheafMultiplicity_pushforwardStructureSheaf (i : Z ⟶ X) [IsClosedImmersion i]
    (ξ : genericPoints Z) :
    sheafMultiplicity ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z)) (i ξ.1) =
      componentMultiplicity i ξ := by
  unfold sheafMultiplicity componentMultiplicity
  congr 2
  exact length_stalk_pushforwardStructureSheaf i ξ.1
    (IsClosedImmersion.isClosedEmbedding i).isInducing

/-! ### The delta-dimension of the support -/

/-- If `dim_δ(Z) ≤ k` then the reduced support of `i_* 𝒪_Z` has delta-dimension at most `k`:
that support is the image of `i`, where the relative dimension is bounded by `dim_δ(Z)`. -/
theorem schemeDeltaDimension_reducedSupport_pushforwardStructureSheaf_le
    (C : ChowSituation.{u}) {X Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (i : Z ⟶ X) [IsClosedImmersion i] {k : ℤ}
    (hZ : schemeDeltaDimension C (i ≫ f) ≤ (k : EInt)) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    schemeDeltaDimension C
        ((reducedSupport ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z))).subschemeι
          ≫ f) ≤ (k : EInt) := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine schemeDeltaDimension_le_of_forall_relativeDimension_le C f _ fun w => ?_
  obtain ⟨z, hz⟩ :
      (reducedSupport ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z))).subschemeι w ∈
      Set.range (ConcreteCategory.hom i.base) := by
    rw [← supp_pushforwardStructureSheaf i, ← coe_support_reducedSupport,
      ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨w, rfl⟩
  rw [← hz]
  exact relativeDimension_le_of_schemeDeltaDimension_le C f i hZ z

/-! ### Stacks 02QY -/

/-- **Stacks 02QY.** For a closed subscheme `i : Z ⟶ X` of delta-dimension at most `k`, the
`k`-cycle of `Z` is the `k`-cycle of its structure sheaf: `[Z]_k = [𝒪_Z]_k`. -/
@[stacks 02QY]
theorem cycleAssociatedToClosedSubscheme_eq_cycleAssociatedToCoherentSheaf
    (C : ChowSituation.{u}) {X Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (i : Z ⟶ X) [IsClosedImmersion i] (k : ℤ)
    (hZ : schemeDeltaDimension C (i ≫ f) ≤ (k : EInt)) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    cycleAssociatedToClosedSubscheme C f i k =
      cycleAssociatedToCoherentSheaf C f ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z)) k
        (schemeDeltaDimension_reducedSupport_pushforwardStructureSheaf_le C f i hZ) := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine Subtype.ext ?_
  apply Function.locallyFinsuppWithin.ext
  intro x
  by_cases hk : relativeDimension C.dimensionFunction f x = k
  · by_cases hgen : ∃ ξ : genericPoints Z, i ξ.1 = x
    · obtain ⟨ξ, rfl⟩ := hgen
      rw [cycleAssociatedToClosedSubscheme_apply C f i k ξ hk,
        cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq C f _ k _ hk,
        sheafMultiplicity_pushforwardStructureSheaf i ξ]
    · rw [cycleAssociatedToClosedSubscheme_apply_eq_zero C f i k x
          (fun ⟨ξ, hξ, _⟩ => hgen ⟨ξ, hξ⟩),
        cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq C f _ k _ hk]
      by_cases hrange : x ∈ Set.range (ConcreteCategory.hom i.base)
      · obtain ⟨z, rfl⟩ := hrange
        obtain ⟨W, hW⟩ := isGenericPoint_component_of_relativeDimension_eq C f i hZ z hk
        exact absurd ⟨⟨z, show closure {z} ∈ irreducibleComponents Z from hW ▸ W.2⟩, rfl⟩ hgen
      · exact (sheafMultiplicity_eq_zero_of_notMem_supp _
          (by rw [supp_pushforwardStructureSheaf i]; exact hrange)).symm
  · rw [cycleAssociatedToClosedSubscheme_apply_eq_zero C f i k x (fun ⟨ξ, _, h⟩ => hk h),
      cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne C f _ k _ hk]

end Stacks.Chow

end
