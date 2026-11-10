module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClassConstruction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedGroup
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.OpenImmersionComposite
public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantRank
public import StacksCore.Tactic.StacksAttribute

/-!
# The bivariant class of a virtual normal bundle of arbitrary rank

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `i : Z ⟶ X` be a closed immersion and let `𝒩` be a virtual normal bundle
for `i` (Stacks 0FBQ). Stacks 0FBK asserts that the construction preceding it defines a bivariant
class

  `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧`

in the completed bivariant group of Stacks 0FE0. When `𝒩` has constant rank `r` that class is
`Stacks.Chow.virtualNormalBundleClass`, in `A^r(Z ⟶ X)`. In general the rank of `𝒩` is only
locally constant, and this file builds the class in the completed group, connected component by
connected component of `Z`.

## The construction

Let `Z_a` be a connected component of `Z` and `X_b` the connected component of `X` it maps into.
The rank of `𝒩` is constant on `Z_a`, equal to `r_a`. The open subscheme

  `U_a = X_b ∖ i(Z ∖ Z_a)`

of `X` satisfies `i⁻¹(U_a) = Z_a`, so the square formed by `i`, the closed immersion
`i_a : Z_a ⟶ U_a` and the two open immersions is cartesian, and the base change `𝒩|_{Z_a}` of
`𝒩` (Stacks 0FBJ) is a virtual normal bundle for `i_a` of constant rank `r_a`. The component of
`c(Z ⟶ X, 𝒩)` at `Z_a` is then

  `c(Z_a ⟶ U_a, 𝒩|_{Z_a}) ∘ (U_a ⟶ X_b)^* ∈ A^{r_a}(Z_a ⟶ X_b)`,

which is the construction of Stacks 0FBQ (3) for the closed immersion `Z_a ⟶ X_b` and the open
`U_a ⊆ X_b`.

## Main definitions

* `Stacks.Chow.componentNeighbourhood` — the open `U_a ⊆ X`.
* `Stacks.Chow.componentRestriction` — the closed immersion `i_a : Z_a ⟶ U_a`.
* `Stacks.Chow.componentRank` — the rank `r_a` of a finite locally free module on `Z_a`.
* `Stacks.Chow.VirtualNormalBundle.toComponent` — the virtual normal bundle `𝒩|_{Z_a}` of `i_a`.
* `Stacks.Chow.completedVirtualNormalGysinClass` — **Stacks 0FBK**, `c(Z ⟶ X, 𝒩)` in
  `A^*(Z ⟶ X)^∧`.

## Main results

* `Stacks.Chow.preimage_componentNeighbourhood`, `Stacks.Chow.isPullback_componentRestriction` —
  the square of the construction is cartesian.
* `Stacks.Chow.isFiniteLocallyFreeOfRank_componentRank` — a finite locally free module has
  constant rank on a connected component.
* `Stacks.Chow.completedVirtualNormalGysinClass_apply` — the component of the class at `Z_a`.
* `Stacks.Chow.componentRank_eq_of_isFiniteLocallyFreeOfRank` — at constant rank `r` every
  component has degree `r`.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBJ](https://stacks.math.columbia.edu/tag/0FBJ)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The cartesian square at a connected component -/

section Component

variable {Z X : Scheme.{u}} [LocallyConnectedSpace Z] [LocallyConnectedSpace X] (i : Z ⟶ X)
  [IsClosedImmersion i] (a : _root_.ConnectedComponents Z)

omit [LocallyConnectedSpace X] in
/-- The image under the closed immersion `i` of the complement of a connected component `Z_a` of
`Z` is closed. -/
theorem isClosed_image_compl_connectedComponentOpens :
    IsClosed (i '' (Z.connectedComponentOpens a : Set Z)ᶜ) :=
  i.isClosedEmbedding.isClosedMap _ (Z.connectedComponentOpens a).isOpen.isClosed_compl

/-- **The open `U_a = X_b ∖ i(Z ∖ Z_a)`** for a connected component `Z_a` of `Z` and the connected
component `X_b` of `X` it maps into: the largest open of `X_b` meeting `Z` in `Z_a` only. -/
def componentNeighbourhood : X.Opens :=
  X.connectedComponentOpens (i.continuous.connectedComponentsMap a) ⊓
    ⟨(i '' (Z.connectedComponentOpens a : Set Z)ᶜ)ᶜ,
      (isClosed_image_compl_connectedComponentOpens i a).isOpen_compl⟩

/-- The open `U_a` is contained in the connected component `X_b` of `X`. -/
theorem componentNeighbourhood_le :
    componentNeighbourhood i a ≤
      X.connectedComponentOpens (i.continuous.connectedComponentsMap a) :=
  inf_le_left

/-- `i⁻¹(U_a) = Z_a`. -/
theorem preimage_componentNeighbourhood :
    i ⁻¹ᵁ componentNeighbourhood i a = Z.connectedComponentOpens a := by
  ext z
  change i z ∈ componentNeighbourhood i a ↔ z ∈ Z.connectedComponentOpens a
  constructor
  · rintro ⟨-, h⟩
    by_contra hz
    exact h ⟨z, hz, rfl⟩
  · intro hz
    refine ⟨i.connectedComponentOpens_le_preimage a hz, ?_⟩
    rintro ⟨z', hz', he⟩
    exact hz' (i.isClosedEmbedding.injective he ▸ hz)

/-- **The closed immersion `i_a : Z_a ⟶ U_a`**, the restriction of `i`. -/
def componentRestriction :
    (Z.connectedComponentOpens a : Scheme.{u}) ⟶ (componentNeighbourhood i a : Scheme.{u}) :=
  i.resLE _ _ (preimage_componentNeighbourhood i a).ge

/-- The composite `Z_a ⟶ U_a ⟶ X` equals the composite `Z_a ⟶ Z ⟶ X`. -/
@[reassoc (attr := simp)]
theorem componentRestriction_ι :
    componentRestriction i a ≫ (componentNeighbourhood i a).ι =
      (Z.connectedComponentOpens a).ι ≫ i :=
  i.resLE_comp_ι _

/-- **The square of the construction is cartesian**: `i_a : Z_a ⟶ U_a` is the base change of `i`
along the open immersion `U_a ⟶ X`, because `i⁻¹(U_a) = Z_a`. -/
theorem isPullback_componentRestriction :
    IsPullback (componentRestriction i a) (Z.connectedComponentOpens a).ι
      (componentNeighbourhood i a).ι i := by
  refine (isPullback_morphismRestrict i (componentNeighbourhood i a)).of_iso
    (Z.isoOfEq (preimage_componentNeighbourhood i a)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ (by simp) (by simp)
  · rw [Iso.refl_hom, Category.comp_id, ← cancel_mono (componentNeighbourhood i a).ι,
      morphismRestrict_ι, Category.assoc, componentRestriction_ι, Scheme.isoOfEq_hom_ι_assoc]
  · rw [Iso.refl_hom, Category.comp_id, Scheme.isoOfEq_hom_ι]

/-- The restriction `i_a : Z_a ⟶ U_a` is a closed immersion. -/
instance isClosedImmersion_componentRestriction : IsClosedImmersion (componentRestriction i a) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_componentRestriction i a).flip inferInstance

/-- The open immersion `U_a ⟶ X_b`. -/
abbrev componentInclusion :
    (componentNeighbourhood i a : Scheme.{u}) ⟶
      (X.connectedComponentOpens (i.continuous.connectedComponentsMap a) : Scheme.{u}) :=
  X.homOfLE (componentNeighbourhood_le i a)

/-- `Z_a ⟶ U_a ⟶ X_b` is the restriction of `i` to `Z_a`. -/
theorem componentRestriction_comp_componentInclusion :
    componentRestriction i a ≫ componentInclusion i a = i.resConnectedComponent a := by
  rw [← cancel_mono (X.connectedComponentOpens (i.continuous.connectedComponentsMap a)).ι,
    Category.assoc, Scheme.homOfLE_ι, componentRestriction_ι,
    Scheme.Hom.resConnectedComponent_comp_ι]

end Component

/-! ### The rank on a connected component -/

section Rank

variable {Z : Scheme.{u}} [LocallyConnectedSpace Z] (E : Z.Modules)
  [SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (a : _root_.ConnectedComponents Z)

/-- The rank of a finite locally free module on a connected component `Z_a`: its fibre rank at a
point of `Z_a`, which does not depend on the point. -/
def componentRank : ℕ :=
  E.fiberRank (_root_.ConnectedComponents.surjective_coe a).choose

/-- A finite locally free module has fibre rank `componentRank` at every point of `Z_a`: the fibre
rank is locally constant, hence constant on the connected set `Z_a`. -/
theorem fiberRank_eq_componentRank (x : Z) (hx : x ∈ Z.connectedComponentOpens a) :
    E.fiberRank x = componentRank E a := by
  have : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E :=
    ⟨(inferInstance :
      SheafOfModules.IsFiniteLocallyFree.{u, u, u} E).exists_isFiniteLocallyFreeData⟩
  have hlc := Scheme.Modules.isLocallyConstant_fiberRank E
  set x₀ := (_root_.ConnectedComponents.surjective_coe a).choose
  have hx₀ : (x₀ : _root_.ConnectedComponents Z) = a :=
    (_root_.ConnectedComponents.surjective_coe a).choose_spec
  have hxx₀ : x ∈ connectedComponent x₀ := by
    rw [← connectedComponents_preimage_singleton]
    exact ((Scheme.mem_connectedComponentOpens Z).1 hx).trans hx₀.symm
  exact hlc.apply_eq_of_isPreconnected isPreconnected_connectedComponent hxx₀
    mem_connectedComponent

/-- **A finite locally free module has constant rank on a connected component**: its pullback to
`Z_a` is finite locally free of rank `componentRank`. -/
theorem isFiniteLocallyFreeOfRank_componentRank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (Z.connectedComponentOpens a).ι).obj E) (componentRank E a) :=
  Scheme.Modules.isFiniteLocallyFreeOfRank_pullback_of_fiberRank_eq E _ _
    (fiberRank_eq_componentRank E a)

omit [LocallyConnectedSpace Z] [SheafOfModules.IsFiniteLocallyFree E] in
/-- On a module finite locally free of constant rank `r`, the rank on every connected component
is `r`. -/
theorem componentRank_eq_of_isFiniteLocallyFreeOfRank (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] : componentRank E a = r :=
  Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank E r _

end Rank

/-! ### The virtual normal bundle on a connected component -/

section Bundle

variable {Z X : Scheme.{u}} [LocallyConnectedSpace Z] [LocallyConnectedSpace X] (i : Z ⟶ X)
  [IsClosedImmersion i] (a : _root_.ConnectedComponents Z)

/-- **The virtual normal bundle `𝒩|_{Z_a}` of `i_a : Z_a ⟶ U_a`**, the base change of `𝒩` along
the cartesian square of the construction (Stacks 0FBJ). -/
def VirtualNormalBundle.toComponent (𝒩 : VirtualNormalBundle i) :
    VirtualNormalBundle (componentRestriction i a) :=
  𝒩.baseChange i (componentRestriction i a) (Z.connectedComponentOpens a).ι
    (componentNeighbourhood i a).ι (isPullback_componentRestriction i a)

/-- The bundle of `𝒩|_{Z_a}` is finite locally free of rank `componentRank 𝒩.bundle a`. -/
instance VirtualNormalBundle.isFiniteLocallyFreeOfRank_toComponent (𝒩 : VirtualNormalBundle i) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (𝒩.toComponent i a).bundle
      (componentRank 𝒩.bundle a) :=
  isFiniteLocallyFreeOfRank_componentRank 𝒩.bundle a

end Bundle

/-! ### The class -/

section Class

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ)

omit [LocallyOfFiniteType sZ] [LocallyOfFiniteType sX] in
include hi in
/-- The composite `Z_a ⟶ U_a ⟶ X ⟶ S` equals the composite `Z_a ⟶ Z ⟶ S`. -/
theorem componentRestriction_comp_structureMorphism [LocallyConnectedSpace Z]
    [LocallyConnectedSpace X] (a : _root_.ConnectedComponents Z) :
    componentRestriction i a ≫ ((componentNeighbourhood i a).ι ≫ sX) =
      (Z.connectedComponentOpens a).ι ≫ sZ := by
  rw [componentRestriction_ι_assoc, hi]

/-- **Stacks 0FBK, the class `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧`** of a virtual normal bundle `𝒩` of
arbitrary rank for a closed immersion `i : Z ⟶ X`. On a connected component `Z_a` of `Z`, on which
`𝒩` has constant rank `r_a`, it is the class `c(Z_a ⟶ U_a, 𝒩|_{Z_a}) ∘ (U_a ⟶ X_b)^*` of degree
`r_a`, for the open `U_a = X_b ∖ i(Z ∖ Z_a)` of the connected component `X_b` of `X` containing
`i(Z_a)`, through which `Z_a ⟶ X_b` factors as the closed immersion `Z_a ⟶ U_a` cut out by the
base change of `i`. -/
@[stacks 0FBK "the bivariant class c(Z → X, 𝒩) ∈ A^*(Z → X)^∧ of a virtual normal bundle 𝒩 of \
arbitrary rank for a closed immersion Z → X"]
def completedVirtualNormalGysinClass (𝒩 : VirtualNormalBundle i) :
    completedBivariantGroup C (gysinSystemOfInvertible C) sZ sX i hi :=
  letI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  fun a ↦ DirectSum.of _ (componentRank 𝒩.bundle a : ℤ)
    (BivariantClass.copy C (gysinSystemOfInvertible C) ((Z.connectedComponentOpens a).ι ≫ sZ)
      ((X.connectedComponentOpens (i.continuous.connectedComponentsMap a)).ι ≫ sX)
      (componentRestriction_comp_componentInclusion i a) _
      (i.resConnectedComponent_comp_ι_comp hi a) (by simp)
      (openImmersionComposite C ((Z.connectedComponentOpens a).ι ≫ sZ)
        ((componentNeighbourhood i a).ι ≫ sX)
        ((X.connectedComponentOpens (i.continuous.connectedComponentsMap a)).ι ≫ sX)
        (componentRestriction i a) (componentInclusion i a)
        (componentRestriction_comp_structureMorphism C sZ sX i hi a)
        (by rw [← Category.assoc, Scheme.homOfLE_ι]) (componentRank 𝒩.bundle a : ℤ)
        (virtualNormalBundleClass C ((Z.connectedComponentOpens a).ι ≫ sZ)
          ((componentNeighbourhood i a).ι ≫ sX) (componentRestriction i a)
          (componentRestriction_comp_structureMorphism C sZ sX i hi a) (𝒩.toComponent i a)
          (componentRank 𝒩.bundle a))))

/-- **Stacks 0FBK.** On a connected component `Z_a` of `Z` the class `c(Z ⟶ X, 𝒩)` is concentrated
in degree `r_a`, the rank of `𝒩` on `Z_a`, where it is `c(Z_a ⟶ U_a, 𝒩|_{Z_a}) ∘ (U_a ⟶ X_b)^*`. -/
theorem completedVirtualNormalGysinClass_apply [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
    (𝒩 : VirtualNormalBundle i) (a : _root_.ConnectedComponents Z) :
    completedVirtualNormalGysinClass C sZ sX i hi 𝒩 a =
      DirectSum.of _ (componentRank 𝒩.bundle a : ℤ)
        (BivariantClass.copy C (gysinSystemOfInvertible C) ((Z.connectedComponentOpens a).ι ≫ sZ)
          ((X.connectedComponentOpens (i.continuous.connectedComponentsMap a)).ι ≫ sX)
          (componentRestriction_comp_componentInclusion i a) _
          (i.resConnectedComponent_comp_ι_comp hi a) (by simp)
          (openImmersionComposite C ((Z.connectedComponentOpens a).ι ≫ sZ)
            ((componentNeighbourhood i a).ι ≫ sX)
            ((X.connectedComponentOpens (i.continuous.connectedComponentsMap a)).ι ≫ sX)
            (componentRestriction i a) (componentInclusion i a)
            (componentRestriction_comp_structureMorphism C sZ sX i hi a)
            (by rw [← Category.assoc, Scheme.homOfLE_ι]) (componentRank 𝒩.bundle a : ℤ)
            (virtualNormalBundleClass C ((Z.connectedComponentOpens a).ι ≫ sZ)
              ((componentNeighbourhood i a).ι ≫ sX) (componentRestriction i a)
              (componentRestriction_comp_structureMorphism C sZ sX i hi a) (𝒩.toComponent i a)
              (componentRank 𝒩.bundle a)))) :=
  rfl

end Class

end Stacks.Chow

end
