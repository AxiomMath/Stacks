module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedPushforwardRationalEquivalenceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceCycleComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinPushforwardFirstChernCapCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrimeDivisorIsoTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreEquivalences
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafLengthImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspaceImage

/-!
# The cycle of a closed subspace along closed immersions and isomorphisms

In Situation 0EDT let `X/B` be good. For a closed immersion `j : T → X` over `B` and a closed
subspace `Y ⊆ T` with `dim_δ(Y) ≤ k`, the pushforward `j_*[Y]_k` of the cycle of Stacks 0EE9 is
supported on the images in `X` of the integral closed subspaces `V ⊆ Y`, with coefficient at the
image of `V` the multiplicity of `V` in `Y` when that image has δ-dimension `k`. Consequently, if
`j₁ : T₁ → X` and `j₂ : T₂ → X` are two closed immersions over `B`, and closed subspaces
`Y₁ ⊆ T₁`, `Y₂ ⊆ T₂` are identified by an isomorphism `Y₁ ≅ Y₂` over `X`, then

`(j₁)_*[Y₁]_k = (j₂)_*[Y₂]_k`.

The case `T₁ = X`, `T₂ = X'`, `j₁ = e`, `j₂ = 𝟙` is the invariance of `[Y]_k` under an
isomorphism of good spaces `e : X ≅ X'` over `B`. The case `T₁ = W`, `T₂ = E` of an integral
closed subspace `W ⊆ X` and a closed subspace `E ⊆ X`, with `Y₁ = W ×_X E` and `Y₂ = E ×_X W`, is
the identity

`(W → X)_*[W ×_X E]_k = (E → X)_*[E ×_X W]_k`.

## Main definitions

* `AlgebraicGeometry.Space.IntegralClosedSubspace.isoPushforward`: the isomorphism, over the
  ambient space, of an integral closed subspace with its image along a closed immersion.

## Main results

* `AlgebraicGeometry.Space.closedSubspaceMultiplicity_pushforward_of_iso`: the multiplicity of
  Stacks 0EE9 is invariant under an isomorphism of closed subspaces.
* `AlgebraicGeometry.Space.cycleClosedPushforward_closedSubspaceCycle_apply_pushforward` and
  `AlgebraicGeometry.Space.cycleClosedPushforward_closedSubspaceCycle_apply_of_forall_ne`: the
  coefficients of `j_*[Y]_k`.
* `AlgebraicGeometry.Space.cycleGroupClosedPushforward_closedSubspaceCycle_eq_of_iso`: the
  comparison `(j₁)_*[Y₁]_k = (j₂)_*[Y₂]_k`.
* `AlgebraicGeometry.Space.cycleGroupClosedPushforward_closedSubspaceCycle_of_iso`: the
  invariance of `[Y]_k` under an isomorphism of good spaces.
* `AlgebraicGeometry.Space.integralClosedSubspacePushforward_closedSubspaceCycle_preimage_eq`:
  `(W → X)_*[W ×_X E]_k = (E → X)_*[E ×_X W]_k`.

## References

* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace CategoryTheory.Subfunctor

/-- For subfunctors `G` and `H` of `F`, the isomorphism between the inverse image of `H` in `G`
and the inverse image of `G` in `H` which is the identity on underlying elements. -/
@[simps]
def preimageιIso {C : Type*} [Category C] {F : C ⥤ Type*}
    (G H : Subfunctor F) : (H.preimage G.ι).toFunctor ≅ (G.preimage H.ι).toFunctor where
  hom := { app := fun _ => ↾fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩ }
  inv := { app := fun _ => ↾fun y => ⟨⟨y.1.1, y.2⟩, y.1.2⟩ }

/-- The isomorphism `CategoryTheory.Subfunctor.preimageιIso` commutes with the inclusions into
the ambient functor. -/
theorem preimageιIso_hom_comp_ι {C : Type*} [Category C]
    {F : C ⥤ Type*} (G H : Subfunctor F) :
    (preimageιIso G H).hom ≫ (G.preimage H.ι).ι ≫ H.ι =
      (H.preimage G.ι).ι ≫ G.ι :=
  rfl

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Integral closed subspaces under an isomorphism -/

section Equiv

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The point set of the image of an integral closed subspace under an isomorphism is the image
of its point set. -/
theorem IntegralClosedSubspace.subspacePointSet_equivOfIso (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXdec : IsDecentSpace B S hS X)
    (hYdec : IsDecentSpace B S hS Y) (e : X ≅ Y) (Z : IntegralClosedSubspace B S hS X) :
    subspacePointSet B S hS Y
        (IntegralClosedSubspace.equivOfIso B S hS hX hY hXdec hYdec e Z).subspace =
      pointsMap B S hS X e.hom '' subspacePointSet B S hS X Z.subspace :=
  IntegralClosedSubspace.subspacePointSet_pushforward B S hS hY hX hYdec _ Z

/-- The generic point of the image of an integral closed subspace under an isomorphism is the
image of its generic point. -/
theorem IntegralClosedSubspace.ambientGenericPoint_equivOfIso (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXdec : IsDecentSpace B S hS X)
    (hYdec : IsDecentSpace B S hS Y) (e : X ≅ Y) (Z : IntegralClosedSubspace B S hS X) :
    (IntegralClosedSubspace.equivOfIso B S hS hX hY hXdec hYdec e Z).ambientGenericPoint B S hS =
      pointsMap B S hS X e.hom (Z.ambientGenericPoint B S hS) :=
  IntegralClosedSubspace.ambientGenericPoint_pushforward B S hS hY hX hYdec _ Z

section Image

variable (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXdec : IsDecentSpace B S hS X) {i : Y ⟶ X} (hi : IsClosedImmersion B S hS i)
    (V : IntegralClosedSubspace B S hS Y)

include hi in
/-- The image subfunctor of an integral closed subspace along a closed immersion is a closed
subspace. -/
theorem IntegralClosedSubspace.isClosedSubspace_image :
    IsClosedSubspace B S hS (V.subspace.image i) := by
  have : Mono i := mono_of_isClosedImmersion B S hS i hi
  refine ⟨isAlgebraicSpace_of_iso B S hS (asIso (V.subspace.toImage i))
    V.isClosedSubspace.1, ?_⟩
  have h : (V.subspace.image i).ι = inv (V.subspace.toImage i) ≫ V.subspace.ι ≫ i := by
    rw [IsIso.eq_inv_comp, Subfunctor.toImage_ι]
  rw [h]
  exact isClosedImmersion_comp B S hS _ _ (isClosedImmersion_of_isIso B S hS _)
    (isClosedImmersion_comp B S hS _ _ V.isClosedSubspace.2 hi)

/-- The points of the image of an integral closed subspace along a closed immersion are the
points of its image integral closed subspace. -/
theorem IntegralClosedSubspace.range_pointsMap_comp_eq_subspacePointSet_pushforward :
    Set.range (pointsMap B S hS V.subspace.toFunctor (V.subspace.ι ≫ i)) =
      subspacePointSet B S hS X
        (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).subspace := by
  rw [IntegralClosedSubspace.subspacePointSet_pushforward, pointsMap_comp, Set.range_comp]

include hX in
/-- The inclusion of an integral closed subspace followed by a closed immersion factors through
the image integral closed subspace. -/
theorem IntegralClosedSubspace.exists_lift_pushforward :
    ∃ g : V.subspace.toFunctor ⟶
        (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).subspace.toFunctor,
      g ≫ (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).subspace.ι =
        V.subspace.ι ≫ i :=
  (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS hX V.isClosedSubspace.1 _
    (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).isClosedSubspace
    V.isIntegralSpace.1 (V.subspace.ι ≫ i)).2
    (IntegralClosedSubspace.range_pointsMap_comp_eq_subspacePointSet_pushforward hX hY hXdec hi
      V).subset

include hX in
/-- The inclusion of the image integral closed subspace factors through the image subfunctor. -/
theorem IntegralClosedSubspace.exists_lift_image :
    ∃ g : (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).subspace.toFunctor ⟶
        (V.subspace.image i).toFunctor,
      g ≫ (V.subspace.image i).ι =
        (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).subspace.ι := by
  have : Mono i := mono_of_isClosedImmersion B S hS i hi
  have h₁ := IntegralClosedSubspace.range_pointsMap_comp_eq_subspacePointSet_pushforward hX hY
    hXdec hi V
  have h₂ : Set.range (pointsMap B S hS _ (V.subspace.image i).ι) =
      Set.range (pointsMap B S hS V.subspace.toFunctor (V.subspace.ι ≫ i)) := by
    rw [← Subfunctor.toImage_ι, pointsMap_comp, Set.range_comp,
      (bijective_pointsMap_of_isIso B S hS (V.subspace.toImage i)).2.range_eq, Set.image_univ]
  exact (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS hX
    (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).isClosedSubspace.1 _
    (IntegralClosedSubspace.isClosedSubspace_image hi V)
    (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).isIntegralSpace.1 _).2
    (h₂.trans h₁).symm.subset

/-- For a closed immersion `i : Y ⟶ X` of algebraic spaces with `X` decent and an integral closed
subspace `V ⊆ Y`, the isomorphism over `X` of `V` with the integral closed subspace `i(V) ⊆ X`
induced by the inclusion of `V` followed by `i`. -/
noncomputable def IntegralClosedSubspace.isoPushforward :
    V.subspace.toFunctor ≅
      (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).subspace.toFunctor :=
  have : Mono i := mono_of_isClosedImmersion B S hS i hi
  have : Mono (V.subspace.ι ≫ i) :=
    mono_of_isClosedImmersion B S hS _ (isClosedImmersion_comp B S hS _ _ V.isClosedSubspace.2 hi)
  have : Mono (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).subspace.ι :=
    mono_of_isClosedImmersion B S hS _
      (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).isClosedSubspace.2
  have h₁ : inv (V.subspace.toImage i) ≫ V.subspace.ι ≫ i = (V.subspace.image i).ι := by
    rw [IsIso.inv_comp_eq, Subfunctor.toImage_ι]
  have hg := (IntegralClosedSubspace.exists_lift_pushforward hX hY hXdec hi V).choose_spec
  have hg' := (IntegralClosedSubspace.exists_lift_image hX hY hXdec hi V).choose_spec
  { hom := (IntegralClosedSubspace.exists_lift_pushforward hX hY hXdec hi V).choose
    inv := (IntegralClosedSubspace.exists_lift_image hX hY hXdec hi V).choose ≫
      inv (V.subspace.toImage i)
    hom_inv_id := by
      rw [← cancel_mono (V.subspace.ι ≫ i), Category.assoc, Category.assoc, h₁, hg', hg,
        Category.id_comp]
    inv_hom_id := by
      rw [← cancel_mono (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).subspace.ι,
        Category.assoc, Category.assoc, hg, h₁, hg', Category.id_comp] }

/-- The isomorphism of an integral closed subspace with its image lies over `X`. -/
@[reassoc (attr := simp)]
theorem IntegralClosedSubspace.isoPushforward_hom_comp_ι :
    (IntegralClosedSubspace.isoPushforward hX hY hXdec hi V).hom ≫
        (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).subspace.ι =
      V.subspace.ι ≫ i :=
  (IntegralClosedSubspace.exists_lift_pushforward hX hY hXdec hi V).choose_spec

end Image

end Equiv

/-! ### The multiplicity under an isomorphism of closed subspaces -/

section Multiplicity

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- For an isomorphism `φ : Y ≅ Y'` of algebraic spaces with `Y'` decent and an integral closed
subspace `V ⊆ Y`, the length of `𝒪_{Y'}` at the canonical geometric point over the generic point
of the image of `V` is the length of `𝒪_Y` at the canonical geometric point over the generic
point of `V`. -/
theorem geometricLength_canonicalGeometricPoint_pushforward_of_iso
    {Y Y' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y)
    (hY' : IsAlgebraicSpace D.site D.base D.base_mem Y')
    (hY'dec : IsDecentSpace D.site D.base D.base_mem Y') (φ : Y ≅ Y')
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    geometricLength D.site D.base D.base_mem ⟨Y', hY'⟩
        (canonicalGeometricPoint D.site D.base D.base_mem Y'
          ((IntegralClosedSubspace.pushforward D.site D.base D.base_mem hY' hY hY'dec
            (isClosedImmersion_of_isIso D.site D.base D.base_mem φ.hom) V).ambientGenericPoint
              D.site D.base D.base_mem))
        (SheafOfModules.unit _) =
      geometricLength D.site D.base D.base_mem ⟨Y, hY⟩
        (canonicalGeometricPoint D.site D.base D.base_mem Y
          (V.ambientGenericPoint D.site D.base D.base_mem)) (SheafOfModules.unit _) := by
  refine (geometricLength_structureSheafModule_eq_of_iso (X := ⟨Y, hY⟩) (Y := ⟨Y', hY'⟩) φ _ _
    ?_).symm
  rw [canonicalGeometricPoint_image, canonicalGeometricPoint_image,
    IntegralClosedSubspace.ambientGenericPoint_pushforward]

/-- Let `Y ⊆ X` and `Y' ⊆ X'` be closed subspaces and `φ : Y ≅ Y'` an isomorphism of algebraic
spaces, with `X'` decent. The multiplicity in `Y'` of the image of an integral closed subspace
`V ⊆ Y` is the multiplicity of `V` in `Y`. -/
theorem closedSubspaceMultiplicity_pushforward_of_iso (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y) (Y' : Subfunctor X')
    (hY' : IsClosedSubspace D.site D.base D.base_mem Y')
    (hX'dec : IsDecentSpace D.site D.base D.base_mem X') (φ : Y.toFunctor ≅ Y'.toFunctor)
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor) :
    closedSubspaceMultiplicity D Y' hY'
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hY'.1 hY.1
          (isDecentSpace_of_relativelyRepresentable D.site D.base D.base_mem hY'.1 _ hY'.2.1
            hX'dec)
          (isClosedImmersion_of_isIso D.site D.base D.base_mem φ.hom) V) =
      closedSubspaceMultiplicity D Y hY V := by
  rw [closedSubspaceMultiplicity, closedSubspaceMultiplicity,
    geometricLength_canonicalGeometricPoint_pushforward_of_iso D hY.1 hY'.1]

end Multiplicity

/-! ### The cycle of a closed subspace pushed forward along a closed immersion -/

section Pushforward

variable (D : BaseSpaceDimensionSituation.{u})
    {X T : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hXdec : IsDecentSpace D.site D.base D.base_mem X) {j : T ⟶ X}
    (hj : IsClosedImmersion D.site D.base D.base_mem j) (sT : T ⟶ D.space) (hT : D.IsGood sT)
    (Y : Subfunctor T) (hY : IsClosedSubspace D.site D.base D.base_mem Y) (k : ℤ)
    (hdim : deltaDimensionSubspace D sT hT Y hY ≤ (k : EInt))

/-- The image in `X` of an integral closed subspace `V ⊆ Y ⊆ T` along `j : T → X` is its image
along the composite closed immersion `Y → T → X`. -/
private theorem pushforward_pushforward_closedSubspace
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor) :
    IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX hT.1 hXdec hj
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hT.1 hY.1
          (D.isDecentSpace_of_isGood sT hT) hY.2 V) =
      IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX hY.1 hXdec
        (isClosedImmersion_comp D.site D.base D.base_mem Y.ι j hY.2 hj) V :=
  IntegralClosedSubspace.pushforward_pushforward hX hT.1 hY.1 hXdec
    (D.isDecentSpace_of_isGood sT hT) rfl hY.2 hj
    (isClosedImmersion_comp D.site D.base D.base_mem Y.ι j hY.2 hj) V

/-- Let `j : T → X` be a closed immersion over the base and `Y ⊆ T` a closed subspace with
`dim_δ(Y) ≤ k`. At the image in `X` of an integral closed subspace `V ⊆ Y`, the coefficient of
`j_*[Y]_k` is the multiplicity of `V` in `Y` if that image has δ-dimension `k`, and zero
otherwise. -/
theorem cycleClosedPushforward_closedSubspaceCycle_apply_pushforward (sX : X ⟶ D.space)
    (hsX : IsLocallyOfFiniteType D.site D.base D.base_mem sX) (hjs : j ≫ sX = sT)
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor) :
    cycleClosedPushforward D hX hT.1 hXdec hj (closedSubspaceCycle D sT hT Y hY k hdim).1
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX hY.1 hXdec
          (isClosedImmersion_comp D.site D.base D.base_mem Y.ι j hY.2 hj) V) =
      if deltaDimension D sX (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX
          hY.1 hXdec (isClosedImmersion_comp D.site D.base D.base_mem Y.ι j hY.2 hj) V) = k
      then closedSubspaceMultiplicity D Y hY V else 0 := by
  rw [← pushforward_pushforward_closedSubspace D hX hXdec hj sT hT Y hY V,
    cycleClosedPushforward_apply_pushforward,
    IntegralClosedSubspace.deltaDimension_pushforward D sX hsX hX hT.1 hXdec hj, hjs]
  exact closedSubspaceCycle_apply_closedSubspaceComponentImage D sT hT Y hY k hdim V

/-- The coefficient of `j_*[Y]_k` at an integral closed subspace of `X` which is not the image of
an integral closed subspace of `Y` is zero. -/
theorem cycleClosedPushforward_closedSubspaceCycle_apply_of_forall_ne
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor,
      IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX hY.1 hXdec
        (isClosedImmersion_comp D.site D.base D.base_mem Y.ι j hY.2 hj) V ≠ Z) :
    cycleClosedPushforward D hX hT.1 hXdec hj (closedSubspaceCycle D sT hT Y hY k hdim).1 Z =
      0 := by
  by_cases h : ∃ Z', IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX hT.1 hXdec
      hj Z' = Z
  · obtain ⟨Z', rfl⟩ := h
    rw [cycleClosedPushforward_apply_pushforward]
    exact closedSubspaceCycle_apply_eq_zero_of_forall_ne D sT hT Y hY k hdim Z' fun V hV =>
      hZ V ((pushforward_pushforward_closedSubspace D hX hXdec hj sT hT Y hY V).symm.trans
        (congrArg _ hV))
  · exact cycleClosedPushforward_apply_of_forall_ne D hX hT.1 hXdec hj _ Z
      fun Z' hZ' => h ⟨Z', hZ'⟩

end Pushforward

section Comparison

variable (D : BaseSpaceDimensionSituation.{u})
    {X T₁ T₂ : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- In Situation 0EDT let `X/B` be good, let `j₁ : T₁ → X` and `j₂ : T₂ → X` be closed
immersions over the base, and let `Y₁ ⊆ T₁` and `Y₂ ⊆ T₂` be closed subspaces with
`dim_δ(Y₁), dim_δ(Y₂) ≤ k`. If an isomorphism `φ : Y₁ ≅ Y₂` of algebraic spaces commutes with
the maps to `X`, then

`(j₁)_*[Y₁]_k = (j₂)_*[Y₂]_k`

in `Z_k(X)`. -/
theorem cycleGroupClosedPushforward_closedSubspaceCycle_eq_of_iso (sX : X ⟶ D.space)
    (hX : D.IsGood sX) {j₁ : T₁ ⟶ X} (hj₁ : IsClosedImmersion D.site D.base D.base_mem j₁)
    {j₂ : T₂ ⟶ X} (hj₂ : IsClosedImmersion D.site D.base D.base_mem j₂) (s₁ : T₁ ⟶ D.space)
    (hT₁ : D.IsGood s₁) (s₂ : T₂ ⟶ D.space) (hT₂ : D.IsGood s₂) (hs₁ : j₁ ≫ sX = s₁)
    (hs₂ : j₂ ≫ sX = s₂) (Y₁ : Subfunctor T₁) (hY₁ : IsClosedSubspace D.site D.base D.base_mem Y₁)
    (Y₂ : Subfunctor T₂) (hY₂ : IsClosedSubspace D.site D.base D.base_mem Y₂)
    (φ : Y₁.toFunctor ≅ Y₂.toFunctor) (hφ : φ.hom ≫ Y₂.ι ≫ j₂ = Y₁.ι ≫ j₁) (k : ℤ)
    (hd₁ : deltaDimensionSubspace D s₁ hT₁ Y₁ hY₁ ≤ (k : EInt))
    (hd₂ : deltaDimensionSubspace D s₂ hT₂ Y₂ hY₂ ≤ (k : EInt)) :
    cycleGroupClosedPushforward D hX.1 hT₁.1 (D.isDecentSpace_of_isGood sX hX) hj₁ sX hX.2.2 s₁
        hs₁ k (closedSubspaceCycle D s₁ hT₁ Y₁ hY₁ k hd₁) =
      cycleGroupClosedPushforward D hX.1 hT₂.1 (D.isDecentSpace_of_isGood sX hX) hj₂ sX hX.2.2
        s₂ hs₂ k (closedSubspaceCycle D s₂ hT₂ Y₂ hY₂ k hd₂) := by
  have hXdec := D.isDecentSpace_of_isGood sX hX
  have hY₁dec : IsDecentSpace D.site D.base D.base_mem Y₁.toFunctor :=
    isDecentSpace_of_relativelyRepresentable D.site D.base D.base_mem hY₁.1 _ hY₁.2.1
      (D.isDecentSpace_of_isGood s₁ hT₁)
  have hY₂dec : IsDecentSpace D.site D.base D.base_mem Y₂.toFunctor :=
    isDecentSpace_of_relativelyRepresentable D.site D.base D.base_mem hY₂.1 _ hY₂.2.1
      (D.isDecentSpace_of_isGood s₂ hT₂)
  have hc₁ := isClosedImmersion_comp D.site D.base D.base_mem Y₁.ι j₁ hY₁.2 hj₁
  have hc₂ := isClosedImmersion_comp D.site D.base D.base_mem Y₂.ι j₂ hY₂.2 hj₂
  have hφ' : φ.inv ≫ Y₁.ι ≫ j₁ = Y₂.ι ≫ j₂ := by
    rw [← hφ, Iso.inv_hom_id_assoc]
  have key : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem Y₁.toFunctor,
      IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY₂.1 hXdec hc₂
          (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hY₂.1 hY₁.1 hY₂dec
            (isClosedImmersion_of_isIso D.site D.base D.base_mem φ.hom) V) =
        IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY₁.1 hXdec hc₁ V :=
    IntegralClosedSubspace.pushforward_pushforward hX.1 hY₂.1 hY₁.1 hXdec hY₂dec hφ
      (isClosedImmersion_of_isIso D.site D.base D.base_mem φ.hom) hc₂ hc₁
  have key' : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem Y₂.toFunctor,
      IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY₁.1 hXdec hc₁
          (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hY₁.1 hY₂.1 hY₁dec
            (isClosedImmersion_of_isIso D.site D.base D.base_mem φ.inv) V) =
        IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY₂.1 hXdec hc₂ V :=
    IntegralClosedSubspace.pushforward_pushforward hX.1 hY₁.1 hY₂.1 hXdec hY₁dec hφ'
      (isClosedImmersion_of_isIso D.site D.base D.base_mem φ.inv) hc₁ hc₂
  refine Subtype.ext (funext fun Z => ?_)
  change cycleClosedPushforward D hX.1 hT₁.1 hXdec hj₁
      (closedSubspaceCycle D s₁ hT₁ Y₁ hY₁ k hd₁).1 Z =
    cycleClosedPushforward D hX.1 hT₂.1 hXdec hj₂ (closedSubspaceCycle D s₂ hT₂ Y₂ hY₂ k hd₂).1 Z
  by_cases h : ∃ V, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY₁.1 hXdec
      hc₁ V = Z
  · obtain ⟨V, rfl⟩ := h
    rw [cycleClosedPushforward_closedSubspaceCycle_apply_pushforward D hX.1 hXdec hj₁ s₁ hT₁ Y₁
      hY₁ k hd₁ sX hX.2.2 hs₁, ← key V,
      cycleClosedPushforward_closedSubspaceCycle_apply_pushforward D hX.1 hXdec hj₂ s₂ hT₂ Y₂
      hY₂ k hd₂ sX hX.2.2 hs₂, closedSubspaceMultiplicity_pushforward_of_iso D Y₁ hY₁ Y₂ hY₂
      (D.isDecentSpace_of_isGood s₂ hT₂) φ V]
  · rw [cycleClosedPushforward_closedSubspaceCycle_apply_of_forall_ne D hX.1 hXdec hj₁ s₁ hT₁ Y₁
      hY₁ k hd₁ Z fun V hV => h ⟨V, hV⟩,
      cycleClosedPushforward_closedSubspaceCycle_apply_of_forall_ne D hX.1 hXdec hj₂ s₂ hT₂ Y₂
      hY₂ k hd₂ Z fun V hV => h ⟨_, (key' V).trans hV⟩]

end Comparison

/-! ### Invariance of the cycle of a closed subspace under an isomorphism -/

section Invariance

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- In Situation 0EDT let `e : X ≅ X'` be an isomorphism of good algebraic spaces over the base,
let `Y ⊆ X` and `Y' ⊆ X'` be closed subspaces of δ-dimension at most `k`, and let `φ : Y ≅ Y'` be
an isomorphism lying over `e`. Then `e` carries the cycle `[Y]_k` to the cycle `[Y']_k`:

`e_*[Y]_k = [Y']_k`

in `Z_k(X')`. -/
theorem cycleGroupClosedPushforward_closedSubspaceCycle_of_iso (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sX' : X' ⟶ D.space) (hX' : D.IsGood sX') (e : X ≅ X')
    (he : e.hom ≫ sX' = sX) (Y : Subfunctor X) (hY : IsClosedSubspace D.site D.base D.base_mem Y)
    (Y' : Subfunctor X') (hY' : IsClosedSubspace D.site D.base D.base_mem Y')
    (φ : Y.toFunctor ≅ Y'.toFunctor) (hφ : φ.hom ≫ Y'.ι = Y.ι ≫ e.hom) (k : ℤ)
    (hd : deltaDimensionSubspace D sX hX Y hY ≤ (k : EInt))
    (hd' : deltaDimensionSubspace D sX' hX' Y' hY' ≤ (k : EInt)) :
    cycleGroupClosedPushforward D hX'.1 hX.1 (D.isDecentSpace_of_isGood sX' hX')
        (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom) sX' hX'.2.2 sX he k
        (closedSubspaceCycle D sX hX Y hY k hd) =
      closedSubspaceCycle D sX' hX' Y' hY' k hd' := by
  rw [cycleGroupClosedPushforward_closedSubspaceCycle_eq_of_iso D sX' hX'
    (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom)
    (isClosedImmersion_of_isIso D.site D.base D.base_mem (𝟙 X')) sX hX sX' hX' he
    (Category.id_comp sX') Y hY Y' hY' φ (by rw [Category.comp_id, hφ]) k hd hd']
  exact Subtype.ext
    (cycleClosedPushforward_id_eq_self D hX'.1 (D.isDecentSpace_of_isGood sX' hX') _ _)

/-- In the situation of
`AlgebraicGeometry.Space.cycleGroupClosedPushforward_closedSubspaceCycle_of_iso`, the coefficient
of `[Y']_k` at the image of an integral closed subspace `Z ⊆ X` is the coefficient of `[Y]_k` at
`Z`. -/
theorem closedSubspaceCycle_apply_equivOfIso (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sX' : X' ⟶ D.space) (hX' : D.IsGood sX') (e : X ≅ X') (he : e.hom ≫ sX' = sX)
    (Y : Subfunctor X) (hY : IsClosedSubspace D.site D.base D.base_mem Y) (Y' : Subfunctor X')
    (hY' : IsClosedSubspace D.site D.base D.base_mem Y') (φ : Y.toFunctor ≅ Y'.toFunctor)
    (hφ : φ.hom ≫ Y'.ι = Y.ι ≫ e.hom) (k : ℤ)
    (hd : deltaDimensionSubspace D sX hX Y hY ≤ (k : EInt))
    (hd' : deltaDimensionSubspace D sX' hX' Y' hY' ≤ (k : EInt))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (closedSubspaceCycle D sX' hX' Y' hY' k hd').1
        (IntegralClosedSubspace.equivOfIso _ _ _ hX.1 hX'.1 (D.isDecentSpace_of_isGood sX hX)
          (D.isDecentSpace_of_isGood sX' hX') e Z) =
      (closedSubspaceCycle D sX hX Y hY k hd).1 Z := by
  rw [← cycleGroupClosedPushforward_closedSubspaceCycle_of_iso D sX hX sX' hX' e he Y hY Y' hY'
    φ hφ k hd hd']
  exact cycleClosedPushforward_apply_pushforward D hX'.1 hX.1 _ _ _ Z

end Invariance

/-! ### The fibre product `W ×_X E` read on `W` and on `E` -/

section FibreProduct

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (E : ClosedSubspaces D.site D.base D.base_mem X)
    (hE : D.IsGood (E.1.ι ≫ p)) (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : D.IsGood (W.subspace.ι ≫ p))

/-- In Situation 0EDT let `X/B` be good, let `E ⊆ X` be a closed subspace and `W ⊆ X` an integral
closed subspace. The fibre product `W ×_X E` is a closed subspace of `W`, and `E ×_X W` is a
closed subspace of `E`; when both have δ-dimension at most `k`, their `k`-cycles have the same
pushforward to `X`:

`(W → X)_*[W ×_X E]_k = (E → X)_*[E ×_X W]_k`. -/
theorem integralClosedSubspacePushforward_closedSubspaceCycle_preimage_eq (k : ℤ)
    (hd : deltaDimensionSubspace D (W.subspace.ι ≫ p) hW (E.1.preimage W.subspace.ι)
      (isClosedSubspace_preimage D.site D.base D.base_mem W.subspace.ι E.1 hp.1
        W.isClosedSubspace.1 E.2) ≤ (k : EInt))
    (hd' : deltaDimensionSubspace D (E.1.ι ≫ p) hE (W.subspace.preimage E.1.ι)
      (isClosedSubspace_preimage D.site D.base D.base_mem E.1.ι W.subspace hp.1 hE.1
        W.isClosedSubspace) ≤ (k : EInt)) :
    integralClosedSubspacePushforward D p hp W k
        (closedSubspaceCycle D (W.subspace.ι ≫ p) hW (E.1.preimage W.subspace.ι)
          (isClosedSubspace_preimage D.site D.base D.base_mem W.subspace.ι E.1 hp.1
            W.isClosedSubspace.1 E.2) k hd) =
      closedSubspaceCyclePushforward D p hp E k
        (closedSubspaceCycle D (E.1.ι ≫ p) hE (W.subspace.preimage E.1.ι)
          (isClosedSubspace_preimage D.site D.base D.base_mem E.1.ι W.subspace hp.1 hE.1
            W.isClosedSubspace) k hd') :=
  cycleGroupClosedPushforward_closedSubspaceCycle_eq_of_iso D p hp W.isClosedSubspace.2 E.2.2
    _ hW _ hE rfl rfl _ _ _ _ (Subfunctor.preimageιIso W.subspace E.1)
    (Subfunctor.preimageιIso_hom_comp_ι W.subspace E.1) k hd hd'

include hp in
/-- If an integral closed subspace `W ⊆ X` of δ-dimension `k + 1` is not contained in the closed
subspace `E ⊆ X`, then the fibre product `W ×_X E`, read as a closed subspace of `W`, has
δ-dimension at most `k`. -/
theorem deltaDimensionSubspace_preimage_integralClosedSubspace_le_of_not_le (k : ℤ)
    (hWk : deltaDimension D p W = k + 1) (hWE : ¬ W.subspace ≤ E.1) :
    deltaDimensionSubspace D (W.subspace.ι ≫ p) hW (E.1.preimage W.subspace.ι)
      (isClosedSubspace_preimage D.site D.base D.base_mem W.subspace.ι E.1 hp.1
        W.isClosedSubspace.1 E.2) ≤ (k : EInt) := by
  have hgen := notMem_subspacePointSet_ambientGenericPoint_of_not_le D hp.1 E.1 E.2 W hWE
  have hlqf : IsLocallyQuasiFinite D.site D.base D.base_mem W.subspace.ι :=
    isLocallyQuasiFinite_of_isImmersion D.site D.base D.base_mem W.subspace.ι
      (isImmersion_of_isClosedImmersion D.site D.base D.base_mem W.isClosedSubspace.2)
  rw [deltaDimensionSubspace_eq_deltaDimensionClosed]
  refine (deltaDimensionClosed_le_coe_iff D (W.subspace.ι ≫ p) hW _ _ k).2 fun t ht => ?_
  rw [subspacePointSet_preimage D.site D.base D.base_mem W.subspace.ι E.1] at ht
  have hcomp : inducedDimensionValue D.site D.base D.base_mem D.delta (W.subspace.ι ≫ p) t =
      inducedDimensionValue D.site D.base D.base_mem D.delta p
        (pointsMap D.site D.base D.base_mem W.subspace.toFunctor W.subspace.ι t) :=
    D.deltaValue_comp_of_isLocallyQuasiFinite hW.1 hp.1 W.subspace.ι p hlqf hp.2.2 t
  rw [hcomp]
  exact inducedDimensionValue_le_of_mem_of_ne D p hp k W hWk ⟨t, rfl⟩ fun h => hgen (h ▸ ht)

/-- For an integral closed subspace `W ⊆ X` of δ-dimension `k + 1` not contained in `E`, the
pushforward to `X` of the cycle `[E ∩ W]_k` on `E` of clause (1)(a) of Stacks 0ER1 is the
pushforward to `X` of the cycle `[W ×_X E]_k` on `W`. -/
theorem integralClosedSubspacePushforward_closedSubspaceCycle_preimage_eq_gysinIntersectionCycle
    (k : ℤ) (hWk : deltaDimension D p W = k + 1) (hWE : ¬ W.subspace ≤ E.1) :
    integralClosedSubspacePushforward D p hp W k
        (closedSubspaceCycle D (W.subspace.ι ≫ p) hW (E.1.preimage W.subspace.ι)
          (isClosedSubspace_preimage D.site D.base D.base_mem W.subspace.ι E.1 hp.1
            W.isClosedSubspace.1 E.2) k
          (deltaDimensionSubspace_preimage_integralClosedSubspace_le_of_not_le D p hp E W hW k
            hWk hWE)) =
      closedSubspaceCyclePushforward D p hp E k (gysinIntersectionCycle D p hp E hE k W hWk hWE) :=
  integralClosedSubspacePushforward_closedSubspaceCycle_preimage_eq D p hp E hE W hW k _ _

end FibreProduct

end AlgebraicGeometry.Space

end
