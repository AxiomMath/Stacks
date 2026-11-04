module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GlobalSectionDivisorCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinClosedSubspaceIntersectionAdditivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinPushforwardFirstChernCapCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceCycleTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorCycleOfGoodDifference
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RegularSectionZeroSchemeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.TrivialRestrictionGysin
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemeOfCanonicalSection
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemePullback

/-!
# Intersecting the cycle of a closed subspace with an invertible sheaf along a regular section

In Situation 0EDT let `X/B` be good and let `ℒ` be an invertible `𝒪_X`-module. Let `Y ⊆ X` be a
closed subspace with `dim_δ(Y) ≤ k + 1` and let `s ∈ Γ(Y, ℒ|_Y)` be a regular section, with zero
scheme `Z(s) ⊆ Y` (Stacks 0845). **Stacks 0EQN** asserts

`c₁(ℒ) ∩ [Y]_{k+1} = [Z(s)]_k`  in `CH_k(X)`.

The proof is the source's. Write `[Y]_{k+1} = ∑ n_i [Y_i]` over the irreducible components `Y_i`
of `Y` of δ-dimension `k + 1`, viewed as integral closed subspaces `W_i ⊆ X`. The restriction
`s_i = s|_{W_i}` is a nonzero section of `ℒ|_{W_i}`: otherwise `W_i → Y` would factor through
`Z(s)`, whose δ-dimension is at most `k`. By Stacks 0EQF on the integral space `W_i`, the cycle
`[Z(s_i)]_k` is the Weil divisor of `s_i`, which differs from the component cycle
`c₁(ℒ|_{W_i}) ∩ [W_i]` of Stacks 0EQJ by a principal divisor (Stacks 0EPT). Hence
`c₁(ℒ) ∩ [Y]_{k+1} = ∑ n_i [Z(s_i)]_k` in `CH_k(X)`. Finally `Z(s_i)` is the inverse image of
`Z(s)` along `W_i → Y` (Stacks 0846), so `∑ n_i [Z(s_i)]_k` is the pushforward to `X` of the
right-hand side of Stacks 0EQL on `Y`, which is `[Z(s)]_k`.

## Main definitions

* `AlgebraicGeometry.Space.closedSubspaceModuleRestrict`: the restriction `ℒ|_Y` of an
  `𝒪_X`-module to a closed subspace.
* `AlgebraicGeometry.Space.closedSubspaceComponentImageSection`: the restriction `s|_W` of a
  section of `ℒ|_Y` to the image `W ⊆ X` of an integral closed subspace of `Y`, as a section of
  `ℒ|_W`.

## Main results

* `AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_vanishingLocus_eq_canonicalDivisorCycleAt`:
  Stacks 0EQF at the canonical choices, in degree `k`.
* `AlgebraicGeometry.Space.closedSubspaceComponentImageSection_ne_zero`: `s|_W ≠ 0`.
* `cycleClosedPushforward_vanishingLocus_closedSubspaceComponentImageSection`:
  the cycles of `Z(s|_W)` on `W` and of `Z(s|_V)` on `V` have the same pushforward to `X`.
* `chowClassCanonical_firstChernCapCycleMap_closedSubspaceCycle_eq_vanishingLocus`:
  **Stacks 0EQN**, in the Chow group of Stacks 0EQ6 at the canonical embeddings of Stacks 0ENK.
* `AlgebraicGeometry.Space.canonicalFirstChernCap_closedSubspaceCycle_eq_chowClass_vanishingLocus`:
  its image in the coarser quotient `AlgebraicGeometry.Space.chowGroup`.

## Implementation notes

The cycle `[Z(s)]_k` lives on `Y`, where `Z(s)` is a closed subspace, and is read on `X` through
the pushforward along the closed immersion `Y → X`; this is the identification of `Z_k(Y)` with
the `k`-cycles of `X` supported on `Y` that the source makes implicitly.

The Chow group is that of Stacks 0EQ6 in a universe at least `u + 1`: the relation of rational
equivalence there admits families indexed by the integral closed subspaces of `Y`.

## References

* [Stacks Project, Tag 0EQN](https://stacks.math.columbia.edu/tag/0EQN)
* [Stacks Project, Tag 0EQF](https://stacks.math.columbia.edu/tag/0EQF)
* [Stacks Project, Tag 0EQL](https://stacks.math.columbia.edu/tag/0EQL)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 0846](https://stacks.math.columbia.edu/tag/0846)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u v

namespace CategoryTheory.Subfunctor

/-- For an isomorphism `e : P ≅ Q` and a morphism `b : P ⟶ R`, the inverse image of a subfunctor
`A ⊆ R` along `e⁻¹ ≫ b` is isomorphic to its inverse image along `b`, through `e⁻¹`. -/
@[simps]
def preimageIsoPreimageComp {C : Type*} [Category C] {P Q R : C ⥤ Type v} (e : P ≅ Q)
    (b : P ⟶ R) (A : Subfunctor R) :
    (A.preimage (e.inv ≫ b)).toFunctor ≅ (A.preimage b).toFunctor where
  hom := { app := fun U => ↾fun x => ⟨e.inv.app U x.1, x.2⟩
           naturality := fun U V f => by
             ext x
             apply Subtype.ext
             change e.inv.app V (Q.map f x.1) = P.map f (e.inv.app U x.1)
             exact NatTrans.naturality_apply e.inv f x.1 }
  inv := { app := fun U => ↾fun y => ⟨e.hom.app U y.1, by
              change b.app U (e.inv.app U (e.hom.app U y.1)) ∈ A.obj U
              simpa using y.2⟩
           naturality := fun U V f => by
             ext y
             apply Subtype.ext
             change e.hom.app V (P.map f y.1) = Q.map f (e.hom.app U y.1)
             exact NatTrans.naturality_apply e.hom f y.1 }
  hom_inv_id := by
    ext U x
    exact Subtype.ext (show e.hom.app U (e.inv.app U x.1) = x.1 by simp)
  inv_hom_id := by
    ext U x
    exact Subtype.ext (show e.inv.app U (e.hom.app U x.1) = x.1 by simp)

/-- The isomorphism `CategoryTheory.Subfunctor.preimageIsoPreimageComp` lies over `e⁻¹`. -/
theorem preimageIsoPreimageComp_hom_comp_ι {C : Type*} [Category C] {P Q R : C ⥤ Type v}
    (e : P ≅ Q) (b : P ⟶ R) (A : Subfunctor R) :
    (preimageIsoPreimageComp e b A).hom ≫ (A.preimage b).ι =
      (A.preimage (e.inv ≫ b)).ι ≫ e.inv :=
  rfl

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Stacks 0EQF at the canonical choices, in degree `k` -/

section IntegralCase

variable (D : BaseSpaceDimensionSituation.{u})

/-- **The zero cycle of a nonzero section of an invertible module on an integral space is its
canonical Weil divisor.** In Situation 0EDT let `T/B` be good and integral with
`dim_δ(T) = k + 1`, let `ℳ` be an invertible `𝒪_T`-module and `σ ∈ Γ(T, ℳ)` nonzero. Then the
coefficient family of `[Z(σ)]_k` is that of the Weil divisor `div_ℳ(σ)` of Stacks 0EQE at the
canonical choices, `AlgebraicGeometry.Space.canonicalDivisorCycleAt`, of the meromorphic section
that `σ` is. This is the first identity of Stacks 0EQF, read in `Z_k(T)`. -/
theorem cycleCoeffOfClosedSubspace_vanishingLocus_eq_canonicalDivisorCycleAt
    {T : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sT : T ⟶ D.space)
    (hT : D.IsGood sT) (hint : IsIntegralSpace D.site D.base D.base_mem T)
    (M : Modules.{u, u} D.site D.base D.base_mem T hT.1)
    (hM : IsInvertibleModule (⟨T, hT.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) M)
    {σ : M.sections} (hσ : σ ≠ 0) {k : ℤ}
    (hk : deltaDimensionClosed D sT hT Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) :
    cycleCoeffOfClosedSubspace D sT hT (vanishingLocus D sT hT M σ).1
        (vanishingLocus D sT hT M σ).2 k
        (canonicalGeometricPoint D.site D.base D.base_mem _) =
      (canonicalDivisorCycleAt D sT hT hint M hM
        (globalSectionMeromorphic D.site D.base D.base_mem hT.1 M σ)
        ((isRegularMeromorphicSection_iff_ne_zero D.site D.base D.base_mem hT.1 hint
          (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sT hT) M hM _).2
          (globalSectionMeromorphic_ne_zero D.site D.base D.base_mem hT.1 M hM hσ)) hk).1 := by
  have h := zeroSchemeCycleCoeff_eq_invertibleDivisorCoefficients_globalSection D sT hT hint M
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM) hk hσ _
    (canonicalGeometricPoint_liesOver D _)
  rw [add_sub_cancel_right] at h
  exact h

end IntegralCase

/-! ### The restriction of a section of `ℒ|_Y` to the image of a component of `Y` -/

section ComponentImage

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (Y : ClosedSubspaces D.site D.base D.base_mem X)

/-- The restriction `ℒ|_Y` of an `𝒪_X`-module to a closed subspace `Y ⊆ X`: its inverse image of
Stacks 03LU along the closed immersion `Y → X`. -/
abbrev closedSubspaceModuleRestrict :
    Modules.{u, u} D.site D.base D.base_mem Y.1.toFunctor Y.2.1 :=
  (modulePullback D.site D.base D.base_mem
    (closedSubspaceHom D.site D.base D.base_mem hX.1 Y.1 Y.2)).obj L

/-- The restriction `ℒ|_Y` of an invertible `𝒪_X`-module to a closed subspace is invertible. -/
private theorem isInvertible_closedSubspaceModuleRestrict
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L) :
    AlgebraicGeometry.SheafOfModules.IsInvertible
      (structureCommRings D.site D.base D.base_mem ⟨Y.1.toFunctor, Y.2.1⟩)
      (structureRingSheaf D.site D.base D.base_mem ⟨Y.1.toFunctor, Y.2.1⟩).property
      (closedSubspaceModuleRestrict D sX hX L Y) :=
  isInvertible_modulePullback_obj D.site D.base D.base_mem
    (closedSubspaceHom D.site D.base D.base_mem hX.1 Y.1 Y.2) L
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL)

/-- A closed immersion of spaces is locally quasi-finite. -/
private theorem isLocallyQuasiFinite_of_isClosedImmersion
    {A B : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {f : A ⟶ B}
    (hf : IsClosedImmersion D.site D.base D.base_mem f) :
    IsLocallyQuasiFinite D.site D.base D.base_mem f :=
  isLocallyQuasiFinite_of_isImmersion D.site D.base D.base_mem _
    (isImmersion_of_isClosedImmersion D.site D.base D.base_mem hf)

/-- For an integral closed subspace `V ⊆ Y` of a closed subspace `Y ⊆ X`, the morphism from the
image `W = V → Y → X` of `V` in `X` to `Y`: the inverse of the isomorphism `V ≅ W` over `X`,
followed by the inclusion of `V`. -/
def closedSubspaceComponentImageHom
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor) :
    (⟨(closedSubspaceComponentImage D sX hX Y.1 Y.2 V).subspace.toFunctor,
        (closedSubspaceComponentImage D sX hX Y.1 Y.2 V).isClosedSubspace.1⟩ :
      AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y.1.toFunctor, Y.2.1⟩ :=
  ObjectProperty.homMk ((IntegralClosedSubspace.isoPushforward hX.1 Y.2.1
    (D.isDecentSpace_of_isGood sX hX) Y.2.2 V).inv ≫ V.subspace.ι)

/-- The morphism `W → Y` lies over `X`. -/
theorem closedSubspaceComponentImageHom_comp_closedSubspaceHom
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor) :
    closedSubspaceComponentImageHom D sX hX Y V ≫
        closedSubspaceHom D.site D.base D.base_mem hX.1 Y.1 Y.2 =
      closedSubspaceHom D.site D.base D.base_mem hX.1
        (closedSubspaceComponentImage D sX hX Y.1 Y.2 V).subspace
        (closedSubspaceComponentImage D sX hX Y.1 Y.2 V).isClosedSubspace := by
  refine ObjectProperty.hom_ext _ ?_
  show ((IntegralClosedSubspace.isoPushforward hX.1 Y.2.1 (D.isDecentSpace_of_isGood sX hX)
    Y.2.2 V).inv ≫ V.subspace.ι) ≫ Y.1.ι = _
  rw [Category.assoc, ← IntegralClosedSubspace.isoPushforward_hom_comp_ι hX.1 Y.2.1
    (D.isDecentSpace_of_isGood sX hX) Y.2.2 V, Iso.inv_hom_id_assoc]
  rfl

/-- The comparison `(W → Y)^*(ℒ|_Y) ≅ ℒ|_W` of inverse images along `W → Y → X` and `W → X`. -/
def closedSubspaceComponentImageRestrictIso
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor) :
    (modulePullback D.site D.base D.base_mem (closedSubspaceComponentImageHom D sX hX Y V)).obj
        (closedSubspaceModuleRestrict D sX hX L Y) ≅
      integralClosedSubspaceRestrict D sX hX L (closedSubspaceComponentImage D sX hX Y.1 Y.2 V) :=
  (modulePullbackCompIso D.site D.base D.base_mem (closedSubspaceComponentImageHom D sX hX Y V)
      (closedSubspaceHom D.site D.base D.base_mem hX.1 Y.1 Y.2)).app L ≪≫
    eqToIso (by rw [closedSubspaceComponentImageHom_comp_closedSubspaceHom D sX hX Y V])

/-- **The restriction `s|_W` of a section `s ∈ Γ(Y, ℒ|_Y)` to the image `W ⊆ X` of an integral
closed subspace `V ⊆ Y`**, as a section of `ℒ|_W`: the inverse image of `s` along `W → Y`, read
in `ℒ|_W` through `AlgebraicGeometry.Space.closedSubspaceComponentImageRestrictIso`. -/
def closedSubspaceComponentImageSection (s : (closedSubspaceModuleRestrict D sX hX L Y).sections)
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor) :
    (integralClosedSubspaceRestrict D sX hX L
      (closedSubspaceComponentImage D sX hX Y.1 Y.2 V)).sections :=
  SheafOfModules.sectionsMap (closedSubspaceComponentImageRestrictIso D sX hX L Y V).hom
    (modulePullbackSections D.site D.base D.base_mem
      (closedSubspaceComponentImageHom D sX hX Y V) (closedSubspaceModuleRestrict D sX hX L Y) s)

/-- **The zero scheme of `s|_W` is the inverse image of `Z(s)` along `W → Y`** (Stacks 0846,
part (2)). -/
theorem zeroScheme_closedSubspaceComponentImageSection
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (s : (closedSubspaceModuleRestrict D sX hX L Y).sections)
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor) :
    zeroScheme D.site D.base D.base_mem
        ⟨(closedSubspaceComponentImage D sX hX Y.1 Y.2 V).subspace.toFunctor,
          (closedSubspaceComponentImage D sX hX Y.1 Y.2 V).isClosedSubspace.1⟩
        (integralClosedSubspaceRestrict D sX hX L (closedSubspaceComponentImage D sX hX Y.1 Y.2 V))
        (closedSubspaceComponentImageSection D sX hX L Y s V) =
      ⟨(zeroScheme D.site D.base D.base_mem ⟨Y.1.toFunctor, Y.2.1⟩
          (closedSubspaceModuleRestrict D sX hX L Y) s).1.preimage
          (closedSubspaceComponentImageHom D sX hX Y V).hom,
        isClosedSubspace_preimage D.site D.base D.base_mem _ _ Y.2.1
          (closedSubspaceComponentImage D sX hX Y.1 Y.2 V).isClosedSubspace.1
          (zeroScheme D.site D.base D.base_mem ⟨Y.1.toFunctor, Y.2.1⟩
            (closedSubspaceModuleRestrict D sX hX L Y) s).2⟩ :=
  (zeroScheme_eq_of_iso D.site D.base D.base_mem _ _ _ _ _
    (closedSubspaceComponentImageRestrictIso D sX hX L Y V) rfl).symm.trans
    (zeroScheme_modulePullbackSections D.site D.base D.base_mem _ _ _
      (isInvertible_closedSubspaceModuleRestrict D sX hX L Y hL) s
      (closedSubspaceComponentImageHom D sX hX Y V))

/-- **The restriction of a regular section to the image of a component does not vanish.** Let
`Y ⊆ X` be a closed subspace with `dim_δ(Y) ≤ k + 1`, let `s ∈ Γ(Y, ℒ|_Y)` be a regular section
and let `V ⊆ Y` be an integral closed subspace whose image `W ⊆ X` has δ-dimension `k + 1`. Then
`s|_W ≠ 0`.

If `s|_W` vanished, `W → Y` would factor through `Z(s)` (Stacks 0846, part (2)), so every point of
`W` would have δ-value at most `dim_δ(Z(s)) ≤ k`
(`AlgebraicGeometry.Space.deltaDimensionSubspace_vanishingLocus_le_of_isRegularSection`), against
`dim_δ(W) = k + 1`. -/
theorem closedSubspaceComponentImageSection_ne_zero
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (s : (closedSubspaceModuleRestrict D sX hX L Y).sections)
    (hs : AlgebraicGeometry.IsRegularSection
      (structureCommRings D.site D.base D.base_mem ⟨Y.1.toFunctor, Y.2.1⟩)
      (structureRingSheaf D.site D.base D.base_mem ⟨Y.1.toFunctor, Y.2.1⟩).property s) {k : ℤ}
    (hdim : deltaDimensionSubspace D sX hX Y.1 Y.2 ≤ ((k + 1 : ℤ) : EInt))
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor)
    (hV : deltaDimension D sX (closedSubspaceComponentImage D sX hX Y.1 Y.2 V) = k + 1) :
    closedSubspaceComponentImageSection D sX hX L Y s V ≠ 0 := by
  intro h0
  have hYg := isGood_closedSubspace D sX hX Y
  have hinvY := isInvertible_closedSubspaceModuleRestrict D sX hX L Y hL
  have h1 : modulePullbackSections D.site D.base D.base_mem
      (closedSubspaceComponentImageHom D sX hX Y V) (closedSubspaceModuleRestrict D sX hX L Y) s =
      0 :=
    (sectionsMap_eq_zero_iff_of_iso D.site D.base D.base_mem
      (closedSubspaceComponentImageRestrictIso D sX hX L Y V) _).1 h0
  obtain ⟨h, hh⟩ := (modulePullbackSections_eq_zero_iff_exists_comp_eq_zeroScheme D.site D.base
    D.base_mem ⟨Y.1.toFunctor, Y.2.1⟩
    ⟨(closedSubspaceComponentImage D sX hX Y.1 Y.2 V).subspace.toFunctor,
      (closedSubspaceComponentImage D sX hX Y.1 Y.2 V).isClosedSubspace.1⟩
    (closedSubspaceModuleRestrict D sX hX L Y) hinvY s
    (closedSubspaceComponentImageHom D sX hX Y V)).1 h1
  have hZdim := deltaDimensionSubspace_vanishingLocus_le_of_isRegularSection D (Y.1.ι ≫ sX) hYg
    (closedSubspaceModuleRestrict D sX hX L Y) hinvY s hs
    (deltaDimensionClosed_univ_closedSubspace_le D sX hX Y _ hdim)
  rw [deltaDimensionSubspace_eq_deltaDimensionClosed] at hZdim
  have hgW : (closedSubspaceComponentImageHom D sX hX Y V).hom ≫ Y.1.ι =
      (closedSubspaceComponentImage D sX hX Y.1 Y.2 V).subspace.ι :=
    congrArg (fun m => m.hom)
      (closedSubspaceComponentImageHom_comp_closedSubspaceHom D sX hX Y V)
  have hglqf : IsLocallyQuasiFinite D.site D.base D.base_mem
      (closedSubspaceComponentImageHom D sX hX Y V).hom :=
    isLocallyQuasiFinite_of_isClosedImmersion D
      (isClosedImmersion_comp D.site D.base D.base_mem _ _
        (isClosedImmersion_of_isIso D.site D.base D.base_mem _) V.isClosedSubspace.2)
  have hle : deltaDimensionClosed D
      ((closedSubspaceComponentImage D sX hX Y.1 Y.2 V).subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX (closedSubspaceComponentImage D sX hX Y.1 Y.2 V))
      Set.univ isClosed_univ ≤ (k : EInt) := by
    refine (deltaDimensionClosed_le_coe_iff D _ _ _ _ k).2 fun t _ => ?_
    have hcomp := D.deltaValue_comp_of_isLocallyQuasiFinite
      (closedSubspaceComponentImage D sX hX Y.1 Y.2 V).isClosedSubspace.1 hYg.1
      (closedSubspaceComponentImageHom D sX hX Y V).hom (Y.1.ι ≫ sX) hglqf hYg.2.2 t
    rw [← Category.assoc, hgW] at hcomp
    show D.deltaValue ((closedSubspaceComponentImage D sX hX Y.1 Y.2 V).subspace.ι ≫ sX) t ≤ k
    rw [hcomp]
    refine (deltaDimensionClosed_le_coe_iff D _ _ _ _ k).1 hZdim _ ⟨pointsMap D.site D.base
      D.base_mem _ h.hom t, ?_⟩
    rw [← pointsMap_comp_apply]
    exact congrArg (fun m => pointsMap D.site D.base D.base_mem _ m.hom t) hh
  rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX
    (closedSubspaceComponentImage D sX hX Y.1 Y.2 V), hV] at hle
  have := WithBotTop.coe_le_coe.1 hle
  omega

/-- `[Y]_k` depends only on the subfunctor `Y`: equal closed subspaces have equal cycles. -/
theorem closedSubspaceCycle_congr {Z Z' : Subfunctor X} (h : Z = Z')
    (hZ : IsClosedSubspace D.site D.base D.base_mem Z)
    (hZ' : IsClosedSubspace D.site D.base D.base_mem Z') (k : ℤ)
    (hd : deltaDimensionSubspace D sX hX Z hZ ≤ (k : EInt))
    (hd' : deltaDimensionSubspace D sX hX Z' hZ' ≤ (k : EInt)) :
    closedSubspaceCycle D sX hX Z hZ k hd = closedSubspaceCycle D sX hX Z' hZ' k hd' := by
  subst h
  rfl

/-- **`dim_δ(Z(s)) ≤ k` for a regular section `s` of `ℒ|_Y` on a closed subspace `Y ⊆ X` with
`dim_δ(Y) ≤ k + 1`**, so that the cycle `[Z(s)]_k` of Stacks 0EE9 is defined. This is
`AlgebraicGeometry.Space.deltaDimensionSubspace_vanishingLocus_le_of_isRegularSection` on `Y`. -/
theorem deltaDimensionSubspace_vanishingLocus_closedSubspaceModuleRestrict_le
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (s : (closedSubspaceModuleRestrict D sX hX L Y).sections)
    (hs : AlgebraicGeometry.IsRegularSection
      (structureCommRings D.site D.base D.base_mem ⟨Y.1.toFunctor, Y.2.1⟩)
      (structureRingSheaf D.site D.base D.base_mem ⟨Y.1.toFunctor, Y.2.1⟩).property s) {k : ℤ}
    (hdim : deltaDimensionSubspace D sX hX Y.1 Y.2 ≤ ((k + 1 : ℤ) : EInt)) :
    deltaDimensionSubspace D (Y.1.ι ≫ sX) (isGood_closedSubspace D sX hX Y)
        (vanishingLocus D (Y.1.ι ≫ sX) (isGood_closedSubspace D sX hX Y)
          (closedSubspaceModuleRestrict D sX hX L Y) s).1
        (vanishingLocus D (Y.1.ι ≫ sX) (isGood_closedSubspace D sX hX Y)
          (closedSubspaceModuleRestrict D sX hX L Y) s).2 ≤ (k : EInt) :=
  deltaDimensionSubspace_vanishingLocus_le_of_isRegularSection D (Y.1.ι ≫ sX)
    (isGood_closedSubspace D sX hX Y) (closedSubspaceModuleRestrict D sX hX L Y)
    (isInvertible_closedSubspaceModuleRestrict D sX hX L Y hL) s hs
    (deltaDimensionClosed_univ_closedSubspace_le D sX hX Y _ hdim)

/-- **The cycle of `Z(s|_W)` pushed forward to `X` is the cycle of `Z(s|_V)` pushed forward to
`X`.** Let `Y ⊆ X` be a closed subspace with `dim_δ(Y) ≤ k + 1`, `s ∈ Γ(Y, ℒ|_Y)` a regular
section and `V ⊆ Y` an integral closed subspace with image `W ⊆ X`. Then

`(W → X)_*[Z(s|_W)]_k = (Y → X)_*(V → Y)_*[Z(s|_V)]_k`

as coefficient families on `X`. Both zero schemes are inverse images of `Z(s)`, along `W → Y` and
along `V → Y` (Stacks 0846, part (2)), and the isomorphism `V ≅ W` over `X` identifies them; the
cycles of isomorphic closed subspaces have the same pushforward
(`AlgebraicGeometry.Space.cycleGroupClosedPushforward_closedSubspaceCycle_eq_of_iso`), both
δ-dimensions being at most `dim_δ(Z(s)) ≤ k`. -/
theorem cycleClosedPushforward_vanishingLocus_closedSubspaceComponentImageSection
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (s : (closedSubspaceModuleRestrict D sX hX L Y).sections)
    (hs : AlgebraicGeometry.IsRegularSection
      (structureCommRings D.site D.base D.base_mem ⟨Y.1.toFunctor, Y.2.1⟩)
      (structureRingSheaf D.site D.base D.base_mem ⟨Y.1.toFunctor, Y.2.1⟩).property s) {k : ℤ}
    (hdim : deltaDimensionSubspace D sX hX Y.1 Y.2 ≤ ((k + 1 : ℤ) : EInt))
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor) :
    cycleClosedPushforward D hX.1
        (closedSubspaceComponentImage D sX hX Y.1 Y.2 V).isClosedSubspace.1
        (D.isDecentSpace_of_isGood sX hX)
        (closedSubspaceComponentImage D sX hX Y.1 Y.2 V).isClosedSubspace.2
        (cycleCoeffOfClosedSubspace D
          ((closedSubspaceComponentImage D sX hX Y.1 Y.2 V).subspace.ι ≫ sX)
          (isGood_integralClosedSubspace D sX hX (closedSubspaceComponentImage D sX hX Y.1 Y.2 V))
          (vanishingLocus D _ (isGood_integralClosedSubspace D sX hX
            (closedSubspaceComponentImage D sX hX Y.1 Y.2 V))
            (integralClosedSubspaceRestrict D sX hX L
              (closedSubspaceComponentImage D sX hX Y.1 Y.2 V))
            (closedSubspaceComponentImageSection D sX hX L Y s V)).1
          (vanishingLocus D _ (isGood_integralClosedSubspace D sX hX
            (closedSubspaceComponentImage D sX hX Y.1 Y.2 V))
            (integralClosedSubspaceRestrict D sX hX L
              (closedSubspaceComponentImage D sX hX Y.1 Y.2 V))
            (closedSubspaceComponentImageSection D sX hX L Y s V)).2 k
          (canonicalGeometricPoint D.site D.base D.base_mem _)) =
      cycleClosedPushforward D hX.1 Y.2.1 (D.isDecentSpace_of_isGood sX hX) Y.2.2
        (componentZeroCycleCoeff D (Y.1.ι ≫ sX) (isGood_closedSubspace D sX hX Y)
          (closedSubspaceModuleRestrict D sX hX L Y) s k V
          (canonicalGeometricPoint D.site D.base D.base_mem _)) := by
  have hXdec := D.isDecentSpace_of_isGood sX hX
  have hYg := isGood_closedSubspace D sX hX Y
  have hYdec := D.isDecentSpace_of_isGood _ hYg
  have hWg := isGood_integralClosedSubspace D sX hX (closedSubspaceComponentImage D sX hX Y.1 Y.2 V)
  have hVg := isGood_integralClosedSubspace D (Y.1.ι ≫ sX) hYg V
  have hinvY := isInvertible_closedSubspaceModuleRestrict D sX hX L Y hL
  have hZdim :=
    deltaDimensionSubspace_vanishingLocus_closedSubspaceModuleRestrict_le D sX hX L Y hL s hs hdim
  -- the two zero schemes as inverse images of `Z(s)`
  have h₁ := zeroScheme_closedSubspaceComponentImageSection D sX hX L Y hL s V
  have h₂ := zeroScheme_modulePullbackSections D.site D.base D.base_mem ⟨Y.1.toFunctor, Y.2.1⟩
    ⟨V.subspace.toFunctor, V.isClosedSubspace.1⟩ (closedSubspaceModuleRestrict D sX hX L Y) hinvY s
    (closedSubspaceHom D.site D.base D.base_mem Y.2.1 V.subspace V.isClosedSubspace)
  -- the morphism `W → Y` and the isomorphism `V ≅ W`
  set φ := IntegralClosedSubspace.isoPushforward hX.1 Y.2.1 hXdec Y.2.2 V with hφdef
  have hgW : (φ.inv ≫ V.subspace.ι) ≫ Y.1.ι =
      (closedSubspaceComponentImage D sX hX Y.1 Y.2 V).subspace.ι :=
    congrArg (fun m => m.hom) (closedSubspaceComponentImageHom_comp_closedSubspaceHom D sX hX Y V)
  have hglqf : IsLocallyQuasiFinite D.site D.base D.base_mem (φ.inv ≫ V.subspace.ι) :=
    isLocallyQuasiFinite_of_isClosedImmersion D
      (isClosedImmersion_comp D.site D.base D.base_mem _ _
        (isClosedImmersion_of_isIso D.site D.base D.base_mem _) V.isClosedSubspace.2)
  have hVlqf := isLocallyQuasiFinite_of_isClosedImmersion D V.isClosedSubspace.2
  -- the δ-dimension bounds
  have hd₁' := deltaDimensionSubspace_preimage_le_of_isLocallyQuasiFinite D (Y.1.ι ≫ sX) hYg
    (φ.inv ≫ V.subspace.ι) _ hWg (by rw [← Category.assoc, hgW]) hglqf _
    (vanishingLocus D (Y.1.ι ≫ sX) hYg (closedSubspaceModuleRestrict D sX hX L Y) s).2 hZdim
  have hd₂' := deltaDimensionSubspace_preimage_le_of_isLocallyQuasiFinite D (Y.1.ι ≫ sX) hYg
    V.subspace.ι _ hVg rfl hVlqf _
    (vanishingLocus D (Y.1.ι ≫ sX) hYg (closedSubspaceModuleRestrict D sX hX L Y) s).2 hZdim
  have hd₁ : deltaDimensionSubspace D _ hWg
      (vanishingLocus D _ hWg
        (integralClosedSubspaceRestrict D sX hX L (closedSubspaceComponentImage D sX hX Y.1 Y.2 V))
        (closedSubspaceComponentImageSection D sX hX L Y s V)).1
      (vanishingLocus D _ hWg
        (integralClosedSubspaceRestrict D sX hX L (closedSubspaceComponentImage D sX hX Y.1 Y.2 V))
        (closedSubspaceComponentImageSection D sX hX L Y s V)).2 ≤ (k : EInt) := by
    rw [vanishingLocus, h₁]
    exact hd₁'
  have hd₂ : deltaDimensionSubspace D _ hVg (componentVanishingLocus D (Y.1.ι ≫ sX) hYg
      (closedSubspaceModuleRestrict D sX hX L Y) s V).1
      (componentVanishingLocus D (Y.1.ι ≫ sX) hYg
        (closedSubspaceModuleRestrict D sX hX L Y) s V).2 ≤ (k : EInt) := by
    rw [componentVanishingLocus, h₂]
    exact hd₂'
  -- the isomorphism of the two inverse images over `X`
  have hj₁ := (closedSubspaceComponentImage D sX hX Y.1 Y.2 V).isClosedSubspace.2
  have hj₂ : IsClosedImmersion D.site D.base D.base_mem (V.subspace.ι ≫ Y.1.ι) :=
    isClosedImmersion_comp D.site D.base D.base_mem _ _ V.isClosedSubspace.2 Y.2.2
  have hgW' : φ.inv ≫ V.subspace.ι ≫ Y.1.ι =
      (closedSubspaceComponentImage D sX hX Y.1 Y.2 V).subspace.ι := by
    rw [← Category.assoc]
    exact hgW
  have key := cycleGroupClosedPushforward_closedSubspaceCycle_eq_of_iso D sX hX hj₁ hj₂ _ hWg _
    hVg rfl (Category.assoc _ _ _) _ _ _ _
    (Subfunctor.preimageIsoPreimageComp φ V.subspace.ι
      (vanishingLocus D (Y.1.ι ≫ sX) hYg (closedSubspaceModuleRestrict D sX hX L Y) s).1)
    (by
      rw [← Category.assoc, Subfunctor.preimageIsoPreimageComp_hom_comp_ι, Category.assoc,
        hgW'])
    k hd₁' hd₂'
  have e₁ := closedSubspaceCycle_congr D _ hWg (congrArg Subtype.val h₁) _ _ k hd₁ hd₁'
  have e₂ := closedSubspaceCycle_congr D _ hVg (congrArg Subtype.val h₂) _ _ k hd₂ hd₂'
  rw [componentZeroCycleCoeff, cycleClosedPushforward_cycleClosedPushforward D hX.1 Y.2.1 hVg.1
    hXdec hYdec rfl V.isClosedSubspace.2 Y.2.2 hj₂]
  have := congrArg Subtype.val
    ((congrArg (cycleGroupClosedPushforward D hX.1 hWg.1 hXdec hj₁ sX hX.2.2 _ rfl k) e₁).trans
      (key.trans (congrArg (cycleGroupClosedPushforward D hX.1 hVg.1 hXdec hj₂ sX hX.2.2 _
        (Category.assoc _ _ _) k) e₂).symm))
  exact this

end ComponentImage

/-! ### Stacks 0EQN -/

section RegularSection

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (Y : ClosedSubspaces D.site D.base D.base_mem X)

/-- **An integral closed subspace of `Y` of maximal δ-dimension is an irreducible component of
`Y`**, when `dim_δ(Y) ≤ k + 1`: its generic point has maximal δ-value. -/
theorem isIrreducibleComponent_of_deltaDimension_eq {k : ℤ}
    (hdim : deltaDimensionSubspace D sX hX Y.1 Y.2 ≤ ((k + 1 : ℤ) : EInt))
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor)
    (hV : deltaDimension D (Y.1.ι ≫ sX) V = k + 1) :
    IsIrreducibleComponent D.site D.base D.base_mem (isGood_closedSubspace D sX hX Y).1
      V.subspace := by
  refine ⟨V.isClosedSubspace, V.isIntegralSpace, ?_⟩
  have hgen := V.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem
    (isGood_closedSubspace D sX hX Y).1
  show subspacePointSet D.site D.base D.base_mem _ V.subspace ∈ _
  rw [← hgen.def]
  exact closure_singleton_mem_irreducibleComponents_of_deltaValue_eq D (Y.1.ι ≫ sX)
    (isGood_closedSubspace D sX hX Y) (deltaDimensionClosed_univ_closedSubspace_le D sX hX Y _ hdim)
    _ hV

/-- **Stacks 0EQN.** In Situation 0EDT let `X/B` be good and let `ℒ` be an invertible
`𝒪_X`-module. Let `Y ⊆ X` be a closed subspace with `dim_δ(Y) ≤ k + 1` and let
`s ∈ Γ(Y, ℒ|_Y)` be a regular section. Then

`c₁(ℒ) ∩ [Y]_{k+1} = [Z(s)]_k`  in `CH_k(X)`.

Here `[Y]_{k+1}` is the cycle of Stacks 0EE9 of `Y` on `X`,
`AlgebraicGeometry.Space.closedSubspaceCycle`; `c₁(ℒ) ∩ -` is the cap product of Stacks 0EQJ,
the cycle-level operation `AlgebraicGeometry.Space.firstChernCapCycleMap` at the canonical
component rule `AlgebraicGeometry.Space.canonicalFirstChernRule`, its class taken afterwards;
`Z(s) ⊆ Y` is the zero scheme of Stacks 0845, whose `k`-cycle (defined because `dim_δ(Z(s)) ≤ k`,
`AlgebraicGeometry.Space.deltaDimensionSubspace_vanishingLocus_closedSubspaceModuleRestrict_le`) is
read on `X` through the inclusion `Y → X`; and `CH_k(X)` is the Chow group of Stacks 0EQ6,
`AlgebraicGeometry.Space.chowGroupCanonical`, whose rational equivalences are sums of principal
divisors at the canonical embeddings of Stacks 0ENK.

The proof is the source's. Write `[Y]_{k+1} = ∑ n_i [Y_i]` over the irreducible components `Y_i`
of `Y` of δ-dimension `k + 1`. The restriction `s_i = s|_{Y_i}` is nonzero
(`AlgebraicGeometry.Space.closedSubspaceComponentImageSection_ne_zero`), so by Stacks 0EQF the
cycle `[Z(s_i)]_k` is the Weil divisor of `s_i`
(`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_vanishingLocus_eq_canonicalDivisorCycleAt`),
which differs from the component cycle `c₁(ℒ|_{Y_i}) ∩ [Y_i]` of the cap product by a principal
divisor on `Y_i` at the canonical embeddings (Stacks 0EPT,
`AlgebraicGeometry.Space.isPrincipalDivisorCycleOfGood_zsmul_canonicalDivisorCycleAt_sub`). So
`c₁(ℒ) ∩ [Y]_{k+1} = ∑ n_i [Z(s_i)]_k` in `CH_k(X)`, and the right side is `[Z(s)]_k` by
Stacks 0EQL on `Y`
(`cycleCoeffOfClosedSubspace_vanishingLocus_eq_componentZeroCycleSumCoeff_of_isRegularSection`),
the zero schemes `Z(s_i)` being inverse images of `Z(s)` (Stacks 0846). -/
@[stacks 0EQN "c₁(ℒ) ∩ [Y]_{k+1} = [Z(s)]_k in CH_k(X), for X/B good, ℒ invertible, Y ⊆ X a \
closed subspace with dim_δ(Y) ≤ k + 1 and s ∈ Γ(Y, ℒ|_Y) a regular section; c₁(ℒ) ∩ - is Stacks \
0EQJ at the canonical choices, [Y]_{k+1} and [Z(s)]_k are Stacks 0EE9 (the latter on Y, read on X \
through Y → X), Z(s) is Stacks 0845 and CH_k(X) is Stacks 0EQ6; nothing carried"]
theorem chowClassCanonical_firstChernCapCycleMap_closedSubspaceCycle_eq_vanishingLocus
    (s : (closedSubspaceModuleRestrict D sX hX L Y).sections)
    (hs : AlgebraicGeometry.IsRegularSection
      (structureCommRings D.site D.base D.base_mem ⟨Y.1.toFunctor, Y.2.1⟩)
      (structureRingSheaf D.site D.base D.base_mem ⟨Y.1.toFunctor, Y.2.1⟩).property s) {k : ℤ}
    (hdim : deltaDimensionSubspace D sX hX Y.1 Y.2 ≤ ((k + 1 : ℤ) : EInt)) :
    chowClassCanonical.{max (u + 1) v} D sX hX k
        (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX L hL k)
          (closedSubspaceCycle D sX hX Y.1 Y.2 (k + 1) hdim)) =
      chowClassCanonical.{max (u + 1) v} D sX hX k (closedSubspaceCyclePushforward D sX hX Y k
        (closedSubspaceCycle D (Y.1.ι ≫ sX) (isGood_closedSubspace D sX hX Y)
          (vanishingLocus D (Y.1.ι ≫ sX) (isGood_closedSubspace D sX hX Y)
            (closedSubspaceModuleRestrict D sX hX L Y) s).1
          (vanishingLocus D (Y.1.ι ≫ sX) (isGood_closedSubspace D sX hX Y)
            (closedSubspaceModuleRestrict D sX hX L Y) s).2 k
          (deltaDimensionSubspace_vanishingLocus_closedSubspaceModuleRestrict_le D sX hX L Y hL s
            hs hdim))) := by
  classical
  have hXdec := D.isDecentSpace_of_isGood sX hX
  have hYg := isGood_closedSubspace D sX hX Y
  have hinvY := isInvertible_closedSubspaceModuleRestrict D sX hX L Y hL
  have hdimY := deltaDimensionClosed_univ_closedSubspace_le D sX hX Y _ hdim
  set α := closedSubspaceCycle D sX hX Y.1 Y.2 (k + 1) hdim with hα
  -- the family of the components of `Y` of δ-dimension `k + 1`, read in `X`
  let I₀ := {V : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor //
    α.1 (closedSubspaceComponentImage D sX hX Y.1 Y.2 V) ≠ 0}
  let I := ULift.{v} I₀
  let Zf : I → IntegralClosedSubspace D.site D.base D.base_mem X := fun i =>
    closedSubspaceComponentImage D sX hX Y.1 Y.2 i.down.1
  have hZinj : Function.Injective Zf := fun i j h => ULift.ext _ _ (Subtype.ext
    (IntegralClosedSubspace.injective_pushforward D.site D.base D.base_mem hX.1 Y.2.1 hXdec
      Y.2.2 h))
  have hZfin : LocallyFinite fun i : I =>
      subspacePointSet D.site D.base D.base_mem X (Zf i).subspace :=
    (α.2.1.comp_injective hZinj).subset fun i => by
      simp only [Function.comp_apply]
      rw [if_neg (show α.1 (Zf i) ≠ 0 from i.down.2)]
  have hdimZ : ∀ i : I, deltaDimension D sX (Zf i) = k + 1 := fun i => α.2.2 _ i.down.2
  have hcover : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      α.1 W ≠ 0 → ∃ i, Zf i = W := by
    intro W hW
    by_contra h
    push Not at h
    exact hW (closedSubspaceCycle_apply_eq_zero_of_forall_ne D sX hX Y.1 Y.2 (k + 1) hdim W
      fun V hV => h ⟨⟨V, by rw [hV]; exact hW⟩⟩ hV)
  -- the restrictions `s_i` of `s` and their Weil divisors
  have hσ : ∀ i : I, closedSubspaceComponentImageSection D sX hX L Y s i.down.1 ≠ 0 := fun i =>
    closedSubspaceComponentImageSection_ne_zero D sX hX L Y hL s hs hdim i.down.1 (hdimZ i)
  have hk : ∀ i : I, deltaDimensionClosed D ((Zf i).subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX (Zf i)) Set.univ isClosed_univ =
        ((k + 1 : ℤ) : EInt) := fun i => by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX (Zf i), hdimZ i]
  have hreg : ∀ i : I, IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem _
      (isGood_integralClosedSubspace D sX hX (Zf i)).1
      (integralClosedSubspaceRestrict D sX hX L (Zf i))
      (globalSectionMeromorphic D.site D.base D.base_mem _ _
        (closedSubspaceComponentImageSection D sX hX L Y s i.down.1)) := fun i =>
    (isRegularMeromorphicSection_iff_ne_zero D.site D.base D.base_mem _ (Zf i).isIntegralSpace
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _
        (isGood_integralClosedSubspace D sX hX (Zf i))) _
      (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hL (Zf i)) _).2
      (globalSectionMeromorphic_ne_zero D.site D.base D.base_mem _ _
        (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hL (Zf i)) (hσ i))
  let G : ∀ i : I, CycleGroup D ((Zf i).subspace.ι ≫ sX) k := fun i =>
    canonicalDivisorCycleAt D _ (isGood_integralClosedSubspace D sX hX (Zf i))
      (Zf i).isIntegralSpace (integralClosedSubspaceRestrict D sX hX L (Zf i))
      (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hL (Zf i))
      (globalSectionMeromorphic D.site D.base D.base_mem _ _
        (closedSubspaceComponentImageSection D sX hX L Y s i.down.1)) (hreg i) (hk i)
  -- a sum over a subtype carrying the support is the full sum
  have reindex : ∀ (p : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor → Prop)
      (f : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor → ℤ),
      (∀ V, f V ≠ 0 → p V) → ∑ᶠ j : Subtype p, f j = ∑ᶠ V, f V := by
    intro p f h
    rw [finsum_subtype_eq_finsum_cond]
    refine finsum_congr fun V => ?_
    by_cases hV : p V
    · rw [finsum_eq_if, if_pos hV]
    · rw [finsum_eq_if, if_neg hV]
      by_contra hne
      exact hV (h V (Ne.symm hne))
  -- `[Z(s)]_k = ∑ n_i [Z(s_i)]_k`, by Stacks 0EQL on `Y`
  have hR : closedSubspaceCyclePushforward D sX hX Y k
      (closedSubspaceCycle D (Y.1.ι ≫ sX) hYg
        (vanishingLocus D (Y.1.ι ≫ sX) hYg (closedSubspaceModuleRestrict D sX hX L Y) s).1
        (vanishingLocus D (Y.1.ι ≫ sX) hYg (closedSubspaceModuleRestrict D sX hX L Y) s).2 k
        (deltaDimensionSubspace_vanishingLocus_closedSubspaceModuleRestrict_le D sX hX L Y hL s
          hs hdim)) =
      cycleFamilySum D sX hX Zf hZfin k (fun i => α.1 (Zf i) • G i) := by
    refine Subtype.ext (funext fun T => ?_)
    rw [cycleFamilySum_apply]
    let f := fun V : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor =>
      α.1 (closedSubspaceComponentImage D sX hX Y.1 Y.2 V) *
        cycleClosedPushforward D hX.1 Y.2.1 hXdec Y.2.2
          (componentZeroCycleCoeff D (Y.1.ι ≫ sX) hYg (closedSubspaceModuleRestrict D sX hX L Y) s
            k V (canonicalGeometricPoint D.site D.base D.base_mem _)) T
    have hterm : ∀ i : I,
        (integralClosedSubspacePushforward D sX hX (Zf i) k (α.1 (Zf i) • G i)).1 T =
          f i.down.1 := fun i => by
      rw [map_zsmul]
      have hD := cycleClosedPushforward_vanishingLocus_closedSubspaceComponentImageSection D sX hX
        L Y hL s hs hdim i.down.1
      rw [cycleCoeffOfClosedSubspace_vanishingLocus_eq_canonicalDivisorCycleAt D _
        (isGood_integralClosedSubspace D sX hX (Zf i)) (Zf i).isIntegralSpace _
        (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hL (Zf i)) (hσ i)
        (hk i)] at hD
      exact congrArg (fun x => α.1 (Zf i) * x) (congrFun hD T)
    rw [finsum_congr hterm]
    refine Eq.trans ?_ (finsum_comp_equiv (Equiv.ulift : I ≃ I₀) (f := fun i : I₀ => f i.1)).symm
    show cycleClosedPushforward D hX.1 Y.2.1 hXdec Y.2.2
      (cycleCoeffOfClosedSubspace D (Y.1.ι ≫ sX) hYg
        (vanishingLocus D (Y.1.ι ≫ sX) hYg (closedSubspaceModuleRestrict D sX hX L Y) s).1
        (vanishingLocus D (Y.1.ι ≫ sX) hYg (closedSubspaceModuleRestrict D sX hX L Y) s).2 k
        (canonicalGeometricPoint D.site D.base D.base_mem _)) T = _
    rw [cycleCoeffOfClosedSubspace_vanishingLocus_eq_componentZeroCycleSumCoeff_of_isRegularSection
      D (Y.1.ι ≫ sX) hYg _ s k hinvY hs hdimY]
    refine (cycleClosedPushforward_finsum_mul D hX.1 Y.2.1 hXdec Y.2.2
      (fun V : ComponentsOfDeltaDimension D (Y.1.ι ≫ sX) hYg (k + 1) =>
        fundamentalCycleCoeff D (Y.1.ι ≫ sX) hYg (k + 1)
          (canonicalGeometricPoint D.site D.base D.base_mem _) V.1)
      (fun V => componentZeroCycleCoeff D (Y.1.ι ≫ sX) hYg
        (closedSubspaceModuleRestrict D sX hX L Y) s k V.1
        (canonicalGeometricPoint D.site D.base D.base_mem _)) T).trans ?_
    -- both sides are the sum over all integral closed subspaces of `Y`
    have hn : ∀ V : ComponentsOfDeltaDimension D (Y.1.ι ≫ sX) hYg (k + 1),
        fundamentalCycleCoeff D (Y.1.ι ≫ sX) hYg (k + 1)
          (canonicalGeometricPoint D.site D.base D.base_mem _) V.1 =
        α.1 (closedSubspaceComponentImage D sX hX Y.1 Y.2 V.1) := fun V => by
      rw [hα, closedSubspaceCycle_apply_closedSubspaceComponentImage,
        deltaDimension_closedSubspaceComponentImage]
      rfl
    rw [finsum_congr fun V => congrArg (· * _) (hn V)]
    have hsupp : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor,
        α.1 (closedSubspaceComponentImage D sX hX Y.1 Y.2 V) ≠ 0 →
          IsIrreducibleComponent D.site D.base D.base_mem hYg.1 V.subspace ∧
            deltaDimension D (Y.1.ι ≫ sX) V = k + 1 := fun V hV => by
      have hVk : deltaDimension D (Y.1.ι ≫ sX) V = k + 1 := by
        rw [← deltaDimension_closedSubspaceComponentImage D sX hX Y.1 Y.2 V]
        exact α.2.2 _ hV
      exact ⟨isIrreducibleComponent_of_deltaDimension_eq D sX hX Y hdim V hVk, hVk⟩
    refine (reindex _ f fun V hV => hsupp V (left_ne_zero_of_mul hV)).trans ?_
    exact (reindex _ f fun V hV => left_ne_zero_of_mul hV).symm
  -- the component cycles of the cap product against the Weil divisors of the `s_i`
  rw [firstChernCapCycleMap_eq_cycleFamilySum D sX hX k _ α Zf hZinj
    hZfin hdimZ hcover, hR, ← sub_eq_zero, ← map_sub, ← cycleFamilySum_sub]
  refine chowClassCanonical_cycleFamilySum_eq_zero.{max (u + 1) v} D sX hX k Zf hZfin _ hdimZ
    fun i => ?_
  rw [← smul_sub]
  exact isPrincipalDivisorCycleOfGood_zsmul_canonicalDivisorCycleAt_sub D _
    (isGood_integralClosedSubspace D sX hX (Zf i)) (Zf i).isIntegralSpace _
    (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hL (Zf i)) _ _ _ _ _ _

/-- Stacks 0EQN in the Chow group `AlgebraicGeometry.Space.chowGroup`, whose rational equivalences
quantify the embedding `R(W) → Q(𝒪^h_{W,ξ})` existentially: the image of
`chowClassCanonical_firstChernCapCycleMap_closedSubspaceCycle_eq_vanishingLocus`
under the comparison map `AlgebraicGeometry.Space.chowGroupCanonicalToChowGroup`. -/
theorem canonicalFirstChernCap_closedSubspaceCycle_eq_chowClass_vanishingLocus
    (s : (closedSubspaceModuleRestrict D sX hX L Y).sections)
    (hs : AlgebraicGeometry.IsRegularSection
      (structureCommRings D.site D.base D.base_mem ⟨Y.1.toFunctor, Y.2.1⟩)
      (structureRingSheaf D.site D.base D.base_mem ⟨Y.1.toFunctor, Y.2.1⟩).property s) {k : ℤ}
    (hdim : deltaDimensionSubspace D sX hX Y.1 Y.2 ≤ ((k + 1 : ℤ) : EInt)) :
    canonicalFirstChernCap.{u, max (u + 1) v} D sX hX L hL k
        (closedSubspaceCycle D sX hX Y.1 Y.2 (k + 1) hdim) =
      chowClass.{max (u + 1) v} D sX hX k (closedSubspaceCyclePushforward D sX hX Y k
        (closedSubspaceCycle D (Y.1.ι ≫ sX) (isGood_closedSubspace D sX hX Y)
          (vanishingLocus D (Y.1.ι ≫ sX) (isGood_closedSubspace D sX hX Y)
            (closedSubspaceModuleRestrict D sX hX L Y) s).1
          (vanishingLocus D (Y.1.ι ≫ sX) (isGood_closedSubspace D sX hX Y)
            (closedSubspaceModuleRestrict D sX hX L Y) s).2 k
          (deltaDimensionSubspace_vanishingLocus_closedSubspaceModuleRestrict_le D sX hX L Y hL s
            hs hdim))) :=
  congrArg (chowGroupCanonicalToChowGroup.{max (u + 1) v} D sX hX k)
    (chowClassCanonical_firstChernCapCycleMap_closedSubspaceCycle_eq_vanishingLocus D sX hX L
      hL Y s hs hdim)

end RegularSection

end AlgebraicGeometry.Space

end
