module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalConnectionTensor
public import
  StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AffineRestrictionPresentation
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfPresentation

/-!
# The ideal of the diagonal of the first-order universal thickening

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], let `F` be a sheaf
of `𝒪_{X/S}`-modules on the big crystalline site and let `(U, T, δ)` be an object of `CRIS(X/S)`
with first-order universal thickening `(U, T', δ')` of [Stacks, Tag 07J2].  Write
`D = Γ(T, 𝒪_T)`, `Ω = Γ(T, Ω_{T/S,δ})`, `M = F(U, T, δ)` and `M' = F(U, T', δ')`.

The base change of `M` along `p₀ : D → Γ(T', 𝒪_{T'}) = D ⊕ Ω`, read through the decomposition
`(D ⊕ Ω) ⊗_D M = M ⊕ (Ω ⊗_D M)`, is the map

`M × (Ω ⊗_D M) ⟶ M'`,  `(s, z) ↦ p₀^* s + diffAction z`,

where `Crystalline.GlobalCrystallineSituation.diffAction : Ω ⊗_D M ⟶ M'` is the canonical map
`ω ⊗ s ↦ ω · p₀^* s` of [Stacks, Tag 07J6].  This map is bijective if and only if `diffAction`
is injective with image the ideal of the diagonal, that is, if and only if the datum
`Crystalline.GlobalCrystallineSituation.FirstOrderIdealBaseChange` exists.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.firstOrderSectionsMap`: the base-change map
  `M × (Ω ⊗_D M) ⟶ M'`, `(s, z) ↦ p₀^* s + diffAction z`.
* `Crystalline.GlobalCrystallineSituation.firstOrderSectionsEquiv`: the base-change map as an
  additive equivalence, when it is bijective.
* `Crystalline.GlobalCrystallineSituation.firstOrderIdealBaseChangeOfBijective`: the datum of
  [Stacks, Tag 07J6] obtained from bijectivity of the base-change map.

## Main results

* `Crystalline.GlobalCrystallineSituation.moduleSiteRestrict_siteι_firstOrderSectionsMap`: the
  composite of the base-change map with restriction along the diagonal is the first projection,
  `i^* (p₀^* s + diffAction z) = s`.
* `Crystalline.GlobalCrystallineSituation.firstOrderSectionsMap_zero_left`: the base-change map
  restricted to the second summand is `diffAction`.
* `Crystalline.GlobalCrystallineSituation.injective_diffAction_of_bijective` and
  `Crystalline.GlobalCrystallineSituation.eq_diffAction_of_bijective`: `diffAction` is injective
  with image the ideal of the diagonal when the base-change map is bijective.
* `Crystalline.GlobalCrystallineSituation.bijective_firstOrderSectionsMap_of_datum`: conversely,
  the datum makes the base-change map bijective.
* `Crystalline.GlobalCrystallineSituation.bijective_firstOrderSectionsMap_unit`: the base-change
  map is bijective for `F = 𝒪_{X/S}`.
* `Crystalline.GlobalCrystallineSituation.isAffine_firstOrderThickeningObject`: `T'` is affine
  when `T` is.

## References

* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace PresheafOfModules
open scoped AlgebraicGeometry TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}
variable (M : SheafOfModules.{u} (crystallineStructureSheaf S))

/-! ### The base-change map on global sections -/

/-- **The base change of the sections of `F` along `p₀`**, read through the direct sum
decomposition `Γ(T', 𝒪_{T'}) = Γ(T, 𝒪_T) ⊕ Ω` of [Stacks, Tag 07J2]: the map

`Γ(T, F_T) × (Ω ⊗ Γ(T, F_T)) ⟶ Γ(T', F_{T'})`,  `(s, z) ↦ p₀^* s + diffAction z`.

The first summand is the restriction along `p₀`, the second the canonical map
`Crystalline.GlobalCrystallineSituation.diffAction` of [Stacks, Tag 07J6]. -/
def firstOrderSectionsMap (A : Thickening S) :
    M.val.obj (op A) × (crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) →+
      M.val.obj (op (firstOrderThickeningObject S A)) :=
  AddMonoidHom.mk'
    (fun x ↦ moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) x.1 + diffAction M A x.2)
    (fun x y ↦ by
      change moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) (x.1 + y.1) +
          diffAction M A (x.2 + y.2) = _
      rw [map_add, map_add]
      abel)

/-- The base-change map sends `(s, z)` to `p₀^* s + diffAction z`. -/
@[simp]
theorem firstOrderSectionsMap_apply (A : Thickening S) (s : M.val.obj (op A))
    (z : crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) :
    firstOrderSectionsMap M A (s, z) =
      moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) s + diffAction M A z := rfl

/-- **On the second summand the base-change map is the canonical map of [Stacks, Tag 07J6].** -/
theorem firstOrderSectionsMap_zero_left (A : Thickening S)
    (z : crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) :
    firstOrderSectionsMap M A (0, z) = diffAction M A z := by
  rw [firstOrderSectionsMap_apply, map_zero, zero_add]

/-- **Restriction along `p₀` is a section of restriction along the diagonal.**  The relation
`p₀ ∘ i = id` of [Stacks, Tag 07J2] in `CRIS(X/S)`. -/
theorem moduleSiteRestrict_siteι_siteP₀ (A : Thickening S) (s : M.val.obj (op A)) :
    moduleSiteRestrict M (firstOrderThickeningSiteι S A)
        (moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) s) = s := by
  rw [moduleSiteRestrict_comp, firstOrderThickeningSiteι_comp_P₀, moduleSiteRestrict_id]

/-- **Restriction along the diagonal recovers the first component.**  Restricting
`p₀^* s + diffAction z` along `i : T ⟶ T'` gives `s`. -/
theorem moduleSiteRestrict_siteι_firstOrderSectionsMap (A : Thickening S)
    (x : M.val.obj (op A) × (crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A))) :
    moduleSiteRestrict M (firstOrderThickeningSiteι S A) (firstOrderSectionsMap M A x) = x.1 := by
  show moduleSiteRestrict M (firstOrderThickeningSiteι S A)
      (moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) x.1 + diffAction M A x.2) = _
  rw [map_add, moduleSiteRestrict_siteι_siteP₀, moduleSiteRestrict_siteι_diffAction, add_zero]

/-! ### The datum from bijectivity -/

/-- The base-change map, as an additive equivalence, once it is known to be bijective. -/
def firstOrderSectionsEquiv (A : Thickening S)
    (h : Function.Bijective (firstOrderSectionsMap M A)) :
    M.val.obj (op A) × (crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) ≃+
      M.val.obj (op (firstOrderThickeningObject S A)) :=
  AddEquiv.ofBijective (firstOrderSectionsMap M A) h

/-- **The canonical map of [Stacks, Tag 07J6] is injective** as soon as the base-change map
is. -/
theorem injective_diffAction_of_bijective (A : Thickening S)
    (h : Function.Injective (firstOrderSectionsMap M A)) :
    Function.Injective (diffAction M A) := by
  intro z z' hz
  have hx : firstOrderSectionsMap M A (0, z) = firstOrderSectionsMap M A (0, z') := by
    rw [firstOrderSectionsMap_zero_left, firstOrderSectionsMap_zero_left, hz]
  exact congrArg Prod.snd (h hx)

/-- If `x` is killed by restriction along the diagonal after the base-change map, the map
agrees with `diffAction` on its second component. -/
private theorem firstOrderSectionsMap_eq_diffAction (A : Thickening S)
    (x : M.val.obj (op A) × (crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)))
    (hx : moduleSiteRestrict M (firstOrderThickeningSiteι S A) (firstOrderSectionsMap M A x) = 0) :
    firstOrderSectionsMap M A x = diffAction M A x.2 := by
  rw [moduleSiteRestrict_siteι_firstOrderSectionsMap] at hx
  rw [← firstOrderSectionsMap_zero_left, ← hx]

/-- **A section of `F` over `(U, T', δ')` killed by restriction along the diagonal is in the image
of the canonical map of [Stacks, Tag 07J6]**, as soon as the base-change map is surjective. -/
theorem eq_diffAction_of_bijective (A : Thickening S)
    (h : Function.Surjective (firstOrderSectionsMap M A))
    (t : M.val.obj (op (firstOrderThickeningObject S A)))
    (ht : moduleSiteRestrict M (firstOrderThickeningSiteι S A) t = 0) :
    ∃ z, diffAction M A z = t := by
  obtain ⟨x, hx⟩ := h t
  exact ⟨x.2, (firstOrderSectionsMap_eq_diffAction M A x (hx ▸ ht)).symm.trans hx⟩

/-- **The datum of [Stacks, Tag 07J6] from bijectivity of the base-change map on global
sections.**  The inverse of
`Crystalline.GlobalCrystallineSituation.diffAction` on the ideal of the diagonal is the second
component of the inverse of
`Crystalline.GlobalCrystallineSituation.firstOrderSectionsMap`. -/
def firstOrderIdealBaseChangeOfBijective (A : Thickening S)
    (h : Function.Bijective (firstOrderSectionsMap M A)) :
    FirstOrderIdealBaseChange M A where
  proj := (AddMonoidHom.snd _ _).comp (firstOrderSectionsEquiv M A h).symm.toAddMonoidHom
  proj_diffAction z := by
    have he : (firstOrderSectionsEquiv M A h) (0, z) = diffAction M A z :=
      firstOrderSectionsMap_zero_left M A z
    change ((firstOrderSectionsEquiv M A h).symm (diffAction M A z)).2 = z
    rw [← he, AddEquiv.symm_apply_apply]
  diffAction_proj t ht := by
    change diffAction M A ((firstOrderSectionsEquiv M A h).symm t).2 = t
    have hx : (firstOrderSectionsEquiv M A h) ((firstOrderSectionsEquiv M A h).symm t) = t :=
      AddEquiv.apply_symm_apply _ t
    have h1 : ((firstOrderSectionsEquiv M A h).symm t).1 = 0 := by
      rw [← moduleSiteRestrict_siteι_firstOrderSectionsMap M A
        ((firstOrderSectionsEquiv M A h).symm t)]
      change moduleSiteRestrict M (firstOrderThickeningSiteι S A)
          ((firstOrderSectionsEquiv M A h) ((firstOrderSectionsEquiv M A h).symm t)) = 0
      rw [hx, ht]
    rw [← firstOrderSectionsMap_zero_left, ← h1]
    exact hx

/-- **The datum of [Stacks, Tag 07J6] makes the base-change map bijective.** -/
theorem bijective_firstOrderSectionsMap_of_datum (A : Thickening S)
    (h : FirstOrderIdealBaseChange M A) :
    Function.Bijective (firstOrderSectionsMap M A) := by
  refine ⟨fun x y hxy => ?_, fun t => ?_⟩
  · have h1 : x.1 = y.1 := by
      rw [← moduleSiteRestrict_siteι_firstOrderSectionsMap M A x, hxy,
        moduleSiteRestrict_siteι_firstOrderSectionsMap]
    refine Prod.ext h1 (h.injective_diffAction ?_)
    change moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) x.1 + diffAction M A x.2 =
      moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) y.1 + diffAction M A y.2 at hxy
    rw [h1] at hxy
    exact add_left_cancel hxy
  · refine ⟨(moduleSiteRestrict M (firstOrderThickeningSiteι S A) t,
      h.proj (t - moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A)
        (moduleSiteRestrict M (firstOrderThickeningSiteι S A) t))), ?_⟩
    have hker : moduleSiteRestrict M (firstOrderThickeningSiteι S A)
        (t - moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A)
          (moduleSiteRestrict M (firstOrderThickeningSiteι S A) t)) = 0 := by
      rw [map_sub, moduleSiteRestrict_siteι_siteP₀, sub_self]
    rw [firstOrderSectionsMap_apply, h.diffAction_proj _ hker]
    abel

/-! ### Two consequences -/

/-- **At `F = 𝒪_{X/S}` the base-change map is bijective**, for every object. -/
theorem bijective_firstOrderSectionsMap_unit (A : Thickening S) :
    Function.Bijective
      (firstOrderSectionsMap (SheafOfModules.unit (crystallineStructureSheaf S)) A) :=
  bijective_firstOrderSectionsMap_of_datum _ A (firstOrderIdealBaseChangeUnit A)

/-- **The ambient scheme of the first-order universal thickening of an affine object is
affine.** -/
theorem isAffine_firstOrderThickeningObject (A : Thickening S)
    [IsAffine A.thickening.target.scheme] :
    IsAffine (firstOrderThickeningObject S A).thickening.target.scheme :=
  Stacks.Thickenings.isAffine_of_isThickening
    (firstOrderThickeningι_isThickening A.thickening.target S.S.scheme A.toBase.hom)

/-! ### Underlying spaces and quasi-coherence -/

/-- **`p₀ : T' ⟶ T` is the identity on underlying topological spaces.** -/
theorem firstOrderThickeningSiteP₀_base (A : Thickening S) :
    (firstOrderThickeningSiteP₀ S A).targetHom.hom.base = 𝟙 _ := rfl

/-- **`p₁ : T' ⟶ T` is the identity on underlying topological spaces.** -/
theorem firstOrderThickeningSiteP₁_base (A : Thickening S) :
    (firstOrderThickeningSiteP₁ S A).targetHom.hom.base = 𝟙 _ := rfl

/-- **The diagonal `i : T ⟶ T'` is the identity on underlying topological spaces.** -/
theorem firstOrderThickeningSiteι_base (A : Thickening S) :
    (firstOrderThickeningSiteι S A).targetHom.hom.base = 𝟙 _ := rfl

/-- **The restriction of a locally quasi-coherent sheaf of `𝒪_{X/S}`-modules to the ambient
scheme of an object is quasi-coherent**, as a module on that scheme
(`AlgebraicGeometry.Scheme.Modules.IsQuasicoherent`). -/
theorem isQuasicoherent_ambientModuleRestriction
    {M : SheafOfModules.{u} (crystallineStructureSheaf S)} (hM : IsLocallyQuasiCoherent M)
    (A : Thickening S) : (Thickening.ambientModuleRestriction M A).IsQuasicoherent :=
  (isQuasicoherentOnSite_ambientModuleRestriction hM A).isQuasicoherent

end Crystalline.GlobalCrystallineSituation

end

end
