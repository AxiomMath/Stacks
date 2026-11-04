module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ZariskiRiemannCenterStrictHenselization
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Variety

/-!
# The closure of the generic point in a proper model

Let `B` be a domain with fraction field `K` and `M = (Y, f, j)` a proper model of
`η = Spec K` over `Spec B`. The scheme-theoretic image `Z ⊆ Y` of `j : η ⟶ Y` — the closure of
`j(η)` with its reduced structure — is again a proper model (`ProperModel.closureModel`), refining
`M` through the closed immersion `Z ⟶ Y`. It is integral with generic point `j(η)`, so for a
valuation ring `V ⊆ K` containing `B` the map `𝒪_{Z, z} ⟶ V` at the center `z` is injective: it
is the injective specialization map `𝒪_{Z, z} ⟶ 𝒪_{Z, j(η)}` into the function field, followed by a
map of fields. Since `Z ⟶ Y` is a closed immersion, `𝒪_{Y, y} ⟶ 𝒪_{Z, z}` is surjective, so the
images `A_Y` and `A_Z` of the local rings in `V` agree. Hence

* `A_Y ≅ 𝒪_{Z, z}` for every model `Y` (`ProperModel.closureCenterStalkEquiv`), and the models
  on which the stalk map at the center is injective are cofinal
  (`ProperModel.exists_refinement_centerStalkMap_injective`);
* on such a model, `A_Y^{sh}` is a strict henselization of `𝒪_{Y, y}`
  (`ProperModel.exists_isStrictHenselization_stalk`).

This is the reduction to integral models in Gabber's Zariski–Riemann argument for Travaux de
Gabber, Exposé XVIII-A, Corollary 1.2 (last remark of §2): the colimit of the `A_Y` may be taken
over models on which `A_Y` is the local ring `𝒪_{Y, y_Y(V)}` itself.

## Main definitions

* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.closureModel`: the scheme-theoretic image of
  `j`, as a proper model.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.closureRefinement`: its refinement of `M`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.centerStalkEquiv`: `𝒪_{Y, y} ≅ A_Y` when the
  stalk map at the center is injective.

## Main results

* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.centerStalkMap_injective_of_isIntegral`:
  on an integral model with generic point `j(η)` the stalk map at the center is injective.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.centerRange_closureModel`: `A_Z = A_Y`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.exists_refinement_centerStalkMap_injective`:
  every model is refined by an integral model with the same `A_Y` and injective stalk map.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.exists_isIntegral_of_mem_centerRanges`:
  every `A_Y` is the image of an injective stalk map at the center of an integral model.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.exists_isStrictHenselization_stalk`:
  `(𝒪_{Y, y})^{sh} = A_Y^{sh}` on such models.

## Implementation notes

The identification of strict henselizations is by transport along the isomorphism
`𝒪_{Y, y} ≅ A_Y` (Stacks 04GQ,
`Stacks.StrictHenselization.exists_isStrictHenselization_of_ringEquiv`): it is the case of
zero kernel of Stacks 05WS (`IsLocalRing.strictHenselization_quotient`), where the quotient map
is an isomorphism.

## References

* [StacksProject 01R5](https://stacks.math.columbia.edu/tag/01R5)
* [StacksProject 04GQ](https://stacks.math.columbia.edu/tag/04GQ)
* [StacksProject 05WS](https://stacks.math.columbia.edu/tag/05WS)
* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing Stacks.StrictHenselization

universe u v w

namespace AlgebraicGeometry

/-- **On an integral scheme, a stalk maps injectively to the function field**, and so does its
composite with any ring map out of the function field into a nontrivial ring. -/
theorem Scheme.injective_stalkSpecializes_comp_of_isIntegral {X : Scheme.{u}} [IsIntegral X]
    {x y : X} (hx : x = genericPoint X) (h : x ⤳ y) {R : CommRingCat.{u}} [Nontrivial R]
    (g : X.presheaf.stalk x ⟶ R) :
    Function.Injective (X.presheaf.stalkSpecializes h ≫ g).hom := by
  subst hx
  have hg : Function.Injective g.hom := (g.hom : X.functionField →+* R).injective
  rw [CommRingCat.hom_comp, RingHom.coe_comp]
  refine hg.comp ?_
  rw [injective_iff_map_eq_zero]
  intro s hs
  obtain ⟨U, hyU, a, rfl⟩ := X.presheaf.exists_germ_eq s
  have h1 : (X.presheaf.germ U (genericPoint X) (h.mem_open U.isOpen hyU)).hom a = 0 := by
    rw [← X.presheaf.germ_stalkSpecializes hyU h, CommRingCat.hom_comp, RingHom.comp_apply]
    exact hs
  have ha : a = 0 :=
    germ_injective_of_isIntegral X _ _ (h1.trans (map_zero _).symm)
  rw [ha, map_zero]

namespace Scheme.ZariskiRiemann

variable {B : Type u} [CommRing B] [IsDomain B]

namespace ProperModel

variable (M : ProperModel B) (V : ValuationSubring (FractionRing B))
  (hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V)

/-- **The closure of the generic point**: the scheme-theoretic image `Z` of `j : η ⟶ Y`, a proper
model over `Spec B` through the closed immersion `Z ⟶ Y`, with point `η ⟶ Z`. -/
def closureModel : ProperModel B where
  Y := M.j.image
  f := M.j.imageι ≫ M.f
  j := M.j.toImage
  fac := by rw [Scheme.Hom.toImage_imageι_assoc, M.fac]

/-- The closure of the generic point refines the model, by the closed immersion `Z ⟶ Y`. -/
def closureRefinement : Refinement M.closureModel M where
  π := M.j.imageι
  comm := rfl
  fac := M.j.toImage_imageι

instance isClosedImmersion_closureRefinement_π : IsClosedImmersion M.closureRefinement.π :=
  inferInstanceAs (IsClosedImmersion M.j.imageι)

/-- The closure of the generic point is integral. -/
instance isIntegral_closureModel : IsIntegral M.closureModel.Y :=
  Scheme.Hom.isIntegral_image M.j

/-- The point `j(η)` is the generic point of its closure. -/
theorem closureModel_j_eq_genericPoint :
    M.closureModel.j (closedPoint (FractionRing B)) = genericPoint M.closureModel.Y := by
  have hd : DenseRange M.j.toImage := M.j.toImage.denseRange
  have hrange : Set.range M.j.toImage = {M.j.toImage (closedPoint (FractionRing B))} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      rw [Subsingleton.elim x (closedPoint (FractionRing B))]
      rfl
    · rintro rfl
      exact ⟨_, rfl⟩
  have hgen : IsGenericPoint (M.j.toImage (closedPoint (FractionRing B)))
      (⊤ : Set M.j.image) := by
    change closure _ = _
    rw [← hrange, hd.closure_range]
    rfl
  exact hgen.eq (genericPoint_spec M.closureModel.Y)

/-- **On an integral model with generic point `j(η)`, the stalk map at the center is
injective**: `𝒪_{Y, y} ⟶ V ⊆ K` is the specialization map into the function field `𝒪_{Y, j(η)}`
followed by the map of fields `𝒪_{Y, j(η)} ⟶ K` induced by `j`. -/
theorem centerStalkMap_injective_of_isIntegral [IsIntegral M.Y]
    (hgen : M.j (closedPoint (FractionRing B)) = genericPoint M.Y) :
    Function.Injective (M.centerStalkMap V hV).hom := by
  have hinj := Scheme.injective_stalkSpecializes_comp_of_isIntegral hgen
    (M.j_specializes_centerPoint V hV) (Scheme.stalkClosedPointTo M.j)
  rw [← M.centerStalkMap_comp_algebraMap V hV, CommRingCat.hom_comp, RingHom.coe_comp] at hinj
  exact hinj.of_comp

/-- On the closure of the generic point, the stalk map at the center is injective. -/
theorem centerStalkMap_closureModel_injective :
    Function.Injective (M.closureModel.centerStalkMap V hV).hom :=
  M.closureModel.centerStalkMap_injective_of_isIntegral V hV M.closureModel_j_eq_genericPoint

/-- **Passing to the closure of the generic point does not change `A_Y`**: the stalk map of the
closed immersion `Z ⟶ Y` at the center is surjective. -/
theorem centerRange_closureModel : M.closureModel.centerRange V hV = M.centerRange V hV := by
  refine le_antisymm ?_ (M.closureRefinement.centerRange_mono hV)
  have key : ∀ l : Spec (.of V) ⟶ M.Y, l = M.closureModel.center V hV ≫ M.closureRefinement.π →
      M.closureModel.centerRange V hV ≤ (Scheme.stalkClosedPointTo l).hom.range := by
    rintro l rfl
    rw [Scheme.stalkClosedPointTo_comp]
    rintro _ ⟨s, rfl⟩
    obtain ⟨t, rfl⟩ := M.closureRefinement.π.stalkMap_surjective _ s
    exact ⟨t, rfl⟩
  exact key _ (M.closureRefinement.center_eq hV)

/-- `A_Y` is a local ring (instance form of
`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.isLocalRing_centerRange`). -/
instance instIsLocalRingCenterRange : IsLocalRing (M.centerRange V hV) :=
  M.isLocalRing_centerRange V hV

/-- **`𝒪_{Y, y} ≅ A_Y`** when the stalk map at the center is injective. -/
def centerStalkEquiv (h : Function.Injective (M.centerStalkMap V hV).hom) :
    M.Y.presheaf.stalk (M.centerPoint V hV) ≃+* M.centerRange V hV :=
  RingEquiv.ofBijective (M.centerStalkMap V hV).hom.rangeRestrict
    ⟨fun _ _ hxy => h (congrArg Subtype.val hxy),
      (M.centerStalkMap V hV).hom.rangeRestrict_surjective⟩

/-- `centerStalkEquiv` is the stalk map at the center. -/
theorem coe_centerStalkEquiv (h : Function.Injective (M.centerStalkMap V hV).hom)
    (s : M.Y.presheaf.stalk (M.centerPoint V hV)) :
    (M.centerStalkEquiv V hV h s : V) = (M.centerStalkMap V hV).hom s :=
  rfl

/-- **`A_Y` is the local ring at the center of the closure of the generic point**:
`A_Y ≅ 𝒪_{Z, z}`. -/
def closureCenterStalkEquiv :
    M.closureModel.Y.presheaf.stalk (M.closureModel.centerPoint V hV) ≃+* M.centerRange V hV :=
  (M.closureModel.centerStalkEquiv V hV (M.centerStalkMap_closureModel_injective V hV)).trans
    (RingEquiv.subringCongr (M.centerRange_closureModel V hV))

/-- `closureCenterStalkEquiv` is the stalk map at the center of the closure. -/
theorem coe_closureCenterStalkEquiv
    (s : M.closureModel.Y.presheaf.stalk (M.closureModel.centerPoint V hV)) :
    (M.closureCenterStalkEquiv V hV s : V) = (M.closureModel.centerStalkMap V hV).hom s :=
  rfl

/-- **Integral models with injective stalk maps at the center are cofinal**: every model is
refined by one, the closure of its generic point, with the same `A_Y`. -/
theorem exists_refinement_centerStalkMap_injective :
    ∃ (M' : ProperModel B) (_ : Refinement M' M) (_ : IsIntegral M'.Y),
      M'.j (closedPoint (FractionRing B)) = genericPoint M'.Y ∧
      Function.Injective (M'.centerStalkMap V hV).hom ∧
      M'.centerRange V hV = M.centerRange V hV :=
  ⟨M.closureModel, M.closureRefinement, inferInstance, M.closureModel_j_eq_genericPoint,
    M.centerStalkMap_closureModel_injective V hV, M.centerRange_closureModel V hV⟩

/-- **Every `A_Y` is the local ring at the center of an integral model**: each member of
`AlgebraicGeometry.Scheme.ZariskiRiemann.centerRanges` is the image of an injective stalk map at
the center of an integral model with generic point `j(η)`. -/
theorem exists_isIntegral_of_mem_centerRanges (a : centerRanges V hV) :
    ∃ (M : ProperModel B) (_ : IsIntegral M.Y),
      M.j (closedPoint (FractionRing B)) = genericPoint M.Y ∧
      Function.Injective (M.centerStalkMap V hV).hom ∧ M.centerRange V hV = a.1 := by
  obtain ⟨_, M, rfl⟩ := a
  obtain ⟨M', -, hint, hgen, hinj, heq⟩ := M.exists_refinement_centerStalkMap_injective V hV
  exact ⟨M', hint, hgen, hinj, heq⟩

/-- **`(𝒪_{Y, y})^{sh} = A_Y^{sh}`** on a model whose stalk map at the center is injective
(Stacks 05WS with zero kernel, i.e. transport along `𝒪_{Y, y} ≅ A_Y`, Stacks 04GQ): a strict
henselization of `A_Y` is a strict henselization of `𝒪_{Y, y}`, for the composite structure map
`𝒪_{Y, y} ≅ A_Y → A_Y^{sh}`. -/
theorem exists_isStrictHenselization_stalk (h : Function.Injective (M.centerStalkMap V hV).hom)
    {κsep : Type v} [Field κsep] [Algebra (maximalIdeal (M.centerRange V hV)).ResidueField κsep]
    [IsSepClosure (maximalIdeal (M.centerRange V hV)).ResidueField κsep]
    {Rsh : Type w} [CommRing Rsh] [IsLocalRing Rsh] [Algebra (M.centerRange V hV) Rsh]
    (H : IsStrictHenselization (M.centerRange V hV) κsep Rsh) :
    ∃ (_ : Algebra (M.Y.presheaf.stalk (M.centerPoint V hV)) Rsh)
      (_ : Algebra (maximalIdeal (M.Y.presheaf.stalk (M.centerPoint V hV))).ResidueField κsep)
      (_ : IsSepClosure (maximalIdeal (M.Y.presheaf.stalk (M.centerPoint V hV))).ResidueField
        κsep),
      Nonempty (IsStrictHenselization (M.Y.presheaf.stalk (M.centerPoint V hV)) κsep Rsh) ∧
        ∀ s, algebraMap (M.Y.presheaf.stalk (M.centerPoint V hV)) Rsh s =
          algebraMap (M.centerRange V hV) Rsh (M.centerStalkEquiv V hV h s) := by
  obtain ⟨alg, algκ, hsep, hH, hpin⟩ :=
    exists_isStrictHenselization_of_ringEquiv H (M.centerStalkEquiv V hV h).symm
  refine ⟨alg, algκ, hsep, hH, fun s => ?_⟩
  have := hpin (M.centerStalkEquiv V hV h s)
  rwa [RingEquiv.symm_apply_apply] at this

end ProperModel

end Scheme.ZariskiRiemann

end AlgebraicGeometry

end
