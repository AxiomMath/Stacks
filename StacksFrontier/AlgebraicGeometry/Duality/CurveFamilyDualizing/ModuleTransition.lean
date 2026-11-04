module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreePullbackNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionAssociativity
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.DerivedPullbackUnitLawsOfRingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionComplexLevel

/-!
# Top-degree cohomology of compatible derived identifications

Let `g : X ⟶ Y` be a morphism of ringed spaces, `K` an object of `D(𝒪_Y)` with no cohomology above
degree `d`, and `α : Lg^*K ≅ K'`. Reading `α` in degree `d` through the top-degree comparison
`H^d(Lg^*K) ≅ g^*H^d(K)` of `Stacks.AlgebraicGeometry.TopDegreeBaseChange` gives an isomorphism of
modules `g^*H^d(K) ≅ H^d(K')`. This file records that construction and proves that it carries a
composite of derived identifications (through the composition isomorphism of derived pullbacks,
Stacks 0D5S) to the composite of the module isomorphisms (through the composition isomorphism of
ordinary pullbacks), that it carries the identification `L(𝟙)^* ≅ 𝟭` to `𝟙^* ≅ 𝟭`, and that it is
natural in both ends. This is the passage from a coherent system of derived identifications of
relative dualizing complexes to a coherent system of identifications of relative dualizing
sheaves.

For morphisms of schemes the ordinary pullback `AlgebraicGeometry.Scheme.Modules.pullback f` is
`RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom` by `rfl`, and its composition
isomorphism `AlgebraicGeometry.Scheme.Modules.pullbackComp` is the ringed-space one
(`Stacks.Scheme.Modules.pullbackComp_eq_modulePullbackComp`), so the composition law is also
stated in the shape of the cocycle condition of chart-scheme module systems,
`AlgebraicGeometry.Space.IsChartSchemeModuleCocycle`.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDegreeTransition`.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDegreeTransition_comp`: the composition law.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback_id_hom` and
  `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDegreeTransition_id`: the identity law.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDegreeTransition_trans` and
  `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDegreeTransition_mapIso_trans`: naturality in
  the target and in the source.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDegreeTransition_comp_scheme`: the composition
  law for morphisms of schemes, through `AlgebraicGeometry.Scheme.Modules.pullbackComp`.

## Implementation notes

Every identity is first proved for abstract categories, functors and isomorphisms (the
`topDegreeTransition_*_paste` lemmas), and then instantiated: rewriting inside the long composites
at `SheafOfModules (structureSheafRing _)` and the standard model of its derived category exhausts
the heartbeat budget.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category AlgebraicGeometry
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

section Paste

variable {D₁ D₂ M₁ M₂ : Type*} [Category D₁] [Category D₂] [Category M₁] [Category M₂]

/-- The chase behind `topDegreeTransition_comp`, with every object a variable. -/
theorem topDegreeTransition_comp_paste (H : D₁ ⥤ M₁) (H₂ : D₂ ⥤ M₂) (L : D₂ ⥤ D₁)
    (P : M₂ ⥤ M₁) {K₁ K'' : D₁} {B K' : D₂} {N : M₁} {N' : M₂}
    (c : L.obj B ≅ K₁) (θab : H.obj K₁ ≅ N) (θa : H.obj (L.obj B) ≅ P.obj (H₂.obj B))
    (θb : H₂.obj B ≅ N') (C : P.obj N' ≅ N) (θa' : H.obj (L.obj K') ≅ P.obj (H₂.obj K'))
    (α : B ≅ K') (β : L.obj K' ≅ K'')
    (hcomp : H.map c.hom ≫ θab.hom = θa.hom ≫ P.map θb.hom ≫ C.hom)
    (hnat : H.map (L.map α.hom) ≫ θa'.hom = θa.hom ≫ P.map (H₂.map α.hom)) :
    θab.symm ≪≫ H.mapIso (c.symm ≪≫ L.mapIso α ≪≫ β) =
      C.symm ≪≫ P.mapIso (θb.symm ≪≫ H₂.mapIso α) ≪≫ θa'.symm ≪≫ H.mapIso β := by
  have hcomp' : θab.hom = H.map c.inv ≫ θa.hom ≫ P.map θb.hom ≫ C.hom := by
    rw [← hcomp, ← Category.assoc, ← H.map_comp, c.inv_hom_id, H.map_id, Category.id_comp]
  ext
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [Iso.inv_comp_eq, hcomp']
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.map_hom_inv_id_assoc]
  rw [← reassoc_of% hnat, Iso.hom_inv_id_assoc]

/-- The chase behind `derivedPullbackTopDegreeIsoPullback_id_hom`: a comparison `θ` that is
compatible with the unit laws on the two sides and natural is the composite of the two unit
isomorphisms. -/
theorem topDegreeTransition_id_paste (H : D₁ ⥤ M₁) (L : D₁ ⥤ D₁) (P : M₁ ⥤ M₁)
    (φ : L ≅ 𝟭 D₁) (ι : P ≅ 𝟭 M₁) (K : D₁) (θ₀ : H.obj (L.obj K) ≅ P.obj (H.obj K))
    (θ₁ : H.obj (L.obj (L.obj K)) ≅ P.obj (H.obj (L.obj K)))
    (h1 : H.map (φ.hom.app (L.obj K)) ≫ θ₀.hom =
      θ₁.hom ≫ P.map θ₀.hom ≫ ι.hom.app (P.obj (H.obj K)))
    (h2 : H.map (L.map (φ.hom.app K)) ≫ θ₀.hom = θ₁.hom ≫ P.map (H.map (φ.hom.app K))) :
    θ₀.hom = H.map (φ.hom.app K) ≫ ι.inv.app (H.obj K) := by
  have nφ : L.map (φ.hom.app K) = φ.hom.app (L.obj K) := by
    have h := φ.hom.naturality (φ.hom.app K)
    simp only [Functor.id_map] at h
    exact (Iso.cancel_iso_hom_right _ _ (φ.app K)).1 h
  have nι : P.map θ₀.hom ≫ ι.hom.app (P.obj (H.obj K)) = ι.hom.app (H.obj (L.obj K)) ≫ θ₀.hom :=
    ι.hom.naturality θ₀.hom
  have h1' : H.map (φ.hom.app (L.obj K)) = θ₁.hom ≫ ι.hom.app (H.obj (L.obj K)) := by
    refine (Iso.cancel_iso_hom_right _ _ θ₀).1 ?_
    rw [h1, nι, Category.assoc]
  rw [nφ, h1', Category.assoc] at h2
  have h3 : ι.hom.app (H.obj (L.obj K)) ≫ θ₀.hom = P.map (H.map (φ.hom.app K)) :=
    (Iso.cancel_iso_hom_left θ₁ _ _).1 h2
  have h4 : H.map (φ.hom.app K) ≫ ι.inv.app (H.obj K) =
      ι.inv.app (H.obj (L.obj K)) ≫ P.map (H.map (φ.hom.app K)) :=
    ι.inv.naturality (H.map (φ.hom.app K))
  rw [h4, ← h3, Iso.inv_hom_id_app_assoc]

/-- Unfolding the identity law of `topDegreeTransition`, with every object a variable. -/
theorem topDegreeTransition_id_paste' (H : D₁ ⥤ M₁) {A B C : D₁} {N : M₁}
    (θ : H.obj A ≅ N) (φ : A ≅ B) (ι : N ≅ H.obj B) (e : B ≅ C)
    (h : θ.hom = H.map φ.hom ≫ ι.inv) :
    θ.symm ≪≫ H.mapIso (φ ≪≫ e) = ι ≪≫ H.mapIso e := by
  ext
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp]
  rw [Iso.inv_comp_eq, h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Naturality in the target, with every object a variable. -/
theorem topDegreeTransition_trans_paste (H : D₁ ⥤ M₁) {A B C : D₁} {N : M₁}
    (θ : H.obj A ≅ N) (α : A ≅ B) (e : B ≅ C) :
    θ.symm ≪≫ H.mapIso (α ≪≫ e) = (θ.symm ≪≫ H.mapIso α) ≪≫ H.mapIso e := by
  rw [Functor.mapIso_trans, Iso.trans_assoc]

/-- Naturality in the source, with every object a variable. -/
theorem topDegreeTransition_mapIso_trans_paste (H : D₁ ⥤ M₁) (H₂ : D₂ ⥤ M₂) (L : D₂ ⥤ D₁)
    (P : M₂ ⥤ M₁) {K₀ K : D₂} {K' : D₁}
    (θ₀ : H.obj (L.obj K₀) ≅ P.obj (H₂.obj K₀)) (θ : H.obj (L.obj K) ≅ P.obj (H₂.obj K))
    (e : K₀ ≅ K) (α : L.obj K ≅ K')
    (hnat : H.map (L.map e.hom) ≫ θ.hom = θ₀.hom ≫ P.map (H₂.map e.hom)) :
    θ₀.symm ≪≫ H.mapIso (L.mapIso e ≪≫ α) =
      P.mapIso (H₂.mapIso e) ≪≫ θ.symm ≪≫ H.mapIso α := by
  ext
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp]
  rw [Iso.inv_comp_eq, ← reassoc_of% hnat, Iso.hom_inv_id_assoc]

/-- The composition law read as a cocycle condition, with every object a variable. -/
theorem topDegreeTransition_cocycle_paste {A B C N : M₁} (T : N ≅ C) (Cm : A ≅ N) (U : A ≅ B)
    (V : B ≅ C) (h : T = Cm.symm ≪≫ U ≪≫ V) : U.hom ≫ V.hom = Cm.hom ≫ T.hom := by
  rw [h]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

end Paste

open _root_.DerivedCategory Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedPullback.Composition

variable {X Y Z : RingedSpace.{u, u}}

/-- The standard model of `D(𝒪_W)`, the model of the top-degree comparison. -/
local notation "Dˢ[" W "]" => @DerivedCategory (SheafOfModules (structureSheafRing W)) _ _
  (HasDerivedCategory.standard (SheafOfModules (structureSheafRing W)))

/-- The standard model of `D(𝒪_W)` as an instance term, for `letI`. -/
local notation "stdᴰ[" W "]" =>
  HasDerivedCategory.standard (SheafOfModules (structureSheafRing W))

/-- `H^d` at the standard model of the derived category, the model of the top-degree comparison. -/
abbrev stdHomology (W : RingedSpace.{u, u}) (d : ℤ) :
    @DerivedCategory (SheafOfModules.{u} (structureSheafRing W)) _ _
        (HasDerivedCategory.standard _) ⥤ SheafOfModules.{u} (structureSheafRing W) :=
  @DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) d

/-- **The module identification in the top degree** `g^*H^d(K) ≅ H^d(K')` attached to a derived
identification `α : Lg^*K ≅ K'`, for `K` with no cohomology above `d`. -/
def topDegreeTransition (g : X ⟶ Y) {K K'} (d : ℤ)
    (hK : letI := stdᴰ[Y]; TStructure.t.IsLE K d)
    (α : letI := stdᴰ[X]; letI := stdᴰ[Y]; (derivedPullback g).obj K ≅ K') :
    (modulePullback g).obj ((stdHomology Y d).obj K) ≅ (stdHomology X d).obj K' :=
  letI := stdᴰ[X]; letI := stdᴰ[Y]
  (derivedPullbackTopDegreeIsoPullback g K d hK).symm ≪≫ (stdHomology X d).mapIso α

/-- **Composites of derived identifications give composites of module identifications.** -/
theorem topDegreeTransition_comp (a : X ⟶ Y) (b : Y ⟶ Z) {K K' K''} (d : ℤ)
    (hK : letI := stdᴰ[Z]; TStructure.t.IsLE K d) (hK' : letI := stdᴰ[Y]; TStructure.t.IsLE K' d)
    (α : letI := stdᴰ[Y]; letI := stdᴰ[Z]; (derivedPullback b).obj K ≅ K')
    (β : letI := stdᴰ[X]; letI := stdᴰ[Y]; (derivedPullback a).obj K' ≅ K'') :
    letI := stdᴰ[X]; letI := stdᴰ[Y]; letI := stdᴰ[Z]
    topDegreeTransition (a ≫ b) d hK
        (((derivedPullbackCompIsoCanonical a b).app K).symm ≪≫ (derivedPullback a).mapIso α ≪≫ β) =
      ((Stacks.DerivedPullback.Composition.modulePullbackComp a b).app _).symm ≪≫
        (modulePullback a).mapIso (topDegreeTransition b d hK α) ≪≫
          topDegreeTransition a d hK' β :=
  let := stdᴰ[X]; let := stdᴰ[Y]; let := stdᴰ[Z]
  topDegreeTransition_comp_paste (stdHomology X d) (stdHomology Y d) (derivedPullback a)
    (modulePullback a) ((derivedPullbackCompIsoCanonical a b).app K) _ _ _
    ((Stacks.DerivedPullback.Composition.modulePullbackComp a b).app _) _ α β
    (derivedPullbackTopDegreeIsoPullback_comp a b K d hK)
    (derivedPullbackTopDegreeIsoPullback_hom_naturality a α.hom d
      (isLE_derivedPullback_obj' b K d hK) hK')

/-- **The top-degree comparison along an identity** is the identification `L(𝟙)^* ≅ 𝟭` read in
degree `d`, followed by the inverse of `𝟙^* ≅ 𝟭`. It is forced by the composition law at
`𝟙 ≫ 𝟙`, the two unit laws of the composition isomorphisms, and naturality. -/
theorem derivedPullbackTopDegreeIsoPullback_id_hom
    (K : Dˢ[X]) (d : ℤ)
    (hK : letI := stdᴰ[X]; TStructure.t.IsLE K d) :
    letI := stdᴰ[X]
    (derivedPullbackTopDegreeIsoPullback (𝟙 X) K d hK).hom =
      (stdHomology X d).map
          ((Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso X).hom.app K) ≫
        (modulePullbackId X).inv.app ((stdHomology X d).obj K) := by
  let := stdᴰ[X]
  have hc : (derivedPullbackCompIsoCanonical (𝟙 X) (𝟙 X)).hom.app K =
      (Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso X).hom.app
        ((derivedPullback (𝟙 X)).obj K) :=
    (congrArg (fun i => i.hom.app K)
      (Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackCompIsoCanonical_id_comp
        (𝟙 X))).trans (Category.comp_id _)
  have hC : (Stacks.DerivedPullback.Composition.modulePullbackComp (𝟙 X) (𝟙 X)).hom.app
        ((stdHomology X d).obj K) =
      (modulePullbackId X).hom.app ((modulePullback (𝟙 X)).obj ((stdHomology X d).obj K)) :=
    (congrArg (fun i => i.hom.app ((stdHomology X d).obj K))
      (modulePullbackComp_id_comp (𝟙 X))).trans (Category.comp_id _)
  have h0 := derivedPullbackTopDegreeIsoPullback_comp (𝟙 X) (𝟙 X) K d hK
  rw [hc, hC] at h0
  exact topDegreeTransition_id_paste (stdHomology X d) (derivedPullback (𝟙 X))
    (modulePullback (𝟙 X))
    (Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso X)
    (modulePullbackId X) K _ _ h0
    (derivedPullbackTopDegreeIsoPullback_hom_naturality (𝟙 X)
      ((Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso X).hom.app K) d
      (isLE_derivedPullback_obj' (𝟙 X) K d hK) hK)

/-- **The identity law.** The transition along `𝟙 X` of the identification `L(𝟙)^* ≅ 𝟭` followed
by `e : K ≅ K'` is the identification `𝟙^* ≅ 𝟭` followed by `H^d(e)`. -/
theorem topDegreeTransition_id {K K' : Dˢ[X]}
    (d : ℤ) (hK : letI := stdᴰ[X]; TStructure.t.IsLE K d) (e : K ≅ K') :
    letI := stdᴰ[X]
    topDegreeTransition (𝟙 X) d hK
        ((Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso X).app K ≪≫ e) =
      (modulePullbackId X).app ((stdHomology X d).obj K) ≪≫ (stdHomology X d).mapIso e :=
  letI := stdᴰ[X]
  topDegreeTransition_id_paste' (stdHomology X d) _ _ _ e
    (derivedPullbackTopDegreeIsoPullback_id_hom K d hK)

/-- **Naturality in the target**: composing the derived identification with `e : K' ≅ K₂`
composes the module identification with `H^d(e)`. -/
theorem topDegreeTransition_trans (g : X ⟶ Y) {K K' K₂} (d : ℤ)
    (hK : letI := stdᴰ[Y]; TStructure.t.IsLE K d)
    (α : letI := stdᴰ[X]; letI := stdᴰ[Y]; (derivedPullback g).obj K ≅ K') (e : K' ≅ K₂) :
    topDegreeTransition g d hK (α ≪≫ e) =
      topDegreeTransition g d hK α ≪≫ (stdHomology X d).mapIso e :=
  letI := stdᴰ[X]; letI := stdᴰ[Y]
  topDegreeTransition_trans_paste (stdHomology X d) _ α e

/-- **Naturality in the source**: precomposing the derived identification with `Lg^*(e)` for
`e : K₀ ≅ K` precomposes the module identification with `g^*H^d(e)`. -/
theorem topDegreeTransition_mapIso_trans (g : X ⟶ Y) {K₀ K K'} (d : ℤ)
    (hK₀ : letI := stdᴰ[Y]; TStructure.t.IsLE K₀ d) (hK : letI := stdᴰ[Y]; TStructure.t.IsLE K d)
    (e : K₀ ≅ K) (α : letI := stdᴰ[X]; letI := stdᴰ[Y]; (derivedPullback g).obj K ≅ K') :
    letI := stdᴰ[X]; letI := stdᴰ[Y]
    topDegreeTransition g d hK₀ ((derivedPullback g).mapIso e ≪≫ α) =
      (modulePullback g).mapIso ((stdHomology Y d).mapIso e) ≪≫ topDegreeTransition g d hK α :=
  let := stdᴰ[X]; let := stdᴰ[Y]
  topDegreeTransition_mapIso_trans_paste (stdHomology X d) (stdHomology Y d) (derivedPullback g)
    (modulePullback g) _ _ e α
    (derivedPullbackTopDegreeIsoPullback_hom_naturality g e.hom d hK₀ hK)

/-- **The composition law for morphisms of schemes**, in the shape of the cocycle condition
`AlgebraicGeometry.Space.IsChartSchemeModuleCocycle`: `a^*` of the transition along `b`, followed
by the transition along `a`, is the composition isomorphism
`AlgebraicGeometry.Scheme.Modules.pullbackComp` followed by the transition of the composite
derived identification. -/
theorem topDegreeTransition_comp_scheme {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    {K K' K''} (d : ℤ) (hK : letI := stdᴰ[Z.toRingedSpace]; TStructure.t.IsLE K d)
    (hK' : letI := stdᴰ[Y.toRingedSpace]; TStructure.t.IsLE K' d)
    (α : letI := stdᴰ[Y.toRingedSpace]; letI := stdᴰ[Z.toRingedSpace]
      (derivedPullback b.toLRSHom.toShHom).obj K ≅ K')
    (β : letI := stdᴰ[X.toRingedSpace]; letI := stdᴰ[Y.toRingedSpace]
      (derivedPullback a.toLRSHom.toShHom).obj K' ≅ K'') :
    letI := stdᴰ[X.toRingedSpace]; letI := stdᴰ[Y.toRingedSpace]; letI := stdᴰ[Z.toRingedSpace]
    (Scheme.Modules.pullback a).map (topDegreeTransition b.toLRSHom.toShHom d hK α).hom ≫
        (topDegreeTransition a.toLRSHom.toShHom d hK' β).hom =
      (Scheme.Modules.pullbackComp a b).hom.app ((stdHomology Z.toRingedSpace d).obj K) ≫
        (topDegreeTransition (a ≫ b).toLRSHom.toShHom d hK
          (((derivedPullbackCompIsoCanonical a.toLRSHom.toShHom b.toLRSHom.toShHom).app K).symm ≪≫
            (derivedPullback a.toLRSHom.toShHom).mapIso α ≪≫ β)).hom := by
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))
  rw [Stacks.Scheme.Modules.pullbackComp_eq_modulePullbackComp a b]
  exact topDegreeTransition_cocycle_paste _ _ ((modulePullback a.toLRSHom.toShHom).mapIso
    (topDegreeTransition b.toLRSHom.toShHom d hK α)) _
    (topDegreeTransition_comp a.toLRSHom.toShHom b.toLRSHom.toShHom d hK hK' α β)

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
