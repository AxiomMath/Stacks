module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.AdicFibreTower
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceHypotheses
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatLocusAdicThickenings
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteChangeTower
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningCoherentSystem

/-!
# Grothendieck's existence theorem on the adic fibres (Stacks 08BF)

Let `A` be a Noetherian ring complete with respect to an ideal `I`, write `S = Spec A` and
`Sₙ = Spec(A/Iⁿ)`, let `X ⟶ S` be a separated morphism of finite type of algebraic spaces and
`Xₙ = X ×_S Sₙ`.  Stacks 08BF (*Unwinding Grothendieck's existence theorem*) considers systems
`(𝓕ₙ, φₙ)` where

1. `𝓕ₙ` is a coherent `𝒪_{Xₙ}`-module,
2. `φₙ : iₙ^* 𝓕ₙ₊₁ ⟶ 𝓕ₙ` is an isomorphism, and
3. `Supp(𝓕₁)` is proper over `S₁`,

and states that the completion functor, from coherent `𝒪_X`-modules with support proper over
`A` to such systems, `𝓕 ↦ (𝓕|_{Xₙ})ₙ`, is an equivalence of categories; when `X` is proper
over `A` the conditions on the supports can be omitted.

Here the adic fibres are `AlgebraicGeometry.Space.adicFibreSpaceOf`, indexed from `0`: the `n`-th
one is `Spec(A/Iⁿ⁺¹) ×_S X`, the source's `Xₙ₊₁`.  The systems satisfying (1) and (2) form the
category `AlgebraicGeometry.Space.ThickeningCoherentSystem` of the tower of adic fibres
(`AlgebraicGeometry.Space.AdicFibreSystem`), condition (3) cuts out the full subcategory
`AlgebraicGeometry.Space.AdicFibreSystemsProperOver`, and the functor is the restriction
`AlgebraicGeometry.Space.adicFibreRestrictionOf`, `𝓕 ↦ (𝓕|_{Xₙ}, φₙ)`, with `φₙ` the
comparison of inverse images along `Xₙ ⟶ Xₙ₊₁ ⟶ X`.

## Main definitions

* `AlgebraicGeometry.Space.adicFibreSuccMap`: the transition `Xₙ ⟶ Xₙ₊₁` of the adic fibres.
* `AlgebraicGeometry.Space.AdicFibreSystem`: the systems of conditions (1) and (2).
* `AlgebraicGeometry.Space.isAdicFibreSystemProperOver`,
  `AlgebraicGeometry.Space.AdicFibreSystemsProperOver`: condition (3).
* `AlgebraicGeometry.Space.adicFibreRestrictionOf`: `𝓕 ↦ (𝓕|_{Xₙ})ₙ` on coherent modules; it is
  `AlgebraicGeometry.Space.adicFibreRestriction` of the base, read on a bundled algebraic space.
* `AlgebraicGeometry.Space.adicFibreRestrictionProperOver`: the same functor between the
  categories with the support conditions.

## Main results

* `AlgebraicGeometry.Space.isEquivalence_adicFibreRestrictionProperOver`: **Stacks 08BF**.
* `AlgebraicGeometry.Space.isEquivalence_adicFibreRestriction_of_isProper`: **Stacks 08BF**, the
  case of `X` proper over `A`, with no conditions on the supports.

## References

* [Stacks Project, Tag 08BF](https://stacks.math.columbia.edu/tag/08BF)
* [Stacks Project, Tag 08BE](https://stacks.math.columbia.edu/tag/08BE)
* [Stacks Project, Tag 08B9](https://stacks.math.columbia.edu/tag/08B9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ u₁ u₂ u

namespace CategoryTheory.TowerSystem

variable {C : ℕ → Type u₁} [∀ n, Category.{v₁} (C n)] {P : ∀ n, ObjectProperty (C n)}
  {T : ∀ n, C (n + 1) ⥤ C n}

/-- An isomorphism of systems along a tower from isomorphisms of the terms compatible with the
transition isomorphisms. -/
@[simps]
def isoMk {E E' : TowerSystem P T} (e : ∀ n, (E.term n).obj ≅ (E'.term n).obj)
    (he : ∀ n, (T n).map (e (n + 1)).hom ≫ (E'.transitionIso n).hom =
      (E.transitionIso n).hom ≫ (e n).hom) : E ≅ E' where
  hom := ⟨fun n => (e n).hom, he⟩
  inv := ⟨fun n => (e n).inv, fun n => by
    rw [Iso.eq_comp_inv, Category.assoc, ← he, ← Functor.map_comp_assoc, Iso.inv_hom_id,
      Functor.map_id, Category.id_comp]⟩
  hom_inv_id := hom_ext fun n => (e n).hom_inv_id
  inv_hom_id := hom_ext fun n => (e n).inv_hom_id

variable {D : Type u₂} [Category.{v₂} D] {Q : ObjectProperty D} {L : ∀ n, D ⥤ C n}
  {ρ : ∀ n, L (n + 1) ⋙ T n ≅ L n} {hL : ∀ n M, Q M → P n ((L n).obj M)}

/-- An isomorphism from the restriction of an object `M` of `D` satisfying `Q` to a system `E`,
from isomorphisms `ψₙ : Lₙ M ≅ Eₙ` compatible with comparisons `τₙ : Lₙ ≅ Lₙ₊₁ ⋙ Tₙ` inverse to
the `ρₙ` and with the transition isomorphisms of `E`. -/
def restrictionIsoMk (M : D) (hM : Q M) (E : TowerSystem P T)
    (ψ : ∀ n, (L n).obj M ≅ (E.term n).obj) (τ : ∀ n, L n ≅ L (n + 1) ⋙ T n)
    (hτ : ∀ n, τ n = (ρ n).symm)
    (hψ : ∀ n, (τ n).hom.app M ≫ (T n).map (ψ (n + 1)).hom ≫ (E.transitionIso n).hom =
      (ψ n).hom) :
    (restriction Q L ρ hL).obj ⟨M, hM⟩ ≅ E :=
  isoMk ψ fun n => by
    rw [restriction_obj_transitionIso, ← hψ n, hτ n]
    simp

end CategoryTheory.TowerSystem

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A functor is an equivalence when every morphism between images is the image of a unique
morphism and every object is isomorphic to an image. -/
theorem Functor.isEquivalence_of_existsUnique_map_eq (F : C ⥤ D)
    (hff : ∀ (M N : C) (φ : F.obj M ⟶ F.obj N), ∃! ψ : M ⟶ N, F.map ψ = φ)
    (hes : ∀ E : D, ∃ M : C, Nonempty (F.obj M ≅ E)) : F.IsEquivalence := by
  have : F.Faithful := ⟨fun {M N} a b hab => (hff M N (F.map a)).unique rfl hab.symm⟩
  have : F.Full := ⟨fun {M N} φ => ⟨(hff M N φ).choose, (hff M N φ).choose_spec.1⟩⟩
  have : F.EssSurj := ⟨fun E => let ⟨M, hM⟩ := hes E; ⟨M, hM⟩⟩
  exact { }

/-- The functor `P.lift (Q.ι ⋙ F)` between full subcategories induced by a functor `F` is an
equivalence when every morphism between images of objects satisfying `Q` is the image of a
unique morphism and every object satisfying `P` is isomorphic to the image of an object
satisfying `Q`. -/
theorem ObjectProperty.isEquivalence_lift_comp_ι {Q : ObjectProperty C} {P : ObjectProperty D}
    (F : C ⥤ D) (h : ∀ M : Q.FullSubcategory, P (F.obj M.obj))
    (hff : ∀ (M N : C), Q M → Q N → ∀ φ : F.obj M ⟶ F.obj N, ∃! ψ : M ⟶ N, F.map ψ = φ)
    (hes : ∀ E : D, P E → ∃ M : C, Q M ∧ Nonempty (F.obj M ≅ E)) :
    (P.lift (Q.ι ⋙ F) h).IsEquivalence := by
  refine Functor.isEquivalence_of_existsUnique_map_eq _ (fun M N φ => ?_) (fun E => ?_)
  · obtain ⟨ψ, hψ, hu⟩ := hff M.obj N.obj M.property N.property φ.hom
    exact ⟨ObjectProperty.homMk ψ, ObjectProperty.hom_ext _ hψ,
      fun ψ' h' => ObjectProperty.hom_ext _ (hu ψ'.hom (congrArg (fun χ => χ.hom) h'))⟩
  · obtain ⟨M, hM, ⟨i⟩⟩ := hes E.obj E.property
    exact ⟨⟨M, hM⟩, ⟨ObjectProperty.isoMk _ i⟩⟩

end CategoryTheory

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Triangle

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The comparison `h^* ≅ g^* ⋙ f^*` of `AlgebraicGeometry.Space.modulePullbackTriangle` is,
at each module, the inverse of the comparison `g^* ⋙ f^* ≅ h^*` of
`AlgebraicGeometry.Space.modulePullbackCompIsoOfEq`. -/
theorem modulePullbackTriangle_hom_app {X Y W : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {g : Y ⟶ W} {h : X ⟶ W} (w : f ≫ g = h) (M : Modules.{u, u} B S hS W.1 W.2) :
    (modulePullbackTriangle B S hS w).hom.app M =
      ((modulePullbackCompIsoOfEq B S hS f g w).app M).inv := by
  subst w
  rw [modulePullbackTriangle_rfl]
  simp [modulePullbackCompIsoOfEq]

/-- The comparison `h^* ≅ g^* ⋙ f^*` of `AlgebraicGeometry.Space.modulePullbackTriangle` is the
inverse of the comparison `g^* ⋙ f^* ≅ h^*` of
`AlgebraicGeometry.Space.modulePullbackCompIsoOfEq`. -/
theorem modulePullbackTriangle_eq_symm {X Y W : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {g : Y ⟶ W} {h : X ⟶ W} (w : f ≫ g = h) :
    modulePullbackTriangle B S hS w = (modulePullbackCompIsoOfEq B S hS f g w).symm :=
  Iso.ext (NatTrans.ext (funext fun M => modulePullbackTriangle_hom_app w M))

end Triangle

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  (I : Ideal A) (X : AlgebraicSpaces B (Spec (.of A)) hA)
  (f : X ⟶ schemeSpace (baseObject A B hA))

/-! ### The tower of adic fibres -/

/-- The transition `Xₙ ⟶ Xₙ₊₁` between consecutive adic fibres. -/
abbrev adicFibreSuccMap (n : ℕ) :
    adicFibreSpaceOf A I B hA X f n ⟶ adicFibreSpaceOf A I B hA X f (n + 1) :=
  ObjectProperty.homMk (adicFibreSucc A I B hA (contains_adicThickening A I B hA) f.hom n)

/-- The transitions of the adic fibres are maps over `X`. -/
@[reassoc (attr := simp)]
theorem adicFibreSuccMap_adicFibreInclusion (n : ℕ) :
    adicFibreSuccMap I X f n ≫ adicFibreInclusion A I B hA X f (n + 1) =
      adicFibreInclusion A I B hA X f n :=
  ObjectProperty.hom_ext _ (adicFibreSucc_fst A I B hA (contains_adicThickening A I B hA) f.hom n)

/-- **The adic fibres of `X` form a tower of thickenings** of `X` over `Spec A`. -/
theorem adicFibreSiteChangeTower :
    SiteChangeTower (h := 𝟙 (B.obj hA)) X f I (adicFibreSpaceOf A I B hA X f)
      (adicFibreInclusion A I B hA X f) (adicFibreSuccMap I X f)
      (adicThickeningObject A I B hA (contains_adicThickening A I B hA))
      (adicThickeningMap A I B hA (contains_adicThickening A I B hA))
      (adicFibreProjection A I B hA X f) where
  comp n := adicFibreSuccMap_adicFibreInclusion I X f n
  isPullback n := isPullback_adicFibre A I B hA X f n
  iso n := ⟨Iso.refl _, (Category.id_comp (adicThickeningι A I n)).symm⟩

/-- The projection `Xₙ ⟶ Sₙ` of an adic fibre is locally of finite type when `X ⟶ S` is, being a
base change of it. -/
theorem isLocallyOfFiniteType_adicFibreProjection
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom) (n : ℕ) :
    IsLocallyOfFiniteType B (Spec (.of A)) hA (adicFibreProjection A I B hA X f n).hom :=
  (isLocallyOfFiniteType_isStableUnderBaseChange B (Spec (.of A)) hA).of_isPullback
    (isPullback_adicFibre A I B hA X f n) hf

/-- The adic fibres of an algebraic space locally of finite type over a Noetherian ring are
locally Noetherian. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_adicFibreSpace [IsNoetherianRing A]
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom) (n : ℕ) :
    HasEtaleLocalProperty B (Spec (.of A)) hA (adicFibreSpaceOf A I B hA X f n).1
      (fun V : Scheme.{u} => IsLocallyNoetherian V) :=
  (C1573.fact_isLocallyNoetherian_of_baseObject (adicFibreSpaceOf A I B hA X f n)
    (adicFibreInclusion A I B hA X f n ≫ f)
    (isLocallyOfFiniteType_comp' B (Spec (.of A)) hA _ _ X.2 (schemeSpace (baseObject A B hA)).2
      (isLocallyOfFiniteType_of_isClosedImmersion B (Spec (.of A)) hA _
        (isClosedImmersion_adicFibreFstHom A I B hA X.2 f.hom n)) hf)).out

/-! ### The systems of Stacks 08BF -/

/-- **The systems of Stacks 08BF, conditions (1) and (2)**: coherent `𝒪_{Xₙ}`-modules `𝓕ₙ` on
the adic fibres with isomorphisms `φₙ : iₙ^* 𝓕ₙ₊₁ ≅ 𝓕ₙ`. -/
abbrev AdicFibreSystem :=
  ThickeningCoherentSystem B (Spec (.of A)) hA (adicFibreSpaceOf A I B hA X f)
    (adicFibreSuccMap I X f)

/-- **Condition (3) of Stacks 08BF**: the support of the first term of a system is proper over
`S₁ = Spec(A/I)`. -/
def isAdicFibreSystemProperOver (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom) :
    ObjectProperty (AdicFibreSystem I X f) := fun E =>
  HasProperSupport B (Spec (.of A)) hA (adicFibreSpaceOf A I B hA X f 0).2
    (schemeSpace (adicThickeningObject A I B hA (contains_adicThickening A I B hA) 0)).2
    (adicFibreProjection A I B hA X f 0).hom (isLocallyOfFiniteType_adicFibreProjection I X f hf 0)
    ((SheafOfModules.toSheaf _).obj (E.term 0).obj)

/-- The systems of Stacks 08BF satisfying conditions (1), (2) and (3). -/
abbrev AdicFibreSystemsProperOver (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom) :=
  (isAdicFibreSystemProperOver I X f hf).FullSubcategory

/-- **The completion functor of Stacks 08BF on coherent modules**, `𝓕 ↦ (𝓕|_{Xₙ})ₙ`: the base's
`AlgebraicGeometry.Space.adicFibreRestriction` for a bundled algebraic space `X`. -/
abbrev adicFibreRestrictionOf [IsNoetherianRing A]
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom) :
    CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2 ⥤ AdicFibreSystem I X f :=
  thickeningRestriction B (Spec (.of A)) hA (adicFibreInclusion A I B hA X f)
    (adicFibreSuccMap I X f) (adicFibreSuccMap_adicFibreInclusion I X f)
    (hasEtaleLocalProperty_isLocallyNoetherian_adicFibreSpace I X f hf)

/-- The restriction to the adic fibres of a coherent module with support proper over `A`
satisfies condition (3) of Stacks 08BF: the support of `𝓕|_{X₁}` is the inverse image of the
support of `𝓕` (Stacks 07TZ), proper over `S₁` by Stacks 0CZF. -/
theorem isAdicFibreSystemProperOver_adicFibreRestriction_obj [IsNoetherianRing A]
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom)
    (M : CoherentModulesProperOver B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2
      f.hom hf) :
    isAdicFibreSystemProperOver I X f hf ((adicFibreRestrictionOf I X f hf).obj M.obj) := by
  obtain ⟨hcl, hprop⟩ := M.property
  have hM : IsCoherent B (Spec (.of A)) hA X.1 X.2 M.obj.obj := M.obj.property
  let := hM.toIsCoherentOnSite
  have hsupp := supportOfSheaf_modulePullback_eq B (Spec (.of A)) hA
    (adicFibreInclusion A I B hA X f 0) M.obj.obj hM.toIsQuasicoherentOnSite
    (isFiniteTypeOnSite_of_isCoherentOnSite B (Spec (.of A)) hA X M.obj.obj)
  change HasProperSupport B (Spec (.of A)) hA (adicFibreSpaceOf A I B hA X f 0).2
    (schemeSpace (adicThickeningObject A I B hA (contains_adicThickening A I B hA) 0)).2
    (adicFibreProjection A I B hA X f 0).hom (isLocallyOfFiniteType_adicFibreProjection I X f hf 0)
    ((SheafOfModules.toSheaf _).obj
      ((modulePullback B (Spec (.of A)) hA (adicFibreInclusion A I B hA X f 0)).obj M.obj.obj))
  unfold HasProperSupport
  rw [hsupp]
  exact ⟨_, isProperOver_preimage B (Spec (.of A)) hA (isPullback_adicFibre A I B hA X f 0) hf
    _ hcl hprop⟩

/-- **The completion functor of Stacks 08BF**, from coherent `𝒪_X`-modules with support proper
over `A` to the systems satisfying conditions (1), (2) and (3). -/
def adicFibreRestrictionProperOver [IsNoetherianRing A]
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom) :
    CoherentModulesProperOver B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2 f.hom hf ⥤
      AdicFibreSystemsProperOver I X f hf :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ adicFibreRestrictionOf I X f hf)
    (isAdicFibreSystemProperOver_adicFibreRestriction_obj I X f hf)

/-! ### Stacks 08BF -/

/-- The comparison `iₙ^* ≅ iₙ₊₁^* ⋙ sₙ^*` of the tower of adic fibres is the inverse of the
transition isomorphism of the restricted systems. -/
theorem adicFibreSiteChangeTower_tri_hom_app (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    (n : ℕ) :
    ((adicFibreSiteChangeTower I X f).tri n).hom.app M =
      ((modulePullbackCompIsoOfEq B (Spec (.of A)) hA (adicFibreSuccMap I X f n)
        (adicFibreInclusion A I B hA X f (n + 1))
          (adicFibreSuccMap_adicFibreInclusion I X f n)).app M).inv :=
  modulePullbackTriangle_hom_app _ M

/-- The transition isomorphisms of the restriction of a coherent module to the adic fibres. -/
theorem adicFibreRestriction_obj_transitionIso [IsNoetherianRing A]
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom)
    (M : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2) (n : ℕ) :
    ((adicFibreRestrictionOf I X f hf).obj M).transitionIso n =
      (modulePullbackCompIsoOfEq B (Spec (.of A)) hA (adicFibreSuccMap I X f n)
        (adicFibreInclusion A I B hA X f (n + 1))
          (adicFibreSuccMap_adicFibreInclusion I X f n)).app M.obj :=
  TowerSystem.restriction_obj_transitionIso _ _ _ _ M n

/-- **Stacks 08B9 on the adic fibres**: a family of maps `αₙ : 𝓕|_{Xₙ} ⟶ 𝓖|_{Xₙ}` of
restrictions of coherent modules with support proper over `A`, compatible with the transition
isomorphisms, is the restriction of a unique map `𝓕 ⟶ 𝓖`. -/
theorem existsUnique_hom_of_adicFibreRestriction [IsNoetherianRing A] [IsAdicComplete I A]
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom)
    (M N : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    (hM : isCoherentProperOver B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2 f.hom
      hf M)
    (hN : isCoherentProperOver B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2 f.hom
      hf N)
    (α : ∀ n, (modulePullback B (Spec (.of A)) hA (adicFibreInclusion A I B hA X f n)).obj M.obj ⟶
      (modulePullback B (Spec (.of A)) hA (adicFibreInclusion A I B hA X f n)).obj N.obj)
    (hα : ∀ n, (modulePullback B (Spec (.of A)) hA (adicFibreSuccMap I X f n)).map (α (n + 1)) ≫
        (((adicFibreRestrictionOf I X f hf).obj N).transitionIso n).hom =
      (((adicFibreRestrictionOf I X f hf).obj M).transitionIso n).hom ≫ α n) :
    ∃! ψ : M.obj ⟶ N.obj,
      ∀ n, (modulePullback B (Spec (.of A)) hA (adicFibreInclusion A I B hA X f n)).map ψ =
        α n := by
  let := C1573.fact_isLocallyNoetherian_of_baseObject X f hf
  have hNc : IsCoherent B (Spec (.of A)) hA X.1 X.2 N.obj := N.property
  have hMc : IsCoherent B (Spec (.of A)) hA X.1 X.2 M.obj := M.property
  have hNp : HasProperSupport B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2 f.hom hf
      ((SheafOfModules.toSheaf _).obj N.obj) := hN
  have hMp : HasProperSupport B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2 f.hom hf
      ((SheafOfModules.toSheaf _).obj M.obj) := hM
  refine (adicFibreSiteChangeTower I X f).existsUnique_hom_of_compatible hf N.obj M.obj
    hNc hMc hNp hMp α fun n => ?_
  have h := hα n
  rw [adicFibreRestriction_obj_transitionIso, adicFibreRestriction_obj_transitionIso] at h
  rw [adicFibreSiteChangeTower_tri_hom_app, adicFibreSiteChangeTower_tri_hom_app]
  exact (Iso.comp_inv_eq _).2 (((Iso.eq_inv_comp _).2 h.symm).trans (Category.assoc _ _ _).symm)

/-- **Stacks 08B9 on the adic fibres, for systems**: every morphism between the restrictions of
two coherent modules with support proper over `A` is the restriction of a unique morphism. -/
theorem existsUnique_hom_of_adicFibreRestriction_hom [IsNoetherianRing A] [IsAdicComplete I A]
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom)
    (M N : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    (hM : isCoherentProperOver B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2 f.hom
      hf M)
    (hN : isCoherentProperOver B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2 f.hom
      hf N)
    (φ : (adicFibreRestrictionOf I X f hf).obj M ⟶ (adicFibreRestrictionOf I X f hf).obj N) :
    ∃! ψ : M ⟶ N, (adicFibreRestrictionOf I X f hf).map ψ = φ := by
  obtain ⟨ψ, hψ, hu⟩ := existsUnique_hom_of_adicFibreRestriction I X f hf M N hM hN
    (fun n => φ.app n) (fun n => φ.comm n)
  refine ⟨ObjectProperty.homMk ψ, TowerSystem.hom_ext fun n => hψ n, fun ψ' h => ?_⟩
  refine ObjectProperty.hom_ext _ (hu ψ'.hom fun n => ?_)
  exact congrArg (fun χ : (adicFibreRestrictionOf I X f hf).obj M ⟶
    (adicFibreRestrictionOf I X f hf).obj N => χ.app n) h

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.SiteChangeTower

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {R : Type u} [CommRing R]
  {hR : B.Contains (Spec (.of R))} {h : B.obj hR ⟶ B.obj hS}
  {X : AlgebraicSpaces B S hS} {π : X ⟶ schemeSpace (Over.mk h)} {J : Ideal R}
  {Z : ℕ → AlgebraicSpaces B S hS} {i : ∀ n, Z n ⟶ X} {s : ∀ n, Z n ⟶ Z (n + 1)}
  {T : ℕ → BigFppfOver B S hS} {ι : ∀ n, T n ⟶ Over.mk h} {p : ∀ n, Z n ⟶ schemeSpace (T n)}

/-- **Stacks 08BE on a tower of thickenings, for systems**: a system `(𝓕ₙ, φₙ)` of coherent
modules on the tower whose first term has support proper over `T₀` is isomorphic to the
restriction of a coherent `𝒪_X`-module with support proper over `Spec R`. -/
theorem exists_thickeningRestriction_obj_iso (𝒯 : SiteChangeTower X π J Z i s T ι p)
    [IsNoetherianRing R] [IsAdicComplete J R]
    [Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hπ : IsFiniteType B S hS π.hom) (hsep : IsSeparated B S hS π.hom)
    (hZ : ∀ n, HasEtaleLocalProperty B S hS (Z n).1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (hp : IsLocallyOfFiniteType B S hS (p 0).hom) (E : ThickeningCoherentSystem B S hS Z s)
    (hE : HasProperSupport B S hS (Z 0).2 (schemeSpace (T 0)).2 (p 0).hom hp
      ((SheafOfModules.toSheaf _).obj (E.term 0).obj)) :
    ∃ G : CoherentModules.{u, u} B S hS X.1 X.2,
      HasProperSupport B S hS X.2 (schemeSpace (Over.mk h)).2 π.hom hπ.1
        ((SheafOfModules.toSheaf _).obj G.obj) ∧
      Nonempty ((thickeningRestriction B S hS i s 𝒯.comp hZ).obj G ≅ E) := by
  obtain ⟨G, hG, hGp, ψ, hψ⟩ := 𝒯.exists_of_compatible (fun n => (E.term n).obj) hπ hsep
    (fun n => (E.term n).property) (fun n => E.transitionIso n) hp hE
  exact ⟨⟨G, hG⟩, hGp, ⟨TowerSystem.restrictionIsoMk G hG E ψ (fun n => 𝒯.tri n)
    (fun n => modulePullbackTriangle_eq_symm _) hψ⟩⟩

end AlgebraicGeometry.Space.SiteChangeTower

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  (I : Ideal A) (X : AlgebraicSpaces B (Spec (.of A)) hA)
  (f : X ⟶ schemeSpace (baseObject A B hA))

/-- **Stacks 08BE on the adic fibres**: every system satisfying conditions (1), (2) and (3) of
Stacks 08BF is isomorphic to the restriction of a coherent module with support proper over
`A`. -/
theorem exists_adicFibreRestriction_obj_iso [IsNoetherianRing A] [IsAdicComplete I A]
    (hf : IsFiniteType B (Spec (.of A)) hA f.hom) (hsep : IsSeparated B (Spec (.of A)) hA f.hom)
    (E : AdicFibreSystem I X f) (hE : isAdicFibreSystemProperOver I X f hf.1 E) :
    ∃ G : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2,
      isCoherentProperOver B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2 f.hom hf.1
        G ∧ Nonempty ((adicFibreRestrictionOf I X f hf.1).obj G ≅ E) := by
  let := C1573.fact_isLocallyNoetherian_of_baseObject X f hf.1
  exact (adicFibreSiteChangeTower I X f).exists_thickeningRestriction_obj_iso hf hsep
    (hasEtaleLocalProperty_isLocallyNoetherian_adicFibreSpace I X f hf.1)
    (isLocallyOfFiniteType_adicFibreProjection I X f hf.1 0) E hE

/-- **Stacks 08BF.**  Let `A` be a Noetherian ring complete with respect to an ideal `I`, write
`S = Spec A` and `Sₙ = Spec(A/Iⁿ)`, and let `X ⟶ S` be a separated morphism of algebraic spaces of
finite type, with `Xₙ = X ×_S Sₙ`.  Then the completion functor `𝓕 ↦ (𝓕|_{Xₙ})ₙ`, from coherent
`𝒪_X`-modules with support proper over `A` to systems `(𝓕ₙ, φₙ)` of coherent
`𝒪_{Xₙ}`-modules `𝓕ₙ` with isomorphisms `φₙ : iₙ^* 𝓕ₙ₊₁ ≅ 𝓕ₙ` such that `Supp(𝓕₁)` is proper
over `S₁`, is an equivalence of categories.

The adic fibres are indexed from `0`: `adicFibreSpaceOf A I B hA X f n` is the source's `Xₙ₊₁`. -/
@[stacks 08BF]
theorem isEquivalence_adicFibreRestrictionProperOver [IsNoetherianRing A] [IsAdicComplete I A]
    (hf : IsFiniteType B (Spec (.of A)) hA f.hom) (hsep : IsSeparated B (Spec (.of A)) hA f.hom) :
    (adicFibreRestrictionProperOver I X f hf.1).IsEquivalence :=
  ObjectProperty.isEquivalence_lift_comp_ι (adicFibreRestrictionOf I X f hf.1) _
    (fun M N hM hN φ => existsUnique_hom_of_adicFibreRestriction_hom I X f hf.1 M N hM hN φ)
    (fun E hE => exists_adicFibreRestriction_obj_iso I X f hf hsep E hE)

/-- A coherent module on an algebraic space proper over `Y` has support proper over `Y`. -/
private theorem hasProperSupport_of_isProper_of_isCoherent {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y) {f : X.1 ⟶ Y}
    {hf : IsLocallyOfFiniteType B S hS f} (hp : IsProper B S hS f)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : IsCoherent B S hS X.1 X.2 M) :
    HasProperSupport B S hS X.2 hY f hf ((SheafOfModules.toSheaf _).obj M) := by
  let := hM.toIsCoherentOnSite
  let := isFiniteTypeOnSite_of_isCoherentOnSite B S hS X M
  exact hasProperSupport_toSheaf_of_isProper B S hS X.2 hY f hf hp M

/-- **Stacks 08BF, the case of `X` proper over `A`.**  If `X ⟶ S = Spec A` is proper, the
completion functor `𝓕 ↦ (𝓕|_{Xₙ})ₙ` from all coherent `𝒪_X`-modules to all systems `(𝓕ₙ, φₙ)` of
coherent `𝒪_{Xₙ}`-modules with isomorphisms `φₙ : iₙ^* 𝓕ₙ₊₁ ≅ 𝓕ₙ` is an equivalence of
categories: the conditions on the supports can be omitted. -/
@[stacks 08BF "the special case of X proper over A, where the conditions on the supports are \
omitted"]
theorem isEquivalence_adicFibreRestriction_of_isProper [IsNoetherianRing A] [IsAdicComplete I A]
    (hf : IsProper B (Spec (.of A)) hA f.hom) :
    (adicFibreRestrictionOf I X f hf.2.1.1).IsEquivalence := by
  have hsrc : ∀ M : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2,
      isCoherentProperOver B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2 f.hom
        hf.2.1.1 M := fun M =>
    hasProperSupport_of_isProper_of_isCoherent _ hf M.obj M.property
  have hX₀ : IsProper B (Spec (.of A)) hA (adicFibreProjection A I B hA X f 0).hom :=
    (isProper_isStableUnderBaseChange B (Spec (.of A)) hA).of_isPullback
      (isPullback_adicFibre A I B hA X f 0) hf
  have htgt : ∀ E : AdicFibreSystem I X f, isAdicFibreSystemProperOver I X f hf.2.1.1 E :=
    fun E => hasProperSupport_of_isProper_of_isCoherent _ hX₀ _ (E.term 0).property
  refine Functor.isEquivalence_of_existsUnique_map_eq _
    (fun M N φ => existsUnique_hom_of_adicFibreRestriction_hom I X f hf.2.1.1 M N (hsrc M)
      (hsrc N) φ) (fun E => ?_)
  obtain ⟨G, -, hG⟩ := exists_adicFibreRestriction_obj_iso I X f hf.2.1 hf.1 E (htgt E)
  exact ⟨G, hG⟩

end AlgebraicGeometry.Space

end
