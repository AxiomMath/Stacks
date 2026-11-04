module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.Infinitesimal.ActionOnLifts
public import StacksFrontier.Deformation.Artin.Infinitesimal.Functoriality
public import StacksFrontier.Deformation.Artin.Obstruction.FieldCohomology

/-!
# Base-change tools for Stacks 07YA

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S`, let `x` be an
object of `𝒳` over `Spec A` and let `y ⟶ x` be a morphism lying over `Spec C ⟶ Spec A` for a
ring map `A ⟶ C`. Stacks 07YA compares the lifts of `x` with the lifts of `y`. This file
collects the general tools that comparison is built from; the map of tangent modules itself is
`Deformation.Artin.existsUnique_tangentBaseChange`, in
`StacksFrontier.Deformation.Artin.Obstruction.TangentPullback`, which is stated for an arbitrary
category fibred in groupoids and an arbitrary homomorphism of `S`-algebras.

## Main results

* `Deformation.Artin.exists_cartesian_of_underFiber_iso` — a cartesian pullback datum
  transports along an isomorphism of the lift being pulled back.
* `Deformation.Artin.underFiberClass_eq_of_cartesian` — the pullback of a class of lifts along
  a fixed arrow of the base, compatibly with a fixed arrow of the fibred category, is unique.
* `Deformation.Artin.squareZeroOverBaseMap_naturality` — the morphisms
  `Spec C[N] ⟶ Spec A[M]` of Stacks 07YA at two maps of coefficients form a commutative square
  with the two morphisms of trivial square-zero extensions of a map of coefficients.
* `Deformation.Artin.chartedSquareZeroBaseMap` and its two lemmas — the same morphism for a
  morphism of `Deformation.Artin.ChartedObject`s, the form the charted statements of
  `StacksFrontier.Deformation.Artin.Obstruction.InfAutBaseChangeMap` use.
* `Deformation.Artin.prodRestrictScalarsHom` — the map of coefficients on the diagonal product
  modules determined by a map of coefficients.
* `Deformation.Artin.ActionOnLiftsData.action_difference_eq`,
  `Deformation.Artin.ActionOnLiftsData.difference_eq_of_action` — the action of 07Y9 (2)(b) and
  its difference function determine one another: `action (difference z₁ z₂) z₂ = z₁`, and the
  difference is the unique element of the tangent module carrying one lift class to the other.
* `Deformation.Artin.ActionOnLiftsData.pull_action_of_difference` — a map on lift classes over
  two deformation situations which carries differences to differences along a map of tangent
  modules carries the action of `T_x(I)` to the action of `T_y(J)`.

## References

* [Stacks Project, Tag 07YA](https://stacks.math.columbia.edu/tag/07YA)
* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

/-! ### Pullbacks of lift classes along a fixed arrow of the base -/

section LiftPullback

open CategoryTheory.Functor

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X] (p : X ⥤ C)
  (hp : p.IsFiberedInGroupoids) {U U' V V' : C} {aa : U ⟶ U'} {cc : V ⟶ V'} (D : V' ⟶ U')
  {x y : X} {hx : p.obj x = U} {hy : p.obj y = V} (φ : y ⟶ x)

/-- Composing a lift of `D` with the underlying arrow of a morphism of fibres is again a lift
of `D`. -/
private theorem isHomLift_comp_underFiber_hom
    {u₁ u₂ : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ aa))} (m : u₁ ⟶ u₂)
    {v : X} (ρ : v ⟶ u₁.1.right) (hρ : p.IsHomLift D ρ) :
    p.IsHomLift D (ρ ≫ m.1.right) := by
  have hm : p.IsHomLift (𝟙 U') m.1.right := underPost_isHomLift_right p (𝟙 _) m.1 m.2
  exact IsHomLift.comp_lift_id_right' p D ρ U' m.1.right

/-- The comparison arrows between two cartesian arrows over `D`, induced by mutually inverse
arrows of the targets, compose to the identity. -/
private theorem map_comp_map_eq_id {v₁ v₂ u₁ u₂ : X} (ρ₁ : v₁ ⟶ u₁) (ρ₂ : v₂ ⟶ u₂)
    [p.IsStronglyCartesian D ρ₁] [p.IsStronglyCartesian D ρ₂] (a : u₁ ⟶ u₂) (b : u₂ ⟶ u₁)
    [p.IsHomLift D (ρ₁ ≫ a)] [p.IsHomLift D (ρ₂ ≫ b)] [p.IsHomLift (𝟙 V') (𝟙 v₁)]
    (hab : a ≫ b = 𝟙 u₁) :
    IsCartesian.map p D ρ₂ (ρ₁ ≫ a) ≫ IsCartesian.map p D ρ₁ (ρ₂ ≫ b) = 𝟙 v₁ := by
  refine IsCartesian.ext p D ρ₁ _ _ ?_
  rw [Category.id_comp, Category.assoc, IsCartesian.fac p D ρ₁, ← Category.assoc,
    IsCartesian.fac p D ρ₂, Category.assoc, hab, Category.comp_id]

include hp in
/-- **A cartesian pullback datum transports along an isomorphism of the lift being pulled
back.** Composing the comparison arrow with the underlying arrow of the isomorphism gives a
cartesian arrow to the other lift, compatible with the same arrow `φ`. -/
public theorem exists_cartesian_of_underFiber_iso
    {u₁ u₂ : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ aa))} (α : u₁ ≅ u₂)
    {v : (Under.post p).Fiber (Under.mk (eqToHom hy ≫ cc))}
    (ρ : v.1.right ⟶ u₁.1.right) (hρ : p.IsStronglyCartesian D ρ)
    (hw : v.1.hom ≫ ρ = φ ≫ u₁.1.hom) :
    ∃ ρ' : v.1.right ⟶ u₂.1.right,
      p.IsStronglyCartesian D ρ' ∧ v.1.hom ≫ ρ' = φ ≫ u₂.1.hom := by
  have hρ' := isHomLift_comp_underFiber_hom p D α.hom ρ inferInstance
  refine ⟨ρ ≫ α.hom.1.right, hp.isStronglyCartesian_homLift _ _, ?_⟩
  rw [← Category.assoc, hw, Category.assoc, Under.w α.hom.1]

/-- **The pullback of a class of lifts along a fixed arrow of the base is unique.** Two classes
of lifts of `y` under `cc`, each carrying a strongly cartesian arrow over `D` to a
representative of one class of lifts of `x` under `aa`, compatibly with `φ`, coincide.

This is `Deformation.Artin.eq_of_isSquareZeroLiftBaseChange` with the arrow `D` of the base an
arbitrary one. The transition of Stacks 07YA is stated there with `D` the morphism of trivial
square-zero extensions attached to a map of coefficients, which is not general enough for the
naturality of that transition: there `D` is a composite of two such morphisms. -/
public theorem underFiberClass_eq_of_cartesian
    {u₁ u₂ : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ aa))}
    {v₁ v₂ : (Under.post p).Fiber (Under.mk (eqToHom hy ≫ cc))}
    (hu : Quotient.mk (isIsomorphicSetoid _) u₁ = Quotient.mk (isIsomorphicSetoid _) u₂)
    (ρ₁ : v₁.1.right ⟶ u₁.1.right) (ρ₂ : v₂.1.right ⟶ u₂.1.right)
    (hρ₁ : p.IsStronglyCartesian D ρ₁) (hρ₂ : p.IsStronglyCartesian D ρ₂)
    (hw₁ : v₁.1.hom ≫ ρ₁ = φ ≫ u₁.1.hom) (hw₂ : v₂.1.hom ≫ ρ₂ = φ ≫ u₂.1.hom) :
    Quotient.mk (isIsomorphicSetoid _) v₁ = Quotient.mk (isIsomorphicSetoid _) v₂ := by
  obtain ⟨α⟩ := Quotient.exact hu
  have hhi : α.hom.1.right ≫ α.inv.1.right = 𝟙 u₁.1.right :=
    congrArg (fun m : u₁ ⟶ u₁ => m.1.right) α.hom_inv_id
  have hih : α.inv.1.right ≫ α.hom.1.right = 𝟙 u₂.1.right :=
    congrArg (fun m : u₂ ⟶ u₂ => m.1.right) α.inv_hom_id
  have hl₁ := isHomLift_comp_underFiber_hom p D α.hom ρ₁ inferInstance
  have hl₂ := isHomLift_comp_underFiber_hom p D α.inv ρ₂ inferInstance
  have hsv₁ : p.IsHomLift cc v₁.1.hom := underFiber_isHomLift p hy cc v₁
  have hsv₂ : p.IsHomLift cc v₂.1.hom := underFiber_isHomLift p hy cc v₂
  have hid₁ : p.IsHomLift (𝟙 V') (𝟙 v₁.1.right) :=
    IsHomLift.id (underFiber_right_obj p hy cc v₁)
  have hid₂ : p.IsHomLift (𝟙 V') (𝟙 v₂.1.right) :=
    IsHomLift.id (underFiber_right_obj p hy cc v₂)
  let ι := IsCartesian.map p D ρ₂ (ρ₁ ≫ α.hom.1.right)
  let ι' := IsCartesian.map p D ρ₁ (ρ₂ ≫ α.inv.1.right)
  have hιlift : p.IsHomLift (𝟙 V') ι := IsCartesian.map_isHomLift p D ρ₂ _
  have hι'lift : p.IsHomLift (𝟙 V') ι' := IsCartesian.map_isHomLift p D ρ₁ _
  have hιfac : ι ≫ ρ₂ = ρ₁ ≫ α.hom.1.right := IsCartesian.fac p D ρ₂ _
  have hι'fac : ι' ≫ ρ₁ = ρ₂ ≫ α.inv.1.right := IsCartesian.fac p D ρ₁ _
  have hιι' := map_comp_map_eq_id p D ρ₁ ρ₂ α.hom.1.right α.inv.1.right hhi
  have hι'ι := map_comp_map_eq_id p D ρ₂ ρ₁ α.inv.1.right α.hom.1.right hih
  have hunder : v₁.1.hom ≫ ι = v₂.1.hom := by
    refine IsStronglyCartesian.ext p D ρ₂ cc ?_
    rw [Category.assoc, hιfac, ← Category.assoc, hw₁, Category.assoc, Under.w α.hom.1, hw₂]
  refine Quotient.sound ⟨Functor.Fiber.isoMk (Under.isoMk ⟨ι, ι', hιι', hι'ι⟩ hunder) ?_⟩
  refine IsHomLift.of_fac' (Under.post p) (𝟙 _) _ v₁.2 v₂.2 ?_
  apply Under.UnderMorphism.ext
  simp only [Under.comp_right, Under.eqToHom_right, Under.id_right]
  exact IsHomLift.fac' p (𝟙 V') ι

end LiftPullback

/-! ### The commutative square of the two morphisms `Spec C[N] ⟶ Spec A[M]` -/

section BaseSquare

universe u

variable {A C : Type u} [CommRing A] [CommRing C] (f : A →+* C) (B : BigFppfSite.{u})
  (S : Scheme.{u}) (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (toSC : Spec (.of C) ⟶ S)
  (hf : Spec.map (CommRingCat.ofHom f) ≫ toS = toSC)

include hf in
/-- **The morphisms `Spec C[N] ⟶ Spec A[M]` of Stacks 07YA are natural in the coefficients.**
A map `s : M₁ ⟶ M₂` of `A`-modules and a map `t : N₁ ⟶ N₂` of `C`-modules compatible with two
maps of coefficients across `f` give a commutative square of the four induced morphisms of
trivial square-zero extensions. -/
public theorem squareZeroOverBaseMap_naturality
    {M₁ M₂ : SiteModule A B} {N₁ N₂ : SiteModule C B} (s : M₁ ⟶ M₂) (t : N₁ ⟶ N₂)
    (ψ₁ : M₁.obj ⟶ (ModuleCat.restrictScalars f).obj N₁.obj)
    (ψ₂ : M₂.obj ⟶ (ModuleCat.restrictScalars f).obj N₂.obj)
    (hcompat : s.hom ≫ ψ₂ = ψ₁ ≫ (ModuleCat.restrictScalars f).map t.hom) :
    squareZeroOverBaseMap f B S hS toS toSC hf M₂ N₂ (restrictScalarsAddHom f ψ₂)
          (restrictScalarsAddHom_smul f ψ₂) ≫ squareZeroOverMap A B S hS toS s =
      squareZeroOverMap C B S hS toSC t ≫
        squareZeroOverBaseMap f B S hS toS toSC hf M₁ N₁ (restrictScalarsAddHom f ψ₁)
          (restrictScalarsAddHom_smul f ψ₁) := by
  have hc : ∀ m : (M₁.obj : Type u), ψ₂ (s.hom m) = t.hom (ψ₁ m) := by
    intro m
    simpa using ConcreteCategory.congr_hom hcompat m
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  show Spec.map (CommRingCat.ofHom
        (squareZeroRingBaseMap f (restrictScalarsAddHom f ψ₂)
          (restrictScalarsAddHom_smul f ψ₂))) ≫
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map s.hom.hom).toRingHom) =
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map t.hom.hom).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (squareZeroRingBaseMap f (restrictScalarsAddHom f ψ₁)
          (restrictScalarsAddHom_smul f ψ₁)))
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  show squareZeroRingBaseMap f (restrictScalarsAddHom f ψ₂)
        (restrictScalarsAddHom_smul f ψ₂) ((TrivSqZeroExt.map s.hom.hom) z) =
      (TrivSqZeroExt.map t.hom.hom)
        (squareZeroRingBaseMap f (restrictScalarsAddHom f ψ₁)
          (restrictScalarsAddHom_smul f ψ₁) z)
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [TrivSqZeroExt.fst_map t.hom.hom, squareZeroRingBaseMap_apply,
      squareZeroRingBaseMap_apply]
    exact congrArg f (TrivSqZeroExt.fst_map s.hom.hom z)
  · rw [TrivSqZeroExt.snd_map t.hom.hom, squareZeroRingBaseMap_apply,
      squareZeroRingBaseMap_apply]
    exact (congrArg (fun y => restrictScalarsAddHom f ψ₂ y)
      (TrivSqZeroExt.snd_map s.hom.hom z)).trans (hc (TrivSqZeroExt.snd z))

end BaseSquare

/-! ### The transition on tangent modules -/

section TangentBaseChange

universe u v w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {c : AffineChart S}
  (hp : p.IsFiberedInGroupoids) {P Q : ChartedObject B S hS p c}
  (h : AffineObject.Hom P.obj Q.obj) (f : P.ring →+* Q.ring) (halg : f = h.alg.ringMap)
  (F : TangentFunctorData P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem p P.point
    P.obj.obj.2)
  (G : TangentFunctorData Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem p Q.point
    Q.obj.obj.2)

include halg in
/-- The morphism `Spec C[N] ⟶ Spec A[M]` of Stacks 07YA attached to a morphism of charted
objects and a map of coefficients. -/
public abbrev chartedSquareZeroBaseMap {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    Q.squareZeroBase N ⟶ P.squareZeroBase M :=
  squareZeroOverBaseMap f B S hS P.obj.alg.toScheme Q.obj.alg.toScheme
    (specMap_toScheme_comp h f halg) M N (restrictScalarsAddHom f ψ)
    (restrictScalarsAddHom_smul f ψ)

include halg in
/-- The square-zero immersions and the morphism of charted objects commute with
`Deformation.Artin.chartedSquareZeroBaseMap`. -/
public theorem specMap_comp_squareZeroArrow_chartedSquareZeroBaseMap
    {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    h.alg.specMap ≫ squareZeroArrow P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem M =
      squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N ≫
        chartedSquareZeroBaseMap h f halg ψ :=
  specMap_comp_squareZeroArrow h f halg M N (restrictScalarsAddHom f ψ)
    (restrictScalarsAddHom_smul f ψ)

include halg in
/-- `Deformation.Artin.squareZeroOverBaseMap_naturality` for a morphism of charted objects. -/
public theorem chartedSquareZeroBaseMap_naturality
    {M₁ M₂ : SiteModule P.ring B} {N₁ N₂ : SiteModule Q.ring B} (s : M₁ ⟶ M₂) (t : N₁ ⟶ N₂)
    (ψ₁ : M₁.obj ⟶ (ModuleCat.restrictScalars f).obj N₁.obj)
    (ψ₂ : M₂.obj ⟶ (ModuleCat.restrictScalars f).obj N₂.obj)
    (hcompat : s.hom ≫ ψ₂ = ψ₁ ≫ (ModuleCat.restrictScalars f).map t.hom) :
    chartedSquareZeroBaseMap h f halg ψ₂ ≫
        squareZeroOverMap P.ring B S hS P.obj.alg.toScheme s =
      squareZeroOverMap Q.ring B S hS Q.obj.alg.toScheme t ≫
        chartedSquareZeroBaseMap h f halg ψ₁ :=
  squareZeroOverBaseMap_naturality f B S hS P.obj.alg.toScheme Q.obj.alg.toScheme
    (specMap_toScheme_comp h f halg) s t ψ₁ ψ₂ hcompat

end TangentBaseChange

/-! ### The map of coefficients on the diagonal product modules -/

section ProdCoefficients

universe u

variable {A C : Type u} [CommRing A] [CommRing C] (f : A →+* C) {B : BigFppfSite.{u}}
  (hA : B.Contains (Spec (.of A))) (hC : B.Contains (Spec (.of C)))

/-- The map of coefficients on the two diagonal product modules determined by a map of
coefficients: the pair of two copies of it, written as a sum of composites of the projections,
the map itself and the two inclusions, so that no module structure has to be built by hand. -/
public def prodRestrictScalarsHom {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    (siteModuleProd A B hA M M).obj ⟶
      (ModuleCat.restrictScalars f).obj (siteModuleProd C B hC N N).obj :=
  (siteModuleFst A B hA M M).hom ≫ ψ ≫
      (ModuleCat.restrictScalars f).map (siteModuleInl C B hC N N).hom +
    (siteModuleSnd A B hA M M).hom ≫ ψ ≫
      (ModuleCat.restrictScalars f).map (siteModuleInr C B hC N N).hom

public theorem prodRestrictScalarsHom_apply {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (z : (siteModuleProd A B hA M M).obj) :
    prodRestrictScalarsHom f hA hC ψ z = (ψ z.1, ψ z.2) := by
  have h0 : prodRestrictScalarsHom f hA hC ψ z =
      ((ψ z.1, 0) : ↥N.obj × ↥N.obj) + (0, ψ z.2) := rfl
  rw [h0]
  exact Prod.ext (add_zero _) (zero_add _)

end ProdCoefficients


/-! ### The action half of the functoriality -/

namespace ActionOnLiftsData

section Action

universe u v w

variable {A : Type u} [CommRing A] {B : BigFppfSite.{u}} {S : Scheme.{u}}
  {hS : B.Contains S} {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {x : X}
  {hx : p.obj x = algebraOver A B S hS toS hA}
  {T : TangentFunctorData A B S hS toS hA p x hx}
  {A' : Type u} [CommRing A'] {hA' : B.Contains (Spec (.of A'))}
  {toS' : B.obj hA' ⟶ B.obj hS} {q : A' →+* A} {hq : Function.Surjective q}
  {hsq : (RingHom.ker q) ^ 2 = ⊥}
  {g : algebraOver A B S hS toS hA ⟶ (Over.mk toS' : BigFppfOver B S hS)}

/-- **The action of Stacks 07Y9 (2)(b) is recovered from its difference function.** Acting by
the difference of two lift classes carries the second to the first: the orbit map at a lift is
onto, and the difference of a translate from its source is the translating element. -/
public theorem action_difference_eq
    (α : ActionOnLiftsData A B S hS toS hA p x hx T A' hA' toS' q hq hsq g)
    (z₁ z₂ : liftClassesOver A B S hS toS hA p x hx g) :
    α.action (α.difference z₁ z₂) z₂ = z₁ := by
  obtain ⟨a, ha⟩ := (α.orbit_bijective z₂).2 z₁
  rw [← ha, α.action_difference a z₂]

/-- **The difference function of Stacks 07Y9 (2)(b) is determined by its action.** The
difference of a lift class from a second one is the unique element of the tangent module which
carries the second to the first.

With `Deformation.Artin.ActionOnLiftsData.action_difference_eq` this says that the action and
the difference determine one another. Hence the only field of
`Deformation.Artin.ActionOnLiftsData` tying either of them to the geometry of the fibred
category is `difference_geometric`, and the second commuting square of Stacks 07YA cannot be
proved without transporting `Deformation.Artin.IsGeometricDifference` along the ring map. -/
public theorem difference_eq_of_action
    (α : ActionOnLiftsData A B S hS toS hA p x hx T A' hA' toS' q hq hsq g)
    (a : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
      ↥(T.functor.obj ⟨ModuleCat.of A (RingHom.ker q), α.kernelIsSiteModule⟩))
    (z₁ z₂ : liftClassesOver A B S hS toS hA p x hx g) (ha : α.action a z₂ = z₁) :
    α.difference z₁ z₂ = a := by
  rw [← ha, α.action_difference a z₂]

end Action

section PullAction

universe u v w

variable {A C : Type u} [CommRing A] [CommRing C] {B : BigFppfSite.{u}} {S : Scheme.{u}}
  {hS : B.Contains S} {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  {toSC : Spec (.of C) ⟶ S} {hC : B.Contains (Spec (.of C))}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {x y : X}
  {hx : p.obj x = algebraOver A B S hS toS hA}
  {hy : p.obj y = algebraOver C B S hS toSC hC}
  {T : TangentFunctorData A B S hS toS hA p x hx}
  {T' : TangentFunctorData C B S hS toSC hC p y hy}
  {A' C' : Type u} [CommRing A'] [CommRing C']
  {hA' : B.Contains (Spec (.of A'))} {toS' : B.obj hA' ⟶ B.obj hS}
  {hC' : B.Contains (Spec (.of C'))} {toSC' : B.obj hC' ⟶ B.obj hS}
  {qA : A' →+* A} {hqA : Function.Surjective qA} {hsqA : (RingHom.ker qA) ^ 2 = ⊥}
  {qC : C' →+* C} {hqC : Function.Surjective qC} {hsqC : (RingHom.ker qC) ^ 2 = ⊥}
  {gA : algebraOver A B S hS toS hA ⟶ (Over.mk toS' : BigFppfOver B S hS)}
  {gC : algebraOver C B S hS toSC hC ⟶ (Over.mk toSC' : BigFppfOver B S hS)}

/-- **The second commuting square of Stacks 07YA, reduced to the difference.** Let `α` be the
action of `T_x(I)` on the lifts of `x` over `A'` and `β` the action of `T_y(J)` on the lifts of
`y` over `C'`, as in Stacks 07Y9 (2)(b). A map `pull` on lift classes and a map `L` of tangent
modules which together carry `α`-differences to `β`-differences also carry the `α`-action to the
`β`-action.

The hypothesis `hL` — that `pull` and `L` are compatible with the two difference functions — is
**assumed, not proved**: the differences of this development are the geometric ones of
`Deformation.Artin.IsGeometricDifference`, which glue two lifts over `A' ×_A A'`, and
transporting that gluing along `A ⟶ C` is not available here. What this theorem contributes is
the step of the source's last sentence that does not depend on it: since the action and the
difference determine one another, compatibility with the one is compatibility with the
other. -/
public theorem pull_action_of_difference
    (α : ActionOnLiftsData A B S hS toS hA p x hx T A' hA' toS' qA hqA hsqA gA)
    (β : ActionOnLiftsData C B S hS toSC hC p y hy T' C' hC' toSC' qC hqC hsqC gC)
    (pull : liftClassesOver A B S hS toS hA p x hx gA →
      liftClassesOver C B S hS toSC hC p y hy gC)
    (L : letI : Module A (RingHom.ker qA) := Stacks.Smooth.kerModule hqA hsqA
      letI : Module C (RingHom.ker qC) := Stacks.Smooth.kerModule hqC hsqC
      ↥(T.functor.obj ⟨ModuleCat.of A (RingHom.ker qA), α.kernelIsSiteModule⟩) →
        ↥(T'.functor.obj ⟨ModuleCat.of C (RingHom.ker qC), β.kernelIsSiteModule⟩))
    (hL : ∀ z₁ z₂, β.difference (pull z₁) (pull z₂) = L (α.difference z₁ z₂))
    (t : letI : Module A (RingHom.ker qA) := Stacks.Smooth.kerModule hqA hsqA
      ↥(T.functor.obj ⟨ModuleCat.of A (RingHom.ker qA), α.kernelIsSiteModule⟩))
    (z : liftClassesOver A B S hS toS hA p x hx gA) :
    pull (α.action t z) = β.action (L t) (pull z) := by
  have hdiff : β.difference (pull (α.action t z)) (pull z) = L t := by
    rw [hL (α.action t z) z, α.action_difference t z]
  rw [← hdiff, β.action_difference_eq]

end PullAction

end ActionOnLiftsData

end Deformation.Artin

end
