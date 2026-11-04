module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.CenteredGermDeathOfValuation

/-!
# Finitely many lifts of a geometric point through a point of an étale scheme

Let `U ⟶ Y` be étale, `t : Spec Ω ⟶ Y` a geometric point and `w ∈ U` over `y = t(pt)`. A lift
of `t` to `U` through `w` is a morphism `Spec Ω ⟶ U` over `Y` sending the point to `w`. It factors
through `Spec κ(w)`, so it is given by a field map `κ(w) → Ω`, and lying over `t` says that this
map restricts on `κ(y)` to the map given by `t`. The extension `κ(w)/κ(y)` is finite since
`U ⟶ Y` is unramified and locally of finite type, so there are finitely many such
`κ(y)`-embeddings, hence finitely many lifts. This proves the input
`AlgebraicGeometry.Scheme.ZariskiRiemann.FiniteLiftsAtPoint` of the Zariski–Riemann step of
Gabber's germ-killing argument.

## Main results

* `AlgebraicGeometry.Scheme.ZariskiRiemann.finite_residueField_of_etale`: the residue field
  extensions of an étale morphism are finite.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.exists_specMap_comp_fromSpecResidueField`: a
  field-valued point through `x` factors through `Spec κ(x)`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.finiteLiftsAtPoint`: the proposition
  `AlgebraicGeometry.Scheme.ZariskiRiemann.FiniteLiftsAtPoint` holds.

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

/-- **The residue field extensions of an étale morphism are finite**: for `f : X ⟶ Y` étale and
`x ∈ X`, `κ(x)` is a finite extension of `κ(f x)`. -/
theorem finite_residueField_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Module.Finite (Y.residueField (f x)) (X.residueField x) := by
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
  suffices hfin : Module.Finite
      (IsLocalRing.ResidueField <| Y.presheaf.stalk (f x))
      (IsLocalRing.ResidueField <| X.presheaf.stalk x) by
    convert! hfin
    exact congrArg (fun A : Algebra (Y.residueField (f x)) (X.residueField x) ↦
      @Algebra.toModule _ _ _ _ A) (Algebra.algebra_ext _ _ fun
        y : Y.residueField (f x) ↦ by
      obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective y
      rfl)
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    RingHom.essFiniteType_algebraMap.mpr (LocallyOfFiniteType.stalkMap f x)
  have : Algebra.FormallyUnramified (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    RingHom.formallyUnramified_algebraMap.mpr (FormallyUnramified.stalkMap f x)
  infer_instance

/-- A field-valued point `f : Spec K ⟶ X` through `x` factors through `Spec κ(x)`. -/
theorem exists_specMap_comp_fromSpecResidueField {X : Scheme.{u}} {K : Type u} [Field K]
    (f : Spec (.of K) ⟶ X) {x : X} (hx : f (default : Spec (.of K)) = x) :
    ∃ ι : X.residueField x ⟶ .of K, Spec.map ι ≫ X.fromSpecResidueField x = f := by
  obtain rfl : f (IsLocalRing.closedPoint K) = x :=
    (congrArg f (Subsingleton.elim (IsLocalRing.closedPoint K) (default : Spec (.of K)))).trans hx
  exact ⟨_, descResidueField_stalkClosedPointTo_fromSpecResidueField K X f⟩

/-- Two field-valued points through `x` with the same composite to `Y` induce the same field
map on `κ(g x)`. -/
theorem residueFieldMap_comp_eq_of_comp_eq {X Y : Scheme.{u}} (g : X ⟶ Y) {K : Type u} [Field K]
    {x : X} (ι ι' : X.residueField x ⟶ .of K)
    (h : (Spec.map ι ≫ X.fromSpecResidueField x) ≫ g =
      (Spec.map ι' ≫ X.fromSpecResidueField x) ≫ g) :
    g.residueFieldMap x ≫ ι = g.residueFieldMap x ≫ ι' := by
  have e : (Scheme.SpecToEquivOfField K Y).symm ⟨g x, g.residueFieldMap x ≫ ι⟩ =
      (Scheme.SpecToEquivOfField K Y).symm ⟨g x, g.residueFieldMap x ≫ ι'⟩ := by
    simp only [Scheme.SpecToEquivOfField_symm_apply, Spec.map_comp, Category.assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    simpa only [Category.assoc] using h
  exact eq_of_heq (Sigma.mk.inj_iff.mp ((Scheme.SpecToEquivOfField K Y).symm.injective e)).2

/-- **Finitely many lifts at a point**: for `U ⟶ Y` étale, a geometric point `t` of `Y` and
`w ∈ U`, the lifts of `t` to `U` through `w` are finite in number. Each is
`Spec ι ≫ (Spec κ(w) ⟶ U)` for a `κ(y)`-embedding `ι : κ(w) → Ω`, `y` the image of `w`, and
`κ(w)/κ(y)` is finite (`finite_residueField_of_etale`). -/
theorem finiteLiftsAtPoint : FiniteLiftsAtPoint.{u} := by
  intro Y U Ω _ _ t w
  have : Etale U.hom := U.prop
  -- the morphisms `Spec Ω ⟶ U` over `t` through `w`
  let S : Set (Spec (.of Ω) ⟶ U.left) :=
    {f | f (default : Spec (.of Ω)) = w ∧ f ≫ U.hom = t}
  have hinj : Function.Injective
      (fun ℓ : (Scheme.pointSmallEtale t).fiber.obj U ↦ etaleLiftHom ℓ) :=
    fun ℓ ℓ' h ↦ Over.OverMorphism.ext h
  suffices hS : S.Finite from
    (hS.preimage hinj.injOn).subset fun ℓ hℓ ↦ ⟨hℓ, etaleLiftHom_comp ℓ⟩
  rcases S.eq_empty_or_nonempty with hS | ⟨f₀, hf₀w, hf₀t⟩
  · simp [hS]
  obtain ⟨ι₀, hι₀⟩ := exists_specMap_comp_fromSpecResidueField f₀ hf₀w
  let : Algebra (Y.residueField (U.hom w)) (U.left.residueField w) :=
    (U.hom.residueFieldMap w).hom.toAlgebra
  let : Algebra (Y.residueField (U.hom w)) Ω := (U.hom.residueFieldMap w ≫ ι₀).hom.toAlgebra
  have : Module.Finite (Y.residueField (U.hom w)) (U.left.residueField w) :=
    finite_residueField_of_etale U.hom w
  refine (Set.finite_range fun ψ : U.left.residueField w →ₐ[Y.residueField (U.hom w)] Ω ↦
    Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ U.left.fromSpecResidueField w).subset ?_
  rintro f ⟨hfw, hft⟩
  obtain ⟨ι, rfl⟩ := exists_specMap_comp_fromSpecResidueField f hfw
  have hc : U.hom.residueFieldMap w ≫ ι = U.hom.residueFieldMap w ≫ ι₀ :=
    residueFieldMap_comp_eq_of_comp_eq (X := U.left) (Y := Y) U.hom ι ι₀ (by rw [hft, hι₀, hf₀t])
  exact ⟨{ ι.hom with commutes' := fun a ↦ congrArg (fun k ↦ k.hom a) hc }, rfl⟩

end AlgebraicGeometry.Scheme.ZariskiRiemann
