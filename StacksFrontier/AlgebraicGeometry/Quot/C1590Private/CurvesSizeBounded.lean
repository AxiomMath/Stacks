module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Countability.IsomorphismClasses
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyTotalScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion
import StacksFrontier.AlgebraicGeometry.Limits.CountableFlatModel
import StacksFrontier.AlgebraicGeometry.Quot.PolarizedLimitPreserving
import StacksFrontier.AlgebraicGeometry.Size.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.ChowTwistWitness
import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence

/-!
# Axiom [-1] for the stack of curves (towards Stacks 0D5A)

Artin's criterion (Stacks 07Y4), applied to the stack `Curves` in the proof of Stacks 0D5A, asks
for the half of axiom [-1] that `AlgebraicGeometry.Stack.IsSizeBounded` records: the isomorphism
classes of the fibres of `Curves` over the finite type fields of `Spec(ℤ)` are bounded by the
size of one object of the site. This file proves it.

A field `k` of finite type over `Spec(ℤ)` is countable, being a finitely generated ring. A family
of curves `X ⟶ Spec(k)` has a scheme as total space (Stacks 0ADD,
`AlgebraicGeometry.CurveFamily.isRepresentable_total_of_base_eq`), proper and hence of finite
type over `k`; and a family of curves over `Spec(k)` is determined up to isomorphism over the
identity of `Spec(k)` by its total scheme over `k`. Over a countable field there are countably
many isomorphism classes of schemes of finite type (Stacks 0G0U,
`AlgebraicGeometry.countable_isomorphismClasses_of_finiteType`), so the fibre of `Curves` over
`Spec(k)` has countably many isomorphism classes; and `Spec(ℤ)` itself has size at least `ℵ₀`.

## Main definitions

* `AlgebraicGeometry.C1590Private.finiteTypeScheme`: the total scheme of a family of curves over
  the spectrum of a field, as a scheme of finite type over it.

## Main results

* `AlgebraicGeometry.C1590Private.nonempty_fiber_iso_of_finiteTypeScheme_iso`: a family of
  curves over the spectrum of a field is determined by its total scheme.
* `AlgebraicGeometry.C1590Private.isSizeBounded_curvesFiberedCategory`: axiom [-1] for `Curves`,
  in the form `AlgebraicGeometry.Stack.IsSizeBounded` consumed by Artin's criterion.

## References

* [Stacks Project, Tag 07Y3](https://stacks.math.columbia.edu/tag/07Y3)
* [Stacks Project, Tag 0D5A](https://stacks.math.columbia.edu/tag/0D5A)
* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
* [Stacks Project, Tag 0G0U](https://stacks.math.columbia.edu/tag/0G0U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1590Private

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- The underlying type of a commutative ring isomorphic to a countable one is countable. -/
private theorem countable_of_iso {R S : CommRingCat.{u}} (e : R ≅ S) [Countable S] : Countable R :=
  Function.Injective.countable (f := e.hom.hom) (ConcreteCategory.bijective_of_isIso _).1

/-- The global sections of `Spec(ℤ)` are countable. -/
theorem countable_sections_integerBase : Countable Γ(integerBase.{u}, ⊤) :=
  countable_of_iso (Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} ℤ)))

/-- **A field of finite type over `Spec(ℤ)` is countable**: it is a finitely generated algebra
over the integers (`AlgebraicGeometry.countable_sections_of_locallyOfFiniteType`). -/
theorem countable_of_isFiniteTypeOver (U : BigFppfOver B integerBase hZ) {k : Type u} [Field k]
    (hU : U.left.1 = Spec (.of k)) (hft : Deformation.Artin.IsFiniteTypeOver B integerBase hZ U) :
    Countable k := by
  have : LocallyOfFiniteType (B.inclusion.map U.hom) := hft.1
  have : IsAffine (B.inclusion.obj (B.obj hZ)) := inferInstanceAs (IsAffine integerBase.{u})
  have : IsAffine (B.inclusion.obj U.left) := by
    change IsAffine U.left.1
    rw [hU]
    infer_instance
  have hZc : Countable Γ(B.inclusion.obj (B.obj hZ), ⊤) := countable_sections_integerBase
  have h := countable_sections_of_locallyOfFiniteType (B.inclusion.map U.hom) hZc ⊤
    (isAffineOpen_top _)
  have h' : Countable Γ(Spec (.of k), ⊤) := by
    change Countable Γ(U.left.1, ⊤) at h
    rwa [hU] at h
  exact countable_of_iso (Scheme.ΓSpecIso (CommRingCat.of k)).symm

/-- The schemes of finite type over `Spec k`, as a full subcategory of the schemes over it. -/
abbrev FiniteTypeOver (k : Type u) [Field k] :=
  ObjectProperty.FullSubcategory (fun X : Over (Spec (.of k)) =>
    LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom)

section Scheme

variable (y : CurveFamily B hZ) {k : Type u} [Field k]
  (hK : (BigFppfOver.toScheme B integerBase hZ).obj y.base = Spec (.of k))

/-- The object of the site representing the total space of a family of curves over the spectrum
of a field (Stacks 0ADD). -/
noncomputable def totalSchemeObj : BigFppfOver B integerBase hZ :=
  haveI := y.isRepresentable_total_of_base_eq hK
  y.total.obj.reprX

/-- The identification of the represented presheaf with the total space. -/
noncomputable def totalSchemeIso : yoneda.obj (totalSchemeObj y hK) ≅ y.total.obj :=
  haveI := y.isRepresentable_total_of_base_eq hK
  y.total.obj.reprW

/-- The structure morphism of the representing object, to the base of the family. -/
noncomputable def totalSchemeHom : totalSchemeObj y hK ⟶ y.base :=
  yoneda.preimage ((totalSchemeIso y hK).hom ≫ y.toBase.hom)

/-- The structure morphism of the representing object induces the structure morphism of the
family. -/
theorem yoneda_map_totalSchemeHom :
    yoneda.map (totalSchemeHom y hK) = (totalSchemeIso y hK).hom ≫ y.toBase.hom :=
  yoneda.map_preimage _

/-- The representing scheme is proper over the base, as the family is. -/
theorem isProper_totalSchemeHom :
    IsProper ((BigFppfOver.toScheme B integerBase hZ).map (totalSchemeHom y hK)) := by
  apply Space.isProper_toScheme_map_of_isProper_yoneda_map
  rw [yoneda_map_totalSchemeHom]
  exact Space.isProper_comp' B integerBase hZ _ _ y.total.property
    (isAlgebraicSpace_yoneda B integerBase hZ _) (Space.isProper_of_isIso B integerBase hZ _)
    y.proper

/-- The total space of a family of curves over `Spec k` as a scheme of finite type over `k`. -/
noncomputable def finiteTypeScheme : FiniteTypeOver k :=
  haveI := isProper_totalSchemeHom y hK
  ⟨Over.mk ((BigFppfOver.toScheme B integerBase hZ).map (totalSchemeHom y hK) ≫ eqToHom hK),
    inferInstanceAs (LocallyOfFiniteType (_ ≫ eqToHom hK)),
    inferInstanceAs (QuasiCompact (_ ≫ eqToHom hK))⟩

end Scheme


/-- **A family of curves over a field is determined by its total scheme.** Two families of curves
over the same object `U` of the site, which is the spectrum of a field `k`, whose total schemes
are isomorphic over `k` are isomorphic in the fibre of `Curves` over `U`: an isomorphism of the
representing schemes induces one of the total spaces over the identity of `U`, whose square is
cartesian because both horizontal arrows are isomorphisms. -/
theorem nonempty_fiber_iso_of_finiteTypeScheme_iso (U : BigFppfOver B integerBase hZ)
    {k : Type u} [Field k] (y y' : CurveFamily B hZ)
    (ha : (curvesFiberedCategory B hZ).val.p.obj y = U)
    (hb : (curvesFiberedCategory B hZ).val.p.obj y' = U)
    (hKa : (BigFppfOver.toScheme B integerBase hZ).obj y.base = Spec (.of k))
    (hKb : (BigFppfOver.toScheme B integerBase hZ).obj y'.base = Spec (.of k))
    (φ : finiteTypeScheme y hKa ≅ finiteTypeScheme y' hKb) :
    Nonempty (Functor.Fiber.mk ha ≅ Functor.Fiber.mk hb) := by
  have hgpd := (curvesFiberedCategory B hZ).property.fiber_isGroupoid U
  change y.base = U at ha
  change y'.base = U at hb
  let fIso := (ObjectProperty.ι _ ⋙ Over.forget _).mapIso φ
  let ψ : totalSchemeObj y hKa ≅ totalSchemeObj y' hKb := Over.isoMk (B.inclusion.preimageIso fIso)
    ((isTerminal_obj_specULiftZ B hZ).hom_ext _ _)
  have hψ : (BigFppfOver.toScheme B integerBase hZ).map ψ.hom = φ.hom.hom.left :=
    B.inclusion.map_preimage _
  have hbase : y.base = y'.base := ha.trans hb.symm
  have h1 : ψ.hom ≫ totalSchemeHom y' hKb = totalSchemeHom y hKa ≫ eqToHom hbase := by
    apply (BigFppfOver.toScheme B integerBase hZ).map_injective
    have h := φ.hom.hom.w
    simp only [finiteTypeScheme, Over.mk_hom] at h
    simp only [Functor.map_comp, eqToHom_map, hψ]
    simpa using congrArg (· ≫ eqToHom hKb.symm) h
  let Θ : y.total.obj ≅ y'.total.obj :=
    (totalSchemeIso y hKa).symm ≪≫ yoneda.mapIso ψ ≪≫ totalSchemeIso y' hKb
  have hΘ : Θ.hom ≫ y'.toBase.hom = (y.toBase ≫ schemeSpaceMap (eqToHom hbase)).hom := by
    have h2 := congrArg yoneda.map h1
    simp only [Functor.map_comp, yoneda_map_totalSchemeHom] at h2
    exact (congrArg (fun g => (totalSchemeIso y hKa).inv ≫ g) h2).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ yoneda.map (eqToHom hbase)) (Iso.inv_hom_id_assoc _ _)))
  have : IsIso (schemeSpaceMap (eqToHom hbase)) := by
    have : IsIso ((ObjectProperty.ι _).map (schemeSpaceMap (eqToHom hbase))) := by
      change IsIso (yoneda.map _)
      infer_instance
    exact isIso_of_fully_faithful (ObjectProperty.ι _) _
  let c : y ⟶ y' :=
    ⟨eqToHom hbase, (ObjectProperty.isoMk _ Θ).hom,
      IsPullback.of_horiz_isIso ⟨ObjectProperty.hom_ext _ hΘ⟩⟩
  have hc : (curvesFiberedCategory B hZ).val.p.IsHomLift (𝟙 U) c :=
    IsHomLift.of_fac' _ _ _ ha hb (by
      rw [Category.id_comp]
      exact (eqToHom_trans ha hb.symm).symm)
  let m : Functor.Fiber.mk ha ⟶ Functor.Fiber.mk hb := ⟨c, hc⟩
  exact ⟨@asIso _ _ _ _ m (hgpd.all_isIso m)⟩

variable (B hZ) in
/-- **Axiom [-1] for `Curves`**, in the form `AlgebraicGeometry.Stack.IsSizeBounded` consumed by
Artin's criterion: the fibre of `Curves` over the spectrum of a field of finite type over
`Spec(ℤ)` has countably many isomorphism classes, being embedded into the isomorphism classes of
schemes of finite type over a countable field (Stacks 0G0U), and the size of `Spec(ℤ)` is at
least `ℵ₀`. -/
theorem isSizeBounded_curvesFiberedCategory :
    Stack.IsSizeBounded B integerBase hZ (curvesFiberedCategory B hZ) := by
  refine ⟨Over.mk (𝟙 (B.obj hZ)), fun U k _ hU hft => ?_⟩
  have : Countable k := countable_of_isFiniteTypeOver U hU hft
  have hK : ∀ a : (curvesFiberedCategory B hZ).val.p.Fiber U,
      (BigFppfOver.toScheme B integerBase hZ).obj a.1.base = Spec (.of k) := fun a =>
    (congrArg (BigFppfOver.toScheme B integerBase hZ).obj a.2).trans hU
  let F : Quotient (isIsomorphicSetoid ((curvesFiberedCategory B hZ).val.p.Fiber U)) →
      Quotient (isIsomorphicSetoid (FiniteTypeOver k)) := fun q =>
    ⟦finiteTypeScheme q.out.1 (hK q.out)⟧
  have hF : Function.Injective F := by
    intro q q' h
    obtain ⟨φ⟩ := Quotient.exact h
    obtain ⟨ψ⟩ := nonempty_fiber_iso_of_finiteTypeScheme_iso U q.out.1 q'.out.1 q.out.2 q'.out.2
      (hK q.out) (hK q'.out) φ
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    exact Quotient.sound ⟨ψ⟩
  have h1 : Cardinal.mk (Quotient (isIsomorphicSetoid
      ((curvesFiberedCategory B hZ).val.p.Fiber U))) ≤ Cardinal.aleph0 :=
    (Cardinal.mk_le_of_injective hF).trans
      (have := countable_isomorphismClasses_of_finiteType k; Cardinal.mk_le_aleph0)
  have h2 : Cardinal.aleph0 ≤ (Over.mk (𝟙 (B.obj hZ))).left.1.size := by
    have hc : Cardinal.mk Γ(integerBase.{u}, ⊤) = Cardinal.aleph0 := by
      have : Infinite Γ(integerBase.{u}, ⊤) := Infinite.of_injective
        (fun n : ℕ => (Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} ℤ))).inv.hom (ULift.up n))
        (fun m n h => by
          exact_mod_cast congrArg ULift.down
            ((ConcreteCategory.bijective_of_isIso
              (Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} ℤ))).inv).1 h))
      have := countable_sections_integerBase.{u}
      exact Cardinal.mk_eq_aleph0 _
    exact hc.symm.le.trans (Scheme.mk_sections_le_size integerBase ⟨⊤, isAffineOpen_top _⟩)
  exact (Cardinal.lift_le_aleph0.2 h1).trans (Cardinal.aleph0_le_lift.2 h2)

end AlgebraicGeometry.C1590Private

end
