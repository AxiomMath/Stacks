module

public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Countability.CoherentModules
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Countability.IsomorphismClasses
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.RingedSpace
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStackUnconditional
public import StacksFrontier.AlgebraicGeometry.Size.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion

/-!
# Axiom [-1] for the stack of polarized proper schemes

Artin's criterion (Stacks 07Y4), applied to the stack `𝒫olarized` of Stacks 0D4X over
`Spec(ℤ)`, asks for the half of axiom [-1] that `AlgebraicGeometry.Stack.IsSizeBounded` records:
the isomorphism classes of the fibres of `𝒫olarized` over the finite type fields of `Spec(ℤ)`
are bounded by the size of one object of the site. This file proves it.

A field `k` of finite type over `Spec(ℤ)` is countable. A polarized family `(X ⟶ Spec(k), ℒ)` is
proper, so `X` is a scheme of finite type over `k`, and `ℒ` is invertible, hence coherent on the
Noetherian scheme `X`. Over a countable field there are countably many isomorphism classes of
schemes of finite type (Stacks 0G0U), and on each of them countably many isomorphism classes of
coherent modules (Stacks 0G0W). Recording the class of `X` over `k` together with the class of
`ℒ` transported to the chosen representative of that class determines the polarized family up to
isomorphism over `Spec(k)`, so the fibre has countably many isomorphism classes; and every scheme
has size at least `ℵ₀`.

## Main results

* `AlgebraicGeometry.countable_isoClasses_polarizedFiber`: over a finite type field of
  `Spec(ℤ)` the fibre of `𝒫olarized` has countably many isomorphism classes.
* `AlgebraicGeometry.isSizeBounded_polarizedStackUnconditional`: axiom [-1] in the form
  `AlgebraicGeometry.Stack.IsSizeBounded` consumed by Artin's criterion, for `𝒫olarized`.

## Implementation notes

The base is `Spec(ULift ℤ)`, the spectrum of the integers raised to the universe of the site,
with `AlgebraicGeometry.isTerminal_obj_specULiftZ` exhibiting it as terminal, as in the other
statements about `𝒫olarized` over the absolute base.

No Stacks tag is carried here: axiom [-1] is a hypothesis of Stacks 07Y4, not a statement of
the source's section on polarized schemes.

## References

* [Stacks Project, Tag 07Y3](https://stacks.math.columbia.edu/tag/07Y3)
* [Stacks Project, Tag 0D4X](https://stacks.math.columbia.edu/tag/0D4X)
* [Stacks Project, Tag 0G0U](https://stacks.math.columbia.edu/tag/0G0U)
* [Stacks Project, Tag 0G0W](https://stacks.math.columbia.edu/tag/0G0W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

namespace PolarizedSizeBounded

variable {B : BigFppfSite.{u}} {hZ : B.Contains (Spec (CommRingCat.of (ULift.{u} ℤ)))}

/-- A code for a polarized family over `K`: the isomorphism class of its total space among the
schemes of finite type over `K`, and the isomorphism class of a coherent module on the chosen
representative of that class. -/
abbrev Code (K : Scheme.{u}) :=
  Σ c : Quotient (isIsomorphicSetoid (ObjectProperty.FullSubcategory
      (fun X : Over K => LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom))),
    Skeleton (SheafOfModules.CoherentModules c.out.obj.left.ringCatSheaf)

/-- Over the spectrum of a countable field there are countably many codes: countably many
isomorphism classes of schemes of finite type (Stacks 0G0U) and, on each of them, countably many
isomorphism classes of coherent modules (Stacks 0G0W). -/
theorem countable_code {K : Scheme.{u}} {k : Type u} [Field k] [Countable k]
    (h : K = Spec (.of k)) : Countable (Code K) := by
  subst h
  have := countable_isomorphismClasses_of_finiteType k
  have : ∀ c : Quotient (isIsomorphicSetoid (ObjectProperty.FullSubcategory
      (fun X : Over (Spec (.of k)) => LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom))),
      Countable (Skeleton (SheafOfModules.CoherentModules c.out.obj.left.ringCatSheaf)) := by
    intro c
    have : LocallyOfFiniteType c.out.obj.hom := c.out.property.1
    have : QuasiCompact c.out.obj.hom := c.out.property.2
    have := essentiallyCountable_coherentModules_of_finiteType (R := k) c.out.obj.hom
    infer_instance
  infer_instance

variable (B hZ) in
/-- The polarized family `x`, lying over the object `U` of the site, is presented by the code
`c`: its total space is isomorphic over `U` to the representative named by `c`, and its
polarization, transported along that isomorphism, is isomorphic to the representative of the
module class named by `c`. -/
def Presents (U : BigFppfOver B _ hZ) (x : PolarizedFamily B) (hx : x.base = U.left)
    (c : Code (B.inclusion.obj U.left)) : Prop :=
  ∃ e : c.1.out.obj.left ≅ x.total,
    e.hom ≫ x.toBase ≫ eqToHom (congrArg B.inclusion.obj hx) = c.1.out.obj.hom ∧
      Nonempty ((Scheme.Modules.pullback e.hom).obj x.lineBundle ≅
        ((fromSkeleton _).obj c.2).obj)

/-- Every polarized family over an object of the site whose underlying scheme is Noetherian is
presented by some code. -/
theorem exists_presents (U : BigFppfOver B _ hZ) [IsNoetherian (B.inclusion.obj U.left)]
    (x : PolarizedFamily B) (hx : x.base = U.left) : ∃ c, Presents B hZ U x hx c := by
  classical
  let K := B.inclusion.obj U.left
  let q : x.total ⟶ K := x.toBase ≫ eqToHom (congrArg B.inclusion.obj hx)
  have : IsProper x.toBase := x.proper
  have hqft : LocallyOfFiniteType q := inferInstance
  have hqqc : QuasiCompact q := inferInstance
  let Xo : ObjectProperty.FullSubcategory
      (fun X : Over K => LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom) :=
    ⟨Over.mk q, hqft, hqqc⟩
  let c₁ : Quotient (isIsomorphicSetoid (ObjectProperty.FullSubcategory
      (fun X : Over K => LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom))) :=
    Quotient.mk (isIsomorphicSetoid _) Xo
  obtain ⟨E⟩ : Nonempty (c₁.out ≅ Xo) := Quotient.mk_out (s := isIsomorphicSetoid _) Xo
  let e : c₁.out.obj.left ≅ x.total :=
    (Over.forget K).mapIso ((ObjectProperty.ι _).mapIso E)
  have he : e.hom ≫ x.toBase ≫ eqToHom (congrArg B.inclusion.obj hx) = c₁.out.obj.hom :=
    Over.w ((ObjectProperty.ι _).map E.hom)
  -- the transported polarization is coherent
  have hinv : SheafOfModules.IsInvertible c₁.out.obj.left.presheaf
      c₁.out.obj.left.ringCatSheaf.2 ((Scheme.Modules.pullback e.hom).obj x.lineBundle) :=
    have := x.invertible
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback e.hom.toLRSHom.toShHom
      x.lineBundle
  have : LocallyOfFiniteType c₁.out.obj.hom := c₁.out.property.1
  have : QuasiCompact c₁.out.obj.hom := c₁.out.property.2
  have : IsNoetherian c₁.out.obj.left := isNoetherian_of_locallyOfFiniteType c₁.out.obj.hom
  have hfp := Stacks.ModuleDescent.isFinitePresentation_of_isInvertible _ _ hinv
  have hcoh := (Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_iff_isFinitePresentation
    ((Scheme.Modules.pullback e.hom).obj x.lineBundle)).mpr hfp
  let M : SheafOfModules.CoherentModules c₁.out.obj.left.ringCatSheaf :=
    ⟨(Scheme.Modules.pullback e.hom).obj x.lineBundle, hcoh⟩
  refine ⟨⟨c₁, toSkeleton M⟩, e, he, ⟨?_⟩⟩
  exact ((ObjectProperty.ι _).mapIso (fromSkeletonToSkeletonIso M)).symm

/-- Two polarized families over `U` presented by the same code are isomorphic over `U`. -/
theorem exists_iso_of_presents (U : BigFppfOver B _ hZ) {x x' : PolarizedFamily B}
    (hx : x.base = U.left) (hx' : x'.base = U.left)
    {c : Code (B.inclusion.obj U.left)} (h : Presents B hZ U x hx c)
    (h' : Presents B hZ U x' hx' c) :
    ∃ φ : x ⟶ x', φ.baseMap = eqToHom (hx.trans hx'.symm) := by
  obtain ⟨e, he, ⟨eM⟩⟩ := h
  obtain ⟨e', he', ⟨eM'⟩⟩ := h'
  have hcomm : (e.inv ≫ e'.hom) ≫ x'.toBase =
      x.toBase ≫ B.inclusion.map (eqToHom (hx.trans hx'.symm)) := by
    rw [eqToHom_map]
    have h₁ : e.inv ≫ e'.hom ≫ x'.toBase ≫ eqToHom (congrArg B.inclusion.obj hx') =
        x.toBase ≫ eqToHom (congrArg B.inclusion.obj hx) := by
      rw [he', ← he, Iso.inv_hom_id_assoc]
    have h₂ := congrArg (· ≫ eqToHom (congrArg B.inclusion.obj hx'.symm)) h₁
    simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using h₂
  let ψ : (Scheme.Modules.pullback e'.hom).obj x'.lineBundle ≅
      (Scheme.Modules.pullback e.hom).obj x.lineBundle := eM' ≪≫ eM.symm
  refine ⟨{ baseMap := eqToHom (hx.trans hx'.symm)
            totalMap := e.inv ≫ e'.hom
            cartesian := IsPullback.of_horiz_isIso ⟨hcomm⟩
            lineBundleIso :=
              (Scheme.Modules.pullbackComp e.inv e'.hom).symm.app x'.lineBundle ≪≫
                (Scheme.Modules.pullback e.inv).mapIso ψ ≪≫
                (Scheme.Modules.pullbackComp e.inv e.hom).app x.lineBundle ≪≫
                (Scheme.Modules.pullbackCongr e.inv_hom_id).app x.lineBundle ≪≫
                (Scheme.Modules.pullbackId x.total).app x.lineBundle }, rfl⟩

end PolarizedSizeBounded

open PolarizedSizeBounded

variable (B : BigFppfSite.{u}) (hZ : B.Contains (Spec (CommRingCat.of (ULift.{u} ℤ))))

/-- **Countably many polarized proper schemes over a finite type field.** If `U` is an object of
the big fppf site of `Spec(ℤ)` whose underlying scheme is the spectrum of a field `k` of finite
type over `Spec(ℤ)`, the fibre of `𝒫olarized` over `U` has countably many isomorphism
classes. -/
theorem countable_isoClasses_polarizedFiber (U : BigFppfOver B _ hZ) (k : Type u) [Field k]
    (hU : U.left.1 = Spec (.of k)) (hft : Deformation.Artin.IsFiniteTypeOver B _ hZ U) :
    Countable (Quotient (isIsomorphicSetoid
      ((polarizedSliceProjection B hZ (isTerminal_obj_specULiftZ B hZ)).Fiber U))) := by
  classical
  obtain ⟨h₁, h₂⟩ := hft
  have hK : B.inclusion.obj U.left = Spec (.of k) := hU
  have hUaff : IsAffine (B.inclusion.obj U.left) := by
    rw [hK]
    infer_instance
  have hΓ : Countable Γ(B.inclusion.obj U.left, ⊤) :=
    countable_sections_of_finiteType (R := ULift.{u} ℤ) (B.inclusion.map U.hom)
      (isAffineOpen_top (B.inclusion.obj U.left))
  have : Countable k := by
    revert hΓ
    rw [hK]
    exact fun hΓ =>
      (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toEquiv.symm.injective.countable
  have : IsNoetherian (B.inclusion.obj U.left) := by
    rw [hK]
    infer_instance
  have := countable_code hK
  let p := polarizedSliceProjection B hZ (isTerminal_obj_specULiftZ B hZ)
  have hbase : ∀ x : p.Fiber U, x.1.base = U.left := fun x => congrArg Comma.left x.2
  have hpres : ∀ x : p.Fiber U, ∃ c, Presents B hZ U x.1 (hbase x) c :=
    fun x => exists_presents U x.1 (hbase x)
  choose code hcode using hpres
  have hgrp : IsGroupoid (p.Fiber U) :=
    Functor.IsFiberedInGroupoids.fiber_isGroupoid
      (polarizedProjection_isFiberedInGroupoids_unconditional.sliceAtTerminal
        (isTerminal_obj_specULiftZ B hZ)) U
  refine Function.Injective.countable (f := fun q => code q.out) ?_
  intro q q' hqq
  rw [← Quotient.out_eq q, ← Quotient.out_eq q']
  apply Quotient.sound
  obtain ⟨φ, hφ⟩ := exists_iso_of_presents U (hbase q.out) (hbase q'.out) (hcode q.out)
    ((congrArg (Presents B hZ U q'.out.1 (hbase q'.out)) hqq).mpr (hcode q'.out))
  have hlift : p.IsHomLift (𝟙 U) φ := by
    refine IsHomLift.of_fac' p (𝟙 U) φ q.out.2 q'.out.2 ?_
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.eqToHom_left, Category.id_comp]
    change φ.baseMap = _
    rw [hφ]
    simp only [eqToHom_trans]
    rfl
  exact ⟨asIso (⟨φ, hlift⟩ : q.out ⟶ q'.out)⟩

/-- **Axiom [-1] for the stack of polarized proper schemes**, in the form
`AlgebraicGeometry.Stack.IsSizeBounded` consumed by Artin's criterion: the isomorphism classes of
the fibres of `𝒫olarized` over the finite type fields of `Spec(ℤ)` are bounded by the size of an
object of the site — indeed they are countable, and every scheme has size at least `ℵ₀`. -/
theorem isSizeBounded_polarizedStackUnconditional :
    Stack.IsSizeBounded B _ hZ
      (polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)) := by
  refine ⟨Over.mk (𝟙 (B.obj hZ)), fun U k _ hU hft => ?_⟩
  have := countable_isoClasses_polarizedFiber B hZ U k hU hft
  refine le_trans ?_ (Cardinal.aleph0_le_lift.mpr (Scheme.aleph0_le_size _))
  exact Cardinal.lift_le_aleph0.mpr (Cardinal.mk_le_aleph0 (α := Quotient
    (isIsomorphicSetoid ((polarizedSliceProjection B hZ (isTerminal_obj_specULiftZ B hZ)).Fiber
      U))))

end AlgebraicGeometry

end
