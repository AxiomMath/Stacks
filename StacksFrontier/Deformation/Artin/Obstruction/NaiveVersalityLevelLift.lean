module

public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityBaseLift
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectVersal

/-!
# Condition (2) of Stacks 06IU for the formal object of a naive obstruction theory

This file closes the second of the two bridges between the cohomological work on
[Stacks, Tag 07YM] and the versality criterion of [Stacks, Tag 06IU]: the base-lifting
condition, condition (2) of that criterion, for the formal object attached to a family `x` over
`Spec A` whose deformation theory is controlled by a morphism `ξ : E ⟶ NL_{A/Λ}` satisfying
hypothesis (i) of the tag and condition (2) of the tag in degree `-1`.

What is proved here is the *level-wise* form of the condition, from
`Deformation.Artin.exists_algHom_lift_of_surjective_derivedTensorFibre_neg_one` together with
the completion presentation of the base; `Deformation.baseLifts_of_levelLifts` then converts it
into the form [Stacks, Tag 06IU] states.

The presentation of a level is written out as the quotient map followed by the transport rather
than as `Deformation.formalLevelProjection`, which is the same term: that abbreviation lives in
`StacksFrontier.Deformation.Schlessinger.VersalExistence`, and importing Schlessinger's
construction here would add a thousand modules to the closure of a file that needs nothing else
from it.

## Main results

* `Deformation.Artin.levelLifts_of_surjective_derivedTensorFibre_neg_one` — the level-wise form:
  for a small extension `f : C' ⟶ C` which is the image of an arrow of the predeformation
  category and a map `η.base ⟶ C` presented through a level of `η`, the map lifts to
  `η.base ⟶ C'`.

## Implementation notes

The data describing the base `η.base` is the one [Stacks, Tag 0CXK] runs on and the one
`Deformation.Artin.liftsAtResiduePoint_of_isSmooth` takes: a morphism
`gR : Spec η.base ⟶ Spec A`, the compatible family `r` of arrows from the levels of `η` to `x`
over it, and the two clauses `hpoints` and `hinj` saying that `Spec η.base ⟶ Spec A` corepresents
the Artinian points of `Spec A` through the chosen residue point. Those two clauses are what the
passage between `η.base ⟶ C` and `A ⟶ C` consists of, and they are exactly the hypotheses the
engine of [Stacks, Tag 0CXK] takes; nothing here reconstructs the completion.

`Mono iΛ` is used in exactly one place, and for exactly the reason
`StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityDegreeNegOne` uses it: the `Λ`-algebra
map `φ : A → C` is read off a morphism of schemes over `S` by
`Deformation.Artin.algHom_of_schemeMap_over`, which needs "over `S`" to imply "over `Spec Λ`".
In [Stacks, Tag 07YM] the affine open `Spec Λ ⟶ S` is an open immersion, hence a monomorphism.

The site containment of `Spec C` and `Spec C'` is *not* a hypothesis: the two algebras are the
projections of objects of the predeformation category, whose points are objects of the fibred
category and therefore lie over schemes the site contains. Only the containment of
`Spec (A ×_C C')` needs an estimate, and the one used is the cardinality bound on the residue
field `k`, which in the application is `Cardinal.mk_residueField_le_max`.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
* [Stacks Project, Tag 06IU](https://stacks.math.columbia.edu/tag/06IU)
* [Stacks Project, Tag 0CXK](https://stacks.math.columbia.edu/tag/0CXK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

attribute [local instance 10000] HasDerivedCategory.standard

universe u v w

/-! ### Site containment of the base of an object of the fibred category -/

section Contains

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : Type v} [Category.{w} F] (p : F ⥤ BigFppfOver B S hS)

/-- An object of the fibred category lies over a scheme the site contains. -/
public theorem contains_of_post_eq {Z : Over S} {Xf : F}
    (h : (p ⋙ Over.post B.inclusion).obj Xf = Z) : B.Contains Z.left := by
  subst h
  exact (p.obj Xf).left.property

/-- An object of the fibred category lying over `Spec A` has `Spec A` in the site.

The identification of `(Over.mk toS).left` with `Spec A` is made here, as a `Scheme`-level
`rfl`, rather than inside `AlgebraicGeometry.BigFppfSite.Contains`: that predicate unfolds to a
comparison of `AlgebraicGeometry.Scheme.size`, and asking the unifier to see through it with a
composite like `↑(C.projection.obj x)` in place of `A` is expensive. -/
public theorem contains_spec_of_post_eq {A : Type u} [CommRing A]
    (toS : Spec (CommRingCat.of A) ⟶ S) {Xf : F}
    (h : (p ⋙ Over.post B.inclusion).obj Xf = Over.mk toS) :
    B.Contains (Spec (CommRingCat.of A)) := by
  have key : ∀ Z : Over S, (p ⋙ Over.post B.inclusion).obj Xf = Z →
      ∀ W : Scheme.{u}, Z.left = W → B.Contains W := by
    intro Z e W eW
    subst e
    subst eW
    exact (p.obj Xf).left.property
  exact key (Over.mk toS) h (Spec (CommRingCat.of A)) rfl

/-- An object lying over `Spec A` as a scheme over `S` lies over
`Deformation.Artin.algebraOver` in the site. -/
public theorem algebraOver_of_post_eq {A : Type u} [CommRing A]
    (toS : Spec (CommRingCat.of A) ⟶ S) (hA : B.Contains (Spec (CommRingCat.of A)))
    {Xf : F} (h : (p ⋙ Over.post B.inclusion).obj Xf = Over.mk toS) :
    p.obj Xf = algebraOver A B S hS toS hA := by
  have key : ∀ (Z : Over S) (hZ : B.Contains Z.left),
      (p ⋙ Over.post B.inclusion).obj Xf = Z → p.obj Xf = overSiteObj B S hS Z hZ := by
    intro Z hZ e
    subst e
    exact (overSiteObj_post_inverse B S hS (p.obj Xf)).symm
  exact (key (Over.mk toS) hA h).trans (overSiteObj_eq_algebraOver B S hS toS hA)

end Contains

/-! ### The level-wise form of condition (2) -/

section LevelLift

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : Type v} [Category.{w} F] (p : F ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
  {Λ A k : Type u} [CommRing Λ] [CommRing A] [Field k]
  [Algebra Λ A] [Algebra Λ k] [Algebra A k]
  (iΛ : Spec (CommRingCat.of Λ) ⟶ S) [Mono iΛ]
  (hA : B.Contains (Spec (CommRingCat.of A)))

include hp hRS in
/-- **Stacks 07YM, condition (2) of Stacks 06IU in its level-wise form.** Let `x` be a family
over `Spec A` whose deformation theory is controlled by `ξ : E ⟶ NL_{A/Λ}` in the sense of
hypothesis (i) of [Stacks, Tag 07YM], with `H^{-1}(ξ ⊗ᴸ_A k)` surjective, and let `η` be a
formal object of the predeformation category of `x` at the residue point, presented over
`Spec A` by `gR : Spec η.base ⟶ Spec A` through the compatible family `r`. Then for every small
extension `f : C' ⟶ C` which is the image of an arrow `gg` of the predeformation category, every
map `η.base ⟶ C` presented through a level of `η` lifts along `f`.

The map `A ⟶ C` the level presentation determines lifts along `f` by
`Deformation.Artin.exists_algHom_lift_of_surjective_derivedTensorFibre_neg_one`, the lift of the
family being the point of `gg`'s source; `hpoints` turns the lift `A ⟶ C'` into a map
`η.base ⟶ C'`, and `hinj` identifies its composite with `f` with the given map. -/
public theorem levelLifts_of_surjective_derivedTensorFibre_neg_one
    (hmkk : Cardinal.mk k ≤ max Cardinal.aleph0 (Cardinal.mk A))
    (T : DerivedTensorProduct A) (E : DerivedCategory (ModuleCat.{u} A))
    (hE : (DerivedCategory.TStructure.t (C := ModuleCat.{u} A)).minus E)
    (ξ : E ⟶ derivedNaiveCotangentComplex Λ A)
    (hsurj : Function.Surjective
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-1)).map
        ((T.tensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A k))).map ξ)))
    {Xf : F}
    (hXf : p.obj Xf = algebraOver A B S hS
      (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) hA)
    (hKill : ∀ (A' : Type u) [CommRing A'] [Algebra Λ A'] [Algebra A' A]
      [IsScalarTower Λ A' A]
      (D : SquareZeroThickening A B S hS
        (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) hA A'),
      D.q = algebraMap A' A →
      Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ iΛ = B.inclusion.map D.toS' →
      Nonempty ((Under.post p).Fiber (Under.mk (eqToHom hXf ≫ D.arrow))) →
      ξ ≫ naiveCotangentBaseMap Λ A' A = 0)
    {x₀ : F}
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (CC : PredeformationConstruction iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (η : Deformation.FormalObject CC.projection)
    (r : ∀ n, (CC.objects (η.level n)).point ⟶ Xf)
    (gR : Spec (CommRingCat.of η.base) ⟶ Spec (CommRingCat.of A))
    (hbase : ∀ n, schemeMap (p ⋙ Over.post B.inclusion)
        (deformationPointBase CC (η.level n) (Deformation.AdicTruncation.obj η.base n)
          (η.level_eq n))
        (algebraOver_post B S hS p _ hA hXf) (r n) =
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Deformation.AdicTruncation.ideal η.base n))) ≫ gR)
    (r₀ : x₀ ⟶ Xf)
    (hclosed : ∀ n, (CC.objects (η.level n)).arrow ≫ r n = r₀)
    (hr₀ : schemeMap (p ⋙ Over.post B.inclusion) hx₀
        (algebraOver_post B S hS p _ hA hXf) r₀ =
      Spec.map (CommRingCat.ofHom (algebraMap A k)))
    (hpoints : ∀ (A₁ : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
      (f : Spec (CommRingCat.of A₁) ⟶ Spec (CommRingCat.of A)),
      f ≫ (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) =
        Spec.map (CommRingCat.ofHom (algebraMap Λ A₁)) ≫ iΛ →
      Spec.map (CommRingCat.ofHom (residueMap A₁)) ≫ f =
        schemeMap (p ⋙ Over.post B.inclusion) hx₀
          (algebraOver_post B S hS p _ hA hXf) r₀ →
      ∃ a : η.base ⟶ Deformation.artinianToComplete.obj A₁,
        Spec.map (CommRingCat.ofHom a.hom.toRingHom) ≫ gR = f)
    (hinj : ∀ (A₁ : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
      (a b : η.base ⟶ Deformation.artinianToComplete.obj A₁),
      Spec.map (CommRingCat.ofHom a.hom.toRingHom) ≫ gR =
        Spec.map (CommRingCat.ofHom b.hom.toRingHom) ≫ gR → a = b) :
    ∀ ⦃y x : CC.carrier⦄ (gg : y ⟶ x),
      InfinitesimalLifting.IsSmallExtension
        (CommRingCat.ofHom (CC.projection.map gg).hom.toRingHom) →
      ∀ (N : ℕ) (c : η.level N ⟶ x),
        ∃ bb : η.base ⟶ Deformation.artinianToComplete.obj (CC.projection.obj y),
          (CC.projection.map gg).hom.comp bb.hom =
            ((CC.projection.map c).hom.comp
              ((eqToHom (η.level_eq N).symm).hom.comp
                (Ideal.Quotient.mkₐ Λ (Deformation.AdicTruncation.ideal η.base N)))) := by
  intro y x gg hsmall N c
  let q := p ⋙ Over.post B.inclusion
  let toSA : Spec (CommRingCat.of A) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ
  have hXq : q.obj Xf = Over.mk toSA := algebraOver_post B S hS p _ hA hXf
  -- the two Artinian algebras and their points
  have hZq := deformationPointBase CC x (CC.projection.obj x) rfl
  have hYq := deformationPointBase CC y (CC.projection.obj y) rfl
  have hLq := deformationPointBase CC (η.level N)
    (Deformation.AdicTruncation.obj η.base N) (η.level_eq N)
  have hC := contains_spec_of_post_eq B S hS p _ hZq
  have hC' := contains_spec_of_post_eq B S hS p _ hYq
  have hZf : p.obj (CC.objects x).point = algebraOver (CC.projection.obj x) B S hS _ hC :=
    algebraOver_of_post_eq B S hS p _ hC hZq
  have hYf : p.obj (CC.objects y).point = algebraOver (CC.projection.obj y) B S hS _ hC' :=
    algebraOver_of_post_eq B S hS p _ hC' hYq
  -- the arrow of the small extension, read on schemes
  have hβ : schemeMap q hZq hYq ((CC.morphisms y x gg).arrow) =
      Spec.map (CommRingCat.ofHom (CC.projection.map gg).hom.toRingHom) :=
    deformationMorphism_base CC (CC.projection.map gg) gg
      (IsHomLift.map CC.projection gg) hYq hZq
  -- the arrow to the family, and the algebra map it names
  let fL : Deformation.AdicTruncation.obj η.base N ⟶ CC.projection.obj x :=
    eqToHom (η.level_eq N).symm ≫ CC.projection.map c
  have hcL : CC.projection.IsHomLift fL c := by
    refine IsHomLift.of_fac' CC.projection fL c (η.level_eq N) rfl ?_
    simp [fL]
  have hcbase : schemeMap q hZq hLq ((CC.morphisms (η.level N) x c).arrow) =
      Spec.map (CommRingCat.ofHom fL.hom.toRingHom) :=
    deformationMorphism_base CC fL c hcL hLq hZq
  let αarr : (CC.objects x).point ⟶ Xf :=
    (CC.morphisms (η.level N) x c).arrow ≫ r N
  have hαsplit : schemeMap q hZq hXq αarr =
      Spec.map (CommRingCat.ofHom fL.hom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Deformation.AdicTruncation.ideal η.base N))) ≫ gR := by
    rw [show αarr = (CC.morphisms (η.level N) x c).arrow ≫ r N from rfl,
      schemeMap_comp q hZq hLq hXq, hcbase, hbase N]
    rfl
  -- the `Λ`-algebra map `A → C`
  let φ : A →ₐ[Λ] CC.projection.obj x :=
    algHom_of_schemeMap_over iΛ (schemeMap q hZq hXq αarr)
      (schemeMap_over q hZq hXq αarr)
  have hφspec : Spec.map (CommRingCat.ofHom (φ : A →+* CC.projection.obj x)) =
      schemeMap q hZq hXq αarr :=
    specMap_algHom_of_schemeMap_over iΛ (schemeMap q hZq hXq αarr)
      (schemeMap_over q hZq hXq αarr)
  -- the residue data of the small extension
  have hsurjf : Function.Surjective (CC.projection.map gg).hom := hsmall.2.2.2.2.1
  have hsqf : RingHom.ker (CC.projection.map gg).hom.toRingHom ^ 2 = ⊥ :=
    smallExtension_kernel_sq_zero (CC.projection.map gg) hsmall
  have hrC' : ∀ z : CC.projection.obj y,
      residueMap (CC.projection.obj x) ((CC.projection.map gg).hom z) =
        residueMap (CC.projection.obj y) z :=
    fun z => (CC.projection.map gg).residue_comm z
  have harr : (CC.objects x).arrow ≫ αarr = r₀ := by
    show (CC.objects x).arrow ≫ (CC.morphisms (η.level N) x c).arrow ≫ r N = r₀
    rw [← Category.assoc, (CC.morphisms (η.level N) x c).triangle, hclosed N]
  have hcomp : Spec.map (CommRingCat.ofHom (residueMap (CC.projection.obj x))) ≫
      Spec.map (CommRingCat.ofHom (φ : A →+* CC.projection.obj x)) =
      Spec.map (CommRingCat.ofHom (algebraMap A k)) := by
    rw [hφspec, ← deformationObject_residueMap CC x _ rfl,
      ← schemeMap_comp q hx₀ hZq hXq, harr, hr₀]
  have hrφ : ∀ a : A, residueMap (CC.projection.obj x) (φ a) = algebraMap A k a := by
    have h2 : CommRingCat.ofHom ((residueMap (CC.projection.obj x)).comp
        (φ : A →+* CC.projection.obj x)) = CommRingCat.ofHom (algebraMap A k) :=
      Spec.map_injective (by rwa [CommRingCat.ofHom_comp, Spec.map_comp])
    exact fun a => RingHom.congr_fun (congrArg CommRingCat.Hom.hom h2) a
  -- the kernel of the small extension, identified with the residue field
  let : Module (CC.projection.obj y) k :=
    Module.compHom k (residueMap (CC.projection.obj y))
  let eker := smallExtension_kernel_linearEquiv_residueField (CC.projection.map gg) hsmall
  have heker : ∀ (z : CC.projection.obj y)
      (i : RingHom.ker (CC.projection.map gg).hom.toRingHom),
      eker.toAddEquiv (z • i) = residueMap (CC.projection.obj y) z * eker.toAddEquiv i :=
    fun z i => eker.map_smul z i
  -- the fibre product lies in the site
  have hsurjA' : Function.Surjective
      (algebraMap (AlgHom.pullback φ (CC.projection.map gg).hom) A) :=
    surjective_fibreProduct_algebraMap φ (CC.projection.map gg).hom hsurjf
  have hmkker : Cardinal.mk
      (RingHom.ker (algebraMap (AlgHom.pullback φ (CC.projection.map gg).hom) A)) ≤
        max Cardinal.aleph0 (Cardinal.mk A) := by
    rw [Cardinal.mk_congr (fibreProductKerEquiv hsurjf hsqf
      (residueMap (CC.projection.obj x)) (residueMap (CC.projection.obj y))
      hrC' hrφ eker.toAddEquiv heker).toEquiv]
    exact hmkk
  have hA' : B.Contains (Spec (CommRingCat.of
      (AlgHom.pullback φ (CC.projection.map gg).hom))) :=
    contains_spec_of_surjective_of_mk_ker_le B hA _ _ hsurjA' hmkker
  -- the lift of the base along the small extension
  obtain ⟨ψ, hψ⟩ := exists_algHom_lift_of_surjective_derivedTensorFibre_neg_one
    B S hS p hp hRS iΛ hA φ (CC.projection.map gg).hom hC hC' hA' hsurjf hsqf
    (residueMap (CC.projection.obj x)) (residueMap (CC.projection.obj y)) hrC' hrφ
    eker.toAddEquiv heker T E hE ξ hsurj hXf hKill hZf hYf
    αarr ((CC.morphisms y x gg).arrow) hφspec.symm hβ
  -- the lift, read as a point of the base
  have hψ1 : Spec.map (CommRingCat.ofHom (ψ : A →+* CC.projection.obj y)) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) =
      Spec.map (CommRingCat.ofHom (algebraMap Λ (CC.projection.obj y))) ≫ iΛ := by
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    exact CommRingCat.hom_ext (RingHom.ext fun l => ψ.commutes l)
  have hresψ : ∀ a : A, residueMap (CC.projection.obj y) (ψ a) =
      residueMap (CC.projection.obj x) (φ a) := by
    intro a
    rw [← hψ]
    exact (hrC' (ψ a)).symm
  have hψ2 : Spec.map (CommRingCat.ofHom (residueMap (CC.projection.obj y))) ≫
      Spec.map (CommRingCat.ofHom (ψ : A →+* CC.projection.obj y)) =
      schemeMap q hx₀ hXq r₀ := by
    rw [hr₀, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun a => (hresψ a).trans (hrφ a))
  obtain ⟨bb, hbb⟩ := hpoints (CC.projection.obj y)
    (Spec.map (CommRingCat.ofHom (ψ : A →+* CC.projection.obj y))) hψ1 hψ2
  -- the given map out of the base, as a morphism of complete local algebras
  let γ : η.base ⟶ Deformation.artinianToComplete.obj (CC.projection.obj x) :=
    Deformation.quotientProjection η.base N ≫ Deformation.artinianToComplete.map fL
  have hγhom : γ.hom = (CC.projection.map c).hom.comp
      ((eqToHom (η.level_eq N).symm).hom.comp
        (Ideal.Quotient.mkₐ Λ (Deformation.AdicTruncation.ideal η.base N))) := by
    show (Deformation.artinianToComplete.map fL).hom.comp
      (Deformation.quotientProjection η.base N).hom = _
    show fL.hom.comp (Ideal.Quotient.mkₐ Λ (Deformation.AdicTruncation.ideal η.base N)) = _
    rw [show fL.hom = (CC.projection.map c).hom.comp (eqToHom (η.level_eq N).symm).hom from
      Deformation.ArtinianLocalAlgCat.comp_hom _ _]
    exact AlgHom.comp_assoc _ _ _
  have hγspec : Spec.map (CommRingCat.ofHom (γ.hom.toRingHom)) ≫ gR =
      Spec.map (CommRingCat.ofHom (φ : A →+* CC.projection.obj x)) := by
    have h1 : CommRingCat.ofHom (γ.hom.toRingHom) =
        CommRingCat.ofHom
            (Ideal.Quotient.mk (Deformation.AdicTruncation.ideal η.base N)) ≫
          CommRingCat.ofHom fL.hom.toRingHom := rfl
    rw [h1, Spec.map_comp, Category.assoc]
    exact hαsplit.symm.trans hφspec.symm
  have hcomp_hom : (bb ≫ Deformation.artinianToComplete.map (CC.projection.map gg)).hom =
      (CC.projection.map gg).hom.comp bb.hom :=
    Deformation.CompleteLocalAlgCat.comp_hom _ _
  have hfinal : bb ≫ Deformation.artinianToComplete.map (CC.projection.map gg) = γ := by
    refine hinj (CC.projection.obj x) _ _ ?_
    rw [hγspec, hcomp_hom,
      show CommRingCat.ofHom ((CC.projection.map gg).hom.comp bb.hom).toRingHom =
        CommRingCat.ofHom bb.hom.toRingHom ≫
          CommRingCat.ofHom (CC.projection.map gg).hom.toRingHom from
        (CommRingCat.ofHom_comp _ _), Spec.map_comp, Category.assoc, hbb,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom hψ)
  refine ⟨bb, ?_⟩
  rw [← hγhom, ← hcomp_hom]
  exact congrArg (·.hom) hfinal

end LevelLift

end Deformation.Artin

end
