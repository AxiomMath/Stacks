module

public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityFieldTangentImage
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectVersal
public import StacksFrontier.Deformation.TangentSpace.Functor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Versality at a point, tested at the dual numbers of a residue field

`Deformation.Artin.IsVersalAt` is a lifting property quantified over the surjections of
`Deformation.ArtinianLocalAlgCat (𝒪_{S,s}) κ`, where `κ` is the residue field of the chosen
point. The direction `(1) ⇒ (2)` of Stacks 07YM uses it at one surjection only: the
augmentation `κ[κ] ⟶ κ` of the dual numbers. This file instantiates it there.

The two sides describe the same test in different vocabularies. Versality presents the base of
a lifting problem as `Spec` of an object of `𝒞_R` over `Spec R`; the lift chain of 07YM
presents it as the site's square-zero object `Spec κ[κ]` over `Spec A`. So the dual numbers
have to be produced *as the site forms them* — `Deformation.Artin.squareZeroRing κ` applied to
`κ` as a module over itself — and then exhibited as an object of `𝒞_R`, which is
`Deformation.Artin.squareZeroArtinianObj`; the field itself is
`Deformation.Artin.fieldArtinianObj`. With those, the two presentations of the base agree.

## Main definitions

* `Deformation.Artin.fieldArtinianObj` — the field `κ` as an object of `𝒞_R`.
* `Deformation.Artin.squareZeroArtinianObj` — the site's trivial square-zero extension
  `κ[M]`, for a finite-dimensional `M`, as an object of `𝒞_R`.
* `Deformation.Artin.squareZeroArtinianProjection` — the augmentation `κ[M] ⟶ κ` of `𝒞_R`,
  which is the surjection the dual-numbers test is taken along.

## Main results

* `Deformation.Artin.schemeMap_eq_of_isHomLift` — the morphism of schemes that
  `Deformation.Artin.schemeMap` extracts from an arrow of the total category is the one
  underlying any arrow of the site that the arrow lies over.
* `Deformation.Artin.algebraOver_post_eq` and `Deformation.Artin.squareZeroOver_post_eq` — the
  two presentations of the base agree.
* `Deformation.Artin.exists_extends_of_liftsAtResiduePoint` — a lift of `x₀` over the dual
  numbers of `κ` extends to `x`.
* `Deformation.Artin.surjective_canonicalTangentMap_of_liftsAtResiduePoint` — the map
  `Der_Λ(A, κ) ⟶ T_x(κ)` on tangent spaces is surjective. This is the previous result composed
  with `Deformation.Artin.exists_canonicalTangentMap_eq_of_extends`, and by the duality of
  Stacks 07YK it is condition (2) of the tag in degree `0`.
* `Deformation.Artin.liftsAtResiduePoint_of_isVersalAt` — the hypothesis the two consume is
  `Deformation.Artin.IsVersalAt` itself, read in the residue field
  `Ideal.ResidueField u₀.asIdeal` of the prime, and
  `Deformation.Artin.specMap_primeResidueFieldAlgebra_comp_fromSpecStalk` is the one
  compatibility they ask of the deformation base.

## Implementation notes

The square-zero objects are built for an **abstract** module `M`, never for `ModuleCat.of κ κ`
written out: the ring structure of `TrivSqZeroExt κ M` depends on the right action of `κ` on
`M`, and at the concrete module instance synthesis finds `Semiring.toOppositeModule` rather
than the site's `Deformation.Artin.oppositeModule`, which is a different ring on the same
carrier (one multiplies on the right, the other on the left; they agree by `mul_comm`, not
definitionally). With `M` abstract there is only one candidate, so instantiating the finished
statement at the site module substitutes the site's instance into it.

The lifting property is consumed in the residue-point form
`Deformation.Artin.LiftsAtResiduePoint`, which is what `Deformation.Artin.IsVersalAt` unfolds
to and which transports along an isomorphism of residue fields over the base; the statement
here takes the deformation base `R` and its map to `S` as data, with the single compatibility
that the residue-field point of `Spec A` factors through it. Nothing else about `R` is used.

The two conditions that `Deformation.Artin.LiftsAtResiduePoint` imposes on the arrows are
equalities of morphisms of schemes, read off the `CategoryTheory.Functor.IsHomLift` facts
rather than computed: the identifications of the two bases are definitional, so the
`eqToHom`s they contribute are identities, but not ones `simp` can recognize — their endpoints
agree only after `Deformation.Artin.fieldArtinianObj` and
`Deformation.Artin.squareZeroArtinianObj` unfold, which is past `reducible` transparency. They
are discharged by `show`, which runs at default transparency, and by `congrArg` where a
rewrite under a composite would have needed a motive that is not type-correct.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
* [Stacks Project, Tag 07XF](https://stacks.math.columbia.edu/tag/07XF)
* [Stacks Project, Tag 07YK](https://stacks.math.columbia.edu/tag/07YK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

universe u v

/-! ### The field and its dual numbers as objects of `𝒞_R` -/

section DualNumbersObjects

variable (R k : Type u) [CommRing R] [Field k] [Algebra R k]

/-- The field `k` itself, as an object of `𝒞_R`: it is Artinian and local, and its residue
field is `k`. -/
public def fieldArtinianObj : ArtinianLocalAlgCat.{u, u, u} R k where
  carrier := k
  residueEquiv := Deformation.residueEquivOfAugmentation (AlgHom.id R k) Function.surjective_id

/-- The algebra map of `Deformation.Artin.fieldArtinianObj` is the structure map of `k`. -/
public theorem algebraMap_fieldArtinianObj :
    algebraMap R (fieldArtinianObj R k) = algebraMap R k := rfl

/-- The residue map of `Deformation.Artin.fieldArtinianObj` is the identity. -/
public theorem residueMap_fieldArtinianObj :
    residueMap (fieldArtinianObj R k) = RingHom.id k :=
  RingHom.ext fun _ => rfl

variable (M : ModuleCat.{u} k) [Module.Finite k M]

omit [Module.Finite k M] in
/-- The trivial square-zero extension `k[M]`, formed with the site's right action of `k` on
`M`, is a local ring. -/
@[ega "IV 11.7.1" "more general"]
public theorem isLocalRing_trivSqZeroExt : IsLocalRing (TrivSqZeroExt k M) where
  exists_pair_ne := ⟨0, 1, fun h => zero_ne_one (congrArg TrivSqZeroExt.fst h)⟩
  isUnit_or_isUnit_of_add_one {a b} h := by
    have hab : a.fst + b.fst = 1 := congrArg TrivSqZeroExt.fst h
    exact (IsLocalRing.isUnit_or_isUnit_of_add_one hab).imp
      TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr

/-- The trivial square-zero extension `k[M]` by a finite-dimensional `M` is Artinian. -/
@[ega "IV 11.7.1" "more general"]
public theorem isArtinianRing_trivSqZeroExt : IsArtinianRing (TrivSqZeroExt k M) := by
  let : Module.Finite k (TrivSqZeroExt k M) :=
    inferInstanceAs (Module.Finite k (k × (M : Type u)))
  exact IsArtinianRing.of_finite k _

/-- The trivial square-zero extension `k[M]`, formed as the site forms it, as an object of
`𝒞_R`. The `R`-algebra structure is the one through `k`, so that the algebra map is the
inclusion of the first component of the structure map of `k`. -/
public def squareZeroArtinianObj : ArtinianLocalAlgCat.{u, u, u} R k where
  carrier := TrivSqZeroExt k M
  algebra := ((TrivSqZeroExt.inlHom k M).comp (algebraMap R k)).toAlgebra
  isArtinianRing := isArtinianRing_trivSqZeroExt k M
  isLocalRing := isLocalRing_trivSqZeroExt k M
  residueEquiv :=
    letI : IsLocalRing (TrivSqZeroExt k M) := isLocalRing_trivSqZeroExt k M
    letI : Algebra R (TrivSqZeroExt k M) :=
      ((TrivSqZeroExt.inlHom k M).comp (algebraMap R k)).toAlgebra
    Deformation.residueEquivOfAugmentation
      ({ toRingHom := (TrivSqZeroExt.fstHom k k M).toRingHom,
          commutes' := fun _ => rfl } : TrivSqZeroExt k M →ₐ[R] k)
      TrivSqZeroExt.fst_surjective

/-- The algebra map of `Deformation.Artin.squareZeroArtinianObj` is the structure map of `k`
followed by the inclusion of the first component. -/
public theorem algebraMap_squareZeroArtinianObj (r : R) :
    algebraMap R (squareZeroArtinianObj R k M) r =
      TrivSqZeroExt.inl (algebraMap R k r) := rfl

/-- The augmentation of `Deformation.Artin.squareZeroArtinianObj` onto
`Deformation.Artin.fieldArtinianObj`, which is the surjection the dual-numbers test of
versality is taken along. -/
public def squareZeroArtinianProjection :
    squareZeroArtinianObj R k M ⟶ fieldArtinianObj R k where
  hom :=
    { toRingHom := (TrivSqZeroExt.fstHom k k M).toRingHom
      commutes' := fun _ => rfl }
  isLocal := ⟨fun _ ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha⟩
  residue_comm _ := rfl

/-- The ring map underlying the augmentation is the one reading off the first component. -/
public theorem squareZeroArtinianProjection_hom_toRingHom :
    (squareZeroArtinianProjection R k M).hom.toRingHom =
      (TrivSqZeroExt.fstHom k k M).toRingHom := rfl

/-- The augmentation is surjective, being the first projection. -/
public theorem surjective_squareZeroArtinianProjection :
    Function.Surjective (squareZeroArtinianProjection R k M).hom :=
  TrivSqZeroExt.fst_surjective

end DualNumbersObjects

/-! ### Reading the underlying morphism of schemes off an `IsHomLift` -/

section SchemeMapOfSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : Type v} [Category X] (p : X ⥤ BigFppfOver B S hS)

/-- The morphism of schemes that `Deformation.Artin.schemeMap` extracts from an arrow of the
total category is the one underlying any arrow of the site that the arrow lies over. -/
public theorem schemeMap_eq_of_isHomLift
    {y z : X} {Y₀ Z₀ : BigFppfOver B S hS} (ν : Y₀ ⟶ Z₀) (φ : y ⟶ z) [p.IsHomLift ν φ]
    {Y Z : Over S} (hy : (p ⋙ Over.post B.inclusion).obj y = Y)
    (hz : (p ⋙ Over.post B.inclusion).obj z = Z)
    (eY : Y.left = (BigFppfOver.toScheme B S hS).obj Y₀)
    (eZ : (BigFppfOver.toScheme B S hS).obj Z₀ = Z.left) :
    schemeMap (p ⋙ Over.post B.inclusion) hy hz φ =
      eqToHom eY ≫ (BigFppfOver.toScheme B S hS).map ν ≫ eqToHom eZ := by
  subst hy hz
  change ((Over.post B.inclusion).map (p.map φ)).left = _
  rw [IsHomLift.fac' p ν φ]
  simp only [Functor.map_comp, eqToHom_map, Over.comp_left, Over.eqToHom_left]
  rfl

end SchemeMapOfSite

/-! ### Versality tested at the dual numbers of a residue field -/

section VersalLift

variable (A k : Type u) [CommRing A] [Field k] [Algebra A k]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A))) (hAk : B.Contains (Spec (.of k)))
variable {X : Type v} [Category X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)
  (hxS : (p ⋙ Over.post B.inclusion).obj x = Over.mk toS)
  (hp : p.IsFiberedInGroupoids)
variable (R : Type u) [CommRing R] [Algebra R k] (iR : Spec (.of R) ⟶ S)
  (hiR : Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR =
    Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS)

include hiR in
/-- `Spec k`, as an object of the site over `S`, is the spectrum of the object `k` of `𝒞_R`. -/
public theorem algebraOver_post_eq :
    (Over.post B.inclusion).obj
        (algebraOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (fieldArtinianObj R k))) ≫ iR) := by
  change Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) = _
  rw [← hiR]
  rfl

include hiR in
/-- `Spec k[M]`, as an object of the site over `S`, is the spectrum of the object `k[M]` of
`𝒞_R`: the structure morphism of the site's square-zero object is the inclusion of the first
component followed by the point, and the algebra map of
`Deformation.Artin.squareZeroArtinianObj` is that same composite. -/
public theorem squareZeroOver_post_eq (M : SiteModule k B) [Module.Finite k M.obj] :
    (Over.post B.inclusion).obj
        (squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) M) =
      Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap R (squareZeroArtinianObj R k M.obj))) ≫ iR) := by
  change Over.mk (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom k M.obj)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) = _
  rw [← hiR]
  show Over.mk (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom k M.obj)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR) = _
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

include hA hxS hp hiR in
/-- **Stacks 07YM, the dual-numbers instance of versality.** Let `x₀` be the chosen pullback of
`x` to `Spec k` and let `w` be a lift of `x₀` along the square-zero immersion
`Spec k ⟶ Spec k[k]`. If the lifting property defining versality holds at the point of
`Spec A` determined by the `A`-algebra structure of `k`, then `w`'s structure arrow extends to
`x`: there is an arrow `b` from its target to `x` composing with it to the chosen restriction
arrow.

This is the instantiation of `Deformation.Artin.IsVersalAt` at the surjection
`k[k] ⟶ k` of `𝒞_R`, which is `Deformation.Artin.squareZeroArtinianProjection`; the objects
`Deformation.Artin.squareZeroArtinianObj` and `Deformation.Artin.fieldArtinianObj` are the
site's own square-zero ring and the field, so the two descriptions of the base — the spectrum
of an object of `𝒞_R` over `Spec R`, and the site's square-zero object over `Spec A` — agree
by `Deformation.Artin.squareZeroOver_post_eq` and
`Deformation.Artin.algebraOver_post_eq`. -/
@[stacks 07YM "versality tested at the dual numbers of a residue field"]
public theorem exists_extends_of_liftsAtResiduePoint
    (hkk : B.Contains (Spec (squareZeroRing k (ModuleCat.of k k))))
    (hlifts : LiftsAtResiduePoint (Λ := R) (k := k) iR (p ⋙ Over.post B.inclusion)
      (Over.mk toS) x hxS (Spec.map (CommRingCat.ofHom (algebraMap A k)))) :
    letI : p.IsFibered := hp.isFibered
    ∀ (w : (Under.post p).Fiber (Under.mk (eqToHom
          (((Functor.chosenPullbacks p).pullbackFunctor
            (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
              (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)).obj ⟨x, hx⟩).2 ≫
        squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
          (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)))),
      ∃ b : w.1.right ⟶ x,
        w.1.hom ≫ b = (Functor.chosenPullbacks p).map
          (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
            (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl) ⟨x, hx⟩ := by
  let : p.IsFibered := hp.isFibered
  intro w
  have hx₀ := (((Functor.chosenPullbacks p).pullbackFunctor
    (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
      (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)).obj ⟨x, hx⟩).2
  have hright : p.obj w.1.right =
      squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS)
        (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B) :=
    congrArg Comma.right w.2
  have hhom : p.map w.1.hom ≫ eqToHom hright =
      eqToHom hx₀ ≫ squareZeroArrow k B S hS
        (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
        (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B) :=
    under_hom_comp_eqToHom w.2
  -- The lift lies over the square-zero immersion.
  have hwlift : p.IsHomLift
      (squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
        (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)) w.1.hom := by
    refine IsHomLift.of_fac' p _ w.1.hom hx₀ hright ?_
    calc p.map w.1.hom = (p.map w.1.hom ≫ eqToHom hright) ≫ eqToHom hright.symm := by simp
      _ = (eqToHom hx₀ ≫ squareZeroArrow k B S hS
            (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
            (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)) ≫ eqToHom hright.symm :=
          congrArg (fun t => t ≫ eqToHom hright.symm) hhom
      _ = eqToHom hx₀ ≫ squareZeroArrow k B S hS
            (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
            (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B) ≫ eqToHom hright.symm :=
          Category.assoc _ _ _
  -- The chosen restriction arrow lies over the point of `Spec A`.
  have hηlift : p.IsHomLift
      (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
        (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)
      ((Functor.chosenPullbacks p).map
        (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
          (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl) ⟨x, hx⟩) :=
    ((Functor.chosenPullbacks p).isStronglyCartesian
      (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
        (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)
      ⟨x, hx⟩).toIsHomLift
  -- The two bases, read as spectra of objects of `𝒞_R`.
  have hy : (p ⋙ Over.post B.inclusion).obj
        (((Functor.chosenPullbacks p).pullbackFunctor
          (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
            (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)).obj ⟨x, hx⟩).1 =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (fieldArtinianObj R k))) ≫ iR) :=
    (congrArg (Over.post B.inclusion).obj hx₀).trans
      (algebraOver_post_eq A k B S hS toS hAk R iR hiR)
  have hz : (p ⋙ Over.post B.inclusion).obj w.1.right =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R
        (squareZeroArtinianObj R k (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B).obj))) ≫ iR) :=
    (congrArg (Over.post B.inclusion).obj hright).trans
      (squareZeroOver_post_eq A k B S hS toS R iR hiR (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B))
  refine hlifts (fieldArtinianObj R k)
    (squareZeroArtinianObj R k (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B).obj)
    (squareZeroArtinianProjection R k (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B).obj)
    (surjective_squareZeroArtinianProjection R k
      (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B).obj) _ _ hy hz w.1.hom ?_ _ ?_
  · rw [schemeMap_eq_of_isHomLift B S hS p
      (squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
        (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)) w.1.hom hy hz rfl rfl]
    exact (Category.id_comp _).trans (Category.comp_id _)
  · refine (congrArg (fun t => Spec.map (CommRingCat.ofHom
        (residueMap (fieldArtinianObj R k))) ≫ t)
      (schemeMap_eq_of_isHomLift B S hS p
        (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
          (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)
        ((Functor.chosenPullbacks p).map
          (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
            (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl) ⟨x, hx⟩)
        hy hxS rfl rfl)).trans ?_
    change Spec.map (𝟙 (CommRingCat.of k)) ≫ 𝟙 _ ≫
        Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ 𝟙 _ =
      Spec.map (CommRingCat.ofHom (algebraMap A k))
    simp

end VersalLift

/-! ### Surjectivity of the map on tangent spaces -/

section TangentSurjective

variable (Λ A k : Type u) [CommRing Λ] [CommRing A] [Field k] [Algebra Λ A] [Algebra A k]
  [Algebra Λ k] [IsScalarTower Λ A k]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A))) (hAk : B.Contains (Spec (.of k)))
variable {X : Type v} [Category X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)
  (hxS : (p ⋙ Over.post B.inclusion).obj x = Over.mk toS)
  (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
  (hΩ : B.Contains (Spec (squareZeroRing A (differentialsModule Λ A))))
  (hk : B.Contains (Spec (squareZeroRing A (ModuleCat.of A k))))
  (hkk : B.Contains (Spec (squareZeroRing k (ModuleCat.of k k))))
  (baseMap : Spec (.of Λ) ⟶ S)
  (baseFactorization : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)
variable (R : Type u) [CommRing R] [Algebra R k] (iR : Spec (.of R) ⟶ S)
  (hiR : Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR =
    Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS)

include hxS hRS hΩ baseFactorization hiR in
/-- **Stacks 07YM, the surjectivity of the map on tangent spaces.** If the lifting property
defining versality holds at the point of `Spec A` determined by the `A`-algebra structure of
`k`, then every infinitesimal deformation of `x₀` over the dual numbers of `k` is the image of
a tangent vector `θ : Ω[A⁄Λ] →ₗ[A] k` under the map on tangent spaces, moved across
`Deformation.Artin.canonicalFieldBaseChangeEquiv`.

This is `Deformation.Artin.exists_extends_of_liftsAtResiduePoint`, which produces from
versality the extension of a lift's structure arrow to `x`, composed with
`Deformation.Artin.exists_canonicalTangentMap_eq_of_extends`, which computes the class of an
extendable lift as the image of a tangent vector. Dually — Stacks 07YK — this surjectivity is
the injectivity of `H^0(ξ ⊗ᴸ_A k)`, which is condition (2) of the tag in degree `0`. -/
@[stacks 07YM "(1) implies (2), degree 0: the map on tangent spaces is surjective"]
public theorem surjective_canonicalTangentMap_of_liftsAtResiduePoint [Mono baseMap]
    (hlifts : LiftsAtResiduePoint (Λ := R) (k := k) iR (p ⋙ Over.post B.inclusion)
      (Over.mk toS) x hxS (Spec.map (CommRingCat.ofHom (algebraMap A k)))) :
    letI : p.IsFibered := hp.isFibered
    Function.Surjective (fun θ : Ω[A⁄Λ] →ₗ[A] k =>
      canonicalFieldBaseChangeEquiv A k B S hS toS hA p x hx hp hRS hk hAk hkk
        ((tangentFunctor A B S hS toS hA p x hx hp hRS).liftEquiv
          (⟨ModuleCat.of A k, hk⟩ : SiteModule A B)
          (canonicalTangentMap Λ A k B S hS toS hA p x hx hp hRS hΩ hk baseMap
            baseFactorization θ))) := by
  let : p.IsFibered := hp.isFibered
  intro c
  induction c using Quotient.ind with
  | _ w =>
    obtain ⟨b, hb⟩ := exists_extends_of_liftsAtResiduePoint A k B S hS toS hA hAk p x hx hxS hp
      R iR hiR hkk hlifts w
    exact exists_canonicalTangentMap_eq_of_extends Λ A k B S hS toS hA hAk p x hx hp hRS hΩ hk
      hkk baseMap baseFactorization w b hb

end TangentSurjective

/-! ### Versality at a point, in the residue field of the prime -/

section VersalAtBridge

/-- The ideal at a point of `Spec A` is prime. The carrier of the scheme `Spec A` *is* the
prime spectrum of `A`, so this is `AlgebraicGeometry.PrimeSpectrum.isPrime`; it is recorded
again because instance synthesis does not reach the prime spectrum through the scheme's
coercion to a type, and every statement about `Ideal.ResidueField u.asIdeal` needs it.

Stated for `Spec (CommRingCat.of A)` rather than for a general `R : CommRingCat`: the latter
form does not fire here, the goal's carrier being the plain type `A` while that instance's is
the projection of a metavariable. -/
public instance isPrime_asIdeal {A : Type u} [CommRing A] (u : Spec (CommRingCat.of A)) :
    u.asIdeal.IsPrime :=
  u.isPrime

variable {A : Type u} [CommRing A] {S : Scheme.{u}} (toS : Spec (CommRingCat.of A) ⟶ S)
  (u₀ : Spec (CommRingCat.of A))

/-- The residue field `Ideal.ResidueField u₀.asIdeal` of the prime at a point of `Spec A`, as
an algebra over the local ring of `S` at the image of that point: the scheme's own residue
field is such an algebra, and `AlgebraicGeometry.Scheme.Spec.residueFieldIso` identifies the
two. -/
@[instance_reducible]
public noncomputable def primeResidueFieldAlgebra :
    Algebra (S.presheaf.stalk (basePoint (Over.mk toS) u₀)) u₀.asIdeal.ResidueField :=
  letI := residueFieldAlgebra (Over.mk toS) u₀
  ((Scheme.Spec.residueFieldIso (CommRingCat.of A) u₀).hom.hom.comp
    (algebraMap (S.presheaf.stalk (basePoint (Over.mk toS) u₀))
      ((Over.mk toS).left.residueField u₀))).toAlgebra

/-- The canonical residue-field point of `Spec A` at `u₀`, read through
`AlgebraicGeometry.Scheme.Spec.residueFieldIso`, is the point determined by the `A`-algebra
structure of `Ideal.ResidueField u₀.asIdeal`. Stated without any algebra structure over the
local ring, so that it can be used before one is chosen. -/
public theorem specMap_residueFieldIso_hom_comp_fromSpecResidueField :
    Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of A) u₀).hom ≫
        (Spec (CommRingCat.of A)).fromSpecResidueField u₀ =
      Spec.map (CommRingCat.ofHom (algebraMap A u₀.asIdeal.ResidueField)) := by
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (CommRingCat.of A) u₀,
    ← Category.assoc, ← Spec.map_comp,
    (Scheme.Spec.residueFieldIso (CommRingCat.of A) u₀).inv_hom_id, Spec.map_id,
    Category.id_comp]

/-- The residue-field point of `Spec A` at `u₀` factors through the local ring of `S` at the
image of the point: the compatibility that
`Deformation.Artin.exists_extends_of_liftsAtResiduePoint` asks of the deformation base. -/
public theorem specMap_primeResidueFieldAlgebra_comp_fromSpecStalk :
    letI := primeResidueFieldAlgebra toS u₀
    Spec.map (CommRingCat.ofHom (algebraMap
          (S.presheaf.stalk (basePoint (Over.mk toS) u₀)) u₀.asIdeal.ResidueField)) ≫
        S.fromSpecStalk (basePoint (Over.mk toS) u₀) =
      Spec.map (CommRingCat.ofHom (algebraMap A u₀.asIdeal.ResidueField)) ≫ toS := by
  let := residueFieldAlgebra (Over.mk toS) u₀
  let := primeResidueFieldAlgebra toS u₀
  have hstalk : Spec.map (CommRingCat.ofHom (algebraMap
        (S.presheaf.stalk (basePoint (Over.mk toS) u₀))
        ((Over.mk toS).left.residueField u₀))) ≫
      S.fromSpecStalk (basePoint (Over.mk toS) u₀) =
      (Spec (CommRingCat.of A)).fromSpecResidueField u₀ ≫ toS :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk (residueFieldBasePoint (Over.mk toS) u₀)
  have halg : CommRingCat.ofHom (algebraMap
        (S.presheaf.stalk (basePoint (Over.mk toS) u₀)) u₀.asIdeal.ResidueField) =
      CommRingCat.ofHom (algebraMap (S.presheaf.stalk (basePoint (Over.mk toS) u₀))
        ((Over.mk toS).left.residueField u₀)) ≫
        (Scheme.Spec.residueFieldIso (CommRingCat.of A) u₀).hom := rfl
  rw [halg, Spec.map_comp, Category.assoc, hstalk, ← Category.assoc,
    specMap_residueFieldIso_hom_comp_fromSpecResidueField]

variable {X : Type v} [Category X] (q : X ⥤ Over S) (x : X) (hx : q.obj x = Over.mk toS)

include hx in
/-- **Stacks 07YM.** Versality of `x` at `u₀` is the lifting property at the point of `Spec A`
determined by the algebra structure of the residue field `Ideal.ResidueField u₀.asIdeal` of the
prime -- the field in which the whole 07YM lift chain is written.

`Deformation.Artin.IsVersalAt` is literally the lifting property at the canonical
residue-field point `Spec (U.left.residueField u₀) ⟶ U.left`
(`Deformation.Artin.isVersalAt_iff_liftsAtResiduePoint`), and the property transports along an
isomorphism of residue fields over the local ring
(`Deformation.Artin.liftsAtResiduePoint_changeResidueField`); the isomorphism is the one
induced by `AlgebraicGeometry.Scheme.Spec.residueFieldIso`, and it carries the canonical point
to the one written here. -/
@[stacks 07YM "versality as the lifting property at the residue field of the prime"]
public theorem liftsAtResiduePoint_of_isVersalAt
    (hversal : IsVersalAt (Over.mk toS) q u₀ x hx) :
    LiftsAtResiduePoint (Λ := S.presheaf.stalk (basePoint (Over.mk toS) u₀))
      (k := u₀.asIdeal.ResidueField) (alg := primeResidueFieldAlgebra toS u₀)
      (S.fromSpecStalk (basePoint (Over.mk toS) u₀)) q (Over.mk toS) x hx
      (Spec.map (CommRingCat.ofHom (algebraMap A u₀.asIdeal.ResidueField))) := by
  let := residueFieldAlgebra (Over.mk toS) u₀
  let := primeResidueFieldAlgebra toS u₀
  let e : (Over.mk toS).left.residueField u₀ ≃ₐ[S.presheaf.stalk
      (basePoint (Over.mk toS) u₀)] u₀.asIdeal.ResidueField :=
    { __ := (Scheme.Spec.residueFieldIso (CommRingCat.of A) u₀).commRingCatIsoToRingEquiv
      commutes' := fun _ => rfl }
  have hpt : Spec.map (CommRingCat.ofHom e.toAlgHom.toRingHom) ≫
      (Over.mk toS).left.fromSpecResidueField u₀ =
      Spec.map (CommRingCat.ofHom (algebraMap A u₀.asIdeal.ResidueField)) :=
    specMap_residueFieldIso_hom_comp_fromSpecResidueField u₀
  have h := liftsAtResiduePoint_changeResidueField e
    (S.fromSpecStalk (basePoint (Over.mk toS) u₀)) q (Over.mk toS) x hx
    ((Over.mk toS).left.fromSpecResidueField u₀)
    ((isVersalAt_iff_liftsAtResiduePoint (Over.mk toS) q u₀ x hx).mp hversal)
  rwa [hpt] at h

end VersalAtBridge

end Deformation.Artin
