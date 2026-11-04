module

public import StacksFrontier.Deformation.Artin.Infinitesimal.ActionOnLifts
public import StacksFrontier.Deformation.Artin.RimSchlessinger.Strong

/-!
# Lift classes over augmented rings

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S`, and let `x` be
an object of `𝒳` over `Spec A`. For an `S`-algebra `C` in the site together with an augmentation
`C → A` over `S`, the set `Lift(x, C)` of isomorphism classes of lifts of `x` along
`Spec A ⟶ Spec C` is contravariantly functorial in `Spec C`, that is covariantly functorial in
`C` along ring maps compatible with the augmentations. If `𝒳` satisfies (RS*), then for a fibre
product `P = D ×_A E` in which `E → A` is surjective with square-zero kernel, the map
`Lift(x, P) → Lift(x, D) × Lift(x, E)` is bijective.

These are the formal properties of the sets of lifts on which the infinitesimal deformation
theory of Stacks, Section 98.21 rests; for instance the tangent space `T_x(M)` is
`Lift(x, A[M])`.

## Main definitions

* `Deformation.Artin.AugmentedSiteRing` — an `S`-algebra in the site augmented to `A`.
* `Deformation.Artin.AugmentedSiteRing.classes` — the lift classes `Lift(x, C)`.
* `Deformation.Artin.AugmentedSiteRing.map` — their pullback along a morphism.
* `Deformation.Artin.BasedSiteRing` — augmented rings under a fixed augmented ring `R`, with
  their fibre products `Deformation.Artin.BasedSiteRing.prod` over `A` and the trivial
  square-zero extensions `Deformation.Artin.BasedSiteRing.squareZero`.

## Main results

* `Deformation.Artin.AugmentedSiteRing.map_comp`, `Deformation.Artin.AugmentedSiteRing.map_id` —
  functoriality.
* `Deformation.Artin.AugmentedSiteRing.pair_bijective`,
  `Deformation.Artin.BasedSiteRing.pair_bijective` — condition (RS*) on lift classes.

## Implementation notes

The lift classes are those of `Deformation.Artin.liftClassesOver`, taken along the augmentation
`Spec A ⟶ Spec C`, and pullback is the action of the presheaf of isomorphism classes of the
fibred category `Under.post p` of lifts. Condition (RS*) enters through
`Deformation.Artin.exists_squareZeroLiftEquivalenceOnBigFppfOver` and
`Deformation.Artin.underClassPair_bijective`.

## References

* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local implicit_reducible] Deformation.Artin.squareZeroRing
  CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor
  CategoryTheory.Under.post

universe u v w

namespace Deformation.Artin

variable (A : Type u) [CommRing A]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)

/-- An `S`-algebra `C` whose spectrum lies in the chosen big fppf site, augmented to `A`: a ring
map `C → A` whose induced morphism `Spec A ⟶ Spec C` lies over `S`. -/
public structure AugmentedSiteRing where
  /-- The ring `C`. -/
  ring : CommRingCat.{u}
  /-- `Spec C` is an object of the big fppf site. -/
  contains : B.Contains (Spec ring)
  /-- The structure morphism `Spec C ⟶ S` in the big fppf site. -/
  structureMap : B.obj contains ⟶ B.obj hS
  /-- The augmentation `C → A`. -/
  aug : ring →+* A
  /-- The morphism `Spec A ⟶ Spec C` over `S`. -/
  arrow : algebraOver A B S hS toS hA ⟶
    Over.mk structureMap
  arrow_eq : B.inclusion.map arrow.left = Spec.map (CommRingCat.ofHom aug)

namespace AugmentedSiteRing

variable {A B S hS toS hA}

/-- `Spec C` as an object of the big fppf site over `S`. -/
public abbrev siteOver (D : AugmentedSiteRing A B S hS toS hA) :=
  (Over.mk D.structureMap : BigFppfOver B S hS)

/-- The augmentation `Spec A ⟶ Spec C`, as an object under `Spec A`. -/
public abbrev under (D : AugmentedSiteRing A B S hS toS hA) := Under.mk D.arrow

/-- A morphism of augmented rings `C → D`, recorded as the morphism `Spec D ⟶ Spec C` under
`Spec A`. -/
public abbrev Hom (D E : AugmentedSiteRing A B S hS toS hA) := E.under ⟶ D.under

/-- The morphism of augmented rings given by a ring map compatible with the augmentations and the
structure morphisms. -/
public def homMk {D E : AugmentedSiteRing A B S hS toS hA}
    (f : D.ring →+* E.ring) (hf : E.aug.comp f = D.aug)
    (hs : Spec.map (CommRingCat.ofHom f) ≫ B.inclusion.map D.structureMap =
      B.inclusion.map E.structureMap) : Hom D E := by
  refine Under.homMk (Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom f))) (ObjectProperty.hom_ext _ hs)) ?_
  refine Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_)
  change B.inclusion.map E.arrow.left ≫ Spec.map (CommRingCat.ofHom f) =
    B.inclusion.map D.arrow.left
  rw [E.arrow_eq, D.arrow_eq]
  exact (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom E.aug)).symm.trans
    (congrArg Spec.map (CommRingCat.hom_ext hf))

/-- Morphisms of augmented rings are determined by their morphisms of schemes. -/
public theorem hom_ext {D E : AugmentedSiteRing A B S hS toS hA}
    {f g : Hom D E}
    (h : B.inclusion.map f.right.left = B.inclusion.map g.right.left) : f = g :=
  Under.UnderMorphism.ext (Over.OverMorphism.ext (ObjectProperty.hom_ext _ h))

/-- The isomorphism classes `Lift(x, C)` of lifts of `x` along `Spec A ⟶ Spec C`. -/
public abbrev classes (D : AugmentedSiteRing A B S hS toS hA) :=
  liftClassesOver A B S hS toS hA p x hx D.arrow

/-- The morphism under `p x` underlying a morphism of augmented rings. -/
public def underMap {D E : AugmentedSiteRing A B S hS toS hA} (f : Hom D E) :
    Under.mk (eqToHom hx ≫ E.arrow) ⟶ Under.mk (eqToHom hx ≫ D.arrow) :=
  Under.homMk f.right (by
    change (eqToHom hx ≫ E.arrow) ≫ f.right = eqToHom hx ≫ D.arrow
    rw [Category.assoc]
    exact congrArg (fun k => eqToHom hx ≫ k) (Under.w f))

variable (hp : p.IsFiberedInGroupoids)

/-- Pullback of lift classes along a morphism of augmented rings `C → D`. -/
public def map {D E : AugmentedSiteRing A B S hS toS hA} (f : Hom D E) :
    classes p x hx D → classes p x hx E :=
  letI := underPost_isFibered p hp x
  (Under.post p).isoClassPresheaf.map (underMap p x hx f).op

/-- Pullback of lift classes is functorial. -/
public theorem map_comp {D E F : AugmentedSiteRing A B S hS toS hA}
    (f : Hom D E) (g : Hom E F) (z : classes p x hx D) :
    map p x hx hp (g ≫ f) z = map p x hx hp g (map p x hx hp f z) := by
  let := underPost_isFibered p hp x
  show (Under.post p).isoClassPresheaf.map ((underMap p x hx g) ≫
    (underMap p x hx f)).op z = _
  exact ConcreteCategory.congr_hom
    ((Under.post p).isoClassPresheaf.map_comp (underMap p x hx f).op
      (underMap p x hx g).op) z

/-- Pullback of lift classes along the identity is the identity. -/
public theorem map_id (D : AugmentedSiteRing A B S hS toS hA)
    (z : classes p x hx D) : map p x hx hp (𝟙 D.under) z = z := by
  let := underPost_isFibered p hp x
  show (Under.post p).isoClassPresheaf.map (𝟙 _) z = z
  simp

/-- Pullback along an isomorphism of augmented rings is a bijection of lift classes. -/
public def mapEquiv {D E : AugmentedSiteRing A B S hS toS hA}
    (f : Hom D E) (g : Hom E D) (hf : g ≫ f = 𝟙 _) (hg : f ≫ g = 𝟙 _) :
    classes p x hx D ≃ classes p x hx E where
  toFun := map p x hx hp f
  invFun := map p x hx hp g
  left_inv z := by rw [← map_comp, hf, map_id]
  right_inv z := by rw [← map_comp, hg, map_id]

/-- The pullback of a lift class is computed by any strongly cartesian arrow over the morphism
of spectra which is compatible with the arrows out of `x`. -/
public theorem map_eq_of_lift {D E : AugmentedSiteRing A B S hS toS hA}
    (f : Hom D E)
    (d : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ D.arrow)))
    (e : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ E.arrow)))
    (φ : e.1.right ⟶ d.1.right) (hφ : p.IsStronglyCartesian f.right φ)
    (hw : e.1.hom ≫ φ = d.1.hom) :
    map p x hx hp f (Quotient.mk _ d) = Quotient.mk _ e := by
  let := underPost_isFibered p hp x
  let ψ : e.1 ⟶ d.1 := Under.homMk φ hw
  have hψ : (Under.post p).IsHomLift (underMap p x hx f) ψ := by
    refine IsHomLift.of_fac' _ _ _ e.2 d.2 ?_
    apply Under.UnderMorphism.ext
    have := hφ.toIsHomLift
    simpa [ψ, underMap, Under.post, Under.eqToHom_right] using
      IsHomLift.fac' p f.right φ
  have hc := (underPost_isFiberedInGroupoids p hp x).isStronglyCartesian_homLift
    (underMap p x hx f) ψ
  exact (Functor.isoClassMk_eq_pullbackFiber_of_isCartesian _ d e ψ hψ
    hc.isCartesian_of_isStronglyCartesian).symm

/-- Every pullback of a lift class has a representative with a strongly cartesian arrow to the
original lift. -/
public theorem representative_map {D E : AugmentedSiteRing A B S hS toS hA}
    (f : Hom D E)
    (d : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ D.arrow))) :
    ∃ (e : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ E.arrow)))
      (φ : e.1.right ⟶ d.1.right),
      p.IsStronglyCartesian f.right φ ∧ e.1.hom ≫ φ = d.1.hom ∧
      map p x hx hp f (Quotient.mk _ d) = Quotient.mk _ e := by
  let := underPost_isFibered p hp x
  let c := Functor.chosenPullbacks (Under.post p : Under x ⥤ Under (p.obj x))
  let e := c.obj (underMap p x hx f) d
  let φ := c.map (underMap p x hx f) d
  have hφ : p.IsHomLift f.right φ.right :=
    underPost_isHomLift_right p (underMap p x hx f) φ
      (c.isStronglyCartesian (underMap p x hx f) d).toIsHomLift
  have hstrong := hp.isStronglyCartesian_homLift f.right φ.right
  exact ⟨e, φ.right, hstrong, Under.w φ,
    map_eq_of_lift p x hx hp f d e φ.right hstrong (Under.w φ)⟩

end AugmentedSiteRing

namespace AugmentedSiteRing

variable {A B S hS toS hA}

/-- **Condition (RS*) on lift classes.** For a fibre product `P = D ×_A E` of augmented rings with
`E → A` surjective with square-zero kernel, `Lift(x, P) → Lift(x, D) × Lift(x, E)` is bijective. -/
public theorem pair_bijective (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp)
    (D E P : AugmentedSiteRing A B S hS toS hA)
    (i : Hom P D) (j : Hom P E)
    (hpb : IsPullback
      ((BigFppfOver.toScheme B S hS).map i.right).appTop
      ((BigFppfOver.toScheme B S hS).map j.right).appTop
      (Spec.map (CommRingCat.ofHom D.aug)).appTop
      (Spec.map (CommRingCat.ofHom E.aug)).appTop)
    (hsurj : Function.Surjective E.aug) (hsq : (RingHom.ker E.aug) ^ 2 = ⊥) :
    Function.Bijective (fun z : classes p x hx P =>
      (map p x hx hp i z, map p x hx hp j z)) := by
  let : p.IsFibered := hp.isFibered
  let c := Functor.chosenPullbacks p
  let U : BigFppfOver B S hS :=
    algebraOver A B S hS toS hA
  let V : BigFppfOver B S hS := D.siteOver
  let W : BigFppfOver B S hS := E.siteOver
  let Z : BigFppfOver B S hS := P.siteOver
  let f : U ⟶ V := D.arrow
  let g : U ⟶ W := E.arrow
  let ii : V ⟶ Z := i.right
  let jj : W ⟶ Z := j.right
  have h : f ≫ ii = g ≫ jj := (Under.w i).trans (Under.w j).symm
  have hf : (BigFppfOver.toScheme B S hS).map f =
      Spec.map (CommRingCat.ofHom D.aug) := D.arrow_eq
  have hg : (BigFppfOver.toScheme B S hS).map g =
      Spec.map (CommRingCat.ofHom E.aug) := E.arrow_eq
  obtain ⟨e, he₁, _, he₃⟩ :=
    exists_squareZeroLiftEquivalenceOnBigFppfOver
      B S hS p hp hRS U V W Z
      (hU := show IsAffine (Spec (.of A)) from inferInstance)
      (hV := show IsAffine (Spec D.ring) from inferInstance)
      (hW := show IsAffine (Spec E.ring) from inferInstance)
      (hZ := show IsAffine (Spec P.ring) from inferInstance)
      f g ii jj h
      (by rwa [hf, hg])
      (by
        rw [hg]
        exact specMap_appTop_surjective _ hsurj)
      (by
        rw [hg]
        exact specMap_appTop_ker_sq _ hsq) ⟨x, hx⟩
  have he : ∀ t,
      (e.functor.obj t).1 = isoFiberRestrict p c D.arrow ⟨x, hx⟩
        i.right (D.arrow ≫ i.right) rfl t ∧
      (e.functor.obj t).2 = isoFiberRestrict p c E.arrow ⟨x, hx⟩
        j.right (D.arrow ≫ i.right) ((Under.w j).trans (Under.w i).symm) t := by
    intro t
    refine ⟨Functor.IsoFiber.ext (he₁ t).1 ?_, Functor.IsoFiber.ext (he₁ t).2 (he₃ t).2⟩
    refine (he₃ t).1.trans (heq_of_eq ?_)
    show ((c.pullbackFunctorCompIso D.arrow i.right).symm.app t.obj.left).hom ≫
        t.obj.hom =
      ((c.pullbackFunctorCompIso D.arrow i.right).symm.app t.obj.left).hom ≫
        𝟙 _ ≫ t.obj.hom
    rw [Category.id_comp]
  exact underClassPair_bijective p hp c D.arrow ⟨x, hx⟩ E.arrow i.right j.right
    ((Under.w i).trans (Under.w j).symm) P.arrow (Under.w i) e he

end AugmentedSiteRing

/-- The spectrum of a fibre product of rings over `A` whose spectra lie in the site lies in the
site. -/
public theorem contains_pullback {R T : CommRingCat.{u}}
    (hR : B.Contains (Spec R)) (hT : B.Contains (Spec T))
    (f : R →+* A) (g : T →+* A) :
    B.Contains (Spec (.of (f.pullback g))) := by
  have hbound : Cardinal.mk (f.pullback g) ≤
      max Cardinal.aleph0 (max (Cardinal.mk R) (Cardinal.mk T)) := by
    calc
      _ ≤ Cardinal.mk (R × T) := Cardinal.mk_subtype_le _
      _ = Cardinal.mk R * Cardinal.mk T := by simp only [Cardinal.mk_prod, Cardinal.lift_id]
      _ ≤ max Cardinal.aleph0 (max (Cardinal.mk R) (Cardinal.mk T)) *
          max Cardinal.aleph0 (max (Cardinal.mk R) (Cardinal.mk T)) :=
        mul_le_mul ((le_max_left _ _).trans (le_max_right _ _))
          ((le_max_right _ _).trans (le_max_right _ _)) zero_le zero_le
      _ = _ := Cardinal.mul_eq_self (le_max_left _ _)
  rcases le_total (Cardinal.mk R) (Cardinal.mk T) with h | h
  · exact Scheme.size_Spec_lt_of_mk_le_max (R := T) B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      hT (by simpa [max_eq_right h] using hbound)
  · exact Scheme.size_Spec_lt_of_mk_le_max (R := R) B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      hR (by simpa [max_eq_left h] using hbound)

namespace AugmentedSiteRing

variable {A B S hS toS hA}

/-- An augmented ring receiving a map from a given augmented ring, with the induced structure
morphism to `S`. -/
public def ofRing (R : AugmentedSiteRing A B S hS toS hA)
    (ring : CommRingCat.{u}) (contains : B.Contains (Spec ring))
    (aug : ring →+* A) (base : R.ring →+* ring) (fac : aug.comp base = R.aug) :
    AugmentedSiteRing A B S hS toS hA where
  ring := ring
  contains := contains
  structureMap := ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom base) ≫ B.inclusion.map R.structureMap)
  aug := aug
  arrow := Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom aug))) (by
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom aug) ≫
      (Spec.map (CommRingCat.ofHom base) ≫ B.inclusion.map R.structureMap) = toS
    rw [← Category.assoc, ← Spec.map_comp,
      show CommRingCat.ofHom base ≫ CommRingCat.ofHom aug = CommRingCat.ofHom R.aug from
        CommRingCat.hom_ext fac, ← R.arrow_eq]
    exact congrArg B.inclusion.map (Over.w R.arrow))
  arrow_eq := rfl

end AugmentedSiteRing

/-- An augmented site ring under a fixed augmented ring `R`, whose structure morphism to `S`
factors through `Spec R`. -/
public structure BasedSiteRing (R : AugmentedSiteRing A B S hS toS hA)
    extends AugmentedSiteRing A B S hS toS hA where
  /-- The ring map `R → C`, compatible with the augmentations. -/
  base : R.ring →+* ring
  fac : aug.comp base = R.aug
  structure_fac : Spec.map (CommRingCat.ofHom base) ≫ B.inclusion.map R.structureMap =
    B.inclusion.map structureMap

namespace BasedSiteRing

variable {A B S hS toS hA}

/-- The underlying augmented site ring. -/
public abbrev toAffine {R : AugmentedSiteRing A B S hS toS hA}
    (D : BasedSiteRing A B S hS toS hA R) :
    AugmentedSiteRing A B S hS toS hA := D.toAugmentedSiteRing

/-- A ring map of augmented rings under `R`, compatible with the augmentations and with the maps
from `R`. -/
public structure RingMap {R : AugmentedSiteRing A B S hS toS hA}
    (D E : BasedSiteRing A B S hS toS hA R) where
  /-- The underlying ring map. -/
  hom : D.ring →+* E.ring
  aug_fac : E.aug.comp hom = D.aug
  base_fac : hom.comp D.base = E.base

/-- The morphism of augmented site rings underlying a ring map under `R`. -/
public def RingMap.toHom {R : AugmentedSiteRing A B S hS toS hA}
    {D E : BasedSiteRing A B S hS toS hA R} (f : RingMap D E) :
    AugmentedSiteRing.Hom D.toAffine E.toAffine :=
  AugmentedSiteRing.homMk f.hom f.aug_fac (by
    rw [← D.structure_fac, ← E.structure_fac, ← Category.assoc, ← Spec.map_comp]
    exact congrArg (fun k => Spec.map k ≫ B.inclusion.map R.structureMap)
      (CommRingCat.hom_ext f.base_fac))

/-- Composition of ring maps under `R`. -/
public def RingMap.comp {R : AugmentedSiteRing A B S hS toS hA}
    {D E F : BasedSiteRing A B S hS toS hA R}
    (g : RingMap E F) (f : RingMap D E) : RingMap D F where
  hom := g.hom.comp f.hom
  aug_fac := by rw [← RingHom.comp_assoc, g.aug_fac, f.aug_fac]
  base_fac := by rw [RingHom.comp_assoc, f.base_fac, g.base_fac]

/-- Ring maps under `R` are determined by their underlying ring homomorphisms. -/
public theorem RingMap.ext {R : AugmentedSiteRing A B S hS toS hA}
    {D E : BasedSiteRing A B S hS toS hA R}
    {f g : RingMap D E} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The morphism underlying a composite is the composite of the morphisms. -/
public theorem RingMap.toHom_comp {R : AugmentedSiteRing A B S hS toS hA}
    {D E F : BasedSiteRing A B S hS toS hA R}
    (g : RingMap E F) (f : RingMap D E) :
    (g.comp f).toHom = g.toHom ≫ f.toHom :=
  AugmentedSiteRing.hom_ext (Spec.map_comp (CommRingCat.ofHom f.hom) (CommRingCat.ofHom g.hom))

/-- The lift classes `Lift(x, C)` of an augmented ring under `R`. -/
public abbrev classes {R : AugmentedSiteRing A B S hS toS hA}
    (D : BasedSiteRing A B S hS toS hA R) :=
  AugmentedSiteRing.classes p x hx D.toAffine

/-- Pullback of lift classes along a ring map under `R`. -/
public abbrev map {R : AugmentedSiteRing A B S hS toS hA} (hp : p.IsFiberedInGroupoids)
    {D E : BasedSiteRing A B S hS toS hA R} (f : RingMap D E) :
    classes p x hx D → classes p x hx E :=
  AugmentedSiteRing.map p x hx hp f.toHom

/-- Pullback of lift classes along ring maps under `R` is functorial. -/
public theorem map_comp {R : AugmentedSiteRing A B S hS toS hA} (hp : p.IsFiberedInGroupoids)
    {D E F : BasedSiteRing A B S hS toS hA R}
    (g : RingMap E F) (f : RingMap D E) (z : classes p x hx D) :
    map p x hx hp (g.comp f) z = map p x hx hp g (map p x hx hp f z) := by
  show AugmentedSiteRing.map p x hx hp _ z = _
  rw [RingMap.toHom_comp, AugmentedSiteRing.map_comp]

/-- The base ring `R` itself, as an augmented ring under `R`. -/
public def original (R : AugmentedSiteRing A B S hS toS hA) :
    BasedSiteRing A B S hS toS hA R where
  toAugmentedSiteRing := R
  base := RingHom.id _
  fac := rfl
  structure_fac := by simp

/-- The fibre product `D ×_A E` of two augmented rings under `R`. -/
public def prod {R : AugmentedSiteRing A B S hS toS hA} (D E : BasedSiteRing A B S hS toS hA R) :
    BasedSiteRing A B S hS toS hA R := by
  let base := (D.base.prod E.base).codRestrict (D.aug.pullback E.aug) (by
    intro r
    exact (RingHom.congr_fun D.fac r).trans (RingHom.congr_fun E.fac r).symm)
  exact {
    toAugmentedSiteRing := AugmentedSiteRing.ofRing R (.of (D.aug.pullback E.aug))
      (contains_pullback A B D.contains E.contains D.aug E.aug)
      (D.aug.comp (D.aug.pullbackFst E.aug)) base D.fac
    base := base
    fac := D.fac
    structure_fac := rfl }

/-- The first projection `D ×_A E → D`. -/
public def fst {R : AugmentedSiteRing A B S hS toS hA} (D E : BasedSiteRing A B S hS toS hA R) :
    RingMap (prod D E) D where
  hom := D.aug.pullbackFst E.aug
  aug_fac := rfl
  base_fac := rfl

/-- The second projection `D ×_A E → E`. -/
public def snd {R : AugmentedSiteRing A B S hS toS hA} (D E : BasedSiteRing A B S hS toS hA R) :
    RingMap (prod D E) E where
  hom := D.aug.pullbackSnd E.aug
  aug_fac := (RingHom.pullback_comm_sq D.aug E.aug).symm
  base_fac := rfl

/-- The map into a fibre product `E ×_A F` induced by two maps. -/
public def lift {R : AugmentedSiteRing A B S hS toS hA} {D E F : BasedSiteRing A B S hS toS hA R}
    (f : RingMap D E) (g : RingMap D F) : RingMap D (prod E F) where
  hom := (f.hom.prod g.hom).codRestrict _
    (fun r => (RingHom.congr_fun f.aug_fac r).trans (RingHom.congr_fun g.aug_fac r).symm)
  aug_fac := f.aug_fac
  base_fac := RingHom.ext fun r =>
    Subtype.ext (Prod.ext (RingHom.congr_fun f.base_fac r) (RingHom.congr_fun g.base_fac r))

/-- **Condition (RS*) on lift classes, for rings under `R`.** If `E → A` is surjective with
square-zero kernel, `Lift(x, D ×_A E) → Lift(x, D) × Lift(x, E)` is bijective. -/
public theorem pair_bijective {R : AugmentedSiteRing A B S hS toS hA} (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp)
    (D E : BasedSiteRing A B S hS toS hA R)
    (hsurj : Function.Surjective E.aug) (hsq : (RingHom.ker E.aug) ^ 2 = ⊥) :
    Function.Bijective (fun z : classes p x hx (prod D E) =>
      (map p x hx hp (fst D E) z, map p x hx hp (snd D E) z)) := by
  apply AugmentedSiteRing.pair_bijective p x hx hp hRS
    D.toAffine E.toAffine (prod D E).toAffine (fst D E).toHom (snd D E).toHom
    _ hsurj hsq
  have hpb : IsPullback (CommRingCat.ofHom (RingHom.pullbackFst D.aug E.aug))
      (CommRingCat.ofHom (RingHom.pullbackSnd D.aug E.aug))
      (CommRingCat.ofHom D.aug) (CommRingCat.ofHom E.aug) := by
    apply IsPullback.of_map_of_faithful (forget CommRingCat)
    apply (CategoryTheory.Limits.Types.isPullback_iff _ _ _ _).2
    refine ⟨?_, ?_, ?_⟩
    · ext x
      exact congrArg (fun h : D.aug.pullback E.aug →+* A => h x)
        (RingHom.pullback_comm_sq D.aug E.aug)
    · intro x y hxy
      exact Subtype.ext (Prod.ext hxy.1 hxy.2)
    · intro x y hxy
      exact ⟨⟨(x, y), hxy⟩, rfl, rfl⟩
  apply hpb.of_iso'
    (Scheme.ΓSpecIso (prod D E).ring) (Scheme.ΓSpecIso D.ring)
    (Scheme.ΓSpecIso E.ring) (Scheme.ΓSpecIso (.of A))
  all_goals exact (Scheme.ΓSpecIso_naturality _).symm

end BasedSiteRing

namespace BasedSiteRing

variable {A B S hS toS hA}

/-- The trivial square-zero extension `A[M]`, as an augmented ring under `R`. -/
public def squareZero (R : AugmentedSiteRing A B S hS toS hA) (M : SiteModule A B) :
    BasedSiteRing A B S hS toS hA R where
  toAugmentedSiteRing := {
    ring := squareZeroRing A M.obj
    contains := M.property
    structureMap := (squareZeroOver A B S hS toS M).hom
    aug := (squareZeroProjection A M.obj).hom
    arrow := squareZeroArrow A B S hS toS hA M
    arrow_eq := rfl }
  base := (TrivSqZeroExt.inlHom A M.obj).comp R.aug
  fac := by ext; rfl
  structure_fac := by
    change Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.inlHom A M.obj).comp R.aug)) ≫
      B.inclusion.map R.structureMap =
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj)) ≫ toS
    rw [show CommRingCat.ofHom ((TrivSqZeroExt.inlHom A M.obj).comp R.aug) =
      CommRingCat.ofHom R.aug ≫ CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj) from rfl,
      Spec.map_comp, Category.assoc, ← R.arrow_eq]
    congr 1
    exact congrArg B.inclusion.map (Over.w R.arrow)

/-- The map `A[M] → A[N]` induced by a module map, as a ring map under `R`. -/
public def squareZeroMap (R : AugmentedSiteRing A B S hS toS hA) {M N : SiteModule A B}
    (f : M ⟶ N) : RingMap (squareZero R M) (squareZero R N) where
  hom := (squareZeroRingMap A B f).hom
  aug_fac := by
    ext r
    exact TrivSqZeroExt.fst_map f.hom.hom r
  base_fac := by
    ext r
    exact TrivSqZeroExt.map_inl f.hom.hom (R.aug r)

/-- The morphism of spectra underlying `squareZeroMap` is `squareZeroOverMap`. -/
public theorem squareZeroMap_right (R : AugmentedSiteRing A B S hS toS hA) {M N : SiteModule A B}
    (f : M ⟶ N) : (squareZeroMap R f).toHom.right =
      squareZeroOverMap A B S hS toS f := rfl

/-- The identification of the tangent functor with lift classes over `A[M]` is natural for
pullback along `A[M] → A[N]`. -/
public theorem tangent_natural (R : AugmentedSiteRing A B S hS toS hA) (hp : p.IsFiberedInGroupoids)
    (T : TangentFunctorData A B S hS toS hA p x hx)
    {M N : SiteModule A B} (f : M ⟶ N)
    (a : T.functor.obj M) :
    map p x hx hp (squareZeroMap R f) (T.liftEquiv M a) =
      T.liftEquiv N (T.functor.map f a) := by
  obtain ⟨a', b', ha, hb, φ, hφ, hw⟩ := T.liftEquiv_natural f a
  rw [← ha, ← hb]
  exact AugmentedSiteRing.map_eq_of_lift p x hx hp (squareZeroMap R f).toHom
    a' b' φ hφ hw

/-- The identity ring map under `R`. -/
public def RingMap.id (R : AugmentedSiteRing A B S hS toS hA)
    (D : BasedSiteRing A B S hS toS hA R) : RingMap D D where
  hom := RingHom.id _
  aug_fac := rfl
  base_fac := rfl

/-- Pullback along the identity is the identity. -/
public theorem map_id (R : AugmentedSiteRing A B S hS toS hA) (hp : p.IsFiberedInGroupoids)
    (D : BasedSiteRing A B S hS toS hA R) (z : classes p x hx D) :
    map p x hx hp (RingMap.id R D) z = z := by
  have h : (RingMap.id R D).toHom = 𝟙 D.toAffine.under :=
    AugmentedSiteRing.hom_ext (Spec.map_id _)
  show AugmentedSiteRing.map p x hx hp _ z = z
  rw [h, AugmentedSiteRing.map_id]

/-- The inverse of a ring map under `R` whose underlying map is a ring isomorphism. -/
public def RingMap.inverse (R : AugmentedSiteRing A B S hS toS hA)
    {D E : BasedSiteRing A B S hS toS hA R}
    (f : RingMap D E) (e : D.ring ≃+* E.ring) (he : f.hom = e.toRingHom) : RingMap E D where
  hom := e.symm.toRingHom
  aug_fac := by
    ext y
    obtain ⟨z, rfl⟩ := e.surjective y
    change D.aug (e.symm (e z)) = E.aug (e z)
    rw [e.symm_apply_apply]
    exact (RingHom.congr_fun f.aug_fac z).symm.trans
      (congrArg E.aug (RingHom.congr_fun he z))
  base_fac := by
    ext r
    apply e.injective
    simpa [he] using (RingHom.congr_fun f.base_fac r).symm

/-- Pullback along a ring isomorphism under `R` is a bijection of lift classes. -/
public def equivOfRingEquiv (R : AugmentedSiteRing A B S hS toS hA) (hp : p.IsFiberedInGroupoids)
    {D E : BasedSiteRing A B S hS toS hA R}
    (f : RingMap D E) (e : D.ring ≃+* E.ring) (he : f.hom = e.toRingHom) :
    classes p x hx D ≃ classes p x hx E where
  toFun := map p x hx hp f
  invFun := map p x hx hp (f.inverse R e he)
  left_inv z := by
    rw [← map_comp, show (f.inverse R e he).comp f = RingMap.id R D from
      RingMap.ext (RingHom.ext fun r => by simp [RingMap.comp, RingMap.inverse, RingMap.id, he]),
      map_id]
  right_inv z := by
    rw [← map_comp, show f.comp (f.inverse R e he) = RingMap.id R E from
      RingMap.ext (RingHom.ext fun r => by simp [RingMap.comp, RingMap.inverse, RingMap.id, he]),
      map_id]

end BasedSiteRing

end Deformation.Artin
