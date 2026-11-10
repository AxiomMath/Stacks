module

public import StacksFrontier.Deformation.Artin.Infinitesimal.ActionOnLifts.Presentation
public import StacksFrontier.Deformation.Artin.Infinitesimal.Functoriality
import all StacksFrontier.Deformation.Artin.Infinitesimal.ActionOnLifts.Presentation

/-!
# The action of the tangent module on lift classes

This file continues
`StacksFrontier.Deformation.Artin.Infinitesimal.ActionOnLifts.Presentation`; it is the second
of the three files re-exported by
`StacksFrontier.Deformation.Artin.Infinitesimal.ActionOnLifts`. It contains the trivial
square-zero extensions as based rings, the geometric difference of two lift classes, the
difference map and its additivity, and **Stacks 07Y9 part (2)(b)**,
`Deformation.Artin.exists_actionOnLifts`; then the
diagonal of `A' ×_A A'` and the Eckmann–Hilton argument
`Deformation.Artin.map_add_of_interchange` used for part (1) in
`StacksFrontier.Deformation.Artin.Infinitesimal.ActionOnLifts.InfComparison`.

## References

* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local implicit_reducible] Deformation.Artin.squareZeroRing
  CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor

universe u v w

namespace Deformation.Artin

section Deformations

variable (A : Type u) [CommRing A]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)

namespace BasedRing

variable {A B S hS toS hA}

private def squareZero (R : AffineDeformation A B S hS toS hA) (M : SiteModule A B) :
    BasedRing A B S hS toS hA R where
  toAffineDeformation := {
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

private def squareZeroMap (R : AffineDeformation A B S hS toS hA) {M N : SiteModule A B}
    (f : M ⟶ N) : RingMap (squareZero R M) (squareZero R N) where
  hom := (squareZeroRingMap A B f).hom
  aug_fac := by
    ext r
    exact TrivSqZeroExt.fst_map f.hom.hom r
  base_fac := by
    ext r
    exact TrivSqZeroExt.map_inl f.hom.hom (R.aug r)

private lemma squareZeroMap_right (R : AffineDeformation A B S hS toS hA) {M N : SiteModule A B}
    (f : M ⟶ N) : (squareZeroMap R f).toHom.right =
      squareZeroOverMap A B S hS toS f := rfl

private lemma tangent_natural (R : AffineDeformation A B S hS toS hA) (hp : p.IsFiberedInGroupoids)
    (T : TangentFunctorData A B S hS toS hA p x hx)
    {M N : SiteModule A B} (f : M ⟶ N)
    (a : T.functor.obj M) :
    map p x hx hp (squareZeroMap R f) (T.liftEquiv M a) =
      T.liftEquiv N (T.functor.map f a) := by
  obtain ⟨a', b', ha, hb, φ, hφ, hw⟩ := T.liftEquiv_natural f a
  rw [← ha, ← hb]
  exact AffineDeformation.map_eq_of_lift p x hx hp (squareZeroMap R f).toHom
    a' b' φ hφ hw

private def RingMap.id (R : AffineDeformation A B S hS toS hA)
    (D : BasedRing A B S hS toS hA R) : RingMap D D where
  hom := RingHom.id _
  aug_fac := rfl
  base_fac := rfl

private lemma RingMap.toHom_id (R : AffineDeformation A B S hS toS hA)
    (D : BasedRing A B S hS toS hA R) : (RingMap.id R D).toHom = 𝟙 D.toAffine.under :=
  AffineDeformation.hom_ext (Spec.map_id _)

private lemma map_id (R : AffineDeformation A B S hS toS hA) (hp : p.IsFiberedInGroupoids)
    (D : BasedRing A B S hS toS hA R) (z : classes p x hx D) :
    map p x hx hp (RingMap.id R D) z = z := by
  change AffineDeformation.map p x hx hp _ z = z
  rw [RingMap.toHom_id, AffineDeformation.map_id]

private def RingMap.inverse (R : AffineDeformation A B S hS toS hA)
    {D E : BasedRing A B S hS toS hA R}
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

private lemma RingMap.inverse_comp (R : AffineDeformation A B S hS toS hA)
    {D E : BasedRing A B S hS toS hA R} (f : RingMap D E) (e : D.ring ≃+* E.ring)
    (he : f.hom = e.toRingHom) : (f.inverse R e he).comp f = RingMap.id R D := by
  apply RingMap.ext
  ext r
  change e.symm (f.hom r) = r
  rw [he]
  exact e.symm_apply_apply r

private lemma RingMap.comp_inverse (R : AffineDeformation A B S hS toS hA)
    {D E : BasedRing A B S hS toS hA R} (f : RingMap D E) (e : D.ring ≃+* E.ring)
    (he : f.hom = e.toRingHom) : f.comp (f.inverse R e he) = RingMap.id R E := by
  apply RingMap.ext
  ext r
  change f.hom (e.symm r) = r
  rw [he]
  exact e.apply_symm_apply r

private def equivOfRingEquiv (R : AffineDeformation A B S hS toS hA) (hp : p.IsFiberedInGroupoids)
    {D E : BasedRing A B S hS toS hA R}
    (f : RingMap D E) (e : D.ring ≃+* E.ring) (he : f.hom = e.toRingHom) :
    classes p x hx D ≃ classes p x hx E where
  toFun := map p x hx hp f
  invFun := map p x hx hp (f.inverse R e he)
  left_inv z := by
    rw [← map_comp, RingMap.inverse_comp, map_id]
  right_inv z := by
    rw [← map_comp, RingMap.comp_inverse, map_id]

end BasedRing

private lemma existsUnique_of_pair_equiv {Y V Z : Type*}
    (e : Z ≃ Y × Y) (f : Z ≃ Y × V)
    (hf : ∀ z, (f z).1 = (e z).1) (y : Y) (a : V) :
    ∃! y', (f (e.symm (y, y'))).2 = a := by
  let E := equivFromPairCoordinates e f (fun z => (hf z).symm) y
  refine ⟨E.symm a, E.apply_symm_apply a, ?_⟩
  intro y' hy'
  exact E.injective (hy'.trans (E.apply_symm_apply a).symm)


namespace BasedRing

variable {A B S hS toS hA}

private def squareZeroPair (R : AffineDeformation A B S hS toS hA)
    {D : BasedRing A B S hS toS hA R}
    {M N : SiteModule A B}
    (f : RingMap D (squareZero R M)) (g : RingMap D (squareZero R N)) :
    RingMap D (squareZero R (siteModuleProd A B hA M N)) := by
  have hfst : ∀ r, (f.hom r).fst = (g.hom r).fst := fun r =>
    (RingHom.congr_fun f.aug_fac r).trans (RingHom.congr_fun g.aug_fac r).symm
  refine {
    hom := {
      toFun := fun r => ((f.hom r).fst, ((f.hom r).snd, (g.hom r).snd))
      map_zero' := by
        change ((f.hom 0).fst, ((f.hom 0).snd, (g.hom 0).snd)) =
          (0, (0, 0))
        rw [map_zero, map_zero]
        rfl
      map_one' := by
        change ((f.hom 1).fst, ((f.hom 1).snd, (g.hom 1).snd)) =
          (1, (0, 0))
        rw [map_one, map_one]
        rfl
      map_add' := by
        intro r s
        change ((f.hom (r + s)).fst, ((f.hom (r + s)).snd, (g.hom (r + s)).snd)) = _
        rw [map_add, map_add]
        rfl
      map_mul' := ?_ }
    aug_fac := ?_
    base_fac := ?_ }
  · intro r s
    apply TrivSqZeroExt.ext
    · change (f.hom (r * s)).fst = (f.hom r).fst * (f.hom s).fst
      rw [map_mul]
      rfl
    · apply Prod.ext
      · change (f.hom (r * s)).snd = _
        rw [map_mul]
        rfl
      · change (g.hom (r * s)).snd =
          (f.hom r).fst • (g.hom s).snd + (f.hom s).fst • (g.hom r).snd
        rw [map_mul, hfst r, hfst s]
        rfl
  · exact f.aug_fac
  · apply RingHom.ext
    intro r
    have hf := RingHom.congr_fun f.base_fac r
    have hg := RingHom.congr_fun g.base_fac r
    apply TrivSqZeroExt.ext
    · change (f.hom (D.base r)).fst = R.aug r
      exact congrArg (fun z : TrivSqZeroExt A M.obj => z.fst) hf
    · change ((f.hom (D.base r)).snd, (g.hom (D.base r)).snd) = (0, 0)
      exact Prod.ext (congrArg (fun z : TrivSqZeroExt A M.obj => z.snd) hf)
        (congrArg (fun z : TrivSqZeroExt A N.obj => z.snd) hg)

private lemma squareZeroPair_fst (R : AffineDeformation A B S hS toS hA)
    {D : BasedRing A B S hS toS hA R}
    {M N : SiteModule A B}
    (f : RingMap D (squareZero R M)) (g : RingMap D (squareZero R N)) :
    (squareZeroMap R (siteModuleFst A B hA M N)).comp (squareZeroPair R f g) = f := by
  refine RingMap.ext (RingHom.ext fun r => TrivSqZeroExt.ext ?_ ?_)
  · exact TrivSqZeroExt.fst_map (siteModuleFst A B hA M N).hom.hom _
  · exact TrivSqZeroExt.snd_map (siteModuleFst A B hA M N).hom.hom _

private lemma squareZeroPair_snd (R : AffineDeformation A B S hS toS hA)
    {D : BasedRing A B S hS toS hA R}
    {M N : SiteModule A B}
    (f : RingMap D (squareZero R M)) (g : RingMap D (squareZero R N)) :
    (squareZeroMap R (siteModuleSnd A B hA M N)).comp (squareZeroPair R f g) = g := by
  refine RingMap.ext (RingHom.ext fun r => TrivSqZeroExt.ext ?_ ?_)
  · refine (TrivSqZeroExt.fst_map (siteModuleSnd A B hA M N).hom.hom (
      (squareZeroPair R f g).hom r)).trans ?_
    exact (RingHom.congr_fun f.aug_fac r).trans (RingHom.congr_fun g.aug_fac r).symm
  · exact TrivSqZeroExt.snd_map (siteModuleSnd A B hA M N).hom.hom _

private lemma tangent_pair_add (R : AffineDeformation A B S hS toS hA)
    (hp : p.IsFiberedInGroupoids)
    (T : TangentFunctorData A B S hS toS hA p x hx)
    {D : BasedRing A B S hS toS hA R}
    {M : SiteModule A B}
    (f g : RingMap D (squareZero R M)) (z : classes p x hx D) :
    (T.liftEquiv M).symm (map p x hx hp (D := D) (E := squareZero R M)
        ((squareZeroMap R (siteModuleFst A B hA M M + siteModuleSnd A B hA M M)).comp
          (squareZeroPair R f g)) z) =
      (T.liftEquiv M).symm (map p x hx hp (D := D) (E := squareZero R M) f z) +
        (T.liftEquiv M).symm (map p x hx hp (D := D) (E := squareZero R M) g z) := by
  let N := siteModuleProd A B hA M M
  let a := (T.liftEquiv N).symm
    (map p x hx hp (D := D) (E := squareZero R N) (squareZeroPair R f g) z)
  have ha : T.liftEquiv N a =
      map p x hx hp (D := D) (E := squareZero R N) (squareZeroPair R f g) z :=
    (T.liftEquiv N).apply_symm_apply _
  have hmap (k : N ⟶ M) :
      (T.liftEquiv M).symm (map p x hx hp (D := D) (E := squareZero R M)
        ((squareZeroMap R k).comp (squareZeroPair R f g)) z) = T.functor.map k a := by
    rw [map_comp, ← ha, tangent_natural, Equiv.symm_apply_apply]
  have hf := hmap (siteModuleFst A B hA M M)
  have hg := hmap (siteModuleSnd A B hA M M)
  rw [squareZeroPair_fst] at hf
  rw [squareZeroPair_snd] at hg
  rw [hmap, hf, hg]
  exact ConcreteCategory.congr_hom T.functor.map_add a

end BasedRing

namespace BasedRing

variable {A B S hS toS hA}

private def kernelSite (R : AffineDeformation A B S hS toS hA)
    (hq : Function.Surjective R.aug) (hsq : (RingHom.ker R.aug) ^ 2 = ⊥) :
    SiteModule A B := by
  letI := Stacks.Smooth.kerModule hq hsq
  exact ⟨ModuleCat.of A (RingHom.ker R.aug), isSiteModule_kernel A B R.contains R.aug hq⟩

private def differenceEquiv (R : AffineDeformation A B S hS toS hA)
    (hq : Function.Surjective R.aug) (hsq : (RingHom.ker R.aug) ^ 2 = ⊥) :
    (prod (original R) (original R)).ring ≃+*
      (prod (original R) (squareZero R (kernelSite R hq hsq))).ring :=
  (squareZeroDifferenceEquiv R.aug hq hsq).val

private def differenceMap (R : AffineDeformation A B S hS toS hA)
    (hq : Function.Surjective R.aug) (hsq : (RingHom.ker R.aug) ^ 2 = ⊥) :
    RingMap (prod (original R) (original R))
      (prod (original R) (squareZero R (kernelSite R hq hsq))) where
  hom := (differenceEquiv R hq hsq).toRingHom
  aug_fac := by
    ext y
    exact congrArg R.aug ((squareZeroDifferenceEquiv R.aug hq hsq).property y).1
  base_fac := by
    apply RingHom.ext
    intro r
    have h := (squareZeroDifferenceEquiv R.aug hq hsq).property
      (⟨(r, r), rfl⟩ : R.aug.pullback R.aug)
    apply Subtype.ext
    apply Prod.ext h.1
    exact h.2.trans (TrivSqZeroExt.ext rfl (Subtype.ext (sub_self r)))

private def delta (R : AffineDeformation A B S hS toS hA)
    (hq : Function.Surjective R.aug) (hsq : (RingHom.ker R.aug) ^ 2 = ⊥) :
    RingMap (prod (original R) (original R)) (squareZero R (kernelSite R hq hsq)) :=
  (snd (original R) (squareZero R (kernelSite R hq hsq))).comp (differenceMap R hq hsq)

private lemma delta_apply (R : AffineDeformation A B S hS toS hA)
    (hq : Function.Surjective R.aug) (hsq : (RingHom.ker R.aug) ^ 2 = ⊥)
    (y : (prod (original R) (original R)).ring) :
    (delta R hq hsq).hom y = (R.aug y.1.1, kerDifference R.aug y) :=
  ((squareZeroDifferenceEquiv R.aug hq hsq).property y).2

private lemma differenceMap_fst (R : AffineDeformation A B S hS toS hA)
    (hq : Function.Surjective R.aug) (hsq : (RingHom.ker R.aug) ^ 2 = ⊥) :
    (fst (original R) (squareZero R (kernelSite R hq hsq))).comp (differenceMap R hq hsq) =
      fst (original R) (original R) := by
  apply RingMap.ext
  ext y
  exact ((squareZeroDifferenceEquiv R.aug hq hsq).property y).1

private def triple12 (R : AffineDeformation A B S hS toS hA) :=
  fst (prod (original R) (original R)) (original R)

private def triple23 (R : AffineDeformation A B S hS toS hA) :=
  lift ((snd (original R) (original R)).comp (triple12 R))
    (snd (prod (original R) (original R)) (original R))

private def triple13 (R : AffineDeformation A B S hS toS hA) :=
  lift ((fst (original R) (original R)).comp (triple12 R))
    (snd (prod (original R) (original R)) (original R))

private lemma delta_triple (R : AffineDeformation A B S hS toS hA)
    (hq : Function.Surjective R.aug) (hsq : (RingHom.ker R.aug) ^ 2 = ⊥) :
    (squareZeroMap R (siteModuleFst A B hA (kernelSite R hq hsq) (kernelSite R hq hsq) +
      siteModuleSnd A B hA (kernelSite R hq hsq) (kernelSite R hq hsq))).comp
        (squareZeroPair R ((delta R hq hsq).comp (triple12 R))
          ((delta R hq hsq).comp (triple23 R))) =
      (delta R hq hsq).comp (triple13 R) := by
  apply RingMap.ext
  apply RingHom.ext
  intro y
  apply TrivSqZeroExt.ext
  · refine (TrivSqZeroExt.fst_map _ ((squareZeroPair R ((delta R hq hsq).comp (triple12 R))
      ((delta R hq hsq).comp (triple23 R))).hom y)).trans ?_
    change ((delta R hq hsq).hom ((triple12 R).hom y)).fst =
      ((delta R hq hsq).hom ((triple13 R).hom y)).fst
    rw [delta_apply, delta_apply]
    rfl
  · refine (TrivSqZeroExt.snd_map _ ((squareZeroPair R ((delta R hq hsq).comp (triple12 R))
      ((delta R hq hsq).comp (triple23 R))).hom y)).trans ?_
    change ((delta R hq hsq).hom ((triple12 R).hom y)).snd +
      ((delta R hq hsq).hom ((triple23 R).hom y)).snd =
        ((delta R hq hsq).hom ((triple13 R).hom y)).snd
    rw [delta_apply, delta_apply, delta_apply]
    apply Subtype.ext
    change (y.1.1.1.2 - y.1.1.1.1) + (y.1.2 - y.1.1.1.2) = y.1.2 - y.1.1.1.1
    abel

end BasedRing

namespace BasedRing

variable {A B S hS toS hA}

private def overIso (R : AffineDeformation A B S hS toS hA)
    {D E : BasedRing A B S hS toS hA R}
    (f : RingMap D E) (e : D.ring ≃+* E.ring) (he : f.hom = e.toRingHom) :
    E.toAffine.siteOver ≅ D.toAffine.siteOver where
  hom := f.toHom.right
  inv := (f.inverse R e he).toHom.right
  hom_inv_id := by
    have hm := congrArg RingMap.toHom (RingMap.comp_inverse R f e he)
    rw [RingMap.toHom_comp, RingMap.toHom_id] at hm
    exact congrArg Under.Hom.right hm
  inv_hom_id := by
    have hm := congrArg RingMap.toHom (RingMap.inverse_comp R f e he)
    rw [RingMap.toHom_comp, RingMap.toHom_id] at hm
    exact congrArg Under.Hom.right hm

end BasedRing


private theorem nonempty_actionOnLiftsData
    (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp)
    (A' : Type u) [CommRing A']
    (hA' : B.Contains (Spec (.of A')))
    (toS' : B.obj hA' ⟶ B.obj hS)
    (q : A' →+* A)
    (hq : Function.Surjective q)
    (hsq : (RingHom.ker q) ^ 2 = ⊥)
    (g : algebraOver A B S hS toS hA ⟶
      (Over.mk toS' : BigFppfOver B S hS))
    (hg : B.inclusion.map g.left = Spec.map (CommRingCat.ofHom q)) :
    Nonempty (ActionOnLiftsData A B S hS toS hA p x hx
      (tangentFunctor A B S hS toS hA p x hx hp hRS)
      A' hA' toS' q hq hsq g) := by
  refine ⟨?_⟩
  classical
  let R : AffineDeformation A B S hS toS hA := ⟨.of A', hA', toS', q, g, hg⟩
  let O := BasedRing.original R
  let M := BasedRing.kernelSite R hq hsq
  let W := BasedRing.squareZero R M
  let P := BasedRing.prod O O
  let Q := BasedRing.prod O W
  let P₃ := BasedRing.prod P O
  let T := tangentFunctor A B S hS toS hA p x hx hp hRS
  let TE : (T.functor.obj M : Type _) ≃ BasedRing.classes p x hx W := T.liftEquiv M
  let eP := Equiv.ofBijective _ (BasedRing.pair_bijective p x hx hp hRS O O hq hsq)
  have hwSurj : Function.Surjective W.aug := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hwSq : (RingHom.ker W.aug)^2 = ⊥ := squareZeroProjection_ker_sq A M.obj
  let eQ := Equiv.ofBijective _ (BasedRing.pair_bijective p x hx hp hRS O W hwSurj hwSq)
  let E := BasedRing.equivOfRingEquiv p x hx R hp
    (BasedRing.differenceMap R hq hsq) (BasedRing.differenceEquiv R hq hsq) rfl
  let f := E.trans (eQ.trans (Equiv.prodCongr (Equiv.refl _) TE.symm))
  have hf : ∀ z, (f z).1 = (eP z).1 := by
    intro z
    change BasedRing.map p x hx hp (D := Q) (E := O) (BasedRing.fst O W)
      (BasedRing.map p x hx hp (D := P) (E := Q) (BasedRing.differenceMap R hq hsq) z) =
        BasedRing.map p x hx hp (D := P) (E := O) (BasedRing.fst O O) z
    rw [← BasedRing.map_comp, BasedRing.differenceMap_fst]
  let d := fun z₁ z₂ => (f (eP.symm (z₂, z₁))).2
  have hd (z : BasedRing.classes p x hx P) :
      d (BasedRing.map p x hx hp (D := P) (E := O) (BasedRing.snd O O) z)
        (BasedRing.map p x hx hp (D := P) (E := O) (BasedRing.fst O O) z) =
      TE.symm (BasedRing.map p x hx hp (D := P) (E := W) (BasedRing.delta R hq hsq) z) := by
    change (f (eP.symm (eP z))).2 = _
    rw [eP.symm_apply_apply]
    change TE.symm (BasedRing.map p x hx hp (D := Q) (E := W) (BasedRing.snd O W)
      (BasedRing.map p x hx hp (D := P) (E := Q) (BasedRing.differenceMap R hq hsq) z)) = _
    rw [← BasedRing.map_comp]
    rfl
  have htrans : ∀ z₁ z₂ z₃, d z₁ z₂ + d z₂ z₃ = d z₁ z₃ := by
    intro z₁ z₂ z₃
    obtain ⟨t, ht⟩ := (BasedRing.pair_bijective p x hx hp hRS P O hq hsq).2
      (eP.symm (z₃, z₂), z₁)
    have ht12 : BasedRing.map p x hx hp (D := P₃) (E := P) (BasedRing.triple12 R) t =
        eP.symm (z₃, z₂) := congrArg Prod.fst ht
    have ht3 : BasedRing.map p x hx hp (D := P₃) (E := O) (BasedRing.snd P O) t = z₁ :=
      congrArg Prod.snd ht
    have h1 : BasedRing.map p x hx hp (D := P) (E := O) (BasedRing.fst O O)
        (BasedRing.map p x hx hp (D := P₃) (E := P) (BasedRing.triple12 R) t) = z₃ := by
      rw [ht12]
      exact congrArg Prod.fst (eP.apply_symm_apply (z₃, z₂))
    have h2 : BasedRing.map p x hx hp (D := P) (E := O) (BasedRing.snd O O)
        (BasedRing.map p x hx hp (D := P₃) (E := P) (BasedRing.triple12 R) t) = z₂ := by
      rw [ht12]
      exact congrArg Prod.snd (eP.apply_symm_apply (z₃, z₂))
    have h23fst : (BasedRing.fst O O).comp (BasedRing.triple23 R) =
        (BasedRing.snd O O).comp (BasedRing.triple12 R) := by
      apply BasedRing.RingMap.ext
      rfl
    have h23snd : (BasedRing.snd O O).comp (BasedRing.triple23 R) =
        BasedRing.snd P O := by
      apply BasedRing.RingMap.ext
      rfl
    have h13fst : (BasedRing.fst O O).comp (BasedRing.triple13 R) =
        (BasedRing.fst O O).comp (BasedRing.triple12 R) := by
      apply BasedRing.RingMap.ext
      rfl
    have h13snd : (BasedRing.snd O O).comp (BasedRing.triple13 R) =
        BasedRing.snd P O := by
      apply BasedRing.RingMap.ext
      rfl
    have hd12 := hd (BasedRing.map p x hx hp (D := P₃) (E := P) (BasedRing.triple12 R) t)
    rw [h1, h2, ← BasedRing.map_comp] at hd12
    have hd23 := hd (BasedRing.map p x hx hp (D := P₃) (E := P) (BasedRing.triple23 R) t)
    rw [← BasedRing.map_comp, h23snd, ht3, ← BasedRing.map_comp, h23fst,
      BasedRing.map_comp, h2, ← BasedRing.map_comp] at hd23
    have hd13 := hd (BasedRing.map p x hx hp (D := P₃) (E := P) (BasedRing.triple13 R) t)
    rw [← BasedRing.map_comp, h13snd, ht3, ← BasedRing.map_comp, h13fst,
      BasedRing.map_comp, h1, ← BasedRing.map_comp] at hd13
    rw [hd12, hd23, hd13, add_comm]
    have hadd := BasedRing.tangent_pair_add p x hx R hp T
      ((BasedRing.delta R hq hsq).comp (BasedRing.triple12 R))
      ((BasedRing.delta R hq hsq).comp (BasedRing.triple23 R)) t
    rw [BasedRing.delta_triple] at hadd
    exact hadd.symm
  let D : LiftDifference (T.functor.obj M) (liftClassesOver A B S hS toS hA p x hx g) := {
    difference := d
    difference_self := fun z => by
      apply add_left_cancel (a := d z z)
      simpa using htrans z z z
    difference_trans := htrans
    difference_existsUnique := existsUnique_of_pair_equiv eP f hf }
  refine {
    kernelIsSiteModule := M.property
    action := D.action
    difference := D.difference
    difference_geometric := ?_
    action_difference := D.action_difference
    zero_action := D.action_zero
    add_action := D.action_add
    orbit_bijective := D.action_bijective }
  intro z₁ z₂
  let zP := eP.symm (z₂, z₁)
  obtain ⟨v, hv⟩ := Quotient.exists_rep zP
  obtain ⟨t₁, φ₁, hφ₁, hw₁, ht₁⟩ := AffineDeformation.representative_map p x hx hp
    (BasedRing.snd O O).toHom v
  obtain ⟨t₂, φ₂, hφ₂, hw₂, ht₂⟩ := AffineDeformation.representative_map p x hx hp
    (BasedRing.fst O O).toHom v
  obtain ⟨w, ε, hε, hwε, hw⟩ := AffineDeformation.representative_map p x hx hp
    (BasedRing.differenceMap R hq hsq).toHom v
  obtain ⟨t, ψ, hψ, hwψ, ht⟩ := AffineDeformation.representative_map p x hx hp
    (BasedRing.snd O W).toHom w
  let e := BasedRing.overIso R (BasedRing.differenceMap R hq hsq)
    (BasedRing.differenceEquiv R hq hsq) rfl
  refine ⟨P.contains, Q.contains, P.structureMap, Q.structureMap,
    (BasedRing.fst O O).toHom.right, (BasedRing.snd O O).toHom.right,
    (BasedRing.snd O W).toHom.right, e, BasedRing.differenceEquiv R hq hsq,
    rfl, rfl, rfl, rfl,
    (squareZeroDifferenceEquiv q hq hsq).property,
    t₁, t₂, t, v.1.right, w.1.right, φ₁, φ₂, ψ, ε, ?_, ?_, ?_,
    hφ₁, hφ₂, hψ, hε, hw₁.trans hw₂.symm, ?_⟩
  · exact ht₁.symm.trans
      ((congrArg (AffineDeformation.map p x hx hp (BasedRing.snd O O).toHom) hv).trans
        (congrArg Prod.snd (eP.apply_symm_apply (z₂, z₁))))
  · exact ht₂.symm.trans
      ((congrArg (AffineDeformation.map p x hx hp (BasedRing.fst O O).toHom) hv).trans
        (congrArg Prod.fst (eP.apply_symm_apply (z₂, z₁))))
  · change Quotient.mk _ t = TE (d z₁ z₂)
    change Quotient.mk _ t = TE (TE.symm
      (BasedRing.map p x hx hp (D := Q) (E := W) (BasedRing.snd O W)
        (BasedRing.map p x hx hp (D := P) (E := Q) (BasedRing.differenceMap R hq hsq) zP)))
    rw [TE.apply_symm_apply, ← hv]
    exact ht.symm.trans (congrArg (AffineDeformation.map p x hx hp
      (BasedRing.snd O W).toHom) hw.symm)
  · calc
      t.1.hom ≫ ψ ≫ ε = w.1.hom ≫ ε := by rw [← Category.assoc, hwψ]
      _ = v.1.hom := hwε
      _ = t₁.1.hom ≫ φ₁ := hw₁.symm


/-- **Stacks 07Y9 part (2)(b).** The difference-transport action of the tangent module
`T_x(I)` on the isomorphism classes of lifts of `x` over a square-zero deformation `A' → A`
with kernel `I`. Every orbit map is bijective, so the action is simply transitive whenever
there is a lift. -/
@[stacks 07Y9 "part (2)(b), the action of T_x(I) on the lifts over A'"]
public noncomputable def exists_actionOnLifts
    (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp)
    (A' : Type u) [CommRing A']
    (hA' : B.Contains (Spec (.of A')))
    (toS' : B.obj hA' ⟶ B.obj hS)
    (q : A' →+* A)
    (hq : Function.Surjective q)
    (hsq : (RingHom.ker q) ^ 2 = ⊥)
    (g : algebraOver A B S hS toS hA ⟶
      (Over.mk toS' : BigFppfOver B S hS))
    (hg : B.inclusion.map g.left = Spec.map (CommRingCat.ofHom q)) :
    ActionOnLiftsData A B S hS toS hA p x hx
      (tangentFunctor A B S hS toS hA p x hx hp hRS)
      A' hA' toS' q hq hsq g :=
  Classical.choice (by
    exact nonempty_actionOnLiftsData A B S hS toS hA p x hx
      hp hRS A' hA' toS' q hq hsq g hg)


/-! ### The diagonal of a self-fibre product -/

namespace AffineDeformation

variable {A B S hS toS hA}

private lemma underMap_comp {D E F : AffineDeformation A B S hS toS hA}
    (u : Hom D E) (w : Hom E F) :
    underMap p x hx (w ≫ u) = underMap p x hx w ≫ underMap p x hx u := by
  apply Under.UnderMorphism.ext
  rfl

private lemma underMap_id (D : AffineDeformation A B S hS toS hA) :
    underMap p x hx (𝟙 D.under) = 𝟙 (Under.mk (eqToHom hx ≫ D.arrow)) := by
  apply Under.UnderMorphism.ext
  rfl

end AffineDeformation

namespace BasedRing

variable {A B S hS toS hA}

/-- The square of global sections presenting a fibre product of two based rings is a
pullback square. -/
private lemma prod_isPullbackSquare {R : AffineDeformation A B S hS toS hA}
    (D E : BasedRing A B S hS toS hA R) :
    IsPullback ((BigFppfOver.toScheme B S hS).map (fst D E).toHom.right).appTop
      ((BigFppfOver.toScheme B S hS).map (snd D E).toHom.right).appTop
      (Spec.map (CommRingCat.ofHom D.aug)).appTop
      (Spec.map (CommRingCat.ofHom E.aug)).appTop := by
  apply (ringPullbackIsPullback D.aug E.aug).of_iso'
    (Scheme.ΓSpecIso (prod D E).ring) (Scheme.ΓSpecIso D.ring)
    (Scheme.ΓSpecIso E.ring) (Scheme.ΓSpecIso (.of A)) <;>
    exact (Scheme.ΓSpecIso_naturality _).symm

/-- The diagonal of the self-fibre product of a deformation situation. -/
private def diag (R : AffineDeformation A B S hS toS hA) :
    RingMap (original R) (prod (original R) (original R)) :=
  lift (RingMap.id R (original R)) (RingMap.id R (original R))

private lemma fst_comp_diag (R : AffineDeformation A B S hS toS hA) :
    (fst (original R) (original R)).comp (diag R) = RingMap.id R (original R) := by
  apply RingMap.ext
  apply RingHom.ext
  intro r
  rfl

private lemma snd_comp_diag (R : AffineDeformation A B S hS toS hA) :
    (snd (original R) (original R)).comp (diag R) = RingMap.id R (original R) := by
  apply RingMap.ext
  apply RingHom.ext
  intro r
  rfl

/-- The structural ring map from the ring of a deformation situation to a based ring
over it. -/
private def baseMap (R : AffineDeformation A B S hS toS hA)
    (D : BasedRing A B S hS toS hA R) : RingMap (original R) D where
  hom := D.base
  aug_fac := D.fac
  base_fac := RingHom.comp_id _

/-- **The self-difference vanishes.** Composing the difference map with the diagonal gives
the structural map: the difference of a lift from itself is the trivial deformation. -/
private lemma delta_comp_diag (R : AffineDeformation A B S hS toS hA)
    (hq : Function.Surjective R.aug) (hsq : (RingHom.ker R.aug) ^ 2 = ⊥) :
    (delta R hq hsq).comp (diag R) =
      baseMap R (squareZero R (kernelSite R hq hsq)) := by
  apply RingMap.ext
  apply RingHom.ext
  intro a
  change (delta R hq hsq).hom ((diag R).hom a) = _
  rw [delta_apply]
  exact TrivSqZeroExt.ext rfl (Subtype.ext (sub_self a))

end BasedRing

/-! ### Eckmann–Hilton: a monoid-valued product-preserving functor -/

section EckmannHilton

/-- **The Eckmann–Hilton step.** Let `G` be a functor from the site modules to sets whose
values carry unital binary operations preserved by the transition maps, with the transition
map along a zero module map constant at the unit, and suppose the two projections decompose
the value at `M × M`. Then the transition map along the sum of the projections is the
operation applied to the two transition maps: the binary operation induced by the product
decomposition — which is the addition of Stacks 06I6 — is the given one. -/
private theorem map_add_of_interchange (G : SiteModule A B ⥤ Type w)
    (one : ∀ N : SiteModule A B, G.obj N)
    (mul : ∀ N : SiteModule A B, G.obj N → G.obj N → G.obj N)
    (hmul_one : ∀ (N : SiteModule A B) (a : G.obj N), mul N a (one N) = a)
    (hone_mul : ∀ (N : SiteModule A B) (a : G.obj N), mul N (one N) a = a)
    (hmap_mul : ∀ {N N' : SiteModule A B} (f : N ⟶ N') (a b : G.obj N),
      G.map f (mul N a b) = mul N' (G.map f a) (G.map f b))
    (M : SiteModule A B) (hmap_zero : ∀ a : G.obj M, G.map (0 : M ⟶ M) a = one M)
    (hbij : Function.Bijective (fun z : G.obj (siteModuleProd A B hA M M) =>
      (G.map (siteModuleFst A B hA M M) z, G.map (siteModuleSnd A B hA M M) z)))
    (θ : G.obj (siteModuleProd A B hA M M)) :
    G.map (siteModuleFst A B hA M M + siteModuleSnd A B hA M M) θ =
      mul M (G.map (siteModuleFst A B hA M M) θ)
        (G.map (siteModuleSnd A B hA M M) θ) := by
  let E := Equiv.ofBijective _ hbij
  have hEfst : ∀ z, (E z).1 = G.map (siteModuleFst A B hA M M) z := fun _ => rfl
  have hEsnd : ∀ z, (E z).2 = G.map (siteModuleSnd A B hA M M) z := fun _ => rfl
  have hinl : ∀ a : G.obj M,
      E (G.map (siteModuleInl A B hA M M) a) = (a, one M) := by
    intro a
    refine Prod.ext ((hEfst _).trans ?_) ((hEsnd _).trans ?_)
    · rw [← Functor.map_comp_apply, siteModuleInl_comp_fst,
        Functor.map_id_apply]
    · rw [← Functor.map_comp_apply, siteModuleInl_comp_snd]
      exact hmap_zero a
  have hinr : ∀ b : G.obj M,
      E (G.map (siteModuleInr A B hA M M) b) = (one M, b) := by
    intro b
    refine Prod.ext ((hEfst _).trans ?_) ((hEsnd _).trans ?_)
    · rw [← Functor.map_comp_apply, siteModuleInr_comp_fst]
      exact hmap_zero b
    · rw [← Functor.map_comp_apply, siteModuleInr_comp_snd,
        Functor.map_id_apply]
  have hsum_inl : ∀ a : G.obj M,
      G.map (siteModuleFst A B hA M M + siteModuleSnd A B hA M M)
        (G.map (siteModuleInl A B hA M M) a) = a := by
    intro a
    rw [← Functor.map_comp_apply, Preadditive.comp_add, siteModuleInl_comp_fst,
      siteModuleInl_comp_snd, add_zero, Functor.map_id_apply]
  have hsum_inr : ∀ b : G.obj M,
      G.map (siteModuleFst A B hA M M + siteModuleSnd A B hA M M)
        (G.map (siteModuleInr A B hA M M) b) = b := by
    intro b
    rw [← Functor.map_comp_apply, Preadditive.comp_add, siteModuleInr_comp_fst,
      siteModuleInr_comp_snd, zero_add, Functor.map_id_apply]
  let ν : G.obj M → G.obj M → G.obj M := fun a b =>
    G.map (siteModuleFst A B hA M M + siteModuleSnd A B hA M M) (E.symm (a, b))
  have hν : ∀ a b : G.obj M, ν a b =
      G.map (siteModuleFst A B hA M M + siteModuleSnd A B hA M M) (E.symm (a, b)) :=
    fun _ _ => rfl
  have hν_one_right : ∀ a : G.obj M, ν a (one M) = a := by
    intro a
    have h : E.symm (a, one M) = G.map (siteModuleInl A B hA M M) a :=
      E.symm_apply_eq.2 (hinl a).symm
    rw [hν, h]
    exact hsum_inl a
  have hν_one_left : ∀ b : G.obj M, ν (one M) b = b := by
    intro b
    have h : E.symm (one M, b) = G.map (siteModuleInr A B hA M M) b :=
      E.symm_apply_eq.2 (hinr b).symm
    rw [hν, h]
    exact hsum_inr b
  have hsymm_mul : ∀ a a' b b' : G.obj M,
      E.symm (mul M a a', mul M b b') =
        mul (siteModuleProd A B hA M M) (E.symm (a, b)) (E.symm (a', b')) := by
    intro a a' b b'
    refine E.symm_apply_eq.2 (Prod.ext ?_ ?_)
    · refine ((hEfst _).trans ?_).symm
      rw [hmap_mul]
      refine congrArg₂ (mul M) ?_ ?_
      · exact ((hEfst _).symm.trans (congrArg Prod.fst (E.apply_symm_apply (a, b))))
      · exact ((hEfst _).symm.trans (congrArg Prod.fst (E.apply_symm_apply (a', b'))))
    · refine ((hEsnd _).trans ?_).symm
      rw [hmap_mul]
      refine congrArg₂ (mul M) ?_ ?_
      · exact ((hEsnd _).symm.trans (congrArg Prod.snd (E.apply_symm_apply (a, b))))
      · exact ((hEsnd _).symm.trans (congrArg Prod.snd (E.apply_symm_apply (a', b'))))
  have hν_mul : ∀ a a' b b' : G.obj M,
      ν (mul M a a') (mul M b b') = mul M (ν a b) (ν a' b') := by
    intro a a' b b'
    simp only [hν, hsymm_mul, hmap_mul]
  have hνeq : ∀ a b : G.obj M, ν a b = mul M a b := by
    intro a b
    calc ν a b = ν (mul M a (one M)) (mul M (one M) b) := by
          rw [hmul_one, hone_mul]
      _ = mul M (ν a (one M)) (ν (one M) b) := hν_mul a (one M) (one M) b
      _ = mul M a b := by rw [hν_one_right, hν_one_left]
  have hθ : E.symm (G.map (siteModuleFst A B hA M M) θ,
      G.map (siteModuleSnd A B hA M M) θ) = θ := by
    refine E.symm_apply_eq.2 (Prod.ext ?_ ?_)
    · exact (hEfst θ).symm
    · exact (hEsnd θ).symm
  have hfinal := hνeq (G.map (siteModuleFst A B hA M M) θ)
    (G.map (siteModuleSnd A B hA M M) θ)
  rw [hν, hθ] at hfinal
  exact hfinal

end EckmannHilton

end Deformations

end Deformation.Artin

end
