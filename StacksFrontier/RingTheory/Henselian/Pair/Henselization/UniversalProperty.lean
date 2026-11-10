module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import StacksFrontier.RingTheory.Henselian.Pair.Henselization.Construction
import all StacksFrontier.RingTheory.Henselian.Pair.Henselization.Construction

/-!
# Henselization of a pair: the universal property

For the henselization `A^h` of a pair `(A, I)`, constructed in
`StacksFrontier.RingTheory.Henselian.Pair.Henselization.Construction`, this file shows that
`(A^h, I A^h)` is a henselian pair, that `A / I → A^h / I A^h` is bijective, and that `A^h` is
initial among henselian pairs under `(A, I)`. In particular the inclusion of henselian pairs into
pairs has a left adjoint.

## Main results

* `henselianPair_henselization`: the henselization is a henselian pair.
* `bijective_quotientMap_henselization`: the henselization does not change the quotient by `I`.
* `nonempty_algEquiv_henselization`: any henselian pair with the universal property is isomorphic
  to the henselization.
* `exists_henselization`: existence of the henselization, as a left adjoint to the inclusion of
  henselian pairs into pairs.

## Implementation notes

Pairs are represented by a ring together with an ideal, and a morphism of pairs by a ring
homomorphism carrying the first ideal into the second. The universal property is stated as the
existence of a unique factorization through the henselization rather than by constructing an
adjunction in the categorical sense.

## References

* [Stacks: Tag 0EM7](https://stacks.math.columbia.edu/tag/0EM7)
-/

-- Not `@[expose]`: the public constructions in this file (`henselization` and friends) are
-- defined in terms of private auxiliary diagrams, so their bodies must stay unexposed.
public section

open CategoryTheory CategoryTheory.Limits IsLocalRing Polynomial
open scoped TensorProduct
open Stacks.Henselization.EtaleColimit

universe u v w

section

section

variable (R : Type u) [CommRing R] (I : Ideal R)

attribute [local instance] etale_essentiallySmall
attribute [local instance] Pairs.etale
attribute [local instance] essentiallySmall_pairs
attribute [local instance] isFiltered_pairs

/-- An augmented ind-étale `R`-algebra maps to the colimit of all augmented étale
`R`-algebras. -/
private theorem exists_augmented_ind_map {E : Type u} [CommRing E] [Algebra R E]
    (hE : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R E))
    (δ : E →ₐ[R] R ⧸ I) :
    ∃ τ : E →ₐ[R] (henselization R I : Type u), (aug R I).comp τ = δ := by
  classical
  obtain ⟨K, _, _, pres, hp⟩ := hE
  let obj (j : K) : Pairs R I :=
    CostructuredArrow.mk (Y := ⟨pres.diag.obj j, hp j⟩)
      (CommAlgCat.ofHom (δ.comp (pres.ι.app j).hom))
  let objMap {j k : K} (f : j ⟶ k) : obj j ⟶ obj k :=
    CostructuredArrow.homMk (ObjectProperty.homMk (pres.diag.map f)) (by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro x
      have h := congrArg (fun φ : pres.diag.obj j ⟶ CommAlgCat.of R E =>
        δ (φ.hom x)) (pres.w f)
      convert h using 1 <;> rfl)
  let c : Cocone pres.diag :=
    { pt := henselization R I
      ι :=
        { app := fun j => CommAlgCat.ofHom (stageHom R I (obj j))
          naturality := by
            intro j k f
            apply CommAlgCat.hom_ext
            apply AlgHom.ext
            intro x
            exact stageHom_map R I (objMap f) x } }
  let τ : E →ₐ[R] (henselization R I : Type u) := (pres.isColimit.desc c).hom
  refine ⟨τ, AlgHom.ext fun x => ?_⟩
  obtain ⟨j, y, hy⟩ := CommAlgCat.exists_app_eq pres.isColimit x
  rw [← hy]
  have hfac := ConcreteCategory.congr_hom (pres.isColimit.fac c j) y
  have hfac' : τ ((pres.ι.app j).hom y) = stageHom R I (obj j) y := by
    convert hfac using 1; rfl
  change aug R I (τ ((pres.ι.app j).hom y)) = δ ((pres.ι.app j).hom y)
  rw [hfac', aug_stageHom]
  rfl

/-- Maps from the henselization into itself are determined by their augmentation. -/
private theorem unique_augmented_hom
    (f g : (henselization R I : Type u) →ₐ[R] (henselization R I : Type u))
    (h : (aug R I).comp f = (aug R I).comp g) : f = g := by
  apply AlgHom.ext
  intro x
  obtain ⟨A, y, rfl⟩ := exists_stage R I x
  have hq : (Ideal.Quotient.mkₐ R (I.map (algebraMap R (henselization R I : Type u)))).comp
      (f.comp (stageHom R I A)) =
      (Ideal.Quotient.mkₐ R (I.map (algebraMap R (henselization R I : Type u)))).comp
      (g.comp (stageHom R I A)) := by
    apply AlgHom.ext
    intro z
    have hz := AlgHom.congr_fun h (stageHom R I A z)
    have hm : f (stageHom R I A z) - g (stageHom R I A z) ∈
        I.map (algebraMap R (henselization R I : Type u)) := by
      rw [← ker_aug R I, RingHom.mem_ker]
      change aug R I (f (stageHom R I A z) - g (stageHom R I A z)) = 0
      rw [map_sub]
      apply sub_eq_zero.mpr
      simpa only [map_sub, AlgHom.comp_apply] using hz
    apply sub_eq_zero.mp
    change Ideal.Quotient.mk _ (f (stageHom R I A z)) -
      Ideal.Quotient.mk _ (g (stageHom R I A z)) = 0
    rw [← map_sub]
    exact (Ideal.Quotient.eq_zero_iff_mem).2 hm
  have heq := unique_etale_map_of_quotient R _ (map_le_jacobson R I)
    (f.comp (stageHom R I A)) (g.comp (stageHom R I A)) hq
  exact AlgHom.congr_fun heq y

/-- The augmentation identifies the quotient of the henselization with `R/I`. -/
private noncomputable def quotientAug :
    (henselization R I : Type u) ⧸
      I.map (algebraMap R (henselization R I : Type u)) →ₐ[R] R ⧸ I :=
  Ideal.Quotient.liftₐ _ (aug R I) (fun a ha => by
    apply RingHom.mem_ker.mp
    change a ∈ RingHom.ker (aug R I).toRingHom
    rw [ker_aug R I]
    exact ha)

private theorem quotientAug_mk (x : (henselization R I : Type u)) :
    quotientAug R I (Ideal.Quotient.mk _ x) = aug R I x := by
  rfl

private theorem quotientAug_injective : Function.Injective (quotientAug R I) := by
  intro x y h
  apply sub_eq_zero.mp
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x - y)
  rw [← ha]
  apply (Ideal.Quotient.eq_zero_iff_mem).2
  rw [← ker_aug R I, RingHom.mem_ker]
  have h0 : quotientAug R I (x - y) = 0 := by rw [map_sub, h, sub_self]
  rwa [← ha, quotientAug_mk] at h0

/-- The filtered colimit of augmented étale neighborhoods is a henselian pair. -/
public theorem henselianPair_henselization :
    HenselianPair (henselization R I : Type u)
      (I.map (algebraMap R (henselization R I : Type u))) := by
  let H := (henselization R I : Type u)
  let J : Ideal H := I.map (algebraMap R H)
  change HenselianPair H J
  apply ((henselianPair_tfae.{u, u} H J).out 2 1).mp
  intro E _ hAlgE hEtE σ
  let : Algebra R E :=
    ((algebraMap H E).comp (algebraMap R H)).toAlgebra
  have : IsScalarTower R H E := IsScalarTower.of_algebraMap_eq' rfl
  let δ : E →ₐ[R] R ⧸ I := (quotientAug R I).comp (σ.restrictScalars R)
  have hInd : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R E) :=
    CommAlgCat.ind_etale_comp (ind_henselization R I)
      ((CommAlgCat.etale.{u} H).le_ind (CommAlgCat.of H E) hEtE)
  obtain ⟨τ, hτ⟩ := exists_augmented_ind_map R I hInd δ
  have hcomp : τ.comp (IsScalarTower.toAlgHom R H E) = AlgHom.id R H := by
    apply unique_augmented_hom R I
    apply AlgHom.ext
    intro x
    have hx := AlgHom.congr_fun hτ (algebraMap H E x)
    change aug R I (τ (algebraMap H E x)) =
      quotientAug R I (σ (algebraMap H E x)) at hx
    rw [σ.commutes x] at hx
    change aug R I (τ (algebraMap H E x)) =
      quotientAug R I (Ideal.Quotient.mk J x) at hx
    rw [quotientAug_mk] at hx
    convert hx using 1 <;> rfl
  let τ' : E →ₐ[H] H :=
    { τ.toRingHom with
      commutes' := fun x => by
        have hx := AlgHom.congr_fun hcomp x
        convert hx using 1 <;> rfl }
  refine ⟨τ', AlgHom.ext fun x => ?_⟩
  apply quotientAug_injective R I
  have hx := AlgHom.congr_fun hτ x
  change aug R I (τ x) = quotientAug R I (σ x) at hx
  change quotientAug R I (Ideal.Quotient.mk J (τ' x)) = quotientAug R I (σ x)
  rw [quotientAug_mk]
  exact hx

/-- Equality in the filtered colimit is witnessed at a common later étale neighborhood. -/
private theorem stage_eq_iff {A C : Pairs R I}
    {y : (A.left.obj : Type u)} {z : (C.left.obj : Type u)} :
    stageHom R I A y = stageHom R I C z ↔
      ∃ (D : Pairs R I) (f : A ⟶ D) (g : C ⟶ D),
        Pairs.map R I f y = Pairs.map R I g z := by
  let : PreservesFilteredColimits (forget (CommAlgCat.{u} R)) := by
    change PreservesFilteredColimits
      ((commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙
        Under.forget (CommRingCat.of R) ⋙ forget CommRingCat)
    infer_instance
  let : IsFiltered (Index R I) :=
    IsFiltered.of_equivalence (equivSmallModel (Pairs R I))
  have : PreservesColimitsOfShape (Pairs R I) (forget (CommAlgCat.{u} R)) :=
    preservesColimitsOfShape_of_equiv
      (equivSmallModel (Pairs R I)).symm (forget (CommAlgCat.{u} R))
  exact (pairsCoconeIsColimit R I).eq_iff (pairsFunctor R I)

/-- Compatible maps from stages take equal colimit elements to equal target elements. -/
private theorem stage_map_eq_of_eq {B : Type v} [CommRing B] [Algebra R B]
    (J : Ideal B) (hB : HenselianPair B J)
    (hIJ : I ≤ J.comap (algebraMap R B)) {A C : Pairs R I}
    {y : (A.left.obj : Type u)} {z : (C.left.obj : Type u)}
    (h : stageHom R I A y = stageHom R I C z) :
    Pairs.map_to_henselian R I J hB hIJ A y =
      Pairs.map_to_henselian R I J hB hIJ C z := by
  obtain ⟨D, f, g, heq⟩ := (stage_eq_iff R I).mp h
  have hf := AlgHom.congr_fun (Pairs.map_to_henselian_natural R I J hB hIJ f) y
  have hg := AlgHom.congr_fun (Pairs.map_to_henselian_natural R I J hB hIJ g) z
  calc
    _ = Pairs.map_to_henselian R I J hB hIJ D (Pairs.map R I f y) := by
      simpa only [AlgHom.comp_apply] using hf.symm
    _ = Pairs.map_to_henselian R I J hB hIJ D (Pairs.map R I g z) := by rw [heq]
    _ = _ := by simpa only [AlgHom.comp_apply] using hg

/-- Evaluate an element of the colimit in a henselian target using any stage representative. -/
private noncomputable def mapFun {B : Type v} [CommRing B] [Algebra R B]
    (J : Ideal B) (hB : HenselianPair B J)
    (hIJ : I ≤ J.comap (algebraMap R B))
    (x : (henselization R I : Type u)) : B :=
  let h := exists_stage R I x
  let A := Classical.choose h
  let y := Classical.choose (Classical.choose_spec h)
  Pairs.map_to_henselian R I J hB hIJ A y

private theorem mapFun_stage {B : Type v} [CommRing B] [Algebra R B]
    (J : Ideal B) (hB : HenselianPair B J)
    (hIJ : I ≤ J.comap (algebraMap R B)) (A : Pairs R I)
    (y : (A.left.obj : Type u)) :
    mapFun R I J hB hIJ (stageHom R I A y) =
      Pairs.map_to_henselian R I J hB hIJ A y := by
  classical
  let h := exists_stage R I (stageHom R I A y)
  let C := Classical.choose h
  let z := Classical.choose (Classical.choose_spec h)
  have hz : stageHom R I C z = stageHom R I A y :=
    Classical.choose_spec (Classical.choose_spec h)
  exact stage_map_eq_of_eq R I J hB hIJ hz

/-- Any two elements of the colimit come from the same stage. -/
private theorem exists_common_stage (x y : (henselization R I : Type u)) :
    ∃ (D : Pairs R I) (a c : (D.left.obj : Type u)),
      stageHom R I D a = x ∧ stageHom R I D c = y := by
  obtain ⟨A, a, rfl⟩ := exists_stage R I x
  obtain ⟨C, c, rfl⟩ := exists_stage R I y
  obtain ⟨D, f, g, -⟩ := Pairs.cocone_objs R I A C
  exact ⟨D, _, _, stageHom_map R I f a, stageHom_map R I g c⟩

/-- The colimit evaluation is a ring homomorphism, even when the target lies in a larger
universe than the colimit category. -/
private noncomputable def toHenselianRingHom {B : Type v} [CommRing B] [Algebra R B]
    (J : Ideal B) (hB : HenselianPair B J)
    (hIJ : I ≤ J.comap (algebraMap R B)) :
    (henselization R I : Type u) →+* B where
  toFun := mapFun R I J hB hIJ
  map_one' := by
    let A := Pairs.unit R I
    calc
      mapFun R I J hB hIJ 1 =
          mapFun R I J hB hIJ (stageHom R I A 1) := by rw [map_one]
      _ = 1 := by rw [mapFun_stage, map_one]
  map_mul' := by
    intro x y
    obtain ⟨D, a, c, rfl, rfl⟩ := exists_common_stage R I x y
    rw [← map_mul (stageHom R I D), mapFun_stage, mapFun_stage, mapFun_stage, map_mul]
  map_zero' := by
    let A := Pairs.unit R I
    calc
      mapFun R I J hB hIJ 0 =
          mapFun R I J hB hIJ (stageHom R I A 0) := by rw [map_zero]
      _ = 0 := by rw [mapFun_stage, map_zero]
  map_add' := by
    intro x y
    obtain ⟨D, a, c, rfl, rfl⟩ := exists_common_stage R I x y
    rw [← map_add (stageHom R I D), mapFun_stage, mapFun_stage, mapFun_stage, map_add]

/-- The colimit evaluation preserves the `R`-algebra structures. -/
private noncomputable def toHenselian {B : Type v} [CommRing B] [Algebra R B]
    (J : Ideal B) (hB : HenselianPair B J)
    (hIJ : I ≤ J.comap (algebraMap R B)) :
    (henselization R I : Type u) →ₐ[R] B :=
  { toHenselianRingHom R I J hB hIJ with
    commutes' := fun r => by
      let A := Pairs.unit R I
      change mapFun R I J hB hIJ (algebraMap R (henselization R I : Type u) r) =
        algebraMap R B r
      rw [← (stageHom R I A).commutes r, mapFun_stage,
        (Pairs.map_to_henselian R I J hB hIJ A).commutes r] }

/-- The map to a henselian target is the only `R`-algebra map. -/
private theorem toHenselian_unique {B : Type v} [CommRing B] [Algebra R B]
    (J : Ideal B) (hB : HenselianPair B J)
    (hIJ : I ≤ J.comap (algebraMap R B))
    (g : (henselization R I : Type u) →ₐ[R] B) :
    g = toHenselian R I J hB hIJ := by
  apply AlgHom.ext
  intro x
  obtain ⟨A, y, rfl⟩ := exists_stage R I x
  have hg := map_stage_reduction R I J hIJ g A
  have ht := Pairs.map_to_henselian_spec R I J hB hIJ A
  have heq := unique_etale_map_of_quotient R J hB.1
    (g.comp (stageHom R I A))
    (Pairs.map_to_henselian R I J hB hIJ A) (hg.trans ht.symm)
  change g (stageHom R I A y) = mapFun R I J hB hIJ (stageHom R I A y)
  rw [mapFun_stage]
  exact AlgHom.congr_fun heq y

/-- The map `R ⧸ I → R^h ⧸ I R^h` induced by `R → R^h` is bijective. -/
public theorem bijective_quotientMap_henselization :
    Function.Bijective (Ideal.quotientMap
      (I.map (algebraMap R (henselization R I : Type u)))
      (algebraMap R (henselization R I : Type u)) Ideal.le_comap_map) := by
  let q := Ideal.quotientMap (I.map (algebraMap R (henselization R I : Type u)))
    (algebraMap R (henselization R I : Type u)) Ideal.le_comap_map
  have hq (x : R ⧸ I) : quotientAug R I (q x) = x := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact aug_algebraMap R I r
  refine ⟨fun x y h => ?_, fun y => ?_⟩
  · change q x = q y at h
    exact (hq x).symm.trans ((congrArg (quotientAug R I) h).trans (hq y))
  · exact ⟨quotientAug R I y, quotientAug_injective R I (hq _)⟩

/-- Henselianity is unchanged by a ring isomorphism. -/
private theorem henselianPair_map_equiv {A : Type v} {B : Type w}
    [CommRing A] [CommRing B] (e : A ≃+* B) (J : Ideal A)
    (h : HenselianPair A J) :
    HenselianPair B (J.map e.toRingHom) := by
  refine ⟨?_, ?_⟩
  · have hm := Ideal.map_mono (f := e.toRingHom) h.1
    simpa only [Ideal.map_jacobson_of_bijective (f := e.toRingHom) e.bijective,
      Ideal.map_bot] using hm
  · intro f hf g₀ h₀ hg₀ hh₀ hfac hcop
    let q := Ideal.quotientEquiv J (J.map e.toRingHom) e rfl
    have heq : (Ideal.Quotient.mk J).comp e.symm.toRingHom =
        q.symm.toRingHom.comp (Ideal.Quotient.mk (J.map e.toRingHom)) := by
      ext x
      exact (Ideal.quotientEquiv_symm_mk J (J.map e.toRingHom) e rfl x).symm
    have hfac' : (f.map e.symm.toRingHom).map (Ideal.Quotient.mk J) =
        g₀.map q.symm.toRingHom * h₀.map q.symm.toRingHom := by
      rw [Polynomial.map_map, heq, ← Polynomial.map_map, hfac, Polynomial.map_mul]
    obtain ⟨g, k, hg, hk, hfk, hgq, hkq⟩ := h.2
      (f.map e.symm.toRingHom) (hf.map _) _ _ (hg₀.map _) (hh₀.map _) hfac'
      (hcop.map (Polynomial.mapRingHom q.symm.toRingHom))
    refine ⟨g.map e.toRingHom, k.map e.toRingHom, hg.map _, hk.map _, ?_, ?_, ?_⟩
    · simpa only [Polynomial.map_mul, Polynomial.map_map, RingEquiv.toRingHom_eq_coe,
        RingEquiv.comp_symm, Polynomial.map_id] using
          congrArg (Polynomial.map e.toRingHom) hfk
    · apply Polynomial.map_injective q.symm.toRingHom q.symm.injective
      rw [Polynomial.map_map, ← heq, ← Polynomial.map_map]
      simpa only [Polynomial.map_map, RingEquiv.toRingHom_eq_coe,
        RingEquiv.symm_comp, Polynomial.map_id] using hgq
    · apply Polynomial.map_injective q.symm.toRingHom q.symm.injective
      rw [Polynomial.map_map, ← heq, ← Polynomial.map_map]
      simpa only [Polynomial.map_map, RingEquiv.toRingHom_eq_coe,
        RingEquiv.symm_comp, Polynomial.map_id] using hkq

/-- Henselianity of `(A, I A)` is preserved by passing to `ULift A`. -/
private theorem henselianPair_ulift {A : Type v} [CommRing A] [Algebra R A]
    (h : HenselianPair A (I.map (algebraMap R A))) :
    HenselianPair (ULift.{w} A) (I.map (algebraMap R (ULift.{w} A))) := by
  have h' := henselianPair_map_equiv (ULift.ringEquiv.symm : A ≃+* ULift.{w} A) _ h
  rwa [Ideal.map_map] at h'

/-- An `R`-algebra `Ah` such that `(Ah, I Ah)` is henselian and initial among henselian pairs under
`(R, I)` in the universe `max u v` is isomorphic as an `R`-algebra to `henselization R I`. -/
public theorem nonempty_algEquiv_henselization (Ah : Type v) [CommRing Ah] [Algebra R Ah]
    (hh : HenselianPair Ah (I.map (algebraMap R Ah)))
    (hι : ∀ (B : Type (max u v)) (_ : CommRing B) (J : Ideal B),
      HenselianPair B J →
        ∀ f : R →+* B, I ≤ J.comap f →
          ∃! g : Ah →+* B,
            g.comp (algebraMap R Ah) = f ∧ I.map (algebraMap R Ah) ≤ J.comap g) :
    Nonempty ((henselization R I : Type u) ≃ₐ[R] Ah) := by
  let H := (henselization R I : Type u)
  let f : H →ₐ[R] Ah := toHenselian R I _ hh Ideal.le_comap_map
  have hH := henselianPair_ulift.{u, u, v} R I (henselianPair_henselization R I)
  obtain ⟨g₀, hg₀, -⟩ := hι (ULift.{v} H) inferInstance _ hH
    (algebraMap R (ULift.{v} H)) Ideal.le_comap_map
  let g : Ah →ₐ[R] H :=
    { ULift.ringEquiv.toRingHom.comp g₀ with
      commutes' := fun r => by
        have hr := RingHom.congr_fun hg₀.1 r
        exact congrArg ULift.down hr }
  have hAh := henselianPair_ulift.{u, v, u} R I hh
  have huniq : ∀ p q : Ah →ₐ[R] Ah, p = q := by
    intro p q
    let lift (p : Ah →ₐ[R] Ah) : Ah →ₐ[R] ULift.{u} Ah :=
      (ULift.algEquiv (R := R)).symm.toAlgHom.comp p
    have hs (p : Ah →ₐ[R] Ah) :
        (lift p).toRingHom.comp (algebraMap R Ah) = algebraMap R (ULift.{u} Ah) ∧
          I.map (algebraMap R Ah) ≤
            (I.map (algebraMap R (ULift.{u} Ah))).comap (lift p).toRingHom := by
      refine ⟨(lift p).comp_algebraMap, ?_⟩
      rw [← Ideal.map_le_iff_le_comap, Ideal.map_map]
      exact le_of_eq (congrArg (fun f : R →+* ULift.{u} Ah => I.map f)
        (lift p).comp_algebraMap)
    have he := (hι (ULift.{u} Ah) inferInstance _ hAh
      (algebraMap R (ULift.{u} Ah)) Ideal.le_comap_map).unique (hs p) (hs q)
    exact AlgHom.ext fun x => congrArg ULift.down (RingHom.congr_fun he x)
  refine ⟨AlgEquiv.ofAlgHom f g (huniq _ _) ?_⟩
  exact (toHenselian_unique R I _ (henselianPair_henselization R I)
    Ideal.le_comap_map (g.comp f)).trans
      (toHenselian_unique R I _ (henselianPair_henselization R I)
        Ideal.le_comap_map (AlgHom.id R H)).symm

end

/-- Every pair `(A, I)` has a henselization: there is a henselian pair `(Aʰ, IAʰ)` under `(A, I)`
which is initial among henselian pairs under `(A, I)`. Equivalently, the inclusion of henselian
pairs into pairs has a left adjoint. -/
@[stacks 0A02]
theorem exists_henselization (A : Type u) [CommRing A] (I : Ideal A) :
    ∃ (Ah : Type u) (_ : CommRing Ah) (ι : A →+* Ah),
      HenselianPair Ah (I.map ι) ∧
        ∀ (B : Type v) (_ : CommRing B) (J : Ideal B),
          HenselianPair B J →
            ∀ f : A →+* B, I ≤ J.comap f →
              ∃! g : Ah →+* B, g.comp ι = f ∧ I.map ι ≤ J.comap g := by
  classical
  refine ⟨(henselization A I : Type u), inferInstance,
    algebraMap A (henselization A I : Type u), henselianPair_henselization A I, ?_⟩
  intro B instB J hB f hf
  let : CommRing B := instB
  let : Algebra A B := f.toAlgebra
  have hIJ : I ≤ J.comap (algebraMap A B) := hf
  let g : (henselization A I : Type u) →+* B :=
    (toHenselian A I J hB hIJ).toRingHom
  have hgcomp : g.comp (algebraMap A (henselization A I : Type u)) = f :=
    RingHom.ext (toHenselian A I J hB hIJ).commutes
  refine ⟨g, ⟨hgcomp, ?_⟩, ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change g (algebraMap A (henselization A I : Type u) a) ∈ J
    rw [← RingHom.comp_apply, hgcomp]
    exact hIJ ha
  · intro g' hg'
    let gAlg : (henselization A I : Type u) →ₐ[A] B :=
      { g' with
        commutes' := fun a => by
          have h := congrArg (fun φ : A →+* B => φ a) hg'.1
          convert h using 1 }
    have h := toHenselian_unique A I J hB hIJ gAlg
    have h' := congrArg AlgHom.toRingHom h
    change g' = g
    exact h'

end

end
