module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic

/-!
# Coequalizing two maps of étale algebras

Two maps `f, g : C → D` of étale `A`-algebras can be coequalized inside the category of étale
`A`-algebras: there is an étale `A`-algebra `E` receiving `D`, universal among `A`-algebras on
which `f` and `g` agree.  The construction is the pushout of `C ⊗[A] C → C` along
`C ⊗[A] C → D`, which is étale because the multiplication map of an étale algebra is étale.

This is the step that makes the category of étale algebras under a fixed ring filtered.

## Main results

* `AlgebraicGeometry.ProEtale.etale_coequalize_maps`: the coequalizer of two maps of étale
  algebras, together with its universal property.

## Implementation notes

The coequalizer is produced as an existential statement rather than as a chosen object, with
its universal property spelled out as the last conjunct, because its only consumers are
filteredness arguments which need nothing more.

## References

* [Stacks Project, Tag 097P](https://stacks.math.columbia.edu/tag/097P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

/-- The multiplication map `C ⊗[A] C → C` of an étale `A`-algebra is étale. -/
private theorem etale_tensorProduct_mul (A C : Type u) [CommRing A] [CommRing C]
    [Algebra A C] [Algebra.Etale A C] :
    RingHom.Etale ((Algebra.TensorProduct.lmul' A (S := C)).toRingHom) := by
  let T := TensorProduct A C C
  let : CommRing T := inferInstance
  let : Algebra C T := inferInstance
  have hAT : Algebra.Etale A T := Algebra.Etale.comp A C T
  let : Algebra T C := (Algebra.TensorProduct.lmul' A (S := C)).toRingHom.toAlgebra
  have hmap :
      (Algebra.TensorProduct.lmul' A (S := C)).toRingHom.comp (algebraMap A T) =
        algebraMap A C := by
    ext a
    show ((Algebra.TensorProduct.lmul' A (S := C)).comp
      (Algebra.TensorProduct.includeLeft (R := A) (S := A))) (algebraMap A C a) = _
    rw [Algebra.TensorProduct.lmul'_comp_includeLeft]
    rfl
  have : IsScalarTower A T C := .of_algebraMap_eq fun a =>
    (congrArg (fun f : A →+* C => f a) hmap).symm
  show Algebra.Etale T C
  exact Algebra.Etale.of_restrictScalars A T C

/-- **Stacks Project, Tag 097P.** Two maps `f, g` of étale `A`-algebras `C → D`
admit a coequalizer in étale `A`-algebras: an étale `A`-algebra `E` with maps from `D`
and from `C` identifying the two composites, universal among all `A`-algebras with that
property. -/
public theorem etale_coequalize_maps (A C D : Type u) [CommRing A] [CommRing C]
    [CommRing D] [Algebra A C] [Algebra A D] [Algebra.Etale A C] [Algebra.Etale A D]
    (f g : C →ₐ[A] D) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra A E), Algebra.Etale A E ∧
      ∃ (h : D →ₐ[A] E) (j : C →ₐ[A] E), h.comp f = j ∧ h.comp g = j ∧
        ∀ {F : Type u} [CommRing F] [Algebra A F] (r : D →ₐ[A] F) (s : C →ₐ[A] F),
          r.comp f = s → r.comp g = s →
            ∃ k : E →ₐ[A] F, k.comp h = r ∧ k.comp j = s := by
  let T : Type u := TensorProduct A C C
  let d : T →ₐ[A] C := Algebra.TensorProduct.lmul' A
  let p : T →ₐ[A] D := (Algebra.TensorProduct.lmul' A).comp
    (Algebra.TensorProduct.map f g)
  let j := CommRingCat.ofHom d.toRingHom
  let k := CommRingCat.ofHom p.toRingHom
  let Q : CommRingCat := Limits.pushout j k
  let iQ : CommRingCat.of D ⟶ Q := Limits.pushout.inr j k
  let qA : A →+* Q := iQ.hom.comp (algebraMap A D)
  let : Algebra A Q := qA.toAlgebra
  have hj : CommRingCat.etale j := by
    show RingHom.Etale d.toRingHom
    exact etale_tensorProduct_mul A C
  have hiQ : CommRingCat.etale iQ := MorphismProperty.pushout_inr j k hj
  have hAD : CommRingCat.etale (CommRingCat.ofHom (algebraMap A D)) := by
    show RingHom.Etale (algebraMap A D)
    exact RingHom.etale_algebraMap.mpr inferInstance
  have hAQ : CommRingCat.etale (CommRingCat.ofHom qA) := by
    simpa [qA] using MorphismProperty.comp_mem CommRingCat.etale
      (CommRingCat.ofHom (algebraMap A D)) iQ hAD hiQ
  have hEt : Algebra.Etale A Q := RingHom.etale_algebraMap.mp (by
    show RingHom.Etale qA
    exact hAQ)
  let h : D →ₐ[A] Q := {
    toRingHom := iQ.hom
    commutes' := fun a => rfl }
  refine ⟨Q, inferInstance, inferInstance, hEt, ?_⟩
  have hpush (x y : C) :
      (Limits.pushout.inl j k).hom (x * y) = iQ.hom (f x * g y) := by
    have hx := congrArg (fun z : CommRingCat.of T ⟶ Q => z.hom (x ⊗ₜ[A] y))
      (Limits.pushout.condition (f := j) (g := k))
    change (Limits.pushout.inl j k).hom (Algebra.TensorProduct.lmul' A (x ⊗ₜ[A] y)) =
      iQ.hom (Algebra.TensorProduct.lmul' A ((Algebra.TensorProduct.map f g) (x ⊗ₜ[A] y)))
      at hx
    simpa only [Algebra.TensorProduct.lmul'_apply_tmul, Algebra.TensorProduct.map_tmul] using hx
  have h₁ (c : C) : (Limits.pushout.inl j k).hom c = iQ.hom (f c) := by
    simpa using hpush c 1
  have h₂ (c : C) : (Limits.pushout.inl j k).hom c = iQ.hom (g c) := by
    simpa using hpush 1 c
  let q : C →ₐ[A] Q := {
    toRingHom := (Limits.pushout.inl j k).hom
    commutes' := fun a => by
      have ha := h₁ (algebraMap A C a)
      rw [f.commutes a] at ha
      show (Limits.pushout.inl j k).hom (algebraMap A C a) = qA a
      exact ha }
  refine ⟨h, q, AlgHom.ext fun c => (h₁ c).symm, AlgHom.ext fun c => (h₂ c).symm, ?_⟩
  intro F _ _ r s hrf hrg
  have hw : s.comp d = r.comp p := by
    refine Algebra.TensorProduct.ext' fun x y => ?_
    simp only [AlgHom.comp_apply, d, p, Algebra.TensorProduct.lmul'_apply_tmul,
      Algebra.TensorProduct.map_tmul, map_mul]
    rw [show r (f x) = s x from congrArg (fun q : C →ₐ[A] F => q x) hrf,
      show r (g y) = s y from congrArg (fun q : C →ₐ[A] F => q y) hrg]
  have hw' : j ≫ CommRingCat.ofHom s.toRingHom =
      k ≫ CommRingCat.ofHom r.toRingHom :=
    CommRingCat.hom_ext <| congrArg (fun φ : T →ₐ[A] F => φ.toRingHom) hw
  let kr : Q ⟶ CommRingCat.of F :=
    Limits.pushout.desc (CommRingCat.ofHom s.toRingHom)
      (CommRingCat.ofHom r.toRingHom) hw'
  have hkq : kr.hom.comp q.toRingHom = s.toRingHom :=
    congrArg (fun φ : CommRingCat.of C ⟶ CommRingCat.of F => φ.hom) <|
      Limits.pushout.inl_desc (CommRingCat.ofHom s.toRingHom)
        (CommRingCat.ofHom r.toRingHom) hw'
  let kl : Q →ₐ[A] F := {
    toRingHom := kr.hom
    commutes' := fun a => by
      show kr.hom (algebraMap A Q a) = algebraMap A F a
      rw [← q.commutes a]
      show (kr.hom.comp q.toRingHom) (algebraMap A C a) = _
      rw [hkq]
      exact s.commutes a }
  refine ⟨kl, AlgHom.ext fun x => ?_, AlgHom.ext fun x => congrArg (fun φ : C →+* F => φ x) hkq⟩
  exact congrArg (fun φ : CommRingCat.of D ⟶ CommRingCat.of F => φ.hom x) <|
    Limits.pushout.inr_desc (CommRingCat.ofHom s.toRingHom) (CommRingCat.ofHom r.toRingHom) hw'

end AlgebraicGeometry.ProEtale
