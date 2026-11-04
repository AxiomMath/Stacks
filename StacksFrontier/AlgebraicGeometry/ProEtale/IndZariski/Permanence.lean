module

public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.BaseChange
public import StacksFrontier.AlgebraicGeometry.ProEtale.LocalIso.Permanence
public import StacksCore.Tactic.StacksAttribute

/-!
# Permanence of ind-Zariski ring maps

Ind-Zariski maps cancel on the left in an algebra tower: if `A → B` and `A → C` are ind-Zariski
then so is `B → C`.

## Main results

* `AlgebraicGeometry.ProEtale.isIndZariski_of_retraction`: if `A → B` is ind-Zariski and admits
  a retraction, then the retraction is ind-Zariski.
* `AlgebraicGeometry.ProEtale.isIndZariski_of_left_of_comp`: left cancellation for ind-Zariski
  maps.

## Implementation notes

Left cancellation is deduced from base change and from the retraction statement: the map
`B → C` factors as `B → C ⊗[A] B → C`, where the first map is the base change of `A → C` along
`A → B` and the second is the retraction of the base change of `A → B` along `A → C`.

The retraction statement is proved by transporting the filtered presentation. If `B` is the
filtered colimit of local isomorphisms `A → B i`, then `A` is the filtered colimit of the
algebras `A ⊗[B i] B`; each of those is a local isomorphism over `A` because `B i → B` is one,
by left cancellation for local isomorphisms. The structure map of each stage is surjective,
which is what makes the transition maps and the colimit comparison unique and hence makes the
transported diagram a functor with a colimit cocone.

## References

* [Stacks Project, Tag 096R](https://stacks.math.columbia.edu/tag/096R)
-/

@[expose] public section

namespace AlgebraicGeometry.ProEtale

universe u v w

open CategoryTheory Limits
open scoped TensorProduct

/-- Two morphisms out of a commutative algebra whose structure map is surjective agree. -/
private lemma commAlgCat_hom_ext_of_surjective {R : Type*} [CommRing R] {X Y : CommAlgCat R}
    (h : Function.Surjective (algebraMap R X)) (f g : X ⟶ Y) : f = g := by
  refine CommAlgCat.hom_ext (AlgHom.ext fun x => ?_)
  obtain ⟨r, rfl⟩ := h x
  simp

/-- **Stacks 096R.** A retraction of an ind-Zariski algebra map is ind-Zariski: if `S` is
ind-Zariski over `R` and `R` is an `S`-algebra compatibly with its own identity, then `R` is
ind-Zariski over `S`. -/
theorem isIndZariski_of_retraction (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] [Algebra S R] [IsScalarTower R S R]
    (h : Algebra.IsIndZariski R S) : Algebra.IsIndZariski S R := by
  classical
  obtain ⟨J, _, _, p, hp⟩ := h
  let r : S →ₐ[R] R := IsScalarTower.toAlgHom R S R
  let f (i : J) : p.diag.obj i →ₐ[R] S :=
    ULift.algEquiv.toAlgHom.comp (p.ι.app i).hom
  let (i : J) : Algebra (p.diag.obj i) S := (f i).toRingHom.toAlgebra
  let (i : J) : Algebra (p.diag.obj i) R := (r.comp (f i)).toRingHom.toAlgebra
  have (i : J) : IsScalarTower R (p.diag.obj i) S :=
    IsScalarTower.of_algebraMap_eq fun x => (f i).commutes x |>.symm
  have (i : J) : IsScalarTower R (p.diag.obj i) R :=
    IsScalarTower.of_algebraMap_eq fun x => (r.comp (f i)).commutes x |>.symm
  have (i : J) : IsScalarTower (p.diag.obj i) S R :=
    IsScalarTower.of_algebraMap_eq' rfl
  let D (i : J) : CommAlgCat.{max u v} S := CommAlgCat.of S (S ⊗[p.diag.obj i] R)
  have hs (i : J) : Function.Surjective (algebraMap S (D i)) :=
    Algebra.TensorProduct.includeLeft_surjective S S fun x =>
      ⟨algebraMap R (p.diag.obj i) x, (r.comp (f i)).commutes x⟩
  have hn {i j : J} (a : i ⟶ j) (x : p.diag.obj i) :
      f j (p.diag.map a x) = f i x :=
    congrArg ULift.down (ConcreteCategory.congr_hom (p.ι.naturality a) x)
  let m {i j : J} (a : i ⟶ j) : D i ⟶ D j := CommAlgCat.ofHom
    { toRingHom := Algebra.TensorProduct.mapRingHom (p.diag.map a).hom.toRingHom
        (RingHom.id S) (RingHom.id R)
        (by ext x; exact (hn a x).symm)
        (by ext x; exact congrArg r (hn a x).symm)
      commutes' x := by simp [Algebra.TensorProduct.algebraMap_apply] }
  let d : J ⥤ CommAlgCat.{max u v} S :=
    { obj := D
      map := m
      map_id i := commAlgCat_hom_ext_of_surjective (hs i) _ _
      map_comp a b := commAlgCat_hom_ext_of_surjective (hs _) _ _ }
  let e (i : J) : D i ⟶ CommAlgCat.of S (ULift.{v} R) := CommAlgCat.ofHom
    (ULift.algEquiv.symm.toAlgHom.comp
      (Algebra.TensorProduct.lift (Algebra.ofId S R) (AlgHom.id (p.diag.obj i) R)
        (fun _ _ => .all _ _)))
  let c : Cocone d :=
    { pt := CommAlgCat.of S (ULift.{v} R)
      ι.app := e
      ι.naturality i j a := commAlgCat_hom_ext_of_surjective (hs i) _ _ }
  have hbalance (i : J) (x : p.diag.obj i) :
      algebraMap S (D i) (f i x) =
        algebraMap S (D i) (algebraMap R S (r (f i x))) := by
    have hh (y : p.diag.obj i) :
        algebraMap S (D i) (f i y) =
          Algebra.TensorProduct.includeRight (R := p.diag.obj i) (A := S) (r (f i y)) :=
      (Algebra.TensorProduct.includeLeft.commutes y).trans
        (Algebra.TensorProduct.includeRight.commutes y).symm
    rw [hh]
    convert (hh (algebraMap R (p.diag.obj i) (r (f i x)))).symm using 1 <;>
      simp only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  have hc : IsColimit c := by
    let q (s : Cocone d) : c.pt ⟶ s.pt := by
      let : Algebra R s.pt := ((algebraMap S s.pt).comp (algebraMap R S)).toAlgebra
      let : IsScalarTower R S s.pt := IsScalarTower.of_algebraMap_eq' rfl
      have hh :
          CommAlgCat.ofHom ((IsScalarTower.toAlgHom R S s.pt).comp
            (ULift.algEquiv (R := R)).toAlgHom) =
          CommAlgCat.ofHom ((Algebra.ofId R s.pt).comp
            (r.comp (ULift.algEquiv (R := R)).toAlgHom)) := by
        apply p.isColimit.hom_ext
        intro i; apply CommAlgCat.hom_ext; ext x
        show algebraMap S s.pt (f i x) = algebraMap R s.pt (r (f i x))
        calc
          _ = (s.ι.app i).hom (algebraMap S (D i) (f i x)) :=
            ((s.ι.app i).hom.commutes _).symm
          _ = (s.ι.app i).hom
              (algebraMap S (D i) (algebraMap R S (r (f i x)))) :=
            congrArg (s.ι.app i).hom (hbalance i x)
          _ = _ := (s.ι.app i).hom.commutes _
      exact CommAlgCat.ofHom
        { toRingHom := (algebraMap R s.pt).comp ULift.ringEquiv.toRingHom
          commutes' x := (ConcreteCategory.congr_hom hh (ULift.up x)).symm }
    refine ⟨q, ?_, ?_⟩
    · exact fun s i => commAlgCat_hom_ext_of_surjective (hs i) _ _
    · intro s g hg
      apply commAlgCat_hom_ext_of_surjective
      rintro ⟨x⟩
      exact ⟨algebraMap R S x, ULift.ext _ _ (r.commutes x)⟩
  refine ⟨J, inferInstance, inferInstance, ⟨d, c.ι, hc⟩, ?_⟩
  intro i
  let : Algebra.IsLocalIso R (p.diag.obj i) := hp i
  let : Algebra.IsLocalIso (p.diag.obj i) R :=
    isLocalIso_of_left_of_comp R (p.diag.obj i) R
  exact Algebra.IsLocalIso.instTensorProduct S

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **Stacks 096R.** Ind-Zariski maps cancel on the left in an algebra tower: if `B` and `C` are
ind-Zariski over `A`, then `C` is ind-Zariski over `B`. -/
@[stacks 096R]
theorem isIndZariski_of_left_of_comp (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hAB : Algebra.IsIndZariski A B) (hAC : Algebra.IsIndZariski A C) :
    Algebra.IsIndZariski B C := by
  let r : (C ⊗[A] B) →ₐ[C] C :=
    Algebra.TensorProduct.lift (AlgHom.id C C) (IsScalarTower.toAlgHom A B C)
      (fun _ _ => .all _ _)
  let : Algebra (C ⊗[A] B) C := r.toRingHom.toAlgebra
  have : IsScalarTower C (C ⊗[A] B) C :=
    IsScalarTower.of_algebraMap_eq fun x => (r.commutes x).symm
  have := IsScalarTower.of_algebraMap_eq (R := B) (S := C ⊗[A] B) (A := C)
    (by intro x; simp [r, RingHom.algebraMap_toAlgebra])
  exact Algebra.IsIndZariski.comp B (C ⊗[A] B) C
    (Algebra.IsIndZariski.tensorProduct A C B hAC)
    (isIndZariski_of_retraction C (C ⊗[A] B) (Algebra.IsIndZariski.tensorProduct' A B C hAB))

end AlgebraicGeometry.ProEtale

end
