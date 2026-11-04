module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraEpiDegree

/-!
# Surjectivity of a graded comparison in a sum of degrees

`Stacks.SheafOfModules.epi_unitalHom_app_add` concludes that a unital homomorphism of sheaves of
graded algebras is an epimorphism in the degree `i + j` from its being an **isomorphism** in the
degrees `i` and `j`.  That is more than the argument needs: surjectivity in the two input degrees
already suffices, because what the proof asks of the left vertical arrow of the square

```
  A_i ⊗ A_j ⟶ A_{i + j}
      |            |
  B_i ⊗ B_j ⟶ B_{i + j}
```

is only that it be locally surjective, and the objectwise tensor product of two locally
surjective morphisms of presheaves of modules is locally surjective.

That last statement is the content of this file.  It is proved without ever naming the tensor
product of two morphisms: `Stacks.SheafOfModules.isLocallySurjective_of_tmul_eq` says directly
that a morphism out of an objectwise tensor product which on pure tensors is a second such
morphism precomposed with two locally surjective morphisms is itself locally surjective.  A local
section of the target is, on a covering sieve, the image of some element of the tensor product of
the sections of the two factors; that element is a finite sum of pure tensors, and each factor of
each pure tensor is itself locally in the image, so one further refinement — the intersection of
finitely many covering sieves — exhibits the section as an image.

## Main results

* `Stacks.SheafOfModules.isLocallySurjective_of_tmul_eq`: **the objectwise tensor product of two
  locally surjective morphisms of presheaves of modules is locally surjective**, in the
  composition-free form described above.
* `Stacks.SheafOfModules.epi_unitalHom_app_add_of_epi`: **a unital homomorphism of sheaves of
  graded algebras which is an epimorphism in the degrees `i` and `j` is an epimorphism in the
  degree `i + j`**, provided multiplication of the target in those degrees is locally surjective.
  This is `Stacks.SheafOfModules.epi_unitalHom_app_add` with `IsIso` weakened to `Epi` in the two
  hypotheses.
* `Stacks.SheafOfModules.imageSieve_zero_mem` and `Stacks.SheafOfModules.imageSieve_add_mem`: the
  image sieve of a morphism of presheaves of modules at `0`, and at a sum of two sections whose
  image sieves are covering, is covering.

## Implementation notes

The induction over the tensor product is phrased as a statement about the image sieve of a
section *of the form* `m'(t')`, rather than about a fixed section with a lift.  This is what lets
the additive case appeal to the inductive hypothesis, whose section changes with the summand.

No sieve is constructed by hand: every covering sieve below is either an image sieve, an
intersection of two of them, or the top sieve, and the passage to the sieve being bounded is
`CategoryTheory.GrothendieckTopology.superset_covering`.

## References

* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

open scoped TensorProduct

universe v u w

namespace Stacks.SheafOfModules

/-! ### Image sieves of a morphism of presheaves of modules -/

section ImageSieve

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {F G : Cᵒᵖ ⥤ AddCommGrpCat.{w}}

/-- **The image sieve of a morphism of presheaves of abelian groups at the zero section is
covering**, being the top sieve: the zero section lifts over every arrow. -/
theorem imageSieve_zero_mem (ψ : F ⟶ G) (U : C) :
    Presheaf.imageSieve ψ (0 : ToType (G.obj (op U))) ∈ J U :=
  J.superset_covering (fun W f _ => ⟨0, by rw [map_zero, map_zero]⟩) (J.top_mem U)

/-- **The image sieve of a morphism of presheaves of abelian groups at a sum of two sections with
covering image sieves is covering**: over an arrow of the intersection of the two sieves the sum
of the two lifts is a lift of the sum. -/
theorem imageSieve_add_mem (ψ : F ⟶ G) {U : C} {x y : ToType (G.obj (op U))}
    (hx : Presheaf.imageSieve ψ x ∈ J U) (hy : Presheaf.imageSieve ψ y ∈ J U) :
    Presheaf.imageSieve ψ (x + y) ∈ J U := by
  refine J.superset_covering (fun W f hf => ?_) (J.intersection_covering hx hy)
  obtain ⟨p, hp⟩ := hf.1
  obtain ⟨q, hq⟩ := hf.2
  exact ⟨p + q, by rw [map_add, map_add, hp, hq]⟩

end ImageSieve

/-! ### Local surjectivity of a morphism out of an objectwise tensor product -/

section Tensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {F G F' G' P : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})}

/-- The image sieve of `m` at the image under `m'` of an element of the objectwise tensor product
of the sections of `F'` and `G'` is covering.  This is the induction over that tensor product
which `Stacks.SheafOfModules.isLocallySurjective_of_tmul_eq` runs. -/
private theorem imageSieve_mem_of_tensor (u : F ⟶ F') (v : G ⟶ G')
    (m : PresheafOfModules.tensorObj F G ⟶ P) (m' : PresheafOfModules.tensorObj F' G' ⟶ P)
    (hm : ∀ (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X),
      PresheafOfModules.Hom.app m X (x ⊗ₜ[O.obj X] y) =
        PresheafOfModules.Hom.app m' X (PresheafOfModules.Hom.app u X x ⊗ₜ[O.obj X]
          PresheafOfModules.Hom.app v X y))
    (hu : PresheafOfModules.IsLocallySurjective J u)
    (hv : PresheafOfModules.IsLocallySurjective J v) {U : C}
    (t : (PresheafOfModules.tensorObj F' G').obj (op U)) :
    ∀ s : P.obj (op U), PresheafOfModules.Hom.app m' (op U) t = s →
      Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map m) s ∈ J U := by
  induction t using TensorProduct.induction_on with
  | zero =>
    intro s hs
    have h0 : (0 : P.obj (op U)) = s := (map_zero _).symm.trans hs
    exact h0 ▸ imageSieve_zero_mem ((PresheafOfModules.toPresheaf _).map m) U
  | tmul x y =>
    intro s hs
    refine J.superset_covering (fun W f hf => ?_) (J.intersection_covering
      (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map u) x)
      (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map v) y))
    obtain ⟨p, hp⟩ := Stacks.imageSieve_apply u x f hf.1
    obtain ⟨q, hq⟩ := Stacks.imageSieve_apply v y f hf.2
    have hp' : PresheafOfModules.Hom.app u (op W) p = F'.restrictₛₗ f.op x := hp
    have hq' : PresheafOfModules.Hom.app v (op W) q = G'.restrictₛₗ f.op y := hq
    have htm : (PresheafOfModules.tensorObj F' G').restrictₛₗ f.op (x ⊗ₜ[O.obj (op U)] y) =
        F'.restrictₛₗ f.op x ⊗ₜ[O.obj (op W)] G'.restrictₛₗ f.op y :=
      PresheafOfModules.tensorObj_restrictₛₗ_tmul f.op x y
    refine ⟨p ⊗ₜ[O.obj (op W)] q, ?_⟩
    show PresheafOfModules.Hom.app m (op W) (p ⊗ₜ[O.obj (op W)] q) = P.map f.op s
    rw [hm, hp', hq', ← htm, ← hs]
    exact PresheafOfModules.naturality_apply m' f.op (x ⊗ₜ[O.obj (op U)] y)
  | add a b ha hb =>
    intro s hs
    have hsum : PresheafOfModules.Hom.app m' (op U) a + PresheafOfModules.Hom.app m' (op U) b =
        s := (map_add _ _ _).symm.trans hs
    exact hsum ▸ imageSieve_add_mem ((PresheafOfModules.toPresheaf _).map m) (ha _ rfl) (hb _ rfl)

/-- **A morphism out of an objectwise tensor product which on pure tensors is a locally
surjective morphism precomposed with two locally surjective morphisms is locally surjective.**
Taking `m'` to be the identity of the target this is the statement that the objectwise tensor
product of two locally surjective morphisms of presheaves of modules is locally surjective; the
form below is the one the graded argument uses, and it avoids naming the tensor product of two
morphisms.

A local section of `P` is, on the image sieve of `m'`, the image of an element of the objectwise
tensor product of the sections of `F'` and `G'`; that element is a finite sum of pure tensors,
and the two factors of each pure tensor are locally in the images of `u` and of `v`. -/
theorem isLocallySurjective_of_tmul_eq (u : F ⟶ F') (v : G ⟶ G')
    (m : PresheafOfModules.tensorObj F G ⟶ P) (m' : PresheafOfModules.tensorObj F' G' ⟶ P)
    (hm : ∀ (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X),
      PresheafOfModules.Hom.app m X (x ⊗ₜ[O.obj X] y) =
        PresheafOfModules.Hom.app m' X (PresheafOfModules.Hom.app u X x ⊗ₜ[O.obj X]
          PresheafOfModules.Hom.app v X y))
    (hu : PresheafOfModules.IsLocallySurjective J u)
    (hv : PresheafOfModules.IsLocallySurjective J v)
    (hm' : PresheafOfModules.IsLocallySurjective J m') :
    PresheafOfModules.IsLocallySurjective J m := by
  refine ⟨fun {U} s => ?_⟩
  refine J.transitive (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map m') s) _
    (fun {W} {f} hf => ?_)
  obtain ⟨t, ht⟩ := Stacks.imageSieve_apply m' s f hf
  rw [Presheaf.pullback_imageSieve]
  exact imageSieve_mem_of_tensor u v m m' hm hu hv t _ ht

end Tensor

/-! ### Surjectivity of a graded comparison in a sum of degrees -/

section Graded

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O)}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {A B : _root_.SheafOfModules.GradedAlgebra.{w, w} (TensorSheafification.structureSheaf O hO)}

/-- **A unital homomorphism of sheaves of graded algebras which is an epimorphism in the degrees
`i` and `j` is an epimorphism in the degree `i + j`**, as soon as multiplication of the target in
those two degrees is locally surjective.

This is `Stacks.SheafOfModules.epi_unitalHom_app_add` with the two isomorphy hypotheses weakened
to surjectivity.  A local section of the target in degree `i + j` is locally a sum of products of
homogeneous sections of degrees `i` and `j`, and each factor of such a product is locally in the
image of the comparison — which is all the argument asks of the comparison in the two input
degrees. -/
theorem epi_unitalHom_app_add_of_epi
    (φ : _root_.SheafOfModules.GradedAlgebra.UnitalHom A B) (i j : ℤ)
    (hi : Epi (φ.app i)) (hj : Epi (φ.app j))
    (mB : PresheafOfModules.tensorObj (B.piece i).val (B.piece j).val ⟶ (B.piece (i + j)).val)
    (hmB : ∀ (X : Cᵒᵖ) (x : (B.piece i).val.obj X) (y : (B.piece j).val.obj X),
      PresheafOfModules.Hom.app mB X (x ⊗ₜ[O.obj X] y) = (B.mul i j).app X x y)
    (hmls : PresheafOfModules.IsLocallySurjective J mB) :
    Epi (φ.app (i + j)) := by
  have loc : ∀ k, Epi (φ.app k) → PresheafOfModules.IsLocallySurjective J (φ.app k).val :=
    fun k _ => EpiMono.isLocallySurjective_of_epi (φ.app k)
  refine epi_of_isLocallySurjective_fac (φ.app (i + j))
    (g := PresheafOfModules.ofBilinear (A.mul i j)) rfl ?_
  refine isLocallySurjective_of_tmul_eq (φ.app i).val (φ.app j).val
    (PresheafOfModules.ofBilinear (A.mul i j) ≫ (φ.app (i + j)).val) mB (fun X x y => ?_) (loc i hi)
    (loc j hj) hmls
  exact ((congrArg ((φ.app (i + j)).val.app X)
    (PresheafOfModules.ofBilinear_tmul (A.mul i j) X x y)).trans
      (φ.map_mul i j X x y)).trans (hmB X _ _).symm

end Graded

end Stacks.SheafOfModules

end
