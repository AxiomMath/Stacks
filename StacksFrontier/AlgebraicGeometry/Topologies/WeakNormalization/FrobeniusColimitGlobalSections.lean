module

public import StacksFrontier.AlgebraicGeometry.Topologies.WeakNormalization.FrobeniusLimitHSheaf

/-!
# The Frobenius colimit of global functions, and the two-generator almost blowup square

For a presheaf of commutative rings `G` the presheaf of sets `colim_F G` is the colimit of the
Frobenius tower `G →^F G →^F G → ⋯` along `F : a ↦ a ^ p`.  This file builds that presheaf in
the generality in which `CategoryTheory.Presheaf.frobeniusLimit` is built, records the
element-level calculus of its sections, and proves the one algebraic input the Frobenius colimit
shares with the Frobenius limit: **a surjection whose kernel is uniformly nilpotent induces a
bijection of Frobenius colimits.**

The payload is the last result: for the almost blowup square of More on Flatness, Example 0EVH,

```
E ⟶ X' = Proj (A[T₀,T₁]/(f₂T₀ - f₁T₁))
↓         ↓
Z ⟶ X  = Spec A
```

the square of `colim_F Γ(-, 𝒪)` is cartesian.  This is the identification

`colim_F H⁰(X, 𝒪_X) = colim_F H⁰(Z, 𝒪_Z) ×_{colim_F H⁰(E, 𝒪_E)} colim_F H⁰(X', 𝒪_{X'})`

that the proof of Stacks 0EXD uses for the full faithfulness of its comparison functor, and
which the source gets from Stacks 0EVK.

## Main definitions

* `CategoryTheory.Presheaf.frobeniusColimit`: the presheaf `colim_F G` attached to a presheaf of
  commutative rings `G`.
* `CategoryTheory.Presheaf.frobeniusColimitStage`: the class in `colim_F G` of a section of `G`
  at a stage of the tower.
* `AlgebraicGeometry.frobeniusColimitGlobalSections`: the presheaf `colim_F Γ(-, 𝒪)` on the
  category of all schemes.

## Main results

* `CategoryTheory.Presheaf.exists_frobeniusColimitStage_eq`,
  `…frobeniusColimitStage_succ`, `…frobeniusColimitStage_add`,
  `…exists_pow_eq_of_frobeniusColimitStage_eq`, `…frobeniusColimit_map_stage`: the element-level
  calculus — every section is represented at some stage, moving a representative up a stage
  raises it to the `p`-th power, two representatives at the same stage agree in the colimit
  exactly when some `p`-power of them agrees, and restriction acts on representatives.
* `CategoryTheory.Presheaf.bijective_frobeniusColimit_map_of_surjective_of_pow_eq_zero`: **the
  Frobenius colimit of a uniformly nilpotent thickening is a bijection.**
* `AlgebraicGeometry.bijective_frobeniusColimit_of_surjective_of_ker_sq_eq_bot`: the same for a
  morphism of schemes whose restriction of global functions is surjective with kernel of square
  zero.
* `AlgebraicGeometry.isPullback_frobeniusColimit_twoGeneratorModel`: **the square of
  `colim_F Γ(-, 𝒪)` attached to the model square of Example 0EVH is cartesian.**

## Implementation notes

`AlgebraicGeometry.BigHOver.frobeniusColimitSections`, the presheaf `colim_F Γ(-, 𝒪)` on the big
h category over a scheme, is this file's `CategoryTheory.Presheaf.frobeniusColimit` applied to
`AlgebraicGeometry.BigHOver.sectionsRingPresheaf` — on the nose, which is
`AlgebraicGeometry.BigHOver.frobeniusColimitSections_eq`.  Nothing is duplicated: the generic
construction is the one the site version already is, and the element-level lemmas of
`StacksFrontier.AlgebraicGeometry.Topologies.WeakNormalization.FrobeniusColimitHSheaf`
(`AlgebraicGeometry.BigHOver.colimitStage` and its three companions) are that site instance of
the ones proved here.

The statements of this file are deliberately **site-free**.  Every result about the big h site is
quantified over an arbitrary `AlgebraicGeometry.BigHSite`, of which this development constructs
no term, so a statement indexed by a big h site cannot be instantiated at a concrete scheme.
Stacks 0EXD needs the cartesian square above for the concrete square of Example 0EVH over a
concrete ring `A`, so it is proved here directly, exactly as its Frobenius-limit counterpart
`AlgebraicGeometry.isPullback_frobeniusLimit_twoGeneratorModel` is.

The three formal steps — transport along isomorphisms of the three schemes, cartesianness from a
bijective and an injective leg, and injectivity from a section — use nothing about the Frobenius,
and are `AlgebraicGeometry.isPullback_map_op_of_modelPair`,
`AlgebraicGeometry.isPullback_map_op_of_bijective_of_injective` and
`AlgebraicGeometry.injective_map_op_of_isPullback_of_section`, stated for an arbitrary presheaf
of sets on schemes.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 0EVJ](https://stacks.math.columbia.edu/tag/0EVJ)
* [Stacks Project, Tag 0EVK](https://stacks.math.columbia.edu/tag/0EVK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Presheaf

variable {C : Type*} [Category* C] (G : Cᵒᵖ ⥤ CommRingCat.{u}) (p : ℕ)

/-! ### The Frobenius colimit of a presheaf of commutative rings -/

/-- The Frobenius tower `Γ(-) →^F Γ(-) →^F ⋯` of a presheaf of commutative rings, as a sequence
of presheaves of sets. -/
public def frobeniusTower : ℕ ⥤ (Cᵒᵖ ⥤ Type u) :=
  Functor.ofSequence (X := fun _ ↦ G ⋙ CategoryTheory.forget CommRingCat.{u})
    (fun _ ↦ frobeniusForget G p)

/-- Every transition map of the Frobenius tower is the Frobenius. -/
public theorem frobeniusTower_map_succ (n : ℕ) :
    (frobeniusTower G p).map (homOfLE n.le_succ) = frobeniusForget G p :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-- The presheaf `colim_F G` of sets: the colimit of the Frobenius tower of `G`. -/
public def frobeniusColimit : Cᵒᵖ ⥤ Type u := colimit (frobeniusTower G p)

/-- The class in `colim_F G` of a section of `G` at the stage `n` of the Frobenius tower. -/
public def frobeniusColimitStage (n : ℕ) (X : Cᵒᵖ) (a : ToType (G.obj X)) :
    (frobeniusColimit G p).obj X :=
  (colimit.ι (frobeniusTower G p) n).app X a

/-- Moving a representative one stage up raises it to the `p`-th power. -/
public theorem frobeniusColimitStage_succ (n : ℕ) (X : Cᵒᵖ) (a : ToType (G.obj X)) :
    frobeniusColimitStage G p n X a = frobeniusColimitStage G p (n + 1) X (a ^ p) := by
  have h := colimit.w (frobeniusTower G p) (homOfLE (Nat.le_add_right n 1))
  rw [frobeniusTower_map_succ] at h
  exact (ConcreteCategory.congr_hom (congr_app h X) a).symm

/-- Moving a representative `k` stages up raises it to the `pᵏ`-th power. -/
public theorem frobeniusColimitStage_add (n k : ℕ) (X : Cᵒᵖ) (a : ToType (G.obj X)) :
    frobeniusColimitStage G p n X a = frobeniusColimitStage G p (n + k) X (a ^ p ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_one]; rfl
  | succ k ih =>
    rw [ih, frobeniusColimitStage_succ, ← pow_mul, ← pow_succ]
    rfl

/-- Climbing `k` stages of the Frobenius tower raises a section to its `pᵏ`-th power. -/
public theorem frobeniusTower_map_add (n k : ℕ) (X : Cᵒᵖ) (a : ToType (G.obj X)) :
    ((frobeniusTower G p).map (homOfLE (Nat.le_add_right n k))).app X a = a ^ p ^ k := by
  induction k with
  | zero =>
    rw [Subsingleton.elim (homOfLE (Nat.le_add_right n 0)) (𝟙 n), Functor.map_id, pow_zero, pow_one]
    rfl
  | succ k ih =>
    rw [Subsingleton.elim (homOfLE (Nat.le_add_right n (k + 1)))
      (homOfLE (Nat.le_add_right n k) ≫ homOfLE (Nat.le_succ (n + k))), Functor.map_comp]
    change ((frobeniusTower G p).map (homOfLE (Nat.le_succ (n + k)))).app X
        (((frobeniusTower G p).map (homOfLE (Nat.le_add_right n k))).app X a) = _
    rw [ih, frobeniusTower_map_succ, pow_succ, pow_mul]
    rfl

/-- The Frobenius tower of `G` evaluated at an object: the sequence `Γ(X) →^F Γ(X) →^F ⋯`. -/
public abbrev frobeniusTowerAt (X : Cᵒᵖ) : ℕ ⥤ Type u :=
  frobeniusTower G p ⋙ (evaluation Cᵒᵖ (Type u)).obj X

/-- The sections of `colim_F G` over an object are the colimit of the Frobenius tower of its
sections: colimits of presheaves are computed objectwise. -/
public def frobeniusColimitObjIso (X : Cᵒᵖ) :
    (frobeniusColimit G p).obj X ≅ colimit (frobeniusTowerAt G p X) :=
  colimitObjIsoColimitCompEvaluation _ _

/-- The inverse of `frobeniusColimitObjIso` sends the class at stage `n` to the stage-`n` class. -/
private theorem frobeniusColimitObjIso_inv_ι (n : ℕ) (X : Cᵒᵖ) (a : ToType (G.obj X)) :
    (frobeniusColimitObjIso G p X).inv (colimit.ι (frobeniusTowerAt G p X) n a) =
      frobeniusColimitStage G p n X a :=
  ConcreteCategory.congr_hom
    (colimitObjIsoColimitCompEvaluation_ι_inv (frobeniusTower G p) n X) a

/-- Every section of `colim_F G` over an object is represented at some stage. -/
public theorem exists_frobeniusColimitStage_eq (X : Cᵒᵖ) (x : (frobeniusColimit G p).obj X) :
    ∃ (n : ℕ) (a : ToType (G.obj X)), frobeniusColimitStage G p n X a = x := by
  obtain ⟨n, a, ha⟩ := Types.jointly_surjective' ((frobeniusColimitObjIso G p X).hom x)
  exact ⟨n, a, (frobeniusColimitObjIso_inv_ι G p n X a).symm.trans
    ((congrArg (frobeniusColimitObjIso G p X).inv ha).trans
      ((frobeniusColimitObjIso G p X).hom_inv_id_apply x))⟩

/-- Restriction of a section of `colim_F G` restricts a representative. -/
public theorem frobeniusColimit_map_stage {X Y : Cᵒᵖ} (f : X ⟶ Y) (n : ℕ)
    (a : ToType (G.obj X)) :
    (frobeniusColimit G p).map f (frobeniusColimitStage G p n X a) =
      frobeniusColimitStage G p n Y ((G.map f).hom a) :=
  (ConcreteCategory.congr_hom ((colimit.ι (frobeniusTower G p) n).naturality f) a).symm

/-- **Two representatives at the same stage agree in `colim_F G` exactly when a `p`-power of them
agrees.** The Frobenius tower is indexed by `ℕ`, which is filtered, so an identity in the colimit
is witnessed at a single later stage. -/
public theorem exists_pow_eq_of_frobeniusColimitStage_eq {n : ℕ} {X : Cᵒᵖ}
    {a b : ToType (G.obj X)}
    (h : frobeniusColimitStage G p n X a = frobeniusColimitStage G p n X b) :
    ∃ k : ℕ, a ^ p ^ k = b ^ p ^ k := by
  have hι : colimit.ι (frobeniusTowerAt G p X) n a = colimit.ι (frobeniusTowerAt G p X) n b :=
    (frobeniusColimitObjIso G p X).toEquiv.symm.injective
      ((frobeniusColimitObjIso_inv_ι G p n X a).trans
        (h.trans (frobeniusColimitObjIso_inv_ι G p n X b).symm))
  obtain ⟨j, g, hg⟩ := Types.FilteredColimit.isColimit_eq_iff'
    (colimit.isColimit (frobeniusTowerAt G p X)) a b |>.1 hι
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = n + k := ⟨j - n, by have := leOfHom g; omega⟩
  obtain rfl : g = homOfLE (Nat.le_add_right n k) := Subsingleton.elim _ _
  exact ⟨k, (frobeniusTower_map_add G p n k X a).symm.trans
    (hg.trans (frobeniusTower_map_add G p n k X b))⟩

/-- **A uniformly nilpotent thickening does not change the Frobenius colimit.** If restriction
along `f` is surjective on sections of `G`, the prime `p` vanishes upstairs and some fixed power
of every element of the kernel vanishes, then `f` induces a bijection of Frobenius colimits.

Surjectivity is immediate from a representative; injectivity is the Frobenius identity: the
difference of two representatives with the same image is killed by raising to a high enough
`p`-power, and that is the same as moving the representatives up the tower. -/
public theorem bijective_frobeniusColimit_map_of_surjective_of_pow_eq_zero (hp : p.Prime)
    {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (hsurj : Function.Surjective (G.map f).hom)
    (hcast : (p : ToType (G.obj X)) = 0)
    (hker : ∃ m : ℕ, ∀ x : ToType (G.obj X), (G.map f).hom x = 0 → x ^ m = 0) :
    Function.Bijective ((frobeniusColimit G p).map f) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := hker
  have hmN : m ≤ p ^ m := (Nat.lt_pow_self hp.one_lt).le
  have key : ∀ (t : ℕ) (u v : ToType (G.obj X)),
      frobeniusColimitStage G p t Y ((G.map f).hom u) =
        frobeniusColimitStage G p t Y ((G.map f).hom v) →
      frobeniusColimitStage G p t X u = frobeniusColimitStage G p t X v := by
    intro t u v h
    obtain ⟨j, hj⟩ := exists_pow_eq_of_frobeniusColimitStage_eq G p h
    have hker0 : (G.map f).hom (u ^ p ^ j - v ^ p ^ j) = 0 := by
      rw [map_sub, map_pow, map_pow, hj, sub_self]
    have hnil : (u ^ p ^ j - v ^ p ^ j) ^ (p ^ m) = 0 :=
      pow_eq_zero_of_le hmN (hm _ hker0)
    rw [AlgebraicGeometry.sub_pow_prime_pow_of_natCast_eq_zero p hcast, sub_eq_zero, ← pow_mul,
      ← pow_mul, ← pow_add] at hnil
    rw [frobeniusColimitStage_add G p t (j + m) X u, frobeniusColimitStage_add G p t (j + m) X v,
      hnil]
  refine ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨n, a, rfl⟩ := exists_frobeniusColimitStage_eq G p X x
    obtain ⟨n', b, rfl⟩ := exists_frobeniusColimitStage_eq G p X y
    rw [frobeniusColimitStage_add G p n n' X a, frobeniusColimitStage_add G p n' n X b,
      Nat.add_comm n' n]
    refine key (n + n') _ _ ?_
    rw [← frobeniusColimit_map_stage, ← frobeniusColimit_map_stage,
      ← frobeniusColimitStage_add G p n n' X a, Nat.add_comm n n',
      ← frobeniusColimitStage_add G p n' n X b]
    exact hxy
  · intro y
    obtain ⟨n, b, rfl⟩ := exists_frobeniusColimitStage_eq G p Y y
    obtain ⟨a, ha⟩ := hsurj b
    exact ⟨frobeniusColimitStage G p n X a, by rw [frobeniusColimit_map_stage, ha]⟩

end CategoryTheory.Presheaf

namespace AlgebraicGeometry

/-- The presheaf `colim_F Γ(-, 𝒪)` on the big h category over `S` is the Frobenius colimit of its
presheaf of rings of global functions. -/
public theorem BigHOver.frobeniusColimitSections_eq (B : BigHSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (p : ℕ) :
    BigHOver.frobeniusColimitSections B S hS p =
      CategoryTheory.Presheaf.frobeniusColimit (BigHOver.sectionsRingPresheaf B S hS) p :=
  rfl

/-- The presheaf `colim_F Γ(-, 𝒪)` on the category of all schemes. -/
public abbrev frobeniusColimitGlobalSections (p : ℕ) : Scheme.{u}ᵒᵖ ⥤ Type u :=
  CategoryTheory.Presheaf.frobeniusColimit Scheme.Γ.{u} p

/-- **A square-zero thickening does not change the Frobenius colimit of global functions.** If
restriction of global functions along `f : X ⟶ Y` is surjective with kernel of square zero and
the prime `p` vanishes on `Y`, then `f` induces a bijection of Frobenius colimits of global
functions.

This is the Frobenius-colimit counterpart of
`AlgebraicGeometry.bijective_frobeniusLimit_of_surjective_of_ker_sq_eq_bot`. -/
public theorem bijective_frobeniusColimit_of_surjective_of_ker_sq_eq_bot
    (p : ℕ) (hp : p.Prime) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hChar : (p : Γ(Y, ⊤)) = 0)
    (hsurj : Function.Surjective (Scheme.Γ.map f.op).hom)
    (hker : RingHom.ker (Scheme.Γ.map f.op).hom ^ 2 = ⊥) :
    Function.Bijective ((frobeniusColimitGlobalSections p).map f.op) := by
  refine CategoryTheory.Presheaf.bijective_frobeniusColimit_map_of_surjective_of_pow_eq_zero
    Scheme.Γ.{u} p hp f.op hsurj hChar ⟨2, fun x hx => ?_⟩
  simpa only [hker, Ideal.mem_bot] using Ideal.pow_mem_pow (RingHom.mem_ker.mpr hx) 2

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The Frobenius colimit square of the model square of Example 0EVH is cartesian.**

Restriction of global functions to the modification is surjective with square-zero kernel — the
two assertions of Stacks 0EVJ, `Stacks.AlmostBlowUp.surjective_Γ_modificationToBase` and
`Stacks.AlmostBlowUp.modificationToBase_ker_sq_eq_bot` — hence bijective on Frobenius colimits,
and restriction to the exceptional corner is injective on Frobenius colimits because that corner
is the projective line over the centre, which has a section.

This is the identification
`colim_F H⁰(X, 𝒪) = colim_F H⁰(Z, 𝒪) ×_{colim_F H⁰(E, 𝒪)} colim_F H⁰(X', 𝒪)`
used by the proof of Stacks 0EXD. -/
public theorem isPullback_frobeniusColimit_twoGeneratorModel (p : ℕ) (hp : p.Prime)
    (A : Type u) [CommRing A] (f₁ f₂ : A)
    (hcast : (p : Γ(Spec (.of A), ⊤)) = 0) (E : Scheme.{u}) :
    letI := (Stacks.AlmostBlowUp.twoGeneratorSquare A f₁ f₂).modificationGraded
    ∀ (dm : E ⟶ Proj (Stacks.AlmostBlowUp.modificationGrading A f₁ f₂))
      (em : E ⟶ Spec (.of (Stacks.AlmostBlowUp.centerRing A f₁ f₂))),
      IsPullback em dm (Stacks.AlmostBlowUp.centerToBase A f₁ f₂)
          (Stacks.AlmostBlowUp.modificationToBase A f₁ f₂) →
        IsPullback
          ((frobeniusColimitGlobalSections p).map
            (Stacks.AlmostBlowUp.centerToBase A f₁ f₂).op)
          ((frobeniusColimitGlobalSections p).map
            (Stacks.AlmostBlowUp.modificationToBase A f₁ f₂).op)
          ((frobeniusColimitGlobalSections p).map em.op)
          ((frobeniusColimitGlobalSections p).map dm.op) := by
  let := (Stacks.AlmostBlowUp.twoGeneratorSquare A f₁ f₂).modificationGraded
  intro dm em hm
  have hbij := bijective_frobeniusColimit_of_surjective_of_ker_sq_eq_bot p hp
    (Stacks.AlmostBlowUp.modificationToBase A f₁ f₂) hcast
    (Stacks.AlmostBlowUp.surjective_Γ_modificationToBase A f₁ f₂)
    (Stacks.AlmostBlowUp.modificationToBase_ker_sq_eq_bot A f₁ f₂)
  obtain ⟨s, hs⟩ := exists_section_exceptionalToCenter A f₁ f₂
  exact isPullback_map_op_of_bijective_of_injective (frobeniusColimitGlobalSections p)
    _ _ _ _ hm.w hbij
    (injective_map_op_of_isPullback_of_section (frobeniusColimitGlobalSections p) hm.flip
      (Stacks.AlmostBlowUp.twoGenerator_isPullback A f₁ f₂) s hs)

end AlgebraicGeometry

end
