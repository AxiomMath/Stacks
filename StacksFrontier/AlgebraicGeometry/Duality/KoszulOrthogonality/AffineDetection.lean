module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration
public import StacksFrontier.RingTheory.Koszul.PowerLift.KoszulTorsion
import all StacksFrontier.Homology.DerivedComplete.KoszulTensorVanishing
import all StacksFrontier.RingTheory.Koszul.PowerLift.KoszulTorsion

/-!
# Koszul detection of the zero object in the derived category of a ring

Let `A` be a commutative ring and `f₁, …, f_r ∈ A`. Write `K(f)` for the Koszul complex of the
sequence, re-indexed into non-positive cohomological degrees and viewed in `D(A)`. This file
proves the detection statement that drives [Stacks, Tag 09IR]:

> an object `N` of `D(A)` all of whose cohomology modules are `f_i`-power torsion for every `i`,
> and which receives no nonzero morphism from any shift of `K(f)`, is zero.

The proof is an induction on the length of the sequence which peels off the last entry. Writing
`f = (f', a)`, the Koszul complex of `f` is the cone of multiplication by `a` on the Koszul
complex of `f'` ([Stacks, Tag 0629]), so there is a distinguished triangle

`K(f') --a·𝟙--> K(f') ⟶ K(f) ⟶ K(f')⟦1⟧`.

Apply `Hom(−⟦n⟧, N)` to it. A morphism `t : K(f')⟦n⟧ ⟶ N` killed by `a` factors through
`K(f)⟦n⟧` and hence vanishes, so multiplication by `a` is *injective* on `Hom(K(f')⟦n⟧, N)`. On
the other hand every morphism from a shift of a Koszul complex into `N` is killed by a *power* of
`a`, because the cohomology of `N` is `a`-power torsion — that is the induction of
`StacksFrontier/RingTheory/Koszul/PowerLift/KoszulTorsion.lean`. The two together force
`Hom(K(f')⟦n⟧, N) = 0`, and the inductive hypothesis applies to the shorter sequence `f'`. The
base case is the empty sequence, where `K(∅) = A[0]`.

Every step of that induction stays at the shift `n` it starts from, so the statement it proves
is **degreewise**: no nonzero morphism `K(f)⟦-q⟧ ⟶ N` out of that one shift already forces
`H^q(N) = 0`, because `Hom(A[0]⟦-q⟧, N)` is `Hom_A(A, H^q(N))`. The published form above, with
its quantifier over all of `ℤ`, is that statement in every degree, and is deduced from it here
rather than proved separately. The degreewise form is what the truncated criteria of
[Stacks, Tag 0GEJ] and [Stacks, Tag 0GEK] need, since there only a half-line of shifts is
assumed orthogonal and only a half-line of cohomology is claimed to vanish.

## Main results

* `Stacks.Koszul.Truncation.derivedKoszul` — the Koszul complex of the sequence in `D(A)`.
* `Stacks.Koszul.Truncation.exists_derivedKoszul_snoc_triangle` — the distinguished triangle of
  [Stacks, Tag 0629] in `D(A)`.
* `Stacks.Koszul.Truncation.forall_hom_single_shift_eq_zero_of_forall_hom_derivedKoszul_eq_zero`
  — the induction on the length of the sequence, at a fixed shift.
* `Stacks.Koszul.Truncation.isZero_homology_of_forall_hom_derivedKoszul_eq_zero` — **the
  detection statement, degreewise.**
* `Stacks.Koszul.Truncation.isZero_of_forall_hom_derivedKoszul_eq_zero` — the detection
  statement, in every degree at once.

## Implementation notes

No `@[stacks]` attribute is attached. What is proved here is the algebraic half of the proof of
[Stacks, Tag 09IR]; the tag itself is a statement about the derived category of the affine scheme
`Spec A` and is proved in
`StacksFrontier/AlgebraicGeometry/Duality/KoszulOrthogonality/AffineSituation.lean`.

Nothing about the Koszul complex is rebuilt here. The power torsion of `Hom(K(f)⟦n⟧, N)` is the
induction of `StacksFrontier/RingTheory/Koszul/PowerLift/KoszulTorsion.lean`, whose base case over
the ring in a single degree is `StacksFrontier/RingTheory/Koszul/PowerLift/SingleTorsion.lean`; the
cone presentation of a Koszul complex and the vanishing of the Koszul complex of the empty
sequence away from degree zero are `private` declarations of that file and of
`StacksFrontier/Homology/DerivedComplete/KoszulTensorVanishing.lean`, reused through `import all`
rather than reproved. What is assembled here is the distinguished triangle those give in the
derived category, and the induction that turns the two hypotheses into the vanishing of `N`.

The triangle carries a free `[HasDerivedCategory.{w} (ModuleCat.{u} A)]` binder; the detection
statements do not, because they need `A[0]` to corepresent the cohomology of `D(A)`
(`Stacks.Duality.isZero_homology_of_forall_hom_single_shift_eq_zero`) and so are available only at
the locally small model of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` — which is
also the model at which the affine comparison of [Stacks, Tag 06Z0] is available, so the consumer
loses nothing. `CategoryTheory.HasDerivedCategory.standard` is mentioned nowhere.

## References

* [Stacks Project, Tag 09IR](https://stacks.math.columbia.edu/tag/09IR)
* [Stacks Project, Tag 0629](https://stacks.math.columbia.edu/tag/0629)
* [Stacks Project, Tag 08E3](https://stacks.math.columbia.edu/tag/08E3)
* [Stacks Project, Tag 0GEJ](https://stacks.math.columbia.edu/tag/0GEJ)
* [Stacks Project, Tag 0GEK](https://stacks.math.columbia.edu/tag/0GEK)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
attribute [local instance] ModuleCat.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated Stacks.Koszul.PowerLift

universe w u

namespace Stacks.Koszul.Truncation

variable {A : Type u} [CommRing A]

/-- The Koszul complex `K_•(f₁, …, f_r)` of a finite sequence in a commutative ring `A`, as an
object of `D(A)`: the chain complex `Koszul.seqComplex f` re-indexed as a cochain complex in
non-positive degrees and localized. -/
abbrev derivedKoszul [HasDerivedCategory.{w} (ModuleCat.{u} A)] {r : ℕ} (f : Fin r → A) :
    DerivedCategory (ModuleCat.{u} A) :=
  DerivedCategory.Q.obj ((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat)

section Triangle

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- **The Koszul complex of a sequence extended by one entry is the cone of multiplication by
that entry** ([Stacks, Tag 0629]), as a distinguished triangle of `D(A)`:

`K(f) --a·𝟙--> K(f) ⟶ K(f, a) ⟶ K(f)⟦1⟧`.

At the level of cochain complexes this is `Stacks.Koszul.PowerLift.exists_iso_koszulCochain_snoc`;
the mapping cone of a morphism of cochain complexes gives a distinguished triangle by
`CategoryTheory.DerivedCategory.mappingCone_triangle_distinguished`, and its first morphism is
`a·𝟙` because the localization functor is `A`-linear. -/
theorem exists_derivedKoszul_snoc_triangle {r : ℕ} (f : Fin r → A) (a : A) :
    ∃ (b : derivedKoszul f ⟶ derivedKoszul (Fin.snoc f a))
      (c : derivedKoszul (Fin.snoc f a) ⟶ (derivedKoszul f)⟦(1 : ℤ)⟧),
      Triangle.mk (a • 𝟙 (derivedKoszul f)) b c ∈ distTriang _ := by
  obtain ⟨e⟩ := exists_iso_koszulCochain_snoc f a
  let T := DerivedCategory.Q.mapTriangle.obj
    (CochainComplex.mappingCone.triangle (a • 𝟙 (koszulCochain (A := A) f)))
  let eQ := DerivedCategory.Q.mapIso e.symm
  let T' : Triangle (DerivedCategory (ModuleCat.{u} A)) :=
    Triangle.mk T.mor₁ (T.mor₂ ≫ eQ.hom) (eQ.inv ≫ T.mor₃)
  have eT : T ≅ T' := Triangle.isoMk T T' (Iso.refl _) (Iso.refl _) eQ
    (by simp [T']) (by simp [T'])
    (by
      simp only [T', Triangle.mk_mor₃, Iso.refl_hom, CategoryTheory.Functor.map_id,
        Category.comp_id]
      exact (Iso.hom_inv_id_assoc eQ T.mor₃).symm)
  have hT' : T' ∈ distTriang _ := Pretriangulated.isomorphic_distinguished T
    (DerivedCategory.mappingCone_triangle_distinguished (a • 𝟙 (koszulCochain (A := A) f)))
    T' eT.symm
  obtain ⟨b, c, hbc⟩ : ∃ b c, Triangle.mk T.mor₁ b c ∈ distTriang _ := ⟨_, _, hT'⟩
  have hmor : T.mor₁ = a • 𝟙 (derivedKoszul f) := by
    show DerivedCategory.Q.map (a • 𝟙 (koszulCochain (A := A) f)) = _
    rw [Functor.Linear.map_smul, DerivedCategory.Q.map_id]
    rfl
  rw [hmor] at hbc
  exact ⟨b, c, hbc⟩

/-- **Multiplication by the last entry is injective on morphisms out of the shorter Koszul
complex.** Let `f` be a finite sequence and `a` a further element. If no nonzero morphism goes
from `K(f, a)⟦n⟧` into `N`, then a morphism `K(f)⟦n⟧ ⟶ N` killed by `a` is zero: by the
distinguished triangle `K(f) --a·𝟙--> K(f) ⟶ K(f, a) ⟶ K(f)⟦1⟧` it factors through that same
shift of `K(f, a)`.

The hypothesis is needed at the single shift `n` appearing in the conclusion, which is what makes
the detection statements below degreewise rather than only available with the quantifier over all
of `ℤ`. -/
theorem eq_zero_of_smul_eq_zero_of_forall_hom_derivedKoszul_snoc_eq_zero {r : ℕ} (f : Fin r → A)
    (a : A) (N : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    (h : ∀ g : (derivedKoszul (Fin.snoc f a))⟦n⟧ ⟶ N, g = 0)
    (s : (derivedKoszul f)⟦n⟧ ⟶ N) (hs : a • s = 0) :
    s = 0 := by
  obtain ⟨u, v, hT⟩ := exists_derivedKoszul_snoc_triangle f a
  have hcomp : ((CategoryTheory.shiftFunctor
      (Pretriangulated.Triangle (DerivedCategory (ModuleCat.{u} A))) n).obj
        (Pretriangulated.Triangle.mk (a • 𝟙 (derivedKoszul f)) u v)).mor₁ ≫ s = 0 := by
    show (n.negOnePow • ((a • 𝟙 (derivedKoszul f))⟦n⟧')) ≫ s = 0
    rw [Linear.units_smul_comp, Functor.Linear.map_smul, CategoryTheory.Functor.map_id,
      Linear.smul_comp, Category.id_comp, hs, smul_zero]
  obtain ⟨g, hg⟩ := Pretriangulated.Triangle.yoneda_exact₂ _
    (Pretriangulated.Triangle.shift_distinguished _ hT n) s hcomp
  rw [hg, h g]
  exact comp_zero

end Triangle

/-- **Peeling the whole sequence at a fixed shift.** Let `N` be an object of `D(A)` all of whose
cohomology modules are `f_i`-power torsion for every `i`, and fix an integer `n`. If every
morphism `K(f₁, …, f_r)⟦n⟧ ⟶ N` vanishes, then so does every morphism `A[0]⟦n⟧ ⟶ N`.

This is the induction described in the module documentation, and the shift `n` is the same
throughout it: writing `f = (f', a)`, a morphism `K(f')⟦n⟧ ⟶ N` killed by `a` factors through
`K(f', a)⟦n⟧` and so vanishes
(`Stacks.Koszul.Truncation.eq_zero_of_smul_eq_zero_of_forall_hom_derivedKoszul_snoc_eq_zero`),
while every morphism `K(f')⟦n⟧ ⟶ N` is killed by some power of `a`
(`Stacks.Koszul.PowerLift.homPowerTorsion_koszul`); the two together kill it outright, and the
shorter sequence applies. The empty sequence gives `K(∅) = A[0]`.

That the induction never leaves the shift it starts in is what makes the detection statement
below available degree by degree, which is what the truncated criteria of [Stacks, Tag 0GEJ] and
[Stacks, Tag 0GEK] need. -/
theorem forall_hom_single_shift_eq_zero_of_forall_hom_derivedKoszul_eq_zero :
    ∀ {r : ℕ} (f : Fin r → A) (N : DerivedCategory (ModuleCat.{u} A)),
      (∀ (i : Fin r) (m : ℤ)
        (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) m).obj N),
        ∃ k : ℕ, f i ^ k • x = 0) →
      ∀ n : ℤ, (∀ g : (derivedKoszul f)⟦n⟧ ⟶ N, g = 0) →
        ∀ t : ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A A))⟦n⟧ ⟶ N, t = 0 := by
  intro r
  induction r with
  | zero =>
    intro f N _ n h t
    let eb := (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) n).mapIso
      (KoszulTensorVanishing.koszul_empty_iso_single f)
    rw [← cancel_epi eb.hom, comp_zero]
    exact h _
  | succ r ih =>
    intro f N htor n h
    obtain ⟨f, a, rfl⟩ : ∃ (f' : Fin r → A) (a : A), Fin.snoc f' a = f :=
      ⟨Fin.init f, f (Fin.last r), Fin.snoc_init_self f⟩
    have hlast : ∀ (m : ℤ) (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) m).obj N),
        ∃ k : ℕ, a ^ k • x = 0 := fun m x => by
      simpa only [Fin.snoc_last] using htor (Fin.last r) m x
    refine ih f N (fun i m x => ?_) n (fun t => ?_)
    · simpa only [Fin.snoc_castSucc] using htor i.castSucc m x
    · obtain ⟨k, hk⟩ := homPowerTorsion_koszulObj_shift a N r f n
        (fun j _ _ => homPowerTorsion_singleRing a j N (hlast j)) t
      induction k generalizing t with
      | zero => exact (one_smul A t).symm.trans (by rwa [pow_zero] at hk)
      | succ k ihk =>
        exact ihk t (eq_zero_of_smul_eq_zero_of_forall_hom_derivedKoszul_snoc_eq_zero f a N n h
          (a ^ k • t) (by rwa [smul_smul, ← pow_succ']))

/-- **Degreewise Koszul detection over a ring.** Let `A` be a commutative ring and
`f₁, …, f_r ∈ A`, let `N` be an object of `D(A)` whose cohomology modules are all `f_i`-power
torsion for every `i`, and let `q` be an integer. If every morphism `K(f₁, …, f_r)⟦-q⟧ ⟶ N`
vanishes, then `H^q(N) = 0`.

Peel the sequence at the shift `-q`
(`Stacks.Koszul.Truncation.forall_hom_single_shift_eq_zero_of_forall_hom_derivedKoszul_eq_zero`)
and read the resulting vanishing of `Hom(A[0]⟦-q⟧, N)` as the vanishing of `H^q(N)`, by
`Stacks.Duality.isZero_homology_of_forall_hom_single_shift_eq_zero` for the projective separator
`A` of `ModuleCat A`.

A single shift of `K` controls a single cohomology module. This is the form the truncated
criteria of [Stacks, Tag 0GEJ] and [Stacks, Tag 0GEK] use;
`Stacks.Koszul.Truncation.isZero_of_forall_hom_derivedKoszul_eq_zero` is the case of all shifts
at once. -/
theorem isZero_homology_of_forall_hom_derivedKoszul_eq_zero {r : ℕ} (f : Fin r → A)
    (N : DerivedCategory (ModuleCat.{u} A))
    (htor : ∀ (i : Fin r) (m : ℤ)
      (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) m).obj N),
      ∃ k : ℕ, f i ^ k • x = 0)
    (q : ℤ) (h : ∀ g : (derivedKoszul f)⟦-q⟧ ⟶ N, g = 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj N) :=
  Stacks.Duality.isZero_homology_of_forall_hom_single_shift_eq_zero (ModuleCat.of A A)
    (Stacks.Duality.isZero_of_forall_hom_unit_eq_zero A) N q
    (forall_hom_single_shift_eq_zero_of_forall_hom_derivedKoszul_eq_zero f N htor (-q) h)

/-- **Koszul detection of the zero object of `D(A)`.** Let `A` be a commutative ring and
`f₁, …, f_r ∈ A`. An object `N` of `D(A)` whose cohomology modules are all `f_i`-power torsion for
every `i`, and which receives no nonzero morphism from any shift of the Koszul complex
`K(f₁, …, f_r)`, is zero.

This is the algebraic content of the implication "(2) implies (1)" of [Stacks, Tag 09IR], and it
is `Stacks.Koszul.Truncation.isZero_homology_of_forall_hom_derivedKoszul_eq_zero` in every
degree: an object of `D(A)` with no cohomology at all is zero. -/
theorem isZero_of_forall_hom_derivedKoszul_eq_zero {r : ℕ} (f : Fin r → A)
    (N : DerivedCategory (ModuleCat.{u} A))
    (htor : ∀ (i : Fin r) (m : ℤ)
      (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) m).obj N),
      ∃ k : ℕ, f i ^ k • x = 0)
    (h : ∀ (n : ℤ) (g : (derivedKoszul f)⟦n⟧ ⟶ N), g = 0) : IsZero N :=
  Stacks.Duality.isZero_of_forall_isZero_homology N fun q =>
    isZero_homology_of_forall_hom_derivedKoszul_eq_zero f N htor q (h (-q))

end Stacks.Koszul.Truncation

end
