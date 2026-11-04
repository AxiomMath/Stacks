module

public import StacksFrontier.Algebra.DifferentialGraded.Module.Bijective
public import StacksFrontier.Algebra.DifferentialGraded.Module.OrthogonalAcyclic

/-! # Extending null-homotopies along an exhaustive filtration

Let `(A, d)` be a differential graded algebra and let `P` be a right differential graded
`A`-module carrying an exhaustive filtration by stages `F i` whose transition inclusions are
admissible monomorphisms with cokernels `Q i`. This file proves that `P` is orthogonal on the
left to the acyclic modules as soon as the bottom stage `F 0` and every graded piece `Q i` is,
which is the content of Stacks Tag 09KM once property (P) supplies such a filtration.

The argument is Stacks' telescope argument, carried out on homotopies rather than on triangles.
Orthogonality of the individual stages is *not* enough: a morphism `P ⟶ N` restricts to a
null-homotopic morphism on every stage, but a null-homotopy of `P ⟶ N` exists only if the
null-homotopies on the stages can be chosen compatibly, and the obstruction to that is exactly
what the telescope short exact sequence of Tag 09KL is introduced to kill. Here the compatible
system is constructed directly, one stage at a time.

## Main definitions

* `DifferentialGradedModule.commutatorHom`: the commutator `d ∘ h + h ∘ d` of the differentials
  with a map of degree `-1`, as a homomorphism of differential graded modules.

## Main results

* `DifferentialGradedModule.leftOrthogonal_acyclic_iff`: being orthogonal on the left to the
  acyclic objects of the homotopy category is the same as every homomorphism into an acyclic
  differential graded module being null-homotopic.
* `DifferentialGradedModule.exists_homotopy_zero_extension`: a null-homotopy extends along an
  admissible monomorphism whose cokernel admits only null-homotopic maps into the target, and
  the extension restricts to the homotopy one started with.
* `DifferentialGradedModule.leftOrthogonal_acyclic_of_admissibleFiltration`: the conclusion
  above, for an exhaustive filtration by admissible monomorphisms.

## Implementation notes

*Why the argument is run on homotopies and not on the telescope object.* Stacks proves Tag 09KM
from the telescope short exact sequence of Tag 09KL, which presents `P` as the third term of a
distinguished triangle whose other two terms are `⊕ᵢ Fᵢ P`. The tempting shortcut is to avoid that
object altogether: every stage `F i` is orthogonal on the left to the acyclic modules, the stage
embeddings `F i ⟶ P` exhaust `P`, and `CategoryTheory.ObjectProperty.leftOrthogonal_of_jointlyEpi`
concludes left-orthogonality of the target of any jointly epimorphic family. **That shortcut does
not work, and the statement it needs is false.** Joint epimorphy of the stage embeddings in `K(A)`
would say that two morphisms out of `P` agreeing up to homotopy on every stage agree up to
homotopy, and that fails: the per-stage homotopies need not be compatible with one another. That
incompatibility is precisely the `lim¹` obstruction, and killing it is the entire reason the
telescope is introduced rather than arguing stage by stage. The hypothesis of
`CategoryTheory.ObjectProperty.leftOrthogonal_of_jointlyEpi` asks for less than a colimit, but not
for less than is true.

What is done here instead is the telescope argument at the level of homotopies rather than of
objects. `exists_homotopy_zero_extension` extends a null-homotopy from one stage to the next
*and restricts to the one already chosen* — that second clause is the content, since it is what
makes the system of homotopies compatible — so the stages' homotopies glue over the exhaustive
filtration. This kills the same obstruction as the telescope while never forming `⊕ᵢ Fᵢ P`.

The filtration is taken as plain data — the stages, their embeddings into `P`, the transition
inclusions, the cokernels and the four conditions relating them — rather than as a bundled
property-(P) filtration. The statement therefore does not depend on how that structure is
packaged, and the bundled version is obtained by supplying its fields.

Stages are embedded by injective homomorphisms rather than realised as submodules, so the
element of a stage representing a given element of `P` is only determined up to the embedding;
`DifferentialGradedModule.Hom.mem_grading_of_injective` is what makes such a representative
homogeneous when the element of `P` is, which the degree condition on the glued homotopy needs.

The commutator `d ∘ h + h ∘ d` of a degree `-1` map with the differentials is `A`-linear even
though `h` composed with a single differential is not: the two Leibniz correction terms carry
the signs `(-1)^(n-1)` and `(-1)^n` and cancel. That cancellation is
`DifferentialGradedModule.negOnePow_add_sub_one`, and it is why
`DifferentialGradedModule.commutatorHom` is a homomorphism at all.

As everywhere in this chapter's differential graded interface, the base ring, the algebra and
the modules all live in a single universe `u`, following `DifferentialGradedModule`.

## References

* [Stacks Project, Tag 09KM](https://stacks.math.columbia.edu/tag/09KM), whose proof this file
  carries out; the telescope it rests on is
  [Tag 09KL](https://stacks.math.columbia.edu/tag/09KL) and the vanishing criterion along a
  distinguished triangle is [Tag 0149](https://stacks.math.columbia.edu/tag/0149).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
  {M N : DifferentialGradedModule A}

/-- The signs `(-1)^n` and `(-1)^(n-1)` cancel. -/
theorem negOnePow_add_sub_one (n : ℤ) : (n.negOnePow : ℤ) + ((n - 1).negOnePow : ℤ) = 0 := by
  rw [show n - 1 = n + (-1) from by ring, Int.negOnePow_add]
  simp [Int.negOnePow_neg]

/-- The commutator `d ∘ h + h ∘ d` of the differentials with an `A`-linear map `h` of degree
`-1` is a homomorphism of differential graded modules: the two Leibniz signs cancel, so it is
`A`-linear, it preserves the grading, and it commutes with the differentials because `d² = 0`. -/
def commutatorHom (h : M.M →ₗ[MulOpposite A.A] N.M)
    (hgr : ∀ (n : ℤ) (x : M.M), x ∈ M.grading n → h x ∈ N.grading (n - 1)) : Hom M N where
  toFun := N.d ∘ₗ h.restrictScalars R + (h.restrictScalars R) ∘ₗ M.d
  map_smul := by
    have key : ∀ (n : ℤ) (x : M.M), x ∈ M.grading n → ∀ a : A.A,
        N.d (h (MulOpposite.op a • x)) + h (M.d (MulOpposite.op a • x)) =
          MulOpposite.op a • (N.d (h x) + h (M.d x)) := by
      intro n x hx a
      rw [map_smul, leibniz_apply N (n - 1) (h x) (hgr n x hx) a, leibniz_apply M n x hx a,
        map_add, map_smul, map_zsmul, map_smul]
      have hw : ((n - 1).negOnePow : ℤ) = -(n.negOnePow : ℤ) := by
        have h0 := negOnePow_add_sub_one n; linarith
      rw [hw, neg_smul, smul_add]
      abel
    intro x a
    induction x using DirectSum.Decomposition.inductionOn M.grading with
    | zero => simp
    | homogeneous x => rename_i n; exact key n (x : M.M) x.2 a
    | add x y hx hy =>
      rw [smul_add, map_add, map_add, hx, hy, smul_add]
  map_grading := by
    intro n x hx
    refine (N.grading n).add_mem ?_ ?_
    · have := N.d_mem (n - 1) (h x) (hgr n x hx)
      rwa [show n - 1 + 1 = n from by ring] at this
    · have := hgr (n + 1) (M.d x) (M.d_mem n x hx)
      rwa [show n + 1 - 1 = n from by ring] at this
  map_d := by
    ext x
    have hM := LinearMap.congr_fun M.d_comp_d x
    have hN := LinearMap.congr_fun N.d_comp_d (h x)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hM hN
    simp only [LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.restrictScalars_apply, map_add, hM, hN, map_zero]
    abel

/-- The commutator homomorphism sends `x` to `d (h x) + h (d x)`. -/
@[simp] theorem commutatorHom_toFun_apply (h : M.M →ₗ[MulOpposite A.A] N.M)
    (hgr : ∀ (n : ℤ) (x : M.M), x ∈ M.grading n → h x ∈ N.grading (n - 1)) (x : M.M) :
    (commutatorHom h hgr).toFun x = N.d (h x) + h (M.d x) := rfl

/-- A graded homomorphism as a map of right `A`-modules. -/
def GradedHom.opLinearMap (f : GradedHom M N) : M.M →ₗ[MulOpposite A.A] N.M where
  toFun := f.toFun
  map_add' := f.toFun.map_add
  map_smul' s x := by
    rw [← MulOpposite.op_unop s]
    exact f.map_smul x s.unop

/-- `f.opLinearMap` has the same values as `f`. -/
@[simp] theorem GradedHom.opLinearMap_apply (f : GradedHom M N) (x : M.M) :
    f.opLinearMap x = f.toFun x := rfl

/-- A differential graded module is orthogonal on the left to the acyclic objects of the
homotopy category exactly when every homomorphism from it into an acyclic differential graded
module is null-homotopic. -/
theorem leftOrthogonal_acyclic_iff (M : DifferentialGradedModule A) :
    (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj M) ↔
      ∀ (N : DifferentialGradedModule A), N.toCochainComplex.Acyclic →
        ∀ g : M ⟶ N, Homotopic g 0 := by
  constructor
  · intro hM N hN g
    have h0 : (toHomotopyCategory A).map g = 0 := hM _ hN
    rw [← (toHomotopyCategory A).map_zero M N] at h0
    exact (CategoryTheory.Quotient.functor_map_eq_iff (homotopyRel A) g 0).1 h0
  · intro h Y f hY
    obtain ⟨N⟩ := Y
    induction f using Quot.inductionOn with
    | _ g =>
      show (toHomotopyCategory A).map g = 0
      rw [← (toHomotopyCategory A).map_zero M N]
      exact (CategoryTheory.Quotient.functor_map_eq_iff (homotopyRel A) g 0).2 (h N hY g)

/-- **Extension of a null-homotopy along an admissible monomorphism.** Let `incl : F₁ ⟶ F₂` be
an admissible monomorphism with cokernel `quot : F₂ ⟶ Q`, and let `g : F₂ ⟶ N`. If every
homomorphism `Q ⟶ N` is null-homotopic, then every null-homotopy of `incl ≫ g` extends to a
null-homotopy of `g`.

The graded retraction of `incl` extends the given homotopy to a degree `-1` map `h'` on `F₂`;
the difference `e = g - (d h' + h' d)` is then a homomorphism vanishing on `F₁`, hence induced
by one on the cokernel, which is null-homotopic by hypothesis. Correcting `h'` by that homotopy
gives the extension, and the correction vanishes on `F₁`, so the extension really restricts to
the homotopy one started with. -/
theorem exists_homotopy_zero_extension
    {F₁ F₂ Q : DifferentialGradedModule A}
    (incl : F₁ ⟶ F₂) (quot : F₂ ⟶ Q) (g : F₂ ⟶ N) (g₁ : F₁ ⟶ N)
    (hg₁ : ∀ x, g₁.toFun x = g.toFun (incl.toFun x))
    (hadm : IsAdmissibleMono incl)
    (hsurj : Function.Surjective quot.toFun)
    (hker : LinearMap.ker quot.toFun = LinearMap.range incl.toFun)
    (hQ : ∀ e : Q ⟶ N, Homotopic e 0)
    (h₁ : Homotopy g₁ 0) :
    ∃ h₂ : Homotopy g 0, ∀ x, h₂.toLinearMap (incl.toFun x) = h₁.toLinearMap x := by
  classical
  obtain ⟨π, hπ⟩ := hadm
  obtain ⟨h', hgr', hh'_incl⟩ : ∃ h' : F₂.M →ₗ[MulOpposite A.A] N.M,
      (∀ (n : ℤ) (x : F₂.M), x ∈ F₂.grading n → h' x ∈ N.grading (n - 1)) ∧
        (∀ x, h' (incl.toFun x) = h₁.toLinearMap x) :=
    ⟨h₁.toLinearMap ∘ₗ π.opLinearMap,
      fun n x hx => h₁.map_grading n _ (π.map_grading n x hx),
      fun x => by
        show h₁.toLinearMap (π.toFun (incl.toFun x)) = h₁.toLinearMap x
        rw [hπ]⟩
  obtain ⟨e, he_apply⟩ : ∃ e : F₂ ⟶ N,
      ∀ x, e.toFun x = g.toFun x - (N.d (h' x) + h' (F₂.d x)) :=
    ⟨g - commutatorHom h' hgr', fun x => by
      rw [Hom.hom_sub_toFun]
      simp only [LinearMap.sub_apply, commutatorHom_toFun_apply]⟩
  have he_incl : ∀ x, e.toFun (incl.toFun x) = 0 := by
    intro x
    have hd : F₂.d (incl.toFun x) = incl.toFun (F₁.d x) :=
      (LinearMap.congr_fun incl.map_d x).symm
    have heq := h₁.homotopy_eq x
    simp only [Hom.hom_zero_toFun, LinearMap.zero_apply, sub_zero, hg₁] at heq
    rw [he_apply, hd, hh'_incl, hh'_incl, ← heq, sub_self]
  have hwd : ∀ x y, quot.toFun x = quot.toFun y → e.toFun x = e.toFun y := by
    intro x y hxy
    obtain ⟨z, hz⟩ : x - y ∈ LinearMap.range incl.toFun := by
      rw [← hker, LinearMap.mem_ker, map_sub, hxy, sub_self]
    rw [← sub_eq_zero, ← map_sub, ← hz, he_incl]
  have hquot_incl : ∀ x, quot.toFun (incl.toFun x) = 0 := by
    intro x
    rw [← LinearMap.mem_ker, hker]
    exact ⟨x, rfl⟩
  obtain ⟨ebar, hebar⟩ : ∃ ebar : Q ⟶ N, ∀ x, ebar.toFun (quot.toFun x) = e.toFun x := by
    set σ := Function.surjInv hsurj with hσdef
    have hσ : ∀ y, quot.toFun (σ y) = y := fun y => Function.surjInv_eq hsurj y
    have hadd : ∀ y z : Q.M, e.toFun (σ (y + z)) = e.toFun (σ y) + e.toFun (σ z) := by
      intro y z
      rw [← map_add]
      exact hwd _ _ (by rw [hσ, map_add, hσ, hσ])
    have hsmul : ∀ (r : R) (y : Q.M),
        e.toFun (σ (r • y)) = (RingHom.id R) r • e.toFun (σ y) := by
      intro r y
      show e.toFun (σ (r • y)) = r • e.toFun (σ y)
      rw [← map_smul]
      exact hwd _ _ (by rw [hσ, map_smul, hσ])
    have hopsmul : ∀ (y : Q.M) (a : A.A),
        e.toFun (σ (MulOpposite.op a • y)) = MulOpposite.op a • e.toFun (σ y) := by
      intro y a
      rw [← e.map_smul]
      exact hwd _ _ (by rw [hσ, quot.map_smul, hσ])
    have hgrad : ∀ (n : ℤ) (y : Q.M), y ∈ Q.grading n → e.toFun (σ y) ∈ N.grading n := by
      intro n y hy
      obtain ⟨x, hx, hxy⟩ := Hom.exists_mem_grading_of_surjective hsurj hy
      rw [hwd (σ y) x (by rw [hσ, hxy])]
      exact e.map_grading n x hx
    have hdd : ∀ y : Q.M, e.toFun (σ (Q.d y)) = N.d (e.toFun (σ y)) := by
      intro y
      obtain ⟨x, hx⟩ := hsurj y
      have hdq : Q.d (quot.toFun x) = quot.toFun (F₂.d x) :=
        (LinearMap.congr_fun quot.map_d x).symm
      rw [← hx, hdq, hwd (σ (quot.toFun (F₂.d x))) (F₂.d x) (by rw [hσ]),
        hwd (σ (quot.toFun x)) x (by rw [hσ])]
      exact LinearMap.congr_fun e.map_d x
    exact ⟨{ toFun := { toFun := fun y => e.toFun (σ y), map_add' := hadd, map_smul' := hsmul }
             map_smul := hopsmul
             map_grading := hgrad
             map_d := LinearMap.ext hdd },
      fun x => hwd _ _ (by rw [hσ])⟩
  obtain ⟨k⟩ := hQ ebar
  refine ⟨{ toLinearMap := h' + k.toLinearMap ∘ₗ quot.toGradedHom.opLinearMap
            map_grading := ?_
            homotopy_eq := ?_ }, ?_⟩
  · intro n x hx
    exact (N.grading (n - 1)).add_mem (hgr' n x hx)
      (k.map_grading n _ (quot.map_grading n x hx))
  · intro x
    have hk := k.homotopy_eq (quot.toFun x)
    simp only [Hom.hom_zero_toFun, LinearMap.zero_apply, sub_zero] at hk
    have hdq : quot.toFun (F₂.d x) = Q.d (quot.toFun x) :=
      LinearMap.congr_fun quot.map_d x
    show g.toFun x - (0 : F₂ ⟶ N).toFun x =
      N.d (h' x + k.toLinearMap (quot.toFun x)) +
        (h' (F₂.d x) + k.toLinearMap (quot.toFun (F₂.d x)))
    simp only [Hom.hom_zero_toFun, LinearMap.zero_apply, sub_zero, map_add, hdq]
    have hex : N.d (k.toLinearMap (quot.toFun x)) + k.toLinearMap (Q.d (quot.toFun x))
        = g.toFun x - (N.d (h' x) + h' (F₂.d x)) := by rw [← hk, hebar, he_apply]
    rw [show N.d (h' x) + N.d (k.toLinearMap (quot.toFun x)) +
          (h' (F₂.d x) + k.toLinearMap (Q.d (quot.toFun x)))
        = (N.d (h' x) + h' (F₂.d x)) +
          (N.d (k.toLinearMap (quot.toFun x)) + k.toLinearMap (Q.d (quot.toFun x)))
        from by abel, hex]
    abel
  · intro x
    show h' (incl.toFun x) + k.toLinearMap (quot.toFun (incl.toFun x)) = h₁.toLinearMap x
    rw [hh'_incl, hquot_incl, map_zero, add_zero]

/-- **Stacks 09KM, the inductive core.** Let `P` carry an exhaustive filtration by the stages
`F i`, embedded in `P` by `emb i`, with transition inclusions `incl i` that are admissible
monomorphisms with cokernels `quot i : F (i + 1) ⟶ Q i`. If the bottom stage `F 0` and every
graded piece `Q i` is orthogonal on the left to the acyclic modules, so is `P`.

This is Stacks' telescope argument in its homotopy-theoretic form. Orthogonality of the stages
alone would *not* suffice — the homotopies on the stages have to be chosen compatibly, and the
failure of that compatibility is exactly what the telescope of Tag 09KL is introduced to kill.
Here the compatible system is built directly: `exists_homotopy_zero_extension` extends the
null-homotopy from one stage to the next while restricting to the one already chosen, so the
stages' homotopies glue to a homotopy on the union, which is `P` by exhaustiveness. -/
theorem leftOrthogonal_acyclic_of_admissibleFiltration
    {P : DifferentialGradedModule A}
    (F : ℕ → DifferentialGradedModule A) (Q : ℕ → DifferentialGradedModule A)
    (emb : ∀ i, F i ⟶ P) (incl : ∀ i, F i ⟶ F (i + 1)) (quot : ∀ i, F (i + 1) ⟶ Q i)
    (hemb : ∀ i, Function.Injective (emb i).toFun)
    (hincl : ∀ i x, (emb (i + 1)).toFun ((incl i).toFun x) = (emb i).toFun x)
    (hadm : ∀ i, IsAdmissibleMono (incl i))
    (hsurj : ∀ i, Function.Surjective (quot i).toFun)
    (hker : ∀ i, LinearMap.ker (quot i).toFun = LinearMap.range (incl i).toFun)
    (hexh : ∀ x : P.M, ∃ i y, (emb i).toFun y = x)
    (hbot : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj (F 0)))
    (hQ : ∀ i, (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj (Q i))) :
    (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj P) := by
  classical
  rw [leftOrthogonal_acyclic_iff]
  intro N hN g
  have hQ' : ∀ i (e : Q i ⟶ N), Homotopic e 0 :=
    fun i e => (leftOrthogonal_acyclic_iff _).1 (hQ i) N hN e
  have hbot' : ∀ e : F 0 ⟶ N, Homotopic e 0 :=
    fun e => (leftOrthogonal_acyclic_iff _).1 hbot N hN e
  have hggcomp : ∀ i x, (emb i ≫ g).toFun x = (emb (i + 1) ≫ g).toFun ((incl i).toFun x) := by
    intro i x
    show g.toFun ((emb i).toFun x) = g.toFun ((emb (i + 1)).toFun ((incl i).toFun x))
    rw [hincl]
  have step : ∀ i (h : Homotopy (emb i ≫ g) 0),
      ∃ h' : Homotopy (emb (i + 1) ≫ g) 0,
        ∀ x, h'.toLinearMap ((incl i).toFun x) = h.toLinearMap x :=
    fun i h => exists_homotopy_zero_extension (incl i) (quot i) (emb (i + 1) ≫ g) (emb i ≫ g)
      (hggcomp i) (hadm i) (hsurj i) (hker i) (hQ' i) h
  -- the compatible tower of null-homotopies
  let T : ∀ i, Homotopy (emb i ≫ g) 0 := fun i =>
    Nat.rec (motive := fun i => Homotopy (emb i ≫ g) 0) (hbot' (emb 0 ≫ g)).some
      (fun j hj => (step j hj).choose) i
  have hT : ∀ i x, (T (i + 1)).toLinearMap ((incl i).toFun x) = (T i).toLinearMap x :=
    fun i x => (step i (T i)).choose_spec x
  -- the transition maps of the tower, between arbitrary stages
  have chain : ∀ q p, p ≤ q → ∃ c : F p ⟶ F q,
      (∀ y, (emb q).toFun (c.toFun y) = (emb p).toFun y) ∧
        (∀ y, (T q).toLinearMap (c.toFun y) = (T p).toLinearMap y) := by
    intro q
    induction q with
    | zero =>
      intro p hp
      obtain rfl : p = 0 := Nat.le_zero.mp hp
      exact ⟨𝟙 _, fun _ => rfl, fun _ => rfl⟩
    | succ q ih =>
      intro p hp
      rcases Nat.eq_or_lt_of_le hp with rfl | h
      · exact ⟨𝟙 _, fun _ => rfl, fun _ => rfl⟩
      · obtain ⟨c, hc₁, hc₂⟩ := ih p (Nat.lt_succ_iff.mp h)
        refine ⟨c ≫ incl q, fun y => ?_, fun y => ?_⟩
        · rw [Hom.comp_toFun_apply, hincl, hc₁]
        · rw [Hom.comp_toFun_apply, hT, hc₂]
  -- the value of the tower is independent of the stage it is read at
  have hwdef : ∀ p q (y : (F p).M) (z : (F q).M),
      (emb p).toFun y = (emb q).toFun z →
        (T p).toLinearMap y = (T q).toLinearMap z := by
    have key : ∀ p q (y : (F p).M) (z : (F q).M), p ≤ q →
        (emb p).toFun y = (emb q).toFun z →
          (T p).toLinearMap y = (T q).toLinearMap z := by
      intro p q y z hpq hyz
      obtain ⟨c, hc₁, hc₂⟩ := chain q p hpq
      have : c.toFun y = z := hemb q (by rw [hc₁, hyz])
      rw [← hc₂, this]
    intro p q y z hyz
    rcases le_total p q with h | h
    · exact key p q y z h hyz
    · exact (key q p z y h hyz.symm).symm
  -- the glued homotopy
  obtain ⟨H, hH⟩ : ∃ H : P.M → N.M,
      ∀ p (y : (F p).M), H ((emb p).toFun y) = (T p).toLinearMap y := by
    refine ⟨fun x => (T (hexh x).choose).toLinearMap (hexh x).choose_spec.choose, ?_⟩
    intro p y
    exact hwdef _ _ _ _ (hexh ((emb p).toFun y)).choose_spec.choose_spec
  refine ⟨{ toLinearMap := { toFun := H, map_add' := ?_, map_smul' := ?_ }
            map_grading := ?_
            homotopy_eq := ?_ }⟩
  · intro x x'
    obtain ⟨p, y, rfl⟩ := hexh x
    obtain ⟨q, z, rfl⟩ := hexh x'
    obtain ⟨cp, hcp₁, hcp₂⟩ := chain (max p q) p (le_max_left p q)
    obtain ⟨cq, hcq₁, hcq₂⟩ := chain (max p q) q (le_max_right p q)
    rw [← hcp₁ y, ← hcq₁ z, ← map_add, hH, hH, hH, map_add, hcp₂, hcq₂]
  · intro s x
    obtain ⟨p, y, rfl⟩ := hexh x
    show H (s • (emb p).toFun y) = s • H ((emb p).toFun y)
    rw [← MulOpposite.op_unop s, ← (emb p).map_smul, hH, hH]
    exact map_smul (T p).toLinearMap _ y
  · intro n x hx
    obtain ⟨p, y, rfl⟩ := hexh x
    show H ((emb p).toFun y) ∈ N.grading (n - 1)
    rw [hH]
    exact (T p).map_grading n y (Hom.mem_grading_of_injective (hemb p) hx)
  · intro x
    obtain ⟨p, y, rfl⟩ := hexh x
    have heq := (T p).homotopy_eq y
    simp only [Hom.hom_zero_toFun, LinearMap.zero_apply, sub_zero,
      Hom.comp_toFun_apply] at heq
    have hd : P.d ((emb p).toFun y) = (emb p).toFun ((F p).d y) :=
      (LinearMap.congr_fun (emb p).map_d y).symm
    show g.toFun ((emb p).toFun y) - (0 : P ⟶ N).toFun ((emb p).toFun y) =
      N.d (H ((emb p).toFun y)) + H (P.d ((emb p).toFun y))
    simp only [Hom.hom_zero_toFun, LinearMap.zero_apply, sub_zero]
    rw [hd, hH, hH, heq]

end DifferentialGradedModule
