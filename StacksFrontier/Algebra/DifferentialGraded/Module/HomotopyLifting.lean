module

public import StacksFrontier.Algebra.DifferentialGraded.Module.AdmissibleCriterion
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomotopyExtension

/-! # Lifting null-homotopies along a separated complete filtration

Let `(A, d)` be a differential graded algebra and let `I` be a right differential graded
`A`-module carrying a decreasing filtration by stages `F i` whose transition inclusions are
admissible monomorphisms with graded pieces `G i`, with `F 0 = I`, and which is separated and
complete. This file proves that `I` is orthogonal on the right to the acyclic modules as soon as
every graded piece `G i` is, which is the content of Stacks Tag 09KS once property (I) supplies
such a filtration.

This is the exact dual of
`StacksFrontier/Algebra/DifferentialGraded/Module/HomotopyExtension.lean`, which does the same for
property (P), and it is carried out the same way: on homotopies rather than on triangles.
Orthogonality of the graded pieces does not by itself give a null-homotopy of a map `f : N ⟶ I`;
what it gives is a null-homotopy *modulo* each stage, and those have to be chosen compatibly
with one another. The obstruction to that is what the telescope short exact sequence of Tag 09KR
is introduced to kill. Here the compatible system is constructed directly, one stage at a time,
so the telescope object — a product of differential graded modules, which this encoding does not
provide — is never formed.

## Main results

* `DifferentialGradedModule.rightOrthogonal_acyclic_iff`: being orthogonal on the right to the
  acyclic objects of the homotopy category is the same as every homomorphism from an acyclic
  differential graded module being null-homotopic.
* `DifferentialGradedModule.exists_factor_of_range_le`: a homomorphism whose values lie in the
  image of an injective homomorphism factors through it.
* `DifferentialGradedModule.exists_homotopy_mod_next_stage`: a null-homotopy modulo one stage of
  the filtration can be corrected to a null-homotopy modulo the next stage, by a correction
  whose values lie in the stage one started from.
* `DifferentialGradedModule.rightOrthogonal_acyclic_of_completeFiltration`: the conclusion
  above, for a separated complete filtration by admissible monomorphisms.

## Implementation notes

*What a null-homotopy modulo a stage is.* A degree `-1` map `h : N.M → I.M` of right
`A`-modules is a null-homotopy of `f` modulo `F i` when every value of `f - (d h + h d)` lies in
the image of `F i ⟶ I`. That difference is a *homomorphism* `N ⟶ I`
(`DifferentialGradedModule.commutatorHom`) and `F i ⟶ I` is injective, so it then factors
through `F i` as a homomorphism, which is what the correction step consumes; the condition is
nevertheless stated in the pointwise form, because that is the form in which the limit of the
corrections is taken and the form in which separatedness is applied.

*Completeness is used degreewise.* The filtration being complete means `I = lim I / F p I`, a
limit of differential graded modules, hence computed degreewise. The hypothesis asked for is
accordingly that a sequence of homogeneous elements of a common degree whose consecutive
differences lie in the successive stages is approximated by a single homogeneous element of that
degree, which is exactly what gluing the corrections needs: the maps being glued lower the
degree by one.

*Why the bottom stage needs no hypothesis.* On the property-(P) side the bottom stage of the
filtration carries a hypothesis of its own, because the filtration there starts at `0` and
exhausts `P`. Here it starts at `I` itself, so the zero map is already a null-homotopy modulo
`F 0`, and surjectivity of `F 0 ⟶ I` is all that the base case of the induction needs.

As everywhere in this chapter's differential graded interface, the base ring, the algebra and
the modules all live in a single universe `u`, following `DifferentialGradedModule`.

## References

* [Stacks Project, Tag 09KS](https://stacks.math.columbia.edu/tag/09KS), whose proof this is,
  and [Tag 09KM](https://stacks.math.columbia.edu/tag/09KM), of which it is the dual.
-/

@[expose] public section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
  {N : DifferentialGradedModule A}

/-- A differential graded module is orthogonal on the right to the acyclic objects of the
homotopy category exactly when every homomorphism into it from an acyclic differential graded
module is null-homotopic. -/
theorem rightOrthogonal_acyclic_iff (M : DifferentialGradedModule A) :
    (acyclic' A).rightOrthogonal ((toHomotopyCategory A).obj M) ↔
      ∀ (N : DifferentialGradedModule A), N.toCochainComplex.Acyclic →
        ∀ g : N ⟶ M, Homotopic g 0 := by
  constructor
  · intro hM N hN g
    have h0 : (toHomotopyCategory A).map g = 0 := hM _ hN
    rw [← (toHomotopyCategory A).map_zero N M] at h0
    exact (CategoryTheory.Quotient.functor_map_eq_iff (homotopyRel A) g 0).1 h0
  · intro h Y f hY
    obtain ⟨N⟩ := Y
    induction f using Quot.inductionOn with
    | _ g =>
      change (toHomotopyCategory A).map g = 0
      rw [← (toHomotopyCategory A).map_zero N M]
      exact (CategoryTheory.Quotient.functor_map_eq_iff (homotopyRel A) g 0).2 (h N hY g)

/-- A homomorphism of differential graded modules commutes with the differentials. -/
private theorem toFun_d_apply {K L : DifferentialGradedModule A} (φ : K ⟶ L) (y : K.M) :
    φ.toFun (K.d y) = L.d (φ.toFun y) :=
  LinearMap.congr_fun φ.map_d y

/-- The value of `e - (d h + h d)` at a point, as a homomorphism minus a commutator. -/
private theorem sub_commutatorHom_toFun_apply {T L : DifferentialGradedModule A} (e : T ⟶ L)
    (h : T.M →ₗ[MulOpposite A.A] L.M)
    (hgr : ∀ (n : ℤ) (x : T.M), x ∈ T.grading n → h x ∈ L.grading (n - 1)) (x : T.M) :
    (e - commutatorHom h hgr).toFun x = e.toFun x - (L.d (h x) + h (T.d x)) := by
  rw [Hom.hom_sub_toFun]
  simp only [LinearMap.sub_apply, commutatorHom_toFun_apply]

/-- A homomorphism of differential graded modules all of whose values lie in the image of an
injective homomorphism factors through it, as a homomorphism of differential graded modules. -/
theorem exists_factor_of_range_le {K L : DifferentialGradedModule A} (incl : K ⟶ L)
    (hinj : Function.Injective incl.toFun) {T : DifferentialGradedModule A} (e : T ⟶ L)
    (he : ∀ x, ∃ y, incl.toFun y = e.toFun x) :
    ∃ ebar : T ⟶ K, ∀ x, incl.toFun (ebar.toFun x) = e.toFun x := by
  classical
  have hspec : ∀ x : T.M, incl.toFun ((he x).choose) = e.toFun x := fun x => (he x).choose_spec
  have hadd : ∀ x y : T.M, (he (x + y)).choose = (he x).choose + (he y).choose :=
    fun x y => hinj (by rw [hspec]; simp only [map_add, hspec])
  have hsmulR : ∀ (r : R) (x : T.M), (he (r • x)).choose = r • (he x).choose :=
    fun r x => hinj (by rw [hspec]; simp only [map_smul, hspec])
  have hsmulA : ∀ (x : T.M) (a : A.A),
      (he (MulOpposite.op a • x)).choose = MulOpposite.op a • (he x).choose :=
    fun x a => hinj (by rw [hspec]; simp only [e.map_smul, incl.map_smul, hspec])
  have hdd : ∀ x : T.M, (he (T.d x)).choose = K.d ((he x).choose) := by
    intro x
    refine hinj ?_
    calc incl.toFun ((he (T.d x)).choose) = e.toFun (T.d x) := hspec _
      _ = L.d (e.toFun x) := toFun_d_apply e x
      _ = L.d (incl.toFun ((he x).choose)) := by rw [hspec]
      _ = incl.toFun (K.d ((he x).choose)) := (toFun_d_apply incl _).symm
  have hgrad : ∀ (n : ℤ) (x : T.M), x ∈ T.grading n → (he x).choose ∈ K.grading n := by
    intro n x hx
    refine Hom.mem_grading_of_injective hinj ?_
    rw [hspec]
    exact e.map_grading n x hx
  exact ⟨{
    toFun := { toFun := fun x => (he x).choose, map_add' := hadd, map_smul' := hsmulR }
    map_smul := hsmulA
    map_grading := hgrad
    map_d := LinearMap.ext hdd }, hspec⟩

/-- **The correction step.** Let `incl : F₂ ⟶ F₁` be an admissible monomorphism whose graded
piece is `quot : F₁ ⟶ G`, embedded in `I` compatibly by `emb₁` and `emb₂`. If every homomorphism
`N ⟶ G` is null-homotopic and `h` is a null-homotopy of `f : N ⟶ I` modulo `F₁`, then
`h + emb₁ ∘ k` is one modulo `F₂` for some `k` of degree `-1` into `F₁`.

The graded section of `quot` lifts a null-homotopy of `e ≫ quot` — where `e : N ⟶ F₁` is the
factorization of `f - (d h + h d)` — to a degree `-1` map `k` into `F₁`; the corrected
difference `e - (d k + k d)` is then killed by `quot`, hence factors through `F₂`. -/
theorem exists_homotopy_mod_next_stage {I F₁ F₂ G : DifferentialGradedModule A}
    (emb₁ : F₁ ⟶ I) (emb₂ : F₂ ⟶ I) (incl : F₂ ⟶ F₁) (quot : F₁ ⟶ G) (f : N ⟶ I)
    (hemb₁ : Function.Injective emb₁.toFun)
    (hincl : ∀ x, emb₁.toFun (incl.toFun x) = emb₂.toFun x)
    (hadm : IsAdmissibleMono incl)
    (hsurj : Function.Surjective quot.toFun)
    (hker : LinearMap.ker quot.toFun = LinearMap.range incl.toFun)
    (hG : ∀ e : N ⟶ G, Homotopic e 0)
    (h : N.M →ₗ[MulOpposite A.A] I.M)
    (hgr : ∀ (n : ℤ) (x : N.M), x ∈ N.grading n → h x ∈ I.grading (n - 1))
    (hmod : ∀ x, ∃ y, emb₁.toFun y = f.toFun x - (I.d (h x) + h (N.d x))) :
    ∃ k : N.M →ₗ[MulOpposite A.A] F₁.M,
      (∀ (n : ℤ) (x : N.M), x ∈ N.grading n → k x ∈ F₁.grading (n - 1)) ∧
      ∀ x, ∃ y, emb₂.toFun y = f.toFun x
        - (I.d (h x + emb₁.toFun (k x)) + (h (N.d x) + emb₁.toFun (k (N.d x)))) := by
  classical
  -- the difference `f - (d h + h d)` factors through `F₁`
  obtain ⟨e, he⟩ := exists_factor_of_range_le emb₁ hemb₁ (f - commutatorHom h hgr) (by
    intro x
    obtain ⟨y, hy⟩ := hmod x
    exact ⟨y, by rw [hy, sub_commutatorHom_toFun_apply]⟩)
  have he' : ∀ x, emb₁.toFun (e.toFun x) = f.toFun x - (I.d (h x) + h (N.d x)) := fun x => by
    rw [he x, sub_commutatorHom_toFun_apply]
  -- its image in the graded piece is null-homotopic
  obtain ⟨kk⟩ := hG (e ≫ quot)
  have hkk : ∀ x, quot.toFun (e.toFun x) = G.d (kk.toLinearMap x) + kk.toLinearMap (N.d x) := by
    intro x
    have := kk.homotopy_eq x
    simp only [Hom.hom_zero_toFun, LinearMap.zero_apply, sub_zero,
      Hom.comp_toFun_apply] at this
    exact this
  -- lift it along the graded section of the projection onto the graded piece
  obtain ⟨σ, hσ⟩ :=
    (isAdmissibleShortExact_of_ker_eq_range incl quot hadm hsurj hker).admissibleEpi
  have hk : ∀ (n : ℤ) (x : N.M), x ∈ N.grading n →
      (σ.opLinearMap ∘ₗ kk.toLinearMap) x ∈ F₁.grading (n - 1) :=
    fun n x hx => σ.map_grading (n - 1) _ (kk.map_grading n x hx)
  refine ⟨σ.opLinearMap ∘ₗ kk.toLinearMap, hk, ?_⟩
  have hquotk : ∀ x, quot.toFun ((σ.opLinearMap ∘ₗ kk.toLinearMap) x) = kk.toLinearMap x :=
    fun x => hσ _
  -- the corrected difference is killed by the projection, hence factors through `F₂`
  obtain ⟨ebar, hebar⟩ := exists_factor_of_range_le incl hadm.injective
    (e - commutatorHom (σ.opLinearMap ∘ₗ kk.toLinearMap) hk) (by
      intro x
      rw [← LinearMap.mem_range, ← hker, LinearMap.mem_ker, Hom.hom_sub_toFun]
      simp only [LinearMap.sub_apply, commutatorHom_toFun_apply, map_sub, map_add]
      rw [toFun_d_apply, hquotk, hquotk, hkk x, sub_self])
  intro x
  refine ⟨ebar.toFun x, ?_⟩
  calc emb₂.toFun (ebar.toFun x) = emb₁.toFun (incl.toFun (ebar.toFun x)) := (hincl _).symm
    _ = emb₁.toFun (e.toFun x - (F₁.d ((σ.opLinearMap ∘ₗ kk.toLinearMap) x)
          + (σ.opLinearMap ∘ₗ kk.toLinearMap) (N.d x))) := by
        rw [hebar x, sub_commutatorHom_toFun_apply]
    _ = emb₁.toFun (e.toFun x)
          - (I.d (emb₁.toFun ((σ.opLinearMap ∘ₗ kk.toLinearMap) x))
            + emb₁.toFun ((σ.opLinearMap ∘ₗ kk.toLinearMap) (N.d x))) := by
        rw [map_sub, map_add, toFun_d_apply]
    _ = f.toFun x
          - (I.d (h x + emb₁.toFun ((σ.opLinearMap ∘ₗ kk.toLinearMap) x))
            + (h (N.d x) + emb₁.toFun ((σ.opLinearMap ∘ₗ kk.toLinearMap) (N.d x)))) := by
        rw [he' x, map_add]
        abel

/-- **Stacks 09KS, the inductive core.** Let `I` carry a decreasing filtration by stages `F i`,
embedded in `I` by `emb i`, with transition inclusions `incl i : F (i + 1) ⟶ F i` that are
admissible monomorphisms with graded pieces `quot i : F i ⟶ G i`, with `F 0 = I`, separated and
complete. If every graded piece `G i` is orthogonal on the right to the acyclic modules, so
is `I`. -/
theorem rightOrthogonal_acyclic_of_completeFiltration {I : DifferentialGradedModule A}
    (F : ℕ → DifferentialGradedModule A) (G : ℕ → DifferentialGradedModule A)
    (emb : ∀ i, F i ⟶ I) (incl : ∀ i, F (i + 1) ⟶ F i) (quot : ∀ i, F i ⟶ G i)
    (hemb : ∀ i, Function.Injective (emb i).toFun)
    (hincl : ∀ i x, (emb i).toFun ((incl i).toFun x) = (emb (i + 1)).toFun x)
    (hadm : ∀ i, IsAdmissibleMono (incl i))
    (hsurj : ∀ i, Function.Surjective (quot i).toFun)
    (hker : ∀ i, LinearMap.ker (quot i).toFun = LinearMap.range (incl i).toFun)
    (htop : Function.Surjective (emb 0).toFun)
    (hsep : ∀ x : I.M, (∀ i, ∃ y, (emb i).toFun y = x) → x = 0)
    (hcomplete : ∀ (n : ℤ) (x : ℕ → I.M), (∀ i, x i ∈ I.grading n) →
      (∀ i, ∃ y, y ∈ (F i).grading n ∧ x (i + 1) - x i = (emb i).toFun y) →
      ∃ z, z ∈ I.grading n ∧ ∀ i, ∃ y, y ∈ (F i).grading n ∧ z - x i = (emb i).toFun y)
    (hG : ∀ i, (acyclic' A).rightOrthogonal ((toHomotopyCategory A).obj (G i))) :
    (acyclic' A).rightOrthogonal ((toHomotopyCategory A).obj I) := by
  classical
  rw [rightOrthogonal_acyclic_iff]
  intro N hN f
  have hG' : ∀ i (e : N ⟶ G i), Homotopic e 0 :=
    fun i e => (rightOrthogonal_acyclic_iff (G i)).1 (hG i) N hN e
  -- the base case: the zero map is a null-homotopy modulo the whole module
  have hbase : (∀ (n : ℤ) (x : N.M), x ∈ N.grading n →
        (0 : N.M →ₗ[MulOpposite A.A] I.M) x ∈ I.grading (n - 1)) ∧
      ∀ x, ∃ y, (emb 0).toFun y = f.toFun x
        - (I.d ((0 : N.M →ₗ[MulOpposite A.A] I.M) x)
          + (0 : N.M →ₗ[MulOpposite A.A] I.M) (N.d x)) := by
    refine ⟨fun n x _ => by simp, fun x => ?_⟩
    obtain ⟨y, hy⟩ := htop (f.toFun x)
    exact ⟨y, by simpa using hy⟩
  -- the correction step, in the form the recursion consumes
  have step : ∀ (i : ℕ) (p : {hm : N.M →ₗ[MulOpposite A.A] I.M //
        (∀ (n : ℤ) (x : N.M), x ∈ N.grading n → hm x ∈ I.grading (n - 1)) ∧
        ∀ x, ∃ y, (emb i).toFun y = f.toFun x - (I.d (hm x) + hm (N.d x))}),
      ∃ q : {hm : N.M →ₗ[MulOpposite A.A] I.M //
          (∀ (n : ℤ) (x : N.M), x ∈ N.grading n → hm x ∈ I.grading (n - 1)) ∧
          ∀ x, ∃ y, (emb (i + 1)).toFun y = f.toFun x - (I.d (hm x) + hm (N.d x))},
        ∃ k : N.M →ₗ[MulOpposite A.A] (F i).M,
          (∀ (n : ℤ) (x : N.M), x ∈ N.grading n → k x ∈ (F i).grading (n - 1)) ∧
          ∀ x, q.1 x = p.1 x + (emb i).toFun (k x) := by
    intro i p
    obtain ⟨hm, hgr, hmod⟩ := p
    obtain ⟨k, hk, hk'⟩ := exists_homotopy_mod_next_stage (emb i) (emb (i + 1)) (incl i)
      (quot i) f (hemb i) (hincl i) (hadm i) (hsurj i) (hker i) (hG' i) hm hgr hmod
    refine ⟨⟨hm + (emb i).toGradedHom.opLinearMap ∘ₗ k, fun n x hx => ?_, fun x => ?_⟩,
      k, hk, fun x => rfl⟩
    · exact (I.grading (n - 1)).add_mem (hgr n x hx)
        ((emb i).map_grading (n - 1) _ (hk n x hx))
    · exact hk' x
  -- the tower of corrections
  let D : ∀ i, {hm : N.M →ₗ[MulOpposite A.A] I.M //
      (∀ (n : ℤ) (x : N.M), x ∈ N.grading n → hm x ∈ I.grading (n - 1)) ∧
      ∀ x, ∃ y, (emb i).toFun y = f.toFun x - (I.d (hm x) + hm (N.d x))} := fun i =>
    Nat.rec (motive := fun i => {hm : N.M →ₗ[MulOpposite A.A] I.M //
        (∀ (n : ℤ) (x : N.M), x ∈ N.grading n → hm x ∈ I.grading (n - 1)) ∧
        ∀ x, ∃ y, (emb i).toFun y = f.toFun x - (I.d (hm x) + hm (N.d x))})
      ⟨0, hbase⟩ (fun j hj => (step j hj).choose) i
  have hDdiff : ∀ i, ∃ k : N.M →ₗ[MulOpposite A.A] (F i).M,
      (∀ (n : ℤ) (x : N.M), x ∈ N.grading n → k x ∈ (F i).grading (n - 1)) ∧
      ∀ x, (D (i + 1)).1 x = (D i).1 x + (emb i).toFun (k x) :=
    fun i => (step i (D i)).choose_spec
  -- the corrections converge, one homogeneous piece at a time
  have huniq : ∀ (x : N.M) (z z' : I.M),
      (∀ i, ∃ y, z - (D i).1 x = (emb i).toFun y) →
      (∀ i, ∃ y, z' - (D i).1 x = (emb i).toFun y) → z = z' := by
    intro x z z' hz hz'
    have : z - z' = 0 := by
      refine hsep (z - z') fun i => ?_
      obtain ⟨y, hy⟩ := hz i
      obtain ⟨y', hy'⟩ := hz' i
      exact ⟨y - y', by rw [map_sub, ← hy, ← hy']; abel⟩
    rwa [sub_eq_zero] at this
  have hsum : ∀ (x x' : N.M) (z z' : I.M),
      (∀ i, ∃ y, z - (D i).1 x = (emb i).toFun y) →
      (∀ i, ∃ y, z' - (D i).1 x' = (emb i).toFun y) →
      ∀ i, ∃ y, z + z' - (D i).1 (x + x') = (emb i).toFun y := by
    intro x x' z z' hz hz' i
    obtain ⟨y, hy⟩ := hz i
    obtain ⟨y', hy'⟩ := hz' i
    refine ⟨y + y', ?_⟩
    rw [map_add, map_add, ← hy, ← hy']
    abel
  -- on a homogeneous element the corrections are glued by completeness
  have hglue : ∀ (n : ℤ) (x : N.M), x ∈ N.grading n →
      ∃ z ∈ I.grading (n - 1), ∀ i, ∃ y, z - (D i).1 x = (emb i).toFun y := by
    intro n x hx
    obtain ⟨z, hzmem, hz⟩ := hcomplete (n - 1) (fun i => (D i).1 x)
      (fun i => (D i).2.1 n x hx) (fun i => by
        obtain ⟨k, hk, hk'⟩ := hDdiff i
        exact ⟨k x, hk n x hx, by rw [hk' x]; abel⟩)
    exact ⟨z, hzmem, fun i => by obtain ⟨y, _, hy⟩ := hz i; exact ⟨y, hy⟩⟩
  have hex : ∀ x : N.M, ∃ z : I.M, ∀ i, ∃ y, z - (D i).1 x = (emb i).toFun y := by
    intro x
    induction x using DirectSum.Decomposition.inductionOn N.grading with
    | zero =>
        refine ⟨0, fun i => ⟨0, by rw [map_zero, map_zero, sub_zero]⟩⟩
    | @homogeneous n x =>
        obtain ⟨z, _, hz⟩ := hglue n (x : N.M) x.2
        exact ⟨z, hz⟩
    | add x x' hx hx' =>
        obtain ⟨z, hz⟩ := hx
        obtain ⟨z', hz'⟩ := hx'
        exact ⟨z + z', hsum _ _ _ _ hz hz'⟩
  have hspec : ∀ (x : N.M) (i : ℕ),
      ∃ y, (hex x).choose - (D i).1 x = (emb i).toFun y := fun x => (hex x).choose_spec
  have hgrH : ∀ (n : ℤ) (x : N.M), x ∈ N.grading n → (hex x).choose ∈ I.grading (n - 1) := by
    intro n x hx
    obtain ⟨z, hzmem, hz⟩ := hglue n x hx
    rwa [huniq x _ _ (hspec x) hz]
  have hHadd : ∀ x y : N.M, (hex (x + y)).choose = (hex x).choose + (hex y).choose := by
    intro x y
    exact huniq (x + y) _ _ (hspec (x + y)) (hsum _ _ _ _ (hspec x) (hspec y))
  have hHsmul : ∀ (c : A.Aᵐᵒᵖ) (x : N.M), (hex (c • x)).choose = c • (hex x).choose := by
    intro c x
    refine huniq (c • x) _ _ (hspec (c • x)) fun i => ?_
    obtain ⟨w, hw⟩ := hspec x i
    refine ⟨c • w, ?_⟩
    calc c • (hex x).choose - (D i).1 (c • x)
        = c • ((hex x).choose - (D i).1 x) := by rw [map_smul, smul_sub]
      _ = c • (emb i).toFun w := by rw [hw]
      _ = (emb i).toFun (c • w) := by
          rw [← MulOpposite.op_unop c]
          exact ((emb i).map_smul w c.unop).symm
  refine ⟨{
    toLinearMap :=
      { toFun := fun x => (hex x).choose
        map_add' := hHadd
        map_smul' := hHsmul }
    map_grading := hgrH
    homotopy_eq := ?_ }⟩
  intro x
  rw [Hom.hom_zero_toFun]
  simp only [LinearMap.zero_apply, sub_zero, LinearMap.coe_mk, AddHom.coe_mk]
  -- the glued map is a genuine null-homotopy, by separatedness
  have hzero : f.toFun x - (I.d ((hex x).choose) + (hex (N.d x)).choose) = 0 := by
    refine hsep _ fun i => ?_
    obtain ⟨y, hy⟩ := (D i).2.2 x
    obtain ⟨w, hw⟩ := hspec x i
    obtain ⟨w', hw'⟩ := hspec (N.d x) i
    refine ⟨y - ((F i).d w + w'), ?_⟩
    calc (emb i).toFun (y - ((F i).d w + w'))
        = (emb i).toFun y - (I.d ((emb i).toFun w) + (emb i).toFun w') := by
          rw [map_sub, map_add, toFun_d_apply]
      _ = (f.toFun x - (I.d ((D i).1 x) + (D i).1 (N.d x)))
            - (I.d ((hex x).choose - (D i).1 x)
              + ((hex (N.d x)).choose - (D i).1 (N.d x))) := by
          rw [hy, hw, hw']
      _ = f.toFun x - (I.d ((hex x).choose) + (hex (N.d x)).choose) := by
          rw [map_sub]
          abel
  rw [← sub_eq_zero]
  exact hzero

end DifferentialGradedModule

end
