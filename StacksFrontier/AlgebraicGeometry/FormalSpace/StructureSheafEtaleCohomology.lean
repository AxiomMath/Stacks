module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Module.AmitsurAcyclic
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSurjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallEtaleSite.McQuillanAffineEtale

/-!
# Étale cohomology of the structure sheaf of a countably indexed affine formal algebraic space

Let `X = Spf A` be a countably indexed affine formal algebraic space, so that `A` is weakly
admissible with a countable fundamental system `J₀ ⊇ J₁ ⊇ ⋯` of weak ideals of definition, and
let `{U ⟶ X}` be a covering of `X` in the affine étale site.  By Stacks 0DEE and Stacks 0DEF the
chart is `U = Spf B^∧` for an étale ring map `A → B`, and by Stacks 0AN9 the map `A → B` is
faithfully flat.  The sections of `𝒪_X` over the `(p+1)`-fold self fibre product of `U` over `X`
are the completion `(B^{⊗ p+1})^∧ = lim_k B^{⊗ p+1} ⧸ Jₖ B^{⊗ p+1}`, so the Čech complex of
`𝒪_X` for this covering is the inverse limit over `k` of the Amitsur complexes of `A → B` with
coefficients in `A ⧸ Jₖ`.  This file proves that that inverse limit has no cohomology in positive
degrees, which is the content of Stacks 0DEL.

The two inputs are the acyclicity of the Amitsur complex of a faithfully flat algebra with
arbitrary coefficients, Stacks 023M, and a Mittag-Leffler argument: the transition maps of a
sequential system of acyclic complexes are surjective, so a compatible family of cocycles can be
written as the coboundary of a compatible family.  Countability of the fundamental system enters
exactly here, as the source's proof says.

## Main definitions

* `AlgebraicTopology.amitsurExtendedCochainComplex.mapCoeff`: the extended Amitsur cochain
  complex is functorial in the coefficient module.
* `Stacks.CochainComplexLimit.complex`: the inverse limit of a sequence of cochain complexes of
  modules, formed degreewise from the compatible families.
* `AlgebraicGeometry.FormalSpace.stageCechComplex` and
  `AlgebraicGeometry.FormalSpace.stageCechTransition`: the Amitsur complex of `A → B` with
  coefficients in `A ⧸ Jₖ`, and its transition maps.
* `AlgebraicGeometry.FormalSpace.completedCechComplex`: the Čech complex of `𝒪_X` for the
  covering `{Spf B^∧ ⟶ Spf A}`, that is, the inverse limit of the stage complexes.

## Main results

* `Stacks.CochainComplexLimit.exists_compatible_preimage`: the Mittag-Leffler argument.
* `AlgebraicGeometry.FormalSpace.completedCechComplex_exactAt` and
  `AlgebraicGeometry.FormalSpace.completedCechComplex_homology_isZero`: **Stacks 0DEL** — the
  Čech complex of `𝒪_X` for a covering of a countably indexed affine formal algebraic space by
  one affine étale chart is exact in every positive Čech degree, so that covering has no higher
  Čech cohomology for `𝒪_X`.
* `AlgebraicGeometry.FormalSpace.exists_antitone_isWeakIdealOfDefinition_hasBasis`: a weakly
  admissible ring whose neighbourhood filter of `0` is countably generated has an antitone
  fundamental system of weak ideals of definition.
* `AlgebraicGeometry.FormalSpace.completedCechComplex_homology_isZero_of_isSurjective` and
  `AlgebraicGeometry.FormalSpace.exists_completedCechComplex_homology_isZero_of_isCountablyIndexed`:
  the same vanishing with the source's own geometric hypotheses in place of the antitone
  sequence and the faithful flatness, namely a countably indexed affine formal algebraic space
  `X` and a covering `{Spf B^∧ ⟶ Spf A}` of it by one affine étale chart.

## Implementation notes

*What is carried, and what is not.*  Stacks 0DEL asserts `Hⁿ(X_étale, 𝒪_X) = 0` for `n > 0`.  Its
proof has two halves: a site-theoretic reduction of the sheaf cohomology to the Čech cohomology
of the coverings of the affine étale site (Stacks 03F9, Stacks 03OZ, Stacks 0DEE, Stacks 0DEF),
and the computation that those Čech complexes are acyclic in positive degrees (Stacks 023M,
Stacks 0AS0).  The computation is carried here, together with the reduction of the source's
geometric hypotheses to the hypotheses of that computation; the reduction of the sheaf
cohomology to the Čech complexes is not, and the tag attributes below are qualified
accordingly.  The reason is that this library has no structure sheaf on the étale site of a
formal algebraic space: the affine étale site of `X` exists, as the affine étale site of the
reduction `X_red`, and Stacks 0DEE identifies it with the category of the affine formal
algebraic spaces representable étale over `X`
(`AlgebraicGeometry.FormalSpace.affineEtaleEquivalence`), but Stacks 0DEF is formalized only as
the ring-theoretic category of the completions `B^∧`, with no functor to that category, so no
object of `(X_{affine,étale})^{opp}` is known to be of the form `Spf B^∧` and the sections of
`𝒪_X` cannot be defined.  So the reduction has nothing to be stated about, while the computation is
unconditional.

*Hypotheses.*  Beyond "`X` is a countably indexed affine formal algebraic space" nothing is
assumed, and in fact less is: the fundamental system of weak ideals of definition is replaced by
an arbitrary antitone sequence of ideals `J : ℕ → Ideal A`, and the étale covering `A → B` by an
arbitrary faithfully flat `A`-algebra `B`.  Weak admissibility of `A`, étaleness of `A → B` and
surjectivity of `Spf B^∧ ⟶ Spf A` are used in the source only to produce the sequence `Jₖ` and
the faithful flatness of `A → B` (Stacks 0AN9), so dropping them generalizes the statement.
That those implications hold is proved in the last section: a countably indexed affine formal
algebraic space is the formal spectrum of a weakly admissible ring with a countable fundamental
system of weak ideals of definition, and an affine étale chart whose structure morphism is
surjective has a faithfully flat underlying ring map.

*Indexing.*  `AlgebraicTopology.amitsurExtendedCochainComplex A B M` is the extended complex
`M → B ⊗[A] M → B ⊗[A] B ⊗[A] M → ⋯` placed in degrees `0, 1, 2, …`, so the Čech complex proper
begins in degree `1` and the `n`-th Čech cohomology of the covering is the cohomology of the
extended complex in degree `n + 1`.  Positive Čech degrees are therefore degrees `≥ 2`.

## References

* [Stacks Project, Tag 0DEL](https://stacks.math.columbia.edu/tag/0DEL)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 0AS0](https://stacks.math.columbia.edu/tag/0AS0)
* [Stacks Project, Tag 0AIJ](https://stacks.math.columbia.edu/tag/0AIJ)
* [Stacks Project, Tag 0AN9](https://stacks.math.columbia.edu/tag/0AN9)
* [Stacks Project, Tag 0DEE](https://stacks.math.columbia.edu/tag/0DEE)
* [Stacks Project, Tag 0DEF](https://stacks.math.columbia.edu/tag/0DEF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

namespace AlgebraicTopology

/-! ### Functoriality of the extended Amitsur complex in the coefficient module -/

section Extended

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A morphism of augmented cosimplicial objects, together with a compatible morphism of the
objects extending them on the left, induces a morphism of the extended alternating coface map
complexes. -/
def extendedAlternatingCofaceMapComplex.map {X X' : CosimplicialObject.Augmented C} (Φ : X ⟶ X')
    {Y Y' : C} (e : Y ⟶ X.left) (e' : Y' ⟶ X'.left) (ψ : Y ⟶ Y')
    (hψ : ψ ≫ e' = e ≫ Φ.left) :
    extendedAlternatingCofaceMapComplex X Y e ⟶
      extendedAlternatingCofaceMapComplex X' Y' e' where
  f n := match n with
    | 0 => ψ
    | (n + 1) => ((alternatingCofaceMapComplex C).map Φ.right).f n
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    match i with
    | 0 =>
      change ψ ≫ (e' ≫ X'.hom.app (.mk 0)) = (e ≫ X.hom.app (.mk 0)) ≫ Φ.right.app (.mk 0)
      rw [← Category.assoc, hψ, Category.assoc, Category.assoc,
        CosimplicialObject.Augmented.w_app]
    | (i + 1) =>
      exact ((alternatingCofaceMapComplex C).map Φ.right).comm i (i + 1)

end Extended

section Coefficients

variable (R : Type u) (A : Type v) {M : Type w} {N : Type w} [CommRing R] [CommRing A]
  [Algebra R A] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A linear map of coefficient modules induces a natural transformation of the functors
`- ⊗[R] M` of `AlgebraicTopology.tensorModuleFunctor`. -/
def tensorModuleFunctor.mapCoeff {S : Type*} [CommRing S] [Module S M] [Module S N]
    (φ : M →ₗ[S] N) :
    tensorModuleFunctor.{_, v, w} S M ⟶ tensorModuleFunctor.{_, v, w} S N where
  app T := ModuleCat.ofHom (LinearMap.lTensor T φ)
  naturality T T' f := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext s m
    rfl

/-- A linear map of `R`-modules read as a linear map over the universe lift of `R`. -/
def amitsurAugmentation.liftCoeff (φ : M →ₗ[R] N) : M →ₗ[ULift.{v} R] N where
  toFun := φ
  map_add' := φ.map_add
  map_smul' r x := φ.map_smul r.down x

/-- A linear map of coefficient modules induces a morphism of the augmented cosimplicial objects
of `AlgebraicTopology.amitsurAugmentation`. -/
noncomputable def amitsurAugmentation.mapCoeff (φ : M →ₗ[R] N) :
    amitsurAugmentation R A M ⟶ amitsurAugmentation R A N :=
  ((CosimplicialObject.Augmented.whiskering _ _).map
    (Functor.whiskerRight
      (tensorModuleFunctor.mapCoeff
        (amitsurAugmentation.liftCoeff R φ : M →ₗ[ULift.{v} R] N))
      (ModuleCat.restrictScalars (algebraMap R (ULift.{v} R))))).app _

/-- The extended Amitsur cochain complex is functorial in the coefficient module: a linear map
`M →ₗ[R] N` induces a morphism of complexes
`(M → A ⊗[R] M → ⋯) ⟶ (N → A ⊗[R] N → ⋯)`, in degree `0` the given map and in degree `n + 1`
the map induced on `(A/R)ₙ ⊗[R] -`. -/
noncomputable def amitsurExtendedCochainComplex.mapCoeff (φ : M →ₗ[R] N) :
    amitsurExtendedCochainComplex R A M ⟶ amitsurExtendedCochainComplex R A N :=
  extendedAlternatingCofaceMapComplex.map (amitsurAugmentation.mapCoeff R A φ) _ _
    (ModuleCat.ofHom (R := R)
      (ULift.moduleEquiv.symm.toLinearMap ∘ₗ φ ∘ₗ
        (ULift.moduleEquiv : ULift.{max u v} M ≃ₗ[R] M).toLinearMap))
    (by
      apply ModuleCat.hom_ext
      ext x
      rfl)

/-- A surjective map of coefficient modules induces a surjection in every degree. -/
lemma amitsurExtendedCochainComplex.mapCoeff_f_surjective (φ : M →ₗ[R] N)
    (hφ : Function.Surjective φ) (n : ℕ) :
    Function.Surjective ((amitsurExtendedCochainComplex.mapCoeff R A φ).f n).hom := by
  match n with
  | 0 =>
    intro y
    refine ⟨ULift.up (Function.invFun φ y.down), ?_⟩
    change ULift.up (φ (Function.invFun φ y.down)) = y
    rw [Function.invFun_eq (hφ y.down)]
    rfl
  | (n + 1) =>
    change Function.Surjective ((amitsurAugmentation.mapCoeff R A φ).right.app (.mk n)).hom
    exact LinearMap.lTensor_surjective _ hφ

end Coefficients

end AlgebraicTopology

namespace Stacks.CochainComplexLimit

/-! ### Inverse limits of sequences of cochain complexes of modules -/

variable {A : Type u} [CommRing A] (K : ℕ → CochainComplex (ModuleCat.{u} A) ℕ)
  (t : ∀ k, K (k + 1) ⟶ K k)

/-- The degree-`p` part of the inverse limit of a sequence of cochain complexes: the families
`x k : (K k).X p` compatible with the transition maps. -/
def sections (p : ℕ) : Submodule A (∀ k, (K k).X p) where
  carrier := {x | ∀ k, ((t k).f p).hom (x (k + 1)) = x k}
  add_mem' hx hy k := by
    change ((t k).f p).hom (_ + _) = _
    rw [map_add, hx k, hy k]
    rfl
  zero_mem' k := by
    change ((t k).f p).hom 0 = 0
    rw [map_zero]
  smul_mem' c x hx k := by
    change ((t k).f p).hom (c • _) = _
    rw [map_smul, hx k]
    rfl

/-- The transition maps commute with the differentials, in applied form. -/
lemma transition_d_apply (k m : ℕ) (y : (K (k + 1)).X m) :
    ((K k).d m (m + 1)).hom (((t k).f m).hom y) =
      ((t k).f (m + 1)).hom (((K (k + 1)).d m (m + 1)).hom y) := by
  have h := congrArg ModuleCat.Hom.hom ((t k).comm m (m + 1))
  simp only [ModuleCat.hom_comp] at h
  exact congr($h y)

/-- Two consecutive differentials of a term of the sequence compose to zero, in applied form. -/
lemma d_d_apply (k m : ℕ) (y : (K k).X m) :
    ((K k).d (m + 1) (m + 2)).hom (((K k).d m (m + 1)).hom y) = 0 := by
  have h := congrArg ModuleCat.Hom.hom ((K k).d_comp_d m (m + 1) (m + 2))
  simp only [ModuleCat.hom_comp] at h
  exact congr($h y)

/-- The differential of the inverse limit complex: the differentials of the terms, applied
componentwise. -/
def differential (p : ℕ) : sections K t p →ₗ[A] sections K t (p + 1) where
  toFun x := ⟨fun k => ((K k).d p (p + 1)).hom (x.1 k), fun k => by
    rw [← transition_d_apply K t k p (x.1 (k + 1)), x.2 k]⟩
  map_add' x y := by
    refine Subtype.ext (funext fun k => ?_)
    change ((K k).d p (p + 1)).hom (x.1 k + y.1 k) = _
    rw [map_add]
    rfl
  map_smul' c x := by
    refine Subtype.ext (funext fun k => ?_)
    change ((K k).d p (p + 1)).hom (c • x.1 k) = _
    rw [map_smul]
    rfl

/-- The inverse limit of a sequence of cochain complexes of modules, formed degreewise from the
families compatible with the transition maps. -/
noncomputable def complex : CochainComplex (ModuleCat.{u} A) ℕ :=
  CochainComplex.of (fun p => ModuleCat.of A (sections K t p))
    (fun p => ModuleCat.ofHom (differential K t p)) fun p => by
      apply ModuleCat.hom_ext
      refine LinearMap.ext fun x => Subtype.ext (funext fun k => ?_)
      exact d_d_apply K k p (x.1 k)

/-- The differential of the inverse limit complex is `Stacks.CochainComplexLimit.differential`. -/
lemma complex_d (p : ℕ) :
    (complex K t).d p (p + 1) = ModuleCat.ofHom (differential K t p) := by
  simp [complex]

/-- **Mittag-Leffler.** Let `K 0, K 1, …` be cochain complexes of modules with transition maps
`t k : K (k + 1) ⟶ K k`, each `K k` exact in positive degrees, and let the transition maps be
surjective in degree `p`.  Then a compatible family of cocycles in degree `p + 2` is the
coboundary of a compatible family in degree `p + 1`. -/
theorem exists_compatible_preimage (p : ℕ)
    (hexact : ∀ (k m : ℕ) (z : (K k).X (m + 1)), ((K k).d (m + 1) (m + 2)).hom z = 0 →
      ∃ y : (K k).X m, ((K k).d m (m + 1)).hom y = z)
    (hsurj : ∀ k, Function.Surjective ((t k).f p).hom)
    (x : ∀ k, (K k).X (p + 2))
    (hx : ∀ k, ((t k).f (p + 2)).hom (x (k + 1)) = x k)
    (hz : ∀ k, ((K k).d (p + 2) (p + 3)).hom (x k) = 0) :
    ∃ y : ∀ k, (K k).X (p + 1), (∀ k, ((t k).f (p + 1)).hom (y (k + 1)) = y k) ∧
      ∀ k, ((K k).d (p + 1) (p + 2)).hom (y k) = x k := by
  classical
  have step : ∀ (k : ℕ) (y : (K k).X (p + 1)), ((K k).d (p + 1) (p + 2)).hom y = x k →
      ∃ y' : (K (k + 1)).X (p + 1), ((K (k + 1)).d (p + 1) (p + 2)).hom y' = x (k + 1) ∧
        ((t k).f (p + 1)).hom y' = y := by
    intro k y hy
    obtain ⟨y₀, hy₀⟩ := hexact (k + 1) (p + 1) (x (k + 1)) (hz (k + 1))
    have h1 : ((K k).d (p + 1) (p + 2)).hom (((t k).f (p + 1)).hom y₀) = x k := by
      rw [transition_d_apply K t k (p + 1) y₀, hy₀, hx k]
    obtain ⟨w, hw⟩ := hexact k p (y - ((t k).f (p + 1)).hom y₀) (by
      rw [map_sub, hy, h1, sub_self])
    obtain ⟨w', hw'⟩ := hsurj k w
    refine ⟨y₀ + ((K (k + 1)).d p (p + 1)).hom w', ?_, ?_⟩
    · rw [map_add, hy₀, d_d_apply K (k + 1) p w', add_zero]
    · rw [map_add, ← transition_d_apply K t k p w', hw', hw, add_sub_cancel]
  choose Z hZ₁ hZ₂ using step
  obtain ⟨y₀, hy₀⟩ := hexact 0 (p + 1) (x 0) (hz 0)
  let Y : ∀ k, { y : (K k).X (p + 1) // ((K k).d (p + 1) (p + 2)).hom y = x k } := fun k =>
    Nat.rec (motive := fun k => { y : (K k).X (p + 1) //
        ((K k).d (p + 1) (p + 2)).hom y = x k })
      ⟨y₀, hy₀⟩ (fun k ih => ⟨Z k ih.1 ih.2, hZ₁ k ih.1 ih.2⟩) k
  refine ⟨fun k => (Y k).1, fun k => ?_, fun k => (Y k).2⟩
  change ((t k).f (p + 1)).hom (Z k (Y k).1 (Y k).2) = (Y k).1
  exact hZ₂ k (Y k).1 (Y k).2

/-- The differential of the inverse limit complex, in applied form. -/
private lemma complex_d_hom_apply (p : ℕ) (x : sections K t p) :
    ((complex K t).d p (p + 1)).hom x = differential K t p x := by
  rw [complex_d]
  rfl

/-- Exactness of a complex of modules in degree `m + 1`, in elementwise form. -/
private lemma exactAt_succ_iff_forall (C : CochainComplex (ModuleCat.{u} A) ℕ) (m : ℕ) :
    C.ExactAt (m + 1) ↔ ∀ z : C.X (m + 1), (C.d (m + 1) (m + 2)).hom z = 0 →
      ∃ y : C.X m, (C.d m (m + 1)).hom y = z := by
  rw [HomologicalComplex.exactAt_iff' C m (m + 1) (m + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  rfl

/-- Exactness of the inverse limit complex in degree `p + 2`, under the hypotheses of
`Stacks.CochainComplexLimit.exists_compatible_preimage`. -/
theorem exactAt (p : ℕ)
    (hexact : ∀ (k m : ℕ) (z : (K k).X (m + 1)), ((K k).d (m + 1) (m + 2)).hom z = 0 →
      ∃ y : (K k).X m, ((K k).d m (m + 1)).hom y = z)
    (hsurj : ∀ k, Function.Surjective ((t k).f p).hom) :
    (complex K t).ExactAt (p + 2) := by
  rw [exactAt_succ_iff_forall]
  intro x hx
  have hx' : differential K t (p + 2) x = 0 := (complex_d_hom_apply K t (p + 2) x).symm.trans hx
  obtain ⟨y, hcompat, hy⟩ := exists_compatible_preimage K t p hexact hsurj (fun k => x.1 k) x.2
    fun k => congrArg (fun z : sections K t (p + 3) => z.1 k) hx'
  exact ⟨⟨y, hcompat⟩, (complex_d_hom_apply K t (p + 1) _).trans (Subtype.ext (funext hy))⟩

end Stacks.CochainComplexLimit

namespace AlgebraicGeometry.FormalSpace

/-! ### The Čech complex of the structure sheaf on an affine étale chart -/

open AlgebraicTopology

section Cech

variable {A : Type u} [CommRing A] (B : Type u) [CommRing B] [Algebra A B] (J : ℕ → Ideal A)

/-- The `k`-th stage of the Čech complex of `𝒪_X` for the covering `{Spf B^∧ ⟶ Spf A}`: the
extended Amitsur complex of `A → B` with coefficients in `A ⧸ Jₖ`, namely
`A ⧸ Jₖ → B ⧸ Jₖ B → (B ⊗[A] B) ⧸ Jₖ (B ⊗[A] B) → ⋯`. -/
noncomputable abbrev stageCechComplex (k : ℕ) : CochainComplex (ModuleCat.{u} A) ℕ :=
  amitsurExtendedCochainComplex A B (A ⧸ J k)

variable (hJ : Antitone J)

/-- The transition map `A ⧸ J (k + 1) → A ⧸ J k` of an antitone sequence of ideals. -/
def stageQuotientMap (k : ℕ) : A ⧸ J (k + 1) →ₗ[A] A ⧸ J k :=
  Submodule.mapQ _ _ LinearMap.id (by simpa using hJ (Nat.le_succ k))

/-- The transition maps of the quotients by an antitone sequence of ideals are surjective. -/
lemma stageQuotientMap_surjective (k : ℕ) : Function.Surjective (stageQuotientMap J hJ k) := by
  intro y
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (J k) y
  exact ⟨Submodule.Quotient.mk a, Submodule.mapQ_apply _ _ _ _⟩

/-- The transition map of the stage complexes, induced by `A ⧸ J (k + 1) → A ⧸ J k`. -/
noncomputable def stageCechTransition (k : ℕ) :
    stageCechComplex B J (k + 1) ⟶ stageCechComplex B J k :=
  amitsurExtendedCochainComplex.mapCoeff A B (stageQuotientMap J hJ k)

/-- The Čech complex of `𝒪_X` for the covering `{Spf B^∧ ⟶ Spf A}` of the countably indexed
affine formal algebraic space `X = Spf A`: the inverse limit of the stage complexes, whose
degree-`p + 1` term is `(B^{⊗ p+1})^∧ = lim_k B^{⊗ p+1} ⧸ Jₖ B^{⊗ p+1}`. -/
noncomputable def completedCechComplex : CochainComplex (ModuleCat.{u} A) ℕ :=
  Stacks.CochainComplexLimit.complex (stageCechComplex B J) (stageCechTransition B J hJ)

/-- Let `X = Spf A` be a countably indexed affine formal algebraic space, with `J₀ ⊇ J₁ ⊇ ⋯` a
countable fundamental system of weak ideals of definition of `A`, and let `{Spf B^∧ ⟶ Spf A}` be
a covering in the affine étale site, so that `A → B` is faithfully flat.  Then the Čech complex
of `𝒪_X` for this covering is exact in every positive Čech degree. -/
theorem completedCechComplex_exactAt [Module.FaithfullyFlat A B] (n : ℕ) (hn : 0 < n) :
    (completedCechComplex B J hJ).ExactAt (n + 1) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  refine Stacks.CochainComplexLimit.exactAt _ _ p (fun k m z hzz => ?_) fun k => ?_
  · exact (Stacks.CochainComplexLimit.exactAt_succ_iff_forall _ m).mp
      (Stacks.Descent.amitsurExtendedCochainComplex_acyclic_of_faithfullyFlat A B (A ⧸ J k)
        (m + 1)) z hzz
  · exact amitsurExtendedCochainComplex.mapCoeff_f_surjective A B _
      (stageQuotientMap_surjective J hJ k) p

/-- **Stacks 0DEL.**  Let `X = Spf A` be a countably indexed affine formal algebraic space, with
`J₀ ⊇ J₁ ⊇ ⋯` a countable fundamental system of weak ideals of definition of `A`, and let
`{Spf B^∧ ⟶ Spf A}` be a covering in the affine étale site, so that `A → B` is faithfully flat.
Then `Ȟⁿ({Spf B^∧ ⟶ Spf A}, 𝒪_X) = 0` for `n > 0`. -/
@[stacks 0DEL "the computation half of the proof: for a covering of `X = Spf A` by one affine \
étale chart `Spf B^∧` the Čech cohomology of `𝒪_X` vanishes in every positive degree.  The \
site-theoretic half, the reduction of `Hⁿ(X_étale, 𝒪_X)` to these Čech complexes along Stacks \
03F9, 03OZ, 0DEE and 0DEF, is not carried: this library does have the étale sites of a formal \
algebraic space, `AlgebraicGeometry.FormalSpace.SmallEtale` and its siblings of Stacks 0DEA, \
and Stacks 0DEE as an equivalence, \
AlgebraicGeometry.FormalSpace.affineEtaleEquivalence, but no structure sheaf on an étale site; \
Stacks 0DEF is formalized only as the ring-theoretic category of the completions `B^∧`.  \
Stated for an arbitrary antitone \
sequence of ideals and an arbitrary faithfully flat `A`-algebra, which generalizes the \
source's weakly admissible `A` and étale covering `A → B`"]
theorem completedCechComplex_homology_isZero [Module.FaithfullyFlat A B] (n : ℕ) (hn : 0 < n) :
    IsZero ((completedCechComplex B J hJ).homology (n + 1)) :=
  ((completedCechComplex B J hJ).exactAt_iff_isZero_homology (n + 1)).mp
    (completedCechComplex_exactAt B J hJ n hn)

end Cech

/-! ### From a countably indexed affine formal algebraic space and an étale covering -/

/-- In a weakly admissible linearly topologized ring whose neighbourhood filter of `0` is
countably generated, the weak ideals of definition contain an antitone sequence
`J₀ ⊇ J₁ ⊇ ⋯` which is again a fundamental system of neighbourhoods of `0`. -/
theorem exists_antitone_isWeakIdealOfDefinition_hasBasis {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hcount : (nhds (0 : A)).IsCountablyGenerated) :
    ∃ J : ℕ → Ideal A, Antitone J ∧
      (∀ k, TopologicalRing.IsWeakIdealOfDefinition (J k)) ∧
      (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun k ↦ (J k : Set A) := by
  obtain ⟨U, hU⟩ := Filter.isCountablyGenerated_iff_exists_antitone_basis.mp hcount
  choose I hI hIU using fun n ↦
    (TopologicalRing.hasBasis_nhds_zero_isWeakIdealOfDefinition hA).mem_iff.mp (hU.mem n)
  let J : ℕ → Ideal A := fun n ↦ Nat.rec (I 0) (fun n Jn ↦ Jn ⊓ I (n + 1)) n
  have hJwid : ∀ k, TopologicalRing.IsWeakIdealOfDefinition (J k) := by
    intro k
    induction k with
    | zero => exact hI 0
    | succ n ih =>
      exact TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right ih (hI (n + 1)).1
  have hJle : ∀ k, J k ≤ I k := by
    intro k
    match k with
    | 0 => exact le_rfl
    | (n + 1) => exact inf_le_right
  refine ⟨J, antitone_nat_of_succ_le fun n ↦ inf_le_left, hJwid, Filter.hasBasis_iff.mpr ?_⟩
  intro t
  refine ⟨fun ht ↦ ?_, ?_⟩
  · obtain ⟨n, hn⟩ := hU.mem_iff.mp ht
    exact ⟨n, trivial, fun x hx ↦ hn (hIU n (hJle n hx))⟩
  · rintro ⟨n, -, hn⟩
    exact Filter.mem_of_superset ((hJwid n).1.mem_nhds (J n).zero_mem) hn

/-- Let `A` be a weakly admissible topological ring, let `J : ℕ → Ideal A` be antitone and let
`B^∧` be the completion over `A` of an étale `A`-algebra `B`, presented by quotient systems so
that the morphism `Spf B^∧ ⟶ Spf A` of formal spectra is defined.  If that morphism is
surjective then the Čech complex of `𝒪_X` for the covering `{Spf B^∧ ⟶ Spf A}` of `X = Spf A`
has no cohomology in positive Čech degrees.

Surjectivity of `Spf B^∧ ⟶ Spf A` is faithful flatness of `A → B` by Stacks 0AN9, which is the
hypothesis of `AlgebraicGeometry.FormalSpace.completedCechComplex_homology_isZero`. -/
theorem completedCechComplex_homology_isZero_of_isSurjective (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] (hA : TopologicalRing.IsWeaklyAdmissible A)
    (J : ℕ → Ideal A) (hJ : Antitone J) (Y : EtaleCompletion A)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS Y.completion)
    (g : ContinuousHom D E) (hg : g.toRingHom = Y.structureMap)
    (hcov : IsSurjective B S hS (formalSpectrumMap hA g)) (n : ℕ) (hn : 0 < n) :
    letI : Algebra A Y.carrier := Y.str.toAlgebra
    IsZero ((completedCechComplex Y.carrier J hJ).homology (n + 1)) := by
  let : Algebra A Y.carrier := Y.str.toAlgebra
  have hff : Y.str.FaithfullyFlat :=
    ((etaleFormalSpectrumMap_surjective_tfae B S hS Y.str Y.etale hA D E g hg).out 1 2).mp hcov
  have : Module.FaithfullyFlat A Y.carrier := hff
  exact completedCechComplex_homology_isZero Y.carrier J hJ n hn

/-- **Stacks 0DEL** with the hypotheses of the source.  A countably indexed affine formal
algebraic space `X` is the formal spectrum of a weakly admissible topological ring `A` carrying
a countable antitone fundamental system `J₀ ⊇ J₁ ⊇ ⋯` of weak ideals of definition, and for
every covering `{Spf B^∧ ⟶ Spf A}` of `X` by one affine étale chart, in the sense of Stacks
0DEF and with `Spf B^∧ ⟶ Spf A` surjective, the Čech complex of `𝒪_X` for that covering has no
cohomology in positive Čech degrees.

Affineness of `X` is not assumed: it is part of the conclusion, `X` being exhibited as a formal
spectrum. -/
@[stacks 0DEL "the covering-level content with the source's own hypotheses: a countably indexed \
affine formal algebraic space and a surjective affine étale chart of it, in place of the \
antitone sequence of ideals and the faithfully flat algebra of \
`completedCechComplex_homology_isZero`.  The conclusion is still the vanishing of the Čech \
cohomology of the covering, not of `Hⁿ(X_étale, 𝒪_X)`: this library has no structure sheaf on \
the étale site of a formal algebraic space: Stacks 0DEE is an equivalence here, \
AlgebraicGeometry.FormalSpace.affineEtaleEquivalence, but Stacks 0DEF is formalized only as \
the ring-theoretic category of the completions `B^∧`, so no object \
of the affine étale site is known to be of the form `Spf B^∧` and the sections of `𝒪_X` are \
undefined"]
theorem exists_completedCechComplex_homology_isZero_of_isCountablyIndexed
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X : FppfSheaf B S hS}
    (hc : IsCountablyIndexed B S hS X) :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsLinearTopology A A) (hA : TopologicalRing.IsWeaklyAdmissible A)
      (Q : QuotientSystem B S hS A) (J : ℕ → Ideal A) (hJ : Antitone J),
      (∀ k, TopologicalRing.IsWeakIdealOfDefinition (J k)) ∧
        (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True) (fun k ↦ (J k : Set A)) ∧
        Nonempty (X ≅ formalSpectrum Q) ∧
        ∀ (Y : EtaleCompletion A) (E : QuotientSystem B S hS Y.completion)
          (g : ContinuousHom Q E), g.toRingHom = Y.structureMap →
          IsSurjective B S hS (formalSpectrumMap hA g) → ∀ n : ℕ, 0 < n →
            letI : Algebra A Y.carrier := Y.str.toAlgebra
            IsZero ((completedCechComplex Y.carrier J hJ).homology (n + 1)) := by
  obtain ⟨A, hCR, hTS, hTR, hLT, Q, hWA, hcount, he⟩ :=
    exists_quotientSystem_of_isCountablyIndexed B S hS hc
  obtain ⟨J, hJmono, hJwid, hJbasis⟩ :=
    exists_antitone_isWeakIdealOfDefinition_hasBasis hWA hcount
  exact ⟨A, hCR, hTS, hTR, hLT, hWA, Q, J, hJmono, hJwid, hJbasis, he,
    fun Y E g hg hcov n hn ↦
      completedCechComplex_homology_isZero_of_isSurjective B S hS hWA J hJmono Y Q E g hg
        hcov n hn⟩

end AlgebraicGeometry.FormalSpace

end
