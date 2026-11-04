module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.MvPolynomial.Expand
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.AlphaPCover
public import StacksFrontier.AlgebraicGeometry.Etale.TopologicalProperties.RelativeFrobenius
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.RelativeUniversalHomeomorphism

/-!
# The relative Frobenius of a smooth morphism is an iterated `α_p`-cover

Let `S₀` be a scheme in characteristic `p` and let `X` be an `S₀`-scheme which is smooth of
relative dimension `d`.  This module proves that the relative Frobenius
`F_{X/S₀} : X ⟶ X^{(1)}` is an iterated `α_p`-cover and that it has constant degree `p ^ d`.

The argument is the source's.  Smoothness of relative dimension `d` makes `X` étale over affine
`d`-space locally on `S₀`, so around any point the relative Frobenius of `X/S₀` sits in a square

```
X                 ⟶  X^{(1)}
↓                     ↓
𝔸^d_{S₀}          ⟶  (𝔸^d_{S₀})^{(1)}
```

whose lower arrow is the relative Frobenius of affine `d`-space, which raises each coordinate to
its `p`-th power.  On rings that arrow is `MvPolynomial.expand p`, which factors as the `d`-fold
composition of the maps raising one variable at a time to its `p`-th power, and each of those is
an `α_p`-cover: adjoining a `p`-th root of one variable to the polynomial ring in the others is
exactly `C[z]/(z ^ p - c)` for `c` that variable.  The same factorisation exhibits a basis of
`p ^ d` monomials, which is the degree.  The square is a fibre square because the relative
Frobenius of an étale morphism is an isomorphism, and both properties descend along a fibre
square with affine target.

## Main results

* `AlgebraicGeometry.isIteratedAlphaPCover_relativeFrobenius` — the relative Frobenius of a
  morphism which is smooth of relative dimension `d` over a base in characteristic `p` is an
  iterated `α_p`-cover.
* `AlgebraicGeometry.hasConstantDegree_relativeFrobenius` — it has constant degree `p ^ d`.

Alongside them, and used by them, is `AlgebraicGeometry.HasFiniteBasis` and its calculus: the
datum of a free basis indexed by `Fin n` for a ring map, with its behaviour under composition
(`AlgebraicGeometry.hasFiniteBasis_comp`), under a square of ring isomorphisms
(`AlgebraicGeometry.hasFiniteBasis_of_iso`), for a bijective map
(`AlgebraicGeometry.hasFiniteBasis_of_bijective`), for `R[z]/(z ^ p - c)`
(`AlgebraicGeometry.hasFiniteBasis_adjoinRoot_X_pow_sub_C`), and on the global sections of a
spectrum, of a square of schemes and of a restriction to an open
(`AlgebraicGeometry.hasFiniteBasis_spec_appTop`,
`AlgebraicGeometry.hasFiniteBasis_appTop_of_iso`,
`AlgebraicGeometry.hasFiniteBasis_app_of_morphismRestrict`).  These have nothing to do with the
Frobenius and were `private` here until
`StacksFrontier/AlgebraicGeometry/Crystalline/AlphaPCoverDegree.lean` needed them for the degree of
an `α_p`-cover; a module of their own, next to `AlphaPCover.lean`, would be the right home.

## Relation to [Stacks, Tag 07QB]

Both are proved, with no hypothesis beyond `IsInCharacteristic S₀ p` and
`SmoothOfRelativeDimension d X.hom`, and together they are the first sentence of
[Stacks, Tag 07QB], `F_{X/S₀}` is an iterated `α_p`-cover of degree `p ^ d`, over an arbitrary base
in characteristic `p`.  The source's own proof stops there ("It suffices to prove the first
statement").  `StacksFrontier/AlgebraicGeometry/Crystalline/AlphaPCoverFrobeniusTwistSituation.lean`
reads them in the global crystalline situation of the tag, and
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AlphaPCoverRelativeFrobenius07QB.lean`
deduces from them, through [Stacks, Tag 07QA] at `q = p ^ d`, the bound on
`F_{X/S₀}^* : H^i(Cris(X^{(1)}/S), 𝒢) ⟶ H^i(Cris(X/S), F_{X/S₀, cris}^*𝒢)`.

## References

* [Stacks Project, Lemma 60.26.5, Tag 07QB](https://stacks.math.columbia.edu/tag/07QB)
* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Lemma 60.26.4, Tag 07QA](https://stacks.math.columbia.edu/tag/07QA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open scoped TensorProduct
open Stacks.Frobenius

universe u v w

namespace AlgebraicGeometry

/-! ### Adjoining a `p`-th root of a variable

The polynomial ring `R[x]` with a `p`-th root of `x` adjoined is again a polynomial ring, and the
inclusion of the former in the latter is the map sending `x` to `x ^ p`.  This identifies the map
`R[x] ⟶ R[x]`, `x ↦ x ^ p`, with an `α_p`-cover. -/

open Polynomial in
/-- `R[x][z]/(z ^ p - x)` is again the polynomial ring `R[x]`, with `z` corresponding to `x` and
`x` to `x ^ p`. -/
private def adjoinRootXPowSubXEquiv (R : Type u) [CommRing R] (n : ℕ) :
    AdjoinRoot (X ^ n - C (X : R[X])) ≃+* R[X] := by
  let P : R[X][X] := X ^ n - C X
  let a : AdjoinRoot P := AdjoinRoot.root P
  let f : AdjoinRoot P →+* R[X] :=
    AdjoinRoot.lift (Polynomial.eval₂RingHom C (X ^ n)) X (by simp [P])
  let g : R[X] →+* AdjoinRoot P :=
    Polynomial.eval₂RingHom ((AdjoinRoot.of P).comp C) a
  have hroot : AdjoinRoot.root P ^ n = AdjoinRoot.of P (X : R[X]) := by
    simpa only [P, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] using
      AdjoinRoot.eval₂_root P
  refine RingEquiv.ofRingHom f g ?_ ?_
  · apply Polynomial.ringHom_ext
    · intro r
      change f (Polynomial.eval₂ ((AdjoinRoot.of P).comp C) a (C r)) = C r
      rw [Polynomial.eval₂_C]
      change AdjoinRoot.lift _ _ _ (AdjoinRoot.of P (C r)) = C r
      rw [AdjoinRoot.lift_of]
      exact Polynomial.eval₂_C _ _
    · change f (Polynomial.eval₂ ((AdjoinRoot.of P).comp C) a X) = X
      rw [Polynomial.eval₂_X]
      exact AdjoinRoot.lift_root _
  · apply AdjoinRoot.ringHom_ext
    · ext r <;> simp [f, g, a, P, hroot]
    · simp [f, g, a, P]

open Polynomial in
/-- Under the identification of `R[x][z]/(z ^ p - x)` with `R[x]`, the structure map of
`R[x][z]/(z ^ p - x)` over `R[x]` becomes the map sending `x` to `x ^ p`. -/
private theorem adjoinRootXPowSubXEquiv_of (R : Type u) [CommRing R] (n : ℕ)
    (r : R[X]) :
    adjoinRootXPowSubXEquiv R n (AdjoinRoot.of (X ^ n - C (X : R[X])) r) =
      Polynomial.eval₂RingHom C (X ^ n) r := by
  simp [adjoinRootXPowSubXEquiv]

open Polynomial in
/-- The map `R[x] ⟶ R[x]` sending `x` to `x ^ p` induces an `α_p`-cover on spectra, when `p`
vanishes in `R`. -/
private theorem isAlphaPCover_spec_X_pow (R : Type u) [CommRing R]
    (p : ℕ) (hp : (p : R) = 0) :
    IsAlphaPCover p
      (Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom C (X ^ p : R[X])))) := by
  let e := adjoinRootXPowSubXEquiv R p
  refine ⟨R[X], inferInstance, ?_, X, Iso.refl _,
    Scheme.Spec.mapIso e.toCommRingCatIso.op, ?_⟩
  · simpa using congrArg (Polynomial.C (R := R)) hp
  · have h : CommRingCat.ofHom (Polynomial.eval₂RingHom C (X ^ p : R[X])) =
        CommRingCat.ofHom (AdjoinRoot.of (X ^ p - C (X : R[X]))) ≫
          CommRingCat.ofHom e.toRingHom :=
      CommRingCat.hom_ext (RingHom.ext fun r => (adjoinRootXPowSubXEquiv_of R p r).symm)
    show Spec.map _ ≫ 𝟙 _ = Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (AdjoinRoot.of (X ^ p - C (X : R[X]))))
    rw [Category.comp_id, ← Spec.map_comp, ← h]

/-- Being an `α_p`-cover on spectra transports along a commuting square of ring isomorphisms. -/
private theorem isAlphaPCover_spec_of_ringEquiv
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (g : R' →+* S') (eR : R ≃+* R') (eS : S ≃+* S')
    (h : eS.toRingHom.comp f = g.comp eR.toRingHom) (p : ℕ)
    (hg : IsAlphaPCover p (Spec.map (CommRingCat.ofHom g))) :
    IsAlphaPCover p (Spec.map (CommRingCat.ofHom f)) := by
  apply isAlphaPCover_of_iso p _ _
    (Scheme.Spec.mapIso eS.symm.toCommRingCatIso.op)
    (Scheme.Spec.mapIso eR.symm.toCommRingCatIso.op) ?_ hg
  show Spec.map _ ≫ Spec.map (CommRingCat.ofHom eR.symm.toRingHom) =
    Spec.map (CommRingCat.ofHom eS.symm.toRingHom) ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  apply eS.injective
  have hr := congrArg (fun k : R →+* S' => k (eR.symm r)) h
  show eS (f (eR.symm r)) = eS (eS.symm (g r))
  rw [eS.apply_symm_apply]
  change eS (f (eR.symm r)) = g (eR (eR.symm r)) at hr
  simpa only [eR.apply_symm_apply] using hr

/-! ### Raising the variables of a polynomial ring to the `p`-th power -/

/-- The endomorphism of `MvPolynomial σ R` raising the single variable `i` to its `p`-th power
and fixing the others. -/
private def variablePower (σ R : Type u) [CommRing R] [DecidableEq σ]
    (p : ℕ) (i : σ) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  MvPolynomial.aeval (fun j => if j = i then MvPolynomial.X j ^ p else MvPolynomial.X j)

/-- `MvPolynomial σ R` is the polynomial ring in the variable `i` over the polynomial ring in the
remaining variables. -/
private def variablePolynomialEquiv (σ R : Type u) [CommRing R] [DecidableEq σ]
    (i : σ) : MvPolynomial σ R ≃ₐ[R] Polynomial (MvPolynomial {j : σ // j ≠ i} R) :=
  (MvPolynomial.renameEquiv R (Equiv.optionSubtypeNe i).symm).trans
    (MvPolynomial.optionEquivLeft R {j : σ // j ≠ i})

/-- Under that identification, raising the variable `i` to its `p`-th power becomes the map
sending the polynomial variable to its `p`-th power. -/
private theorem variablePolynomialEquiv_variablePower
    (σ R : Type u) [CommRing R] [DecidableEq σ] (p : ℕ) (i : σ) :
    (variablePolynomialEquiv σ R i).toRingHom.comp (variablePower σ R p i).toRingHom =
      (Polynomial.eval₂RingHom Polynomial.C (Polynomial.X ^ p)).comp
        (variablePolynomialEquiv σ R i).toRingHom := by
  ext j
  · simp [variablePower, variablePolynomialEquiv]
  · by_cases h : j = i
    · subst j
      simp [variablePower, variablePolynomialEquiv]
    · simp [variablePower, variablePolynomialEquiv, h, Equiv.optionSubtypeNe_symm_of_ne h]

/-- Raising one variable to its `p`-th power induces an `α_p`-cover on spectra. -/
private theorem isAlphaPCover_spec_variablePower
    (σ R : Type u) [CommRing R] [DecidableEq σ] (p : ℕ) (hp : (p : R) = 0)
    (i : σ) :
    IsAlphaPCover p
      (Spec.map (CommRingCat.ofHom (variablePower σ R p i).toRingHom)) := by
  have hc : (p : MvPolynomial {j : σ // j ≠ i} R) = 0 := by
    simpa only [map_natCast, map_zero] using
      congrArg (MvPolynomial.C (σ := {j : σ // j ≠ i}) (R := R)) hp
  exact isAlphaPCover_spec_of_ringEquiv _ _
    (variablePolynomialEquiv σ R i).toRingEquiv
    (variablePolynomialEquiv σ R i).toRingEquiv
    (variablePolynomialEquiv_variablePower σ R p i) p
    (isAlphaPCover_spec_X_pow _ p hc)

/-- The endomorphism of `MvPolynomial σ R` raising the variables indexed by `s` to their `p`-th
powers and fixing the others.  At `s = univ` it is `MvPolynomial.expand p`. -/
private def partialExpand (σ R : Type u) [CommRing R] [DecidableEq σ]
    (p : ℕ) (s : Finset σ) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  MvPolynomial.aeval (fun j => if j ∈ s then MvPolynomial.X j ^ p else MvPolynomial.X j)

/-- Raising no variable to its `p`-th power is the identity. -/
private theorem partialExpand_empty (σ R : Type u) [CommRing R] [DecidableEq σ]
    (p : ℕ) : partialExpand σ R p ∅ = AlgHom.id R _ := by
  ext j
  simp [partialExpand]

/-- Adding one variable to the set raised to the `p`-th power composes on one more
`variablePower`. -/
private theorem partialExpand_insert (σ R : Type u) [CommRing R] [DecidableEq σ]
    (p : ℕ) (s : Finset σ) (i : σ) (hi : i ∉ s) :
    partialExpand σ R p (insert i s) =
      (variablePower σ R p i).comp (partialExpand σ R p s) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [partialExpand, variablePower, hi]
  · by_cases hjs : j ∈ s <;> simp [partialExpand, variablePower, hji, hjs]

/-- Raising finitely many variables to their `p`-th powers induces a composition of
`α_p`-covers on spectra, one for each variable. -/
private theorem isAlphaPCoverComposite_spec_partialExpand
    (σ R : Type u) [CommRing R] [DecidableEq σ] (p : ℕ) (hp : (p : R) = 0)
    (s : Finset σ) :
    IsAlphaPCoverComposite p
      (Spec.map (CommRingCat.ofHom (partialExpand σ R p s).toRingHom)) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [partialExpand_empty]
    exact .of_isIso _ (by change IsIso (Spec.map (𝟙 _)); infer_instance)
  | @insert i s hi ih =>
    have h : CommRingCat.ofHom (partialExpand σ R p (insert i s)).toRingHom =
        CommRingCat.ofHom (partialExpand σ R p s).toRingHom ≫
          CommRingCat.ofHom (variablePower σ R p i).toRingHom := by
      rw [partialExpand_insert σ R p s i hi]
      rfl
    rw [h, Spec.map_comp]
    exact .comp (isAlphaPCover_spec_variablePower σ R p hp i) ih

/-- Raising all variables to their `p`-th powers is `MvPolynomial.expand p`. -/
private theorem partialExpand_univ (σ R : Type u) [CommRing R] [Fintype σ] [DecidableEq σ]
    (p : ℕ) : partialExpand σ R p Finset.univ = MvPolynomial.expand p := by
  ext j
  simp [partialExpand, MvPolynomial.expand_X]

/-- **`MvPolynomial.expand p` is a composition of `α_p`-covers.**  On spectra, raising every one
of finitely many variables to its `p`-th power is a composition of as many `α_p`-covers. -/
private theorem isAlphaPCoverComposite_spec_expand
    (σ R : Type u) [CommRing R] [Finite σ] (p : ℕ) (hp : (p : R) = 0) :
    IsAlphaPCoverComposite p
      (Spec.map (CommRingCat.ofHom (MvPolynomial.expand (σ := σ) (R := R) p).toRingHom)) := by
  classical
  have := Fintype.ofFinite σ
  rw [← partialExpand_univ]
  exact isAlphaPCoverComposite_spec_partialExpand σ R p hp Finset.univ

/-! ### Free bases of finite rank

`HasConstantDegree` is a statement about ranks of modules of sections.  It is convenient to track
instead the stronger datum of an explicit basis indexed by `Fin n`, which composes and base
changes without needing the base ring to be nontrivial. -/

/-- A ring map admits a basis of `n` elements: the target is free of rank `n` over the source,
with a chosen basis indexed by `Fin n`. -/
def HasFiniteBasis {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) : Prop :=
  letI := f.toAlgebra
  Nonempty (Module.Basis (Fin n) R S)

/-- Bases of finite rank multiply along a composition of ring maps. -/
theorem hasFiniteBasis_comp {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    (m n : ℕ) (hf : HasFiniteBasis f m) (hg : HasFiniteBasis g n) :
    HasFiniteBasis (g.comp f) (m * n) := by
  let _ := f.toAlgebra
  let _ := g.toAlgebra
  let _ := (g.comp f).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨b⟩ := hf
  obtain ⟨c⟩ := hg
  exact ⟨(b.smulTower c).reindex finProdFinEquiv⟩

/-- Having a basis of finite rank transports along a commuting square of ring isomorphisms. -/
theorem hasFiniteBasis_of_iso {R S R' S' : Type u}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (g : R' →+* S') (eR : R ≃+* R') (eS : S ≃+* S')
    (h : eS.toRingHom.comp f = g.comp eR.toRingHom) (n : ℕ)
    (hg : HasFiniteBasis g n) : HasFiniteBasis f n := by
  let _ := f.toAlgebra
  let _ := g.toAlgebra
  let _ := (g.comp eR.toRingHom).toAlgebra
  let e : S ≃ₗ[R] S' :=
    { eS.toAddEquiv with
      map_smul' := by
        intro r x
        show eS (f r * x) = g (eR r) * eS x
        rw [map_mul]
        exact congrArg (fun a => a * eS x) (congrArg (fun k : R →+* S' => k r) h) }
  obtain ⟨b⟩ := hg
  exact ⟨(b.mapCoeffs eR.symm (by
    intro r x
    show g (eR (eR.symm r)) * x = g r * x
    rw [eR.apply_symm_apply])).map e.symm⟩

/-- A bijective ring map admits a basis of one element. -/
theorem hasFiniteBasis_of_bijective {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Bijective f) :
    HasFiniteBasis f 1 := by
  let _ := f.toAlgebra
  let e : R ≃ₐ[R] S := AlgEquiv.ofBijective (Algebra.ofId R S) hf
  exact ⟨((Module.Basis.singleton (Fin 1) R).map e.toLinearEquiv)⟩

/-- `R[z]/(z ^ p - c)` is free of rank `p` over `R`, on the powers of the adjoined root. -/
theorem hasFiniteBasis_adjoinRoot_X_pow_sub_C
    (R : Type u) [CommRing R] (p : ℕ) (hp : p ≠ 0) (c : R) :
    HasFiniteBasis (AdjoinRoot.of (Polynomial.X ^ p - Polynomial.C c)) p := by
  classical
  show HasFiniteBasis (algebraMap R (AdjoinRoot (Polynomial.X ^ p - Polynomial.C c))) p
  unfold HasFiniteBasis
  rw [toAlgebra_algebraMap]
  by_cases hR : Nontrivial R
  · let _ := hR
    let b := AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C c hp)
    exact ⟨b.basis.reindex (finCongr (by simp [b, AdjoinRoot.powerBasis']))⟩
  · have : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    have : Subsingleton (AdjoinRoot (Polynomial.X ^ p - Polynomial.C c)) :=
      Algebra.subsingleton R _
    exact ⟨Module.Basis.ofEquivFun (LinearEquiv.ofSubsingleton (R := R) _ _)⟩

open Polynomial in
/-- The map `R[x] ⟶ R[x]` sending `x` to `x ^ p` admits a basis of `p` elements. -/
private theorem hasFiniteBasis_eval₂_X_pow (R : Type u) [CommRing R]
    (p : ℕ) (hp : p ≠ 0) :
    HasFiniteBasis (Polynomial.eval₂RingHom C (X ^ p : R[X])) p := by
  let e := adjoinRootXPowSubXEquiv R p
  apply hasFiniteBasis_of_iso _ (AdjoinRoot.of (X ^ p - C (X : R[X])))
    (RingEquiv.refl _) e.symm ?_ p
    (hasFiniteBasis_adjoinRoot_X_pow_sub_C R[X] p hp X)
  apply RingHom.ext
  intro r
  apply e.injective
  show e (e.symm (Polynomial.eval₂RingHom C (X ^ p) r)) = e (AdjoinRoot.of _ r)
  rw [e.apply_symm_apply]
  exact (adjoinRootXPowSubXEquiv_of R p r).symm

/-- Raising one variable to its `p`-th power admits a basis of `p` elements. -/
private theorem hasFiniteBasis_variablePower
    (σ R : Type u) [CommRing R] [DecidableEq σ] (p : ℕ) (hp : p ≠ 0) (i : σ) :
    HasFiniteBasis (variablePower σ R p i).toRingHom p :=
  hasFiniteBasis_of_iso _ _ (variablePolynomialEquiv σ R i).toRingEquiv
    (variablePolynomialEquiv σ R i).toRingEquiv
    (variablePolynomialEquiv_variablePower σ R p i) p
    (hasFiniteBasis_eval₂_X_pow _ p hp)

/-- Raising the variables indexed by `s` to their `p`-th powers admits a basis of `p ^ #s`
elements, one factor of `p` for each variable. -/
private theorem hasFiniteBasis_partialExpand
    (σ R : Type u) [CommRing R] [DecidableEq σ] (p : ℕ) (hp : p ≠ 0) (s : Finset σ) :
    HasFiniteBasis (partialExpand σ R p s).toRingHom (p ^ s.card) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [partialExpand_empty]
    exact hasFiniteBasis_of_bijective (RingHom.id _) Function.bijective_id
  | @insert i s hi ih =>
    rw [partialExpand_insert σ R p s i hi, Finset.card_insert_of_notMem hi, pow_succ]
    exact hasFiniteBasis_comp _ _ _ _ ih (hasFiniteBasis_variablePower σ R p hp i)

/-- **`MvPolynomial.expand p` is free of rank `p ^ d` in `d` variables.** -/
private theorem hasFiniteBasis_expand
    (σ R : Type u) [CommRing R] [Fintype σ] (p : ℕ) (hp : p ≠ 0) :
    HasFiniteBasis (MvPolynomial.expand (σ := σ) (R := R) p).toRingHom
      (p ^ Fintype.card σ) := by
  classical
  rw [← partialExpand_univ]
  exact hasFiniteBasis_partialExpand σ R p hp Finset.univ

/-- Having a basis of finite rank is preserved by base change. -/
theorem HasFiniteBasis.baseChange_tensor {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : R →+* T)
    (n : ℕ) (hf : HasFiniteBasis f n) :
    letI := f.toAlgebra
    letI := g.toAlgebra
    HasFiniteBasis (algebraMap T (T ⊗[R] S)) n := by
  let _ := f.toAlgebra
  let _ := g.toAlgebra
  unfold HasFiniteBasis
  rw [toAlgebra_algebraMap]
  obtain ⟨b⟩ := hf
  exact ⟨b.baseChange T⟩

/-- Taking spectra does not change the map on global sections, up to the canonical identification
of a ring with the global sections of its spectrum. -/
theorem hasFiniteBasis_spec_appTop {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) (hf : HasFiniteBasis f n) :
    HasFiniteBasis (Spec.map (CommRingCat.ofHom f)).appTop.hom n :=
  hasFiniteBasis_of_iso _ f
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
    (Scheme.ΓSpecIso (.of S)).commRingCatIsoToRingEquiv
    (congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))) n hf

/-- Having a basis of finite rank on global sections transports along a commuting square of
schemes whose vertical arrows are isomorphisms. -/
theorem hasFiniteBasis_appTop_of_iso {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (i : X ≅ X') (j : Y ≅ Y')
    (h : f ≫ j.hom = i.hom ≫ g) (n : ℕ) (hg : HasFiniteBasis g.appTop.hom n) :
    HasFiniteBasis f.appTop.hom n := by
  let jIso : Γ(Y', ⊤) ≅ Γ(Y, ⊤) := Scheme.Γ.mapIso j.op
  let iIso : Γ(X', ⊤) ≅ Γ(X, ⊤) := Scheme.Γ.mapIso i.op
  let eR := jIso.commRingCatIsoToRingEquiv
  let eS := iIso.commRingCatIsoToRingEquiv
  apply hasFiniteBasis_of_iso _ g.appTop.hom eR.symm eS.symm ?_ n hg
  have h' : j.hom.appTop ≫ f.appTop = g.appTop ≫ i.hom.appTop := by
    simpa only [Scheme.Hom.comp_appTop] using congrArg Scheme.Hom.appTop h
  apply RingHom.ext
  intro r
  apply eS.injective
  show eS (eS.symm (f.appTop r)) = eS (g.appTop (eR.symm r))
  rw [eS.apply_symm_apply]
  have hr := congrArg (fun k : Γ(Y', ⊤) ⟶ Γ(X, ⊤) => k (eR.symm r)) h'
  change f.appTop (eR (eR.symm r)) = eS (g.appTop (eR.symm r)) at hr
  simpa only [eR.apply_symm_apply] using hr

/-! ### The étale chart over affine space -/

/-- Affine space over isomorphic bases is isomorphic. -/
private def affineSpaceMapIso {n : Type u} {S T : Scheme.{u}}
    (e : S ≅ T) : AffineSpace n S ≅ AffineSpace n T where
  hom := AffineSpace.map n e.hom
  inv := AffineSpace.map n e.inv
  hom_inv_id := by rw [← AffineSpace.map_comp, Iso.hom_inv_id, AffineSpace.map_id]
  inv_hom_id := by rw [← AffineSpace.map_comp, Iso.inv_hom_id, AffineSpace.map_id]

/-- **A smooth morphism of relative dimension `d` is étale over affine `d`-space, locally.**
Around any point of the source there are an affine open `V` of the target, an affine open `U` of
the source lying over it, and an étale morphism from `U` to affine `d`-space over `V` compatible
with the two structure morphisms. -/
private theorem exists_etale_affineSpace_chart
    {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    [SmoothOfRelativeDimension d f] (x : X) :
    ∃ (V : Y.Opens) (_hV : IsAffineOpen V) (U : X.Opens)
      (_hU : IsAffineOpen U) (_ : x ∈ U) (hUV : U ≤ f ⁻¹ᵁ V)
      (π : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) V.toScheme),
      Etale π ∧
        π ≫ (AffineSpace (ULift.{u} (Fin d)) V.toScheme ↘ V.toScheme) =
          f.resLE V U hUV := by
  obtain ⟨V, hV, U, hU, hxU, hUV, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := d) (f := f) x
  let _ : IsAffine U.toScheme := hU
  let _ : IsAffine V.toScheme := hV
  let R := Γ(Y, V)
  let A := Γ(X, U)
  let φCat := f.appLE V U hUV
  let φ := φCat.hom
  let _ : Algebra (↑R) (↑A) := φ.toAlgebra
  let _ : Algebra.IsStandardSmoothOfRelativeDimension d (↑R) (↑A) :=
    hstd.toAlgebra
  obtain ⟨g, hg⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
      (n := d) (R := (↑R)) (S := (↑A))
  let e : ULift.{u} (Fin d) ≃ Fin d := Equiv.ulift
  let renameIso :=
    (MvPolynomial.renameEquiv (↑R) e).toRingEquiv.toCommRingCatIso
  let g' : MvPolynomial (ULift.{u} (Fin d)) (↑R) →ₐ[↑R] ↑A :=
    g.comp (MvPolynomial.renameEquiv (↑R) e).toAlgHom
  let gCat := CommRingCat.ofHom g'.toRingHom
  let gFinCat := CommRingCat.ofHom g.toRingHom
  let cCat : CommRingCat.of (↑R) ⟶
      CommRingCat.of (MvPolynomial (ULift.{u} (Fin d)) (↑R)) :=
    CommRingCat.ofHom (algebraMap (↑R) (MvPolynomial (ULift.{u} (Fin d)) (↑R)))
  let Siso := hU.isoSpec
  let Tiso := hV.isoSpec
  let Biso := affineSpaceMapIso (n := ULift.{u} (Fin d)) Tiso.symm
  let Pspace := AffineSpace.SpecIso (ULift.{u} (Fin d)) (↑R)
  let π : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) V.toScheme :=
    Siso.hom ≫ Spec.map gCat ≫ Pspace.inv ≫ Biso.hom
  refine ⟨V, hV, U, hU, hxU, hUV, π, ?_, ?_⟩
  · have hg' : RingHom.Etale g'.toRingHom := by
      show RingHom.Etale (g.toRingHom.comp
        (MvPolynomial.renameEquiv (↑R) e).toRingEquiv.toRingHom)
      exact (RingHom.Etale.respectsIso.cancel_left_isIso renameIso.hom gFinCat).mpr hg
    let _ : Etale (Spec.map gCat) := HasRingHomProperty.Spec_iff.mpr hg'
    dsimp [π]
    infer_instance
  · have hbase : cCat ≫ gCat = φCat := by
      ext r
      show g' (algebraMap (↑R) (MvPolynomial (ULift.{u} (Fin d)) (↑R)) r) = φ r
      rw [g'.commutes]
      rfl
    have hBiso : Biso.hom ≫
        (AffineSpace (ULift.{u} (Fin d)) V.toScheme ↘ V.toScheme) =
        (AffineSpace (ULift.{u} (Fin d)) (Spec R) ↘ Spec R) ≫ Tiso.inv := by
      dsimp [Biso, affineSpaceMapIso]
      exact AffineSpace.map_over Tiso.inv
    have hPspace : Pspace.inv ≫
        (AffineSpace (ULift.{u} (Fin d)) (Spec R) ↘ Spec R) = Spec.map cCat := by
      show (AffineSpace.SpecIso (ULift.{u} (Fin d)) R).inv ≫
        (AffineSpace (ULift.{u} (Fin d)) (Spec R) ↘ Spec R) = Spec.map cCat
      rw [AffineSpace.SpecIso_inv_over]
      rfl
    dsimp [π]
    simp only [Category.assoc, hBiso]
    rw [← Category.assoc Pspace.inv, hPspace]
    rw [← Category.assoc (Spec.map gCat), ← Spec.map_comp, hbase]
    dsimp [Siso, Tiso]
    rw [IsAffineOpen.isoSpec_hom hU]
    dsimp [φCat]
    calc
      U.toSpecΓ ≫ Spec.map (f.appLE V U hUV) ≫ hV.isoSpec.inv =
          (f.resLE V U hUV ≫ V.toSpecΓ) ≫ hV.isoSpec.inv := by
        rw [← Category.assoc,
          Scheme.Opens.toSpecΓ_SpecMap_appLE f V U hUV]
      _ = f.resLE V U hUV := by
        rw [← IsAffineOpen.isoSpec_hom hV]
        simp

/-! ### The relative Frobenius of affine space -/

/-- The endomorphism of affine space over `S` raising every coordinate to its `p`-th power. -/
private def affineSpacePower (n : Type u) (S : Scheme.{u}) (p : ℕ) :
    AffineSpace n S ⟶ AffineSpace n S :=
  AffineSpace.homOfVector (AffineSpace n S ↘ S) (fun i => AffineSpace.coord S i ^ p)

/-- Raising the coordinates to their `p`-th powers is a morphism over the base. -/
private theorem affineSpacePower_over (n : Type u) (S : Scheme.{u}) (p : ℕ) :
    affineSpacePower n S p ≫ (AffineSpace n S ↘ S) = (AffineSpace n S ↘ S) :=
  AffineSpace.homOfVector_over _ _

/-- On the coordinate `i`, the endomorphism acts by `p`-th powers. -/
private theorem affineSpacePower_appTop_coord (n : Type u) (S : Scheme.{u}) (p : ℕ)
    (i : n) :
    (affineSpacePower n S p).appTop (AffineSpace.coord S i) = AffineSpace.coord S i ^ p :=
  AffineSpace.homOfVector_appTop_coord _ _ _

/-- Raising the coordinates to their `p`-th powers, followed by the absolute Frobenius of the
base acting on affine space, is the absolute Frobenius of affine space. -/
private theorem affineSpacePower_comp_map_absoluteFrobenius
    (n : Type u) (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) :
    affineSpacePower n S p ≫ AffineSpace.map n (absoluteFrobenius S p hS) =
      absoluteFrobenius (AffineSpace n S) p
        (isInCharacteristic_of_hom (AffineSpace n S ↘ S) p hS) := by
  apply AffineSpace.hom_ext
  · rw [Category.assoc, AffineSpace.map_over, ← Category.assoc, affineSpacePower_over]
    exact (absoluteFrobenius_naturality (AffineSpace n S ↘ S) p _ hS).symm
  · intro i
    trans AffineSpace.coord S i ^ p
    · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.map_appTop_coord,
        affineSpacePower_appTop_coord]
    · exact (absoluteFrobenius_app_apply (AffineSpace n S) p _ ⊤
        (AffineSpace.coord S i)).symm

/-- Affine space is its own Frobenius twist: the square exhibiting affine space over the base
twisted by the absolute Frobenius is a fibre square. -/
private def affineSpaceFrobeniusTwistIso
    (n : Type u) (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) :
    AffineSpace n S ≅ ((frobeniusTwist S p hS).obj
      (Over.mk (AffineSpace n S ↘ S))).left :=
  (AffineSpace.isPullback_map (n := n) (absoluteFrobenius S p hS)).isoPullback

/-- The identification of affine space with its Frobenius twist is compatible with the first
projection. -/
private theorem affineSpaceFrobeniusTwistIso_hom_fst
    (n : Type u) (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) :
    (affineSpaceFrobeniusTwistIso n S p hS).hom ≫
      pullback.fst (AffineSpace n S ↘ S) (absoluteFrobenius S p hS) =
      AffineSpace.map n (absoluteFrobenius S p hS) :=
  (AffineSpace.isPullback_map (n := n) (absoluteFrobenius S p hS)).isoPullback_hom_fst

/-- The identification of affine space with its Frobenius twist is compatible with the second
projection. -/
private theorem affineSpaceFrobeniusTwistIso_hom_snd
    (n : Type u) (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) :
    (affineSpaceFrobeniusTwistIso n S p hS).hom ≫
      pullback.snd (AffineSpace n S ↘ S) (absoluteFrobenius S p hS) =
      (AffineSpace n S ↘ S) :=
  (AffineSpace.isPullback_map (n := n) (absoluteFrobenius S p hS)).isoPullback_hom_snd

/-- **The relative Frobenius of affine space raises the coordinates to their `p`-th powers.**
Under the identification of affine space with its own Frobenius twist, the relative Frobenius is
`affineSpacePower`. -/
private theorem relativeFrobenius_affineSpace
    (n : Type u) (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) :
    (relativeFrobenius S p hS (Over.mk (AffineSpace n S ↘ S))).left =
      affineSpacePower n S p ≫ (affineSpaceFrobeniusTwistIso n S p hS).hom := by
  let g : Over.mk (AffineSpace n S ↘ S) ⟶
      (frobeniusTwist S p hS).obj (Over.mk (AffineSpace n S ↘ S)) :=
    Over.homMk (affineSpacePower n S p ≫ (affineSpaceFrobeniusTwistIso n S p hS).hom)
      (by change (_ ≫ _) ≫ pullback.snd (AffineSpace n S ↘ S)
            (absoluteFrobenius S p hS) = (AffineSpace n S ↘ S)
          rw [Category.assoc, affineSpaceFrobeniusTwistIso_hom_snd, affineSpacePower_over])
  have h := eq_relativeFrobenius S p hS (Over.mk (AffineSpace n S ↘ S)) g
    (by change (_ ≫ _) ≫ pullback.fst (AffineSpace n S ↘ S)
            (absoluteFrobenius S p hS) = absoluteFrobenius (AffineSpace n S) p _
        rw [Category.assoc, affineSpaceFrobeniusTwistIso_hom_fst,
          affineSpacePower_comp_map_absoluteFrobenius])
    (by change (_ ≫ _) ≫ pullback.snd (AffineSpace n S ↘ S)
            (absoluteFrobenius S p hS) = (AffineSpace n S ↘ S)
        rw [Category.assoc, affineSpaceFrobeniusTwistIso_hom_snd, affineSpacePower_over])
  exact (congrArg Over.Hom.left h).symm

/-- On the spectrum of a ring, raising the coordinates of affine space to their `p`-th powers is
`MvPolynomial.expand p`. -/
private theorem affineSpacePower_SpecIso_inv
    (n : Type u) (R : CommRingCat.{u}) (p : ℕ) :
    (AffineSpace.SpecIso n R).inv ≫ affineSpacePower n (Spec R) p =
      Spec.map (CommRingCat.ofHom (MvPolynomial.expand (σ := n) (R := R) p).toRingHom) ≫
        (AffineSpace.SpecIso n R).inv := by
  apply AffineSpace.hom_ext
  · rw [Category.assoc, affineSpacePower_over, Category.assoc,
      AffineSpace.SpecIso_inv_over, ← Spec.map_comp]
    have h : CommRingCat.ofHom (MvPolynomial.C (σ := n) (R := R)) ≫
        CommRingCat.ofHom (MvPolynomial.expand (σ := n) (R := R) p).toRingHom =
          CommRingCat.ofHom (MvPolynomial.C (σ := n) (R := R)) :=
      CommRingCat.hom_ext (RingHom.ext (MvPolynomial.expand_C p))
    rw [h]
  · intro i
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply, affineSpacePower_appTop_coord, map_pow,
      AffineSpace.SpecIso_inv_appTop_coord]
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
      CommRingCat.comp_apply, ConcreteCategory.hom_ofHom]
    show _ = (Scheme.ΓSpecIso (.of (MvPolynomial n R))).inv
      (MvPolynomial.expand p (MvPolynomial.X i))
    rw [MvPolynomial.expand_X, map_pow]

/-- The square of `affineSpacePower_SpecIso_inv`, with the isomorphism in the other direction. -/
private theorem affineSpacePower_SpecIso_hom
    (n : Type u) (R : CommRingCat.{u}) (p : ℕ) :
    affineSpacePower n (Spec R) p ≫ (AffineSpace.SpecIso n R).hom =
      (AffineSpace.SpecIso n R).hom ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.expand (σ := n) (R := R) p).toRingHom) := by
  rw [← cancel_epi (AffineSpace.SpecIso n R).inv, ← Category.assoc,
    affineSpacePower_SpecIso_inv]
  simp

/-- Raising the coordinates of affine `d`-space over an affine base to their `p`-th powers
admits a basis of `p ^ d` elements. -/
private theorem hasFiniteBasis_affineSpacePower_Spec
    (n : Type u) [Fintype n] (R : CommRingCat.{u}) (p : ℕ) (hp : p ≠ 0) :
    HasFiniteBasis (affineSpacePower n (Spec R) p).appTop.hom (p ^ Fintype.card n) := by
  let e := AffineSpace.SpecIso n R
  exact hasFiniteBasis_appTop_of_iso _
    (Spec.map (CommRingCat.ofHom (MvPolynomial.expand (σ := n) (R := R) p).toRingHom))
    e e (affineSpacePower_SpecIso_hom n R p) _
    (hasFiniteBasis_spec_appTop _ _ (hasFiniteBasis_expand n R p hp))

/-- Raising the coordinates of affine space over an affine base to their `p`-th powers is a
composition of `α_p`-covers. -/
private theorem isAlphaPCoverComposite_affineSpacePower_Spec
    (n : Type u) [Finite n] (R : CommRingCat.{u}) (p : ℕ) (hp : (p : R) = 0) :
    IsAlphaPCoverComposite p (affineSpacePower n (Spec R) p) := by
  let e := AffineSpace.SpecIso n R
  exact isAlphaPCoverComposite_of_iso p _
    (Spec.map (CommRingCat.ofHom (MvPolynomial.expand (σ := n) (R := R) p).toRingHom))
    e e (affineSpacePower_SpecIso_hom n R p) (isAlphaPCoverComposite_spec_expand n R p hp)

/-- The relative Frobenius is surjective: it is a universal homeomorphism. -/
theorem relativeFrobenius_surjective
    (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p)
    (X : Over S) : Function.Surjective (relativeFrobenius S p hS X).left :=
  ((relativeFrobenius_universalHomeomorphism S p hS X).universally_isHomeomorph
    _ _ _ IsPullback.of_id_snd).surjective

/-! ### Descent along a fibre square with affine target -/

/-- Having a basis of finite rank is preserved along a pushout square of rings. -/
theorem HasFiniteBasis.of_isPushout
    {R A B C : CommRingCat.{u}} {f : R ⟶ A} {g : R ⟶ B}
    {i : A ⟶ C} {j : B ⟶ C} (h : IsPushout f g i j)
    (n : ℕ) (hf : HasFiniteBasis f.hom n) : HasFiniteBasis j.hom n := by
  let _ := f.hom.toAlgebra
  let _ := g.hom.toAlgebra
  let h' := CommRingCat.isPushout_tensorProduct R B A
  let e := h'.isoPushout ≪≫ h.flip.isoPushout.symm
  have he : CommRingCat.ofHom (algebraMap B (B ⊗[R] A)) ≫ e.hom = j := by
    show CommRingCat.ofHom (algebraMap B (B ⊗[R] A)) ≫
      h'.isoPushout.hom ≫ h.flip.isoPushout.inv = j
    show CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫
      h'.isoPushout.hom ≫ h.flip.isoPushout.inv = j
    rw [← Category.assoc, h'.inl_isoPushout_hom]
    exact h.flip.inl_isoPushout_inv
  apply hasFiniteBasis_of_iso _ (algebraMap B (B ⊗[R] A))
    (RingEquiv.refl _) e.symm.commRingCatIsoToRingEquiv ?_ n
    (HasFiniteBasis.baseChange_tensor f.hom g.hom n hf)
  apply RingHom.ext
  intro b
  have he' := congrArg (fun k : B ⟶ C => k b) he
  show e.inv (j b) = (algebraMap B (B ⊗[R] A)) b
  rw [← he']
  exact ConcreteCategory.congr_hom e.hom_inv_id _

/-- Having a basis of finite rank on global sections descends along a fibre square of affine
schemes. -/
theorem HasFiniteBasis.of_isPullback_appTop
    {P X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) (n : ℕ) (hf : HasFiniteBasis f.appTop.hom n) :
    HasFiniteBasis b.appTop.hom n :=
  HasFiniteBasis.of_isPushout (isPushout_appTop_of_isPullback h) n hf

open Polynomial in
/-- Base changing `R[z]/(z ^ p - c)` along `R ⟶ T` gives `T[z]/(z ^ p - c)`. -/
def tensorAdjoinRootXPowSubCEquiv
    (R T : Type u) [CommRing R] [CommRing T] [Algebra R T] (p : ℕ) (c : R) :
    T ⊗[R] AdjoinRoot (X ^ p - C c) ≃ₐ[T]
      AdjoinRoot (X ^ p - C (algebraMap R T c)) :=
  (AdjoinRoot.tensorAlgEquiv (R := R) (T := T) (X ^ p - C c)
    (X ^ p - C (Algebra.TensorProduct.includeRight (R := R) (A := T) c)) (by simp)).trans
      (AdjoinRoot.mapAlgEquiv (Algebra.TensorProduct.rid R T T) _ _ (by
        apply Associated.of_eq
        simp [Algebra.smul_def]))

/-- The base change of an `α_p`-cover of the spectrum of `R` to the spectrum of a `R`-algebra `T`
is an `α_p`-cover. -/
theorem isAlphaPCover_spec_tensor_adjoinRoot
    (R T : Type u) [CommRing R] [CommRing T] [Algebra R T]
    (p : ℕ) (hp : (p : R) = 0) (c : R) :
    IsAlphaPCover p
      (Spec.map (CommRingCat.ofHom
        (algebraMap T (T ⊗[R] AdjoinRoot (Polynomial.X ^ p - Polynomial.C c))))) := by
  let e := tensorAdjoinRootXPowSubCEquiv R T p c
  refine ⟨T, inferInstance, ?_, algebraMap R T c, Iso.refl _,
    Scheme.Spec.mapIso e.symm.toRingEquiv.toCommRingCatIso.op, ?_⟩
  · simpa using congrArg (algebraMap R T) hp
  · show Spec.map _ ≫ 𝟙 _ = Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap T (AdjoinRoot _)))
    rw [Category.comp_id, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext (fun t => (e.symm.commutes t).symm))

/-- **An `α_p`-cover stays an `α_p`-cover under base change**, when the base of the base change is
affine. -/
theorem IsAlphaPCover.of_isPullback
    {P X Y Z : Scheme.{u}} [IsAffine Y]
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) (p : ℕ) (hf : IsAlphaPCover p f) :
    IsAlphaPCover p b := by
  obtain ⟨R, hR, hp, c, eZ, eX, he⟩ := hf
  let T := Γ(Y, ⊤)
  let eY := Y.isoSpec
  let k := eY.inv ≫ g ≫ eZ.hom
  let φ := (Scheme.Spec.preimage k).unop
  have hk : Spec.map φ = k := Scheme.Spec.map_preimage k
  let _ := φ.hom.toAlgebra
  let A := AdjoinRoot (Polynomial.X ^ p - Polynomial.C c)
  have h' : IsPullback (a ≫ eX.hom) (b ≫ eY.hom)
      (alphaPCoverMap p R c) (Spec.map φ) := by
    apply h.of_iso (Iso.refl _) eX eY eZ
    · simp only [Iso.refl_hom, Category.id_comp]
    · simp only [Iso.refl_hom, Category.id_comp]
    · exact he
    · rw [hk]
      simp [k]
  let ht := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R T A)
  let e := h'.flip.isoIsPullback _ _ ht
  exact isAlphaPCover_of_iso p b _ e eY (by
    exact (h'.flip.isoIsPullback_hom_fst _ _ ht).symm)
    (isAlphaPCover_spec_tensor_adjoinRoot R T p hp c)

/-- **A composition of `α_p`-covers stays one under base change**, when the base of the base
change is affine: each stage is base changed in turn, and the intermediate schemes stay affine. -/
theorem IsAlphaPCoverComposite.of_isPullback
    {P X Y Z : Scheme.{u}} [IsAffine Y]
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) (p : ℕ)
    (hf : IsAlphaPCoverComposite p f) :
    IsAlphaPCoverComposite p b := by
  induction hf generalizing P Y with
  | of_isIso f hf => exact .of_isIso b h.isIso_snd_of_isIso
  | @comp X'' X' X f₁ f₂ hf₁ hf₂ ih =>
    have hw : (a ≫ f₁) ≫ f₂ = b ≫ g := by simpa only [Category.assoc] using h.w
    have htfst : pullback.lift (a ≫ f₁) b hw ≫ pullback.fst f₂ g = a ≫ f₁ :=
      pullback.lift_fst _ _ _
    have htsnd : pullback.lift (a ≫ f₁) b hw ≫ pullback.snd f₂ g = b :=
      pullback.lift_snd _ _ _
    have ht : IsPullback a (pullback.lift (a ≫ f₁) b hw) f₁ (pullback.fst f₂ g) := by
      apply IsPullback.of_bot (t := IsPullback.of_hasPullback f₂ g)
      · rw [htsnd]; exact h
      · exact htfst.symm
    have hb : IsAlphaPCoverComposite p (pullback.snd f₂ g) :=
      ih (IsPullback.of_hasPullback f₂ g)
    have : IsAffine (pullback f₂ g) := isAffine_source_of_isAlphaPCoverComposite p hb
    have hc := IsAlphaPCoverComposite.comp
      (IsAlphaPCover.of_isPullback ht p hf₁) hb
    rwa [htsnd] at hc

/-! ### The Frobenius fibre square of an étale morphism -/

/-- **The absolute Frobenius square of an étale morphism is a fibre square**: the relative
Frobenius of an étale morphism is an isomorphism, so the square expressing naturality of the
absolute Frobenius is cartesian. -/
@[sga "4½ Fonctions_L 3.4", sga "4½ Rapport 1.2" "special case"]
theorem isPullback_absoluteFrobenius_of_etale
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] (p : ℕ) [Fact p.Prime]
    (hY : IsInCharacteristic Y p) :
    IsPullback (absoluteFrobenius X p (isInCharacteristic_of_hom f p hY)) f
      f (absoluteFrobenius Y p hY) := by
  have : Etale (Over.mk f).hom := ‹Etale f›
  have : IsIso (relativeFrobenius Y p hY (Over.mk f)).left :=
    (Over.forget Y).map_isIso (relativeFrobenius Y p hY (Over.mk f))
  exact IsPullback.of_iso_pullback
    ⟨absoluteFrobenius_naturality f p _ hY⟩
    (asIso (relativeFrobenius Y p hY (Over.mk f)).left)
    (relativeFrobenius_fst Y p hY (Over.mk f))
    (relativeFrobenius_snd Y p hY (Over.mk f))

/-- Frobenius twisting is a base change, so it carries a morphism of `S`-schemes to a fibre
square over that morphism. -/
theorem isPullback_frobeniusTwist_map
    (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p)
    {X Y : Over S} (f : X ⟶ Y) :
    IsPullback ((frobeniusTwist S p hS).map f).left
      (pullback.fst X.hom (absoluteFrobenius S p hS))
      (pullback.fst Y.hom (absoluteFrobenius S p hS)) f.left := by
  apply IsPullback.of_right
    (t := (IsPullback.of_hasPullback Y.hom (absoluteFrobenius S p hS)).flip)
  · have hsnd : ((frobeniusTwist S p hS).map f).left ≫
        pullback.snd Y.hom (absoluteFrobenius S p hS) =
        pullback.snd X.hom (absoluteFrobenius S p hS) := by
      simpa only [frobeniusTwist_obj_hom] using ((frobeniusTwist S p hS).map f).w
    rw [hsnd, Over.w]
    exact (IsPullback.of_hasPullback X.hom (absoluteFrobenius S p hS)).flip
  · simp [frobeniusTwist, Over.pullback, pullback.lift_fst]

/-- **The relative Frobenius square of an étale morphism is a fibre square.**  This is the fibre
square the source's proof of [Stacks, Tag 07QB] observes: for `f : X ⟶ Y` étale over `S`, the
relative Frobenius of `X` is the base change of the relative Frobenius of `Y` along `f`. -/
theorem isPullback_relativeFrobenius_of_etale
    (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p)
    {X Y : Over S} (f : X ⟶ Y) [Etale f.left] :
    IsPullback (relativeFrobenius S p hS X).left f.left
      ((frobeniusTwist S p hS).map f).left (relativeFrobenius S p hS Y).left := by
  apply IsPullback.of_right (t := (isPullback_frobeniusTwist_map S p hS f).flip)
  · simpa only [relativeFrobenius_fst] using
      isPullback_absoluteFrobenius_of_etale f.left p
        (isInCharacteristic_of_hom Y.hom p hS)
  · exact congrArg Over.Hom.left (relativeFrobenius_naturality S p hS f)

/-- For an étale base `V ⟶ S`, the Frobenius twist over `V` agrees with the Frobenius twist over
`S` of the composed structure morphism. -/
private def frobeniusTwistBaseIso
    {V S : Scheme.{u}} (g : V ⟶ S) [Etale g]
    (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p) (X : Over V) :
    ((frobeniusTwist V p (isInCharacteristic_of_hom g p hS)).obj X).left ≅
      ((frobeniusTwist S p hS).obj (Over.mk (X.hom ≫ g))).left :=
  ((IsPullback.of_hasPullback X.hom
      (absoluteFrobenius V p (isInCharacteristic_of_hom g p hS))).paste_vert
    (isPullback_absoluteFrobenius_of_etale g p hS)).isoPullback

/-- That identification carries the relative Frobenius over `V` to the relative Frobenius
over `S`. -/
private theorem relativeFrobenius_comp_frobeniusTwistBaseIso
    {V S : Scheme.{u}} (g : V ⟶ S) [Etale g]
    (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p) (X : Over V) :
    (relativeFrobenius V p (isInCharacteristic_of_hom g p hS) X).left ≫
      (frobeniusTwistBaseIso g p hS X).hom =
      (relativeFrobenius S p hS (Over.mk (X.hom ≫ g))).left := by
  let H := (IsPullback.of_hasPullback X.hom
    (absoluteFrobenius V p (isInCharacteristic_of_hom g p hS))).paste_vert
      (isPullback_absoluteFrobenius_of_etale g p hS)
  have hfst : (frobeniusTwistBaseIso g p hS X).hom ≫
      pullback.fst (X.hom ≫ g) (absoluteFrobenius S p hS) =
      pullback.fst X.hom (absoluteFrobenius V p (isInCharacteristic_of_hom g p hS)) :=
    H.isoPullback_hom_fst
  have hsnd : (frobeniusTwistBaseIso g p hS X).hom ≫
      pullback.snd (X.hom ≫ g) (absoluteFrobenius S p hS) =
      pullback.snd X.hom (absoluteFrobenius V p (isInCharacteristic_of_hom g p hS)) ≫ g :=
    H.isoPullback_hom_snd
  apply pullback.hom_ext
  · show (_ ≫ _) ≫ pullback.fst (X.hom ≫ g) (absoluteFrobenius S p hS) = _
    rw [Category.assoc, hfst, relativeFrobenius_fst]
    exact (relativeFrobenius_fst S p hS (Over.mk (X.hom ≫ g))).symm
  · show (_ ≫ _) ≫ pullback.snd (X.hom ≫ g) (absoluteFrobenius S p hS) = _
    rw [Category.assoc, hsnd, ← Category.assoc, relativeFrobenius_snd]
    exact (relativeFrobenius_snd S p hS (Over.mk (X.hom ≫ g))).symm

/-- Raising the coordinates to their `p`-th powers commutes with change of base. -/
private theorem affineSpacePower_naturality
    (n : Type u) {V S : Scheme.{u}} (g : V ⟶ S) (p : ℕ) :
    affineSpacePower n V p ≫ AffineSpace.map n g =
      AffineSpace.map n g ≫ affineSpacePower n S p := by
  apply AffineSpace.hom_ext
  · simp only [Category.assoc, AffineSpace.map_over, affineSpacePower_over]
    rw [← Category.assoc, affineSpacePower_over]
  · intro i
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply]
    simp only [AffineSpace.map_appTop_coord, affineSpacePower_appTop_coord, map_pow]

/-- The Frobenius twist of an affine scheme over an affine base is affine. -/
private theorem isAffine_frobeniusTwist_left
    (S : Scheme.{u}) [IsAffine S] (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p)
    (X : Over S) [IsAffine X.left] : IsAffine ((frobeniusTwist S p hS).obj X).left := by
  change IsAffine (pullback X.hom (absoluteFrobenius S p hS))
  infer_instance

/-- **The relative Frobenius of affine `d`-space over an affine base is a composition of `d`
`α_p`-covers, with a basis of `p ^ d` elements.** -/
private theorem relativeFrobenius_affineSpace_affine
    (n : Type u) [Fintype n] (S : Scheme.{u}) [IsAffine S]
    (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p) :
    IsAlphaPCoverComposite p
      (relativeFrobenius S p hS (Over.mk (AffineSpace n S ↘ S))).left ∧
    HasFiniteBasis (relativeFrobenius S p hS
      (Over.mk (AffineSpace n S ↘ S))).left.appTop.hom (p ^ Fintype.card n) := by
  let e := affineSpaceMapIso (n := n) S.isoSpec
  have hc := affineSpacePower_naturality n S.isoSpec.hom p
  have hp : (p : Γ(S, ⊤)) = 0 := hS
  have hcover := isAlphaPCoverComposite_of_iso p _ _ e e hc
    (isAlphaPCoverComposite_affineSpacePower_Spec n Γ(S, ⊤) p hp)
  have hb := hasFiniteBasis_appTop_of_iso _ _ e e hc _
    (hasFiniteBasis_affineSpacePower_Spec n Γ(S, ⊤) p (Fact.out : p.Prime).ne_zero)
  constructor
  · exact isAlphaPCoverComposite_of_iso p _ (affineSpacePower n S p)
      (Iso.refl _) (affineSpaceFrobeniusTwistIso n S p hS).symm
      (by rw [relativeFrobenius_affineSpace]; simp) hcover
  · exact hasFiniteBasis_appTop_of_iso _ (affineSpacePower n S p)
      (Iso.refl _) (affineSpaceFrobeniusTwistIso n S p hS).symm
      (by rw [relativeFrobenius_affineSpace]; simp) _ hb

/-- **The relative Frobenius of a scheme étale over affine `d`-space.**  Descending the previous
statement along the fibre square of the étale chart. -/
private theorem relativeFrobenius_of_affine_etale_chart
    (S : Scheme.{u}) [IsAffine S] (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (X : Over S) [IsAffine X.left]
    (n : Type u) [Fintype n]
    (π : X ⟶ Over.mk (AffineSpace n S ↘ S)) [Etale π.left] :
    IsAlphaPCoverComposite p (relativeFrobenius S p hS X).left ∧
    HasFiniteBasis (relativeFrobenius S p hS X).left.appTop.hom
      (p ^ Fintype.card n) := by
  have : IsAffine (Over.mk (AffineSpace n S ↘ S)).left :=
    inferInstanceAs (IsAffine (AffineSpace n S))
  have := isAffine_frobeniusTwist_left S p hS X
  have := isAffine_frobeniusTwist_left S p hS (Over.mk (AffineSpace n S ↘ S))
  have h := (isPullback_relativeFrobenius_of_etale S p hS π).flip
  obtain ⟨hc, hb⟩ := relativeFrobenius_affineSpace_affine n S p hS
  exact ⟨IsAlphaPCoverComposite.of_isPullback h p hc,
    HasFiniteBasis.of_isPullback_appTop h _ hb⟩

/-- **Locally on the Frobenius twist, the relative Frobenius of a smooth morphism of relative
dimension `d` is a composition of `α_p`-covers with a basis of `p ^ d` elements.**  This is the
local statement from which both conclusions of [Stacks, Tag 07QB] follow. -/
theorem exists_affine_relativeFrobenius_restriction
    (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p)
    (X : Over S) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (x : ((frobeniusTwist S p hS).obj X).left) :
    ∃ W : ((frobeniusTwist S p hS).obj X).left.Opens,
      IsAffineOpen W ∧ x ∈ W ∧
      IsAlphaPCoverComposite p ((relativeFrobenius S p hS X).left ∣_ W) ∧
      HasFiniteBasis ((relativeFrobenius S p hS X).left ∣_ W).appTop.hom (p ^ d) := by
  obtain ⟨x', hx'⟩ := relativeFrobenius_surjective S p hS X x
  obtain ⟨V, hV, U, hU, hxU, hUV, π, hπ, hcomm⟩ :=
    exists_etale_affineSpace_chart X.hom d x'
  have : IsAffine V.toScheme := hV
  have : IsAffine U.toScheme := hU
  have : Etale π := hπ
  let X₀ : Over V.toScheme := Over.mk (X.hom.resLE V U hUV)
  let π₀ : X₀ ⟶ Over.mk (AffineSpace (ULift.{u} (Fin d)) V.toScheme ↘ V.toScheme) :=
    Over.homMk π hcomm
  have : Etale π₀.left := hπ
  have : IsAffine X₀.left := hU
  obtain ⟨hc, hb⟩ := relativeFrobenius_of_affine_etale_chart V.toScheme p
    (isInCharacteristic_of_hom V.ι p hS) X₀ (ULift.{u} (Fin d)) π₀
  let X₁ : Over S := Over.mk (X₀.hom ≫ V.ι)
  let e := frobeniusTwistBaseIso V.ι p hS X₀
  have he := relativeFrobenius_comp_frobeniusTwistBaseIso V.ι p hS X₀
  have hcov : IsAlphaPCoverComposite p (relativeFrobenius S p hS X₁).left :=
    isAlphaPCoverComposite_of_iso p _ _ (Iso.refl _) e.symm
      (by rw [← he]; simp [e]) hc
  have hbas : HasFiniteBasis (relativeFrobenius S p hS X₁).left.appTop.hom (p ^ d) := by
    apply hasFiniteBasis_appTop_of_iso _
      (relativeFrobenius V.toScheme p (isInCharacteristic_of_hom V.ι p hS) X₀).left
      (Iso.refl _) e.symm (by rw [← he]; simp [e]) _
    simpa using hb
  have : IsAffine ((frobeniusTwist S p hS).obj X₁).left := by
    have := isAffine_frobeniusTwist_left V.toScheme p (isInCharacteristic_of_hom V.ι p hS) X₀
    exact IsAffine.of_isIso e.inv
  let i : X₁ ⟶ X := Over.homMk U.ι (by simp [X₁, X₀])
  have : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion U.ι)
  let j := ((frobeniusTwist S p hS).map i).left
  have : IsOpenImmersion j :=
    MorphismProperty.of_isPullback (isPullback_frobeniusTwist_map S p hS i).flip
      (inferInstanceAs (IsOpenImmersion i.left))
  have hi := isPullback_relativeFrobenius_of_etale S p hS i
  let W := j.opensRange
  let eY := j.isoOpensRange
  have hsq : IsPullback ((relativeFrobenius S p hS X₁).left ≫ eY.hom)
      i.left W.ι (relativeFrobenius S p hS X).left := by
    apply hi.of_iso (Iso.refl _) eY (Iso.refl _) (Iso.refl _) <;>
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    exact j.isoOpensRange_hom_ι.symm
  let hr := isPullback_morphismRestrict (relativeFrobenius S p hS X).left W
  let eX := hr.isoIsPullback _ _ hsq
  have hcompat : ((relativeFrobenius S p hS X).left ∣_ W) ≫ eY.inv =
      eX.hom ≫ (relativeFrobenius S p hS X₁).left := by
    rw [← cancel_mono eY.hom]
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      (hr.isoIsPullback_hom_fst _ _ hsq).symm
  refine ⟨W, isAffineOpen_opensRange j, ?_,
    isAlphaPCoverComposite_of_iso p _ _ eX eY.symm hcompat hcov,
    hasFiniteBasis_appTop_of_iso _ _ eX eY.symm hcompat _ hbas⟩
  show x ∈ Set.range j
  refine ⟨(relativeFrobenius S p hS X₁).left ⟨x', hxU⟩, ?_⟩
  exact (congrArg (fun k : U.toScheme ⟶ ((frobeniusTwist S p hS).obj X).left =>
    k ⟨x', hxU⟩) hi.w).trans hx'

/-- A basis of the sections over the whole of a restriction is a basis of the sections over the
open set it restricts to. -/
theorem hasFiniteBasis_app_of_morphismRestrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (n : ℕ)
    (h : HasFiniteBasis (f ∣_ U).appTop.hom n) : HasFiniteBasis (f.app U).hom n := by
  apply hasFiniteBasis_of_iso _ _ U.topIso.symm.commRingCatIsoToRingEquiv
    (f ⁻¹ᵁ U).topIso.symm.commRingCatIsoToRingEquiv ?_ n h
  apply CommRingCat.hom_ext_iff.mp
  show f.app U ≫ (f ⁻¹ᵁ U).topIso.inv = U.topIso.inv ≫ (f ∣_ U).appTop
  rw [← Scheme.Hom.resLE_eq_morphismRestrict]
  simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Scheme.Hom.appLE_eq_app]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-! ### The two conclusions of Tag 07QB -/

/-- **The relative Frobenius of a smooth morphism is an iterated `α_p`-cover.**  Let `S₀` be a
scheme in characteristic `p` and let `X` be an `S₀`-scheme smooth of relative dimension `d`.
Then `F_{X/S₀} : X ⟶ X^{(1)}` is an iterated `α_p`-cover.  This is the covering half of the first
sentence of [Stacks, Tag 07QB], over an arbitrary base in characteristic `p`; the tag itself is
registered in the source's own setting, in
`StacksFrontier/AlgebraicGeometry/Crystalline/AlphaPCoverFrobeniusTwistSituation.lean`. -/
theorem isIteratedAlphaPCover_relativeFrobenius
    (S₀ : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS₀ : IsInCharacteristic S₀ p)
    (X : Over S₀) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] :
    IsIteratedAlphaPCover p (relativeFrobenius S₀ p hS₀ X).left := by
  refine ⟨isInCharacteristic_of_hom ((frobeniusTwist S₀ p hS₀).obj X).hom p hS₀, ?_⟩
  intro x
  obtain ⟨W, _, hx, hc, _⟩ := exists_affine_relativeFrobenius_restriction S₀ p hS₀ X d x
  exact ⟨W, hx, hc⟩

/-- **The relative Frobenius of a smooth morphism has constant degree `p ^ d`.**  Let `S₀` be a
scheme in characteristic `p` and let `X` be an `S₀`-scheme smooth of relative dimension `d`.
Then `F_{X/S₀} : X ⟶ X^{(1)}` has constant degree `p ^ d`.  This is the degree half of the first
sentence of [Stacks, Tag 07QB], over an arbitrary base in characteristic `p`. -/
theorem hasConstantDegree_relativeFrobenius
    (S₀ : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS₀ : IsInCharacteristic S₀ p)
    (X : Over S₀) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] :
    HasConstantDegree (relativeFrobenius S₀ p hS₀ X).left (p ^ d) := by
  intro x
  obtain ⟨W, hW, hx, _, hb⟩ := exists_affine_relativeFrobenius_restriction S₀ p hS₀ X d x
  refine ⟨W, hW, hx, ?_⟩
  have : Nonempty (↑W : Type u) := ⟨⟨x, hx⟩⟩
  let _ := ((relativeFrobenius S₀ p hS₀ X).left.app W).hom.toAlgebra
  obtain ⟨b⟩ := hasFiniteBasis_app_of_morphismRestrict _ W (p ^ d) hb
  exact ⟨Module.Free.of_basis b, by simpa using rank_eq_card_basis b⟩

end AlgebraicGeometry

end
