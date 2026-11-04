module

public import StacksFrontier.Deformation.Formal.MinimalVersal.PowerSeriesDecomposition
public import StacksFrontier.Deformation.FormalObject.ProrepresentableMorphism
public import StacksFrontier.RingTheory.MvPowerSeries.KrullDimension

/-!
# Points of power series algebras in the completed base category

For a Noetherian complete local `Λ`-algebra `R` with residue field `k` and `n : ℕ`, a morphism
`R[[x_1, …, x_n]] ⟶ T` of the completed base category `\widehat{\mathcal C}_Λ` is the same as a
morphism `R ⟶ T` together with `n` elements of the maximal ideal of `T`. This file records that
universal property, its transport along a map exhibiting its target as a power series ring
(`Deformation.IsPowerSeriesOver`), and the Yoneda principle that a morphism inducing a bijection
on all Artinian points is an isomorphism.

## Main results

* `Deformation.mvPowerSeries_ringHom_ext`: two ring maps out of `R[[x_1, …, x_n]]` into a
  Noetherian local ring agreeing on constants and on variables, the variables going to the
  maximal ideal, are equal.
* `Deformation.mvPowerSeriesLift`, `Deformation.mvPowerSeriesObject_hom_ext`: existence and
  uniqueness of morphisms out of `mvPowerSeriesObject R n`.
* `Deformation.IsPowerSeriesOver.exists_coordinates`: coordinates for a power series map, with
  the resulting universal property and dimension formula.
* `Deformation.isIso_of_restrictedCoyonedaMap_app_bijective`: Yoneda reflection of
  isomorphisms for the restricted representable functors (Stacks 06HD).

## Implementation notes

Uniqueness is proved without topology: the difference of the two maps is additive, kills
constants and variables, and satisfies a Leibniz rule, so writing a power series as its constant
term plus a combination of the variables shows inductively that its value lies in every power of
the maximal ideal; Krull's intersection theorem finishes. Existence is
`Deformation.mvPowerSeriesEval`.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u v w

namespace Deformation

/-- **Ring maps out of a power series ring are determined by constants and variables.** Two ring
maps from `R[[x_1, …, x_n]]` to a Noetherian local ring which agree on constants and on the
variables, the variables going into the maximal ideal, are equal. -/
public theorem mvPowerSeries_ringHom_ext {R T : Type*} [CommRing R] [CommRing T] [IsLocalRing T]
    [IsNoetherianRing T] {n : ℕ} (g g' : MvPowerSeries (Fin n) R →+* T)
    (hC : ∀ a, g (MvPowerSeries.C a) = g' (MvPowerSeries.C a))
    (hX : ∀ i, g (MvPowerSeries.X i) = g' (MvPowerSeries.X i))
    (hXm : ∀ i, g' (MvPowerSeries.X i) ∈ maximalIdeal T) : g = g' := by
  have key : ∀ N : ℕ, ∀ s : MvPowerSeries (Fin n) R, g s - g' s ∈ maximalIdeal T ^ N := by
    intro N
    induction N with
    | zero => intro s; simp
    | succ N ih =>
      intro s
      have hmem : s - MvPowerSeries.C (MvPowerSeries.constantCoeff s) ∈
          Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) R)) := by
        rw [MvPowerSeries.span_X_eq_ker_constantCoeff, RingHom.mem_ker]
        simp
      obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
      have hs :
          s = MvPowerSeries.C (MvPowerSeries.constantCoeff s) + ∑ i, a i * MvPowerSeries.X i := by
        rw [ha]; ring
      have hdiff : g s - g' s = ∑ i, (g (a i) - g' (a i)) * g' (MvPowerSeries.X i) := by
        conv_lhs => rw [hs]
        simp only [map_add, map_sum, map_mul, hC, hX, sub_mul, Finset.sum_sub_distrib]
        ring
      rw [hdiff, pow_succ]
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (ih (a i)) (hXm i)
  ext s
  have hbot : g s - g' s ∈ (⊥ : Ideal T) := by
    rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal T) (maximalIdeal.isMaximal T).ne_top]
    exact Ideal.mem_iInf.2 fun N => key N s
  exact sub_eq_zero.mp ((Submodule.mem_bot T).mp hbot)

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **Residue compatibility from a factorization.** A local ring map `h : S → T` between
complete local algebras which restricts along a morphism `f : R ⟶ S` to a morphism `g : R ⟶ T`
respects the identifications of the residue fields with `k`: every element of `S` agrees with
the image of an element of `R` modulo the maximal ideal. -/
public theorem residue_comm_of_comp {R S T : CompleteLocalAlgCat.{u, v, w} Λ k}
    (f : R ⟶ S) (g : R ⟶ T) (h : S →+* T) (hh : IsLocalHom h)
    (hfg : ∀ a, h (f.hom a) = g.hom a) (s : S) :
    T.residueEquiv (residue T (h s)) = S.residueEquiv (residue S s) := by
  obtain ⟨a, ha⟩ : ∃ a : R, R.residueEquiv (residue R a) = S.residueEquiv (residue S s) := by
    obtain ⟨y, hy⟩ := R.residueEquiv.surjective (S.residueEquiv (residue S s))
    obtain ⟨a, rfl⟩ := residue_surjective y
    exact ⟨a, hy⟩
  have hfa : residue S (f.hom a) = residue S s :=
    S.residueEquiv.injective ((f.residue_comm a).trans ha)
  have hsub : h s - g.hom a ∈ maximalIdeal T := by
    rw [← hfg a, ← map_sub]
    exact @map_nonunit _ _ _ _ _ _ h hh _ (Ideal.Quotient.eq.mp hfa.symm)
  have hres : residue T (h s) = residue T (g.hom a) := Ideal.Quotient.eq.mpr hsub
  rw [hres, g.residue_comm a, ha]

/-- A ring isomorphism between local rings carries the maximal ideal into the maximal ideal. -/
public theorem map_mem_maximalIdeal_of_ringEquiv {S T : Type*} [CommRing S] [CommRing T]
    [IsLocalRing S] [IsLocalRing T] (σ : S ≃+* T) {s : S} (hs : s ∈ maximalIdeal S) :
    σ s ∈ maximalIdeal T := by
  rw [mem_maximalIdeal, mem_nonunits_iff] at hs ⊢
  intro hu
  exact hs (by simpa using hu.map σ.symm.toRingHom)

/-- `mvPowerSeriesEval` is a local ring map. -/
public theorem isLocalHom_mvPowerSeriesEval {R T : CompleteLocalAlgCat.{u, v, w} Λ k} {n : ℕ}
    (f : R ⟶ T) (x : Fin n → T) (hx : ∀ i, x i ∈ maximalIdeal T) :
    IsLocalHom (mvPowerSeriesEval f x hx) := by
  refine ⟨fun s hu => ?_⟩
  by_contra hs
  have hsm : s ∈ maximalIdeal (MvPowerSeries (Fin n) R) := (mem_maximalIdeal _).2 hs
  rw [mem_maximalIdeal_mvPowerSeries_iff] at hsm
  exact (mem_maximalIdeal _).1 (mvPowerSeriesEval_mem_maximalIdeal f x hx s hsm) hu

/-- **The morphism out of a power series algebra** determined by a morphism on coefficients and
the images of the variables, taken in the maximal ideal of the target. -/
public noncomputable def mvPowerSeriesLift {R T : CompleteLocalAlgCat.{u, v, w} Λ k} {n : ℕ}
    (f : R ⟶ T) (x : Fin n → T) (hx : ∀ i, x i ∈ maximalIdeal T) :
    mvPowerSeriesObject R n ⟶ T :=
  letI := isLocalHom_mvPowerSeriesEval f x hx
  { hom :=
      { toRingHom := mvPowerSeriesEval f x hx
        commutes' := by
          intro a
          change mvPowerSeriesEval f x hx (algebraMap Λ (MvPowerSeries (Fin n) R) a) = _
          rw [MvPowerSeries.algebraMap_apply, mvPowerSeriesEval_C]
          exact f.hom.commutes a }
    isLocal := isLocalHom_mvPowerSeriesEval f x hx
    residue_comm := fun s =>
      residue_comm_of_comp (mvPowerSeriesCoeffMap R n) f (mvPowerSeriesEval f x hx)
        (isLocalHom_mvPowerSeriesEval f x hx) (fun a => mvPowerSeriesEval_C f x hx a) s }

/-- `mvPowerSeriesLift f x hx` agrees with `f` on constant power series. -/
@[simp]
public theorem mvPowerSeriesLift_hom_C {R T : CompleteLocalAlgCat.{u, v, w} Λ k} {n : ℕ}
    (f : R ⟶ T) (x : Fin n → T) (hx : ∀ i, x i ∈ maximalIdeal T) (a : R) :
    (mvPowerSeriesLift f x hx).hom (MvPowerSeries.C a) = f.hom a :=
  mvPowerSeriesEval_C f x hx a

/-- `mvPowerSeriesLift f x hx` sends the variable `X i` to `x i`. -/
@[simp]
public theorem mvPowerSeriesLift_hom_X {R T : CompleteLocalAlgCat.{u, v, w} Λ k} {n : ℕ}
    (f : R ⟶ T) (x : Fin n → T) (hx : ∀ i, x i ∈ maximalIdeal T) (i : Fin n) :
    (mvPowerSeriesLift f x hx).hom (MvPowerSeries.X i) = x i :=
  mvPowerSeriesEval_X f x hx i

/-- The composite of the coefficient map with `mvPowerSeriesLift f x hx` is `f`. -/
public theorem mvPowerSeriesCoeffMap_comp_lift {R T : CompleteLocalAlgCat.{u, v, w} Λ k}
    {n : ℕ} (f : R ⟶ T) (x : Fin n → T) (hx : ∀ i, x i ∈ maximalIdeal T) :
    mvPowerSeriesCoeffMap R n ≫ mvPowerSeriesLift f x hx = f :=
  CompleteLocalAlgCat.Hom.ext (AlgHom.ext (mvPowerSeriesEval_C f x hx))

/-- The variables of `R[[x_1, …, x_n]]` lie in its maximal ideal. -/
public theorem mvPowerSeries_X_mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R]
    {n : ℕ} (i : Fin n) : (MvPowerSeries.X i : MvPowerSeries (Fin n) R) ∈
      maximalIdeal (MvPowerSeries (Fin n) R) := by
  rw [mem_maximalIdeal_mvPowerSeries_iff]
  simp

/-- A morphism of complete local algebras sends the maximal ideal into the maximal ideal. -/
private theorem hom_mem_maximalIdeal {S T : CompleteLocalAlgCat.{u, v, w} Λ k} (b : S ⟶ T)
    {s : S} (hs : s ∈ maximalIdeal S) : b.hom s ∈ maximalIdeal T := by
  have : IsLocalHom b.hom.toRingHom := b.isLocal
  exact map_nonunit b.hom.toRingHom _ hs

/-- **Morphisms out of a power series algebra are determined by constants and variables.** -/
public theorem mvPowerSeriesObject_hom_ext {R T : CompleteLocalAlgCat.{u, v, w} Λ k} {n : ℕ}
    (g g' : mvPowerSeriesObject R n ⟶ T)
    (hC : mvPowerSeriesCoeffMap R n ≫ g = mvPowerSeriesCoeffMap R n ≫ g')
    (hX : ∀ i, g.hom (MvPowerSeries.X i) = g'.hom (MvPowerSeries.X i)) : g = g' := by
  refine CompleteLocalAlgCat.Hom.ext (AlgHom.ext fun s => DFunLike.congr_fun
    (mvPowerSeries_ringHom_ext (R := R) (T := T) (n := n) g.hom.toRingHom g'.hom.toRingHom
      (fun a => congrArg (fun φ : R ⟶ T => φ.hom a) hC) hX fun i =>
      hom_mem_maximalIdeal g' (mvPowerSeries_X_mem_maximalIdeal i)) s)

/-- **Coordinates for a power series map.** A morphism `f : R ⟶ S` exhibiting `S` as a power
series ring over `R` has coordinates `c_1, …, c_n` in the maximal ideal of `S`, for which a
morphism out of `S` is the same as a morphism out of `R` together with `n` elements of the
maximal ideal of the target; moreover `dim S = dim R + n`. -/
public theorem IsPowerSeriesOver.exists_coordinates {R S : CompleteLocalAlgCat.{u, v, w} Λ k}
    {f : R ⟶ S} (hf : IsPowerSeriesOver f) :
    ∃ (n : ℕ) (c : Fin n → S), (∀ i, c i ∈ maximalIdeal S) ∧
      ringKrullDim S = ringKrullDim R + n ∧
      (∀ {T : CompleteLocalAlgCat.{u, v, w} Λ k} (b b' : S ⟶ T), f ≫ b = f ≫ b' →
        (∀ i, b.hom (c i) = b'.hom (c i)) → b = b') ∧
      (∀ {T : CompleteLocalAlgCat.{u, v, w} Λ k} (g : R ⟶ T) (x : Fin n → T),
        (∀ i, x i ∈ maximalIdeal T) → ∃ b : S ⟶ T, f ≫ b = g ∧ ∀ i, b.hom (c i) = x i) := by
  let : Algebra R S := f.hom.toRingHom.toAlgebra
  obtain ⟨n, ⟨σ⟩⟩ := hf
  have hσC : ∀ a : R, σ (f.hom a) = MvPowerSeries.C a := fun a => by
    have h := σ.commutes a
    rw [MvPowerSeries.algebraMap_apply] at h
    exact h.trans (by simp)
  refine ⟨n, fun i => σ.symm (MvPowerSeries.X i), fun i => ?_, ?_, ?_, ?_⟩
  · exact map_mem_maximalIdeal_of_ringEquiv σ.symm.toRingEquiv
      (mvPowerSeries_X_mem_maximalIdeal i)
  · rw [ringKrullDim_eq_of_ringEquiv σ.toRingEquiv]
    exact MvPowerSeries.ringKrullDim_fin_eq_add R n
  · intro T b b' hbb hc
    have h := mvPowerSeries_ringHom_ext (R := R) (T := T) (n := n)
      (b.hom.toRingHom.comp σ.symm.toRingEquiv.toRingHom)
      (b'.hom.toRingHom.comp σ.symm.toRingEquiv.toRingHom)
      (fun a => by
        have hS : σ.symm (MvPowerSeries.C a) = f.hom a := by
          rw [← hσC a, AlgEquiv.symm_apply_apply]
        simp only [RingHom.comp_apply]
        show b.hom (σ.symm (MvPowerSeries.C a)) = b'.hom (σ.symm (MvPowerSeries.C a))
        rw [hS]
        exact congrArg (fun φ : R ⟶ T => φ.hom a) hbb)
      hc
      (fun i => hom_mem_maximalIdeal b' (map_mem_maximalIdeal_of_ringEquiv
        σ.symm.toRingEquiv (mvPowerSeries_X_mem_maximalIdeal i)))
    exact CompleteLocalAlgCat.Hom.ext
      (AlgHom.ext fun s => by simpa using DFunLike.congr_fun h (σ s))
  · intro T g x hx
    let ev := mvPowerSeriesEval g x hx
    have : IsLocalHom ev := isLocalHom_mvPowerSeriesEval g x hx
    let h : S →+* T := ev.comp σ.toRingEquiv.toRingHom
    have hloc : IsLocalHom h := ⟨fun s hu => by
      simpa using (IsLocalHom.map_nonunit (f := ev) (σ s) hu).map σ.symm.toRingEquiv.toRingHom⟩
    have hfac : ∀ a, h (f.hom a) = g.hom a := fun a => by
      show ev (σ (f.hom a)) = _
      rw [hσC a]
      exact mvPowerSeriesEval_C g x hx a
    refine ⟨{ hom :=
                { toRingHom := h
                  commutes' := fun a => by
                    rw [← f.hom.commutes a]
                    show h (f.hom (algebraMap Λ R a)) = _
                    rw [hfac]
                    exact g.hom.commutes a }
              isLocal := hloc
              residue_comm := fun s => residue_comm_of_comp f g h hloc hfac s }, ?_, ?_⟩
    · exact CompleteLocalAlgCat.Hom.ext (AlgHom.ext hfac)
    · intro i
      show ev (σ (σ.symm (MvPowerSeries.X i))) = x i
      rw [AlgEquiv.apply_symm_apply]
      exact mvPowerSeriesEval_X g x hx i

/-- Precomposition with a composite is the composite of the precompositions, in the opposite
order. -/
public theorem restrictedCoyonedaMap_comp {R S T : CompleteLocalAlgCat.{u, v, w} Λ k}
    (f : R ⟶ S) (g : S ⟶ T) :
    restrictedCoyonedaMap (f ≫ g) = restrictedCoyonedaMap g ≫ restrictedCoyonedaMap f := by
  ext A x
  rfl

/-- Precomposition with the identity is the identity. -/
public theorem restrictedCoyonedaMap_id (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    restrictedCoyonedaMap (𝟙 R) = 𝟙 (restrictedCoyoneda R) := by
  ext A x
  rfl

/-- **Yoneda reflection of isomorphisms (Stacks 06HD).** A morphism of complete local algebras
inducing a bijection on the points with values in every Artinian local algebra is an
isomorphism. -/
public theorem isIso_of_restrictedCoyonedaMap_app_bijective
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S)
    (h : ∀ A, Function.Bijective ((restrictedCoyonedaMap f).app A)) : IsIso f := by
  have : IsIso (restrictedCoyonedaMap f) :=
    (NatTrans.isIso_iff_isIso_app _).2 fun A => (isIso_iff_bijective _).2 (h A)
  obtain ⟨g, hg⟩ := (restrictedCoyonedaMap_bijective S R).2 (inv (restrictedCoyonedaMap f))
  refine ⟨g, ?_, ?_⟩
  · apply (restrictedCoyonedaMap_bijective R R).1
    rw [restrictedCoyonedaMap_comp, hg, IsIso.inv_hom_id, restrictedCoyonedaMap_id]
  · apply (restrictedCoyonedaMap_bijective S S).1
    rw [restrictedCoyonedaMap_comp, hg, IsIso.hom_inv_id, restrictedCoyonedaMap_id]

/-- Isomorphic complete local algebras have the same Krull dimension. -/
public theorem ringKrullDim_eq_of_isIso {R S : CompleteLocalAlgCat.{u, v, w} Λ k}
    (f : R ⟶ S) [IsIso f] : ringKrullDim R = ringKrullDim S := by
  let e : R ≃+* S :=
    { toFun := f.hom
      invFun := (inv f).hom
      left_inv := fun r => congrArg (fun φ : R ⟶ R => φ.hom r) (IsIso.hom_inv_id f)
      right_inv := fun s => congrArg (fun φ : S ⟶ S => φ.hom s) (IsIso.inv_hom_id f)
      map_mul' := map_mul f.hom
      map_add' := map_add f.hom }
  exact ringKrullDim_eq_of_ringEquiv e

end Deformation

end
