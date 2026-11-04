module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Int.Interval
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.Basic
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.ProjectiveTrace

/-!
# Trace of an endomorphism of a perfect complex

An endomorphism of a perfect object of the derived category of a ring `R` has a trace in the
additive commutator quotient `Rⁿᵃᵗ`. It can be computed on any bounded complex of finite
projective modules representing the object, as the alternating sum of the traces in each degree;
the content of the construction is that this is independent of all the choices made.

## Main definitions

* `CategoryTheory.FilteredDerived.alternatingTrace`: the alternating sum of the degreewise traces
  of an endomorphism of a bounded complex of finite projective modules.
* `CategoryTheory.FilteredDerived.perfectDerivedTrace`: the trace of an endomorphism of a perfect
  object of the derived category.

## Main results

* `CategoryTheory.FilteredDerived.perfectDerivedTrace_eq_alternatingTrace`: the derived trace is
  computed by every finite projective representative and every representing cochain map.

## Implementation notes

The trace on a finite projective term is `Stacks.Trace.projectiveModuleTrace`. The definition of
the derived trace chooses a finite projective representative and a cochain representative of the
conjugated endomorphism, both of which exist because such a representative is K-projective.

## References

* [Stacks Project, Tag 03TI](https://stacks.math.columbia.edu/tag/03TI)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped BigOperators

universe u v

namespace CategoryTheory.FilteredDerived

attribute [local instance] HasDerivedCategory.standard

private noncomputable def traceAt (R : Type u) [Ring R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : finiteProjectiveComplex R P) (i : ℤ)
    (f : P.X i ⟶ P.X i) : AdditiveCommutatorQuotient R := by
  letI : Module.Projective R (P.X i) := (hP.2 i).1
  letI : Module.Finite R (P.X i) := (hP.2 i).2
  exact Stacks.Trace.projectiveModuleTrace R (P.X i) f.hom

private lemma traceAt_add (R : Type u) [Ring R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : finiteProjectiveComplex R P) (i : ℤ)
    (f g : P.X i ⟶ P.X i) :
    traceAt R P hP i (f + g) = traceAt R P hP i f + traceAt R P hP i g := by
  let : Module.Projective R (P.X i) := (hP.2 i).1
  let : Module.Finite R (P.X i) := (hP.2 i).2
  simpa [traceAt] using projectiveModuleTrace_add R (P.X i) f.hom g.hom

private noncomputable def signedTraceAt (R : Type u) [Ring R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : finiteProjectiveComplex R P) (i : ℤ)
    (f : P.X i ⟶ P.X i) : AdditiveCommutatorQuotient R :=
  if Even i then traceAt R P hP i f else -traceAt R P hP i f

private noncomputable def signedDegreeTrace (R : Type u) [Ring R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : finiteProjectiveComplex R P) (f : P ⟶ P) (i : ℤ) :
    AdditiveCommutatorQuotient R :=
  signedTraceAt R P hP i (f.f i)

private lemma traceAt_eq_zero_of_isZero (R : Type u) [Ring R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : finiteProjectiveComplex R P) (i : ℤ)
    (f : P.X i ⟶ P.X i) (hi : CategoryTheory.Limits.IsZero (P.X i)) :
    traceAt R P hP i f = 0 := by
  let : Module.Projective R (P.X i) := (hP.2 i).1
  let : Module.Finite R (P.X i) := (hP.2 i).2
  let : Subsingleton (P.X i) := ModuleCat.subsingleton_of_isZero hi
  exact projectiveModuleTrace_eq_zero_of_subsingleton R (P.X i) f.hom

/-- A bounded complex of finite projective modules has only finitely many nonzero terms. -/
public lemma finite_nonzero_degrees (R : Type u) [Ring R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : finiteProjectiveComplex R P) :
    {i : ℤ | ¬ CategoryTheory.Limits.IsZero (P.X i)}.Finite := by
  obtain ⟨lo, hlo⟩ := hP.1.1
  obtain ⟨hi, hhi⟩ := hP.1.2
  let : P.IsStrictlyGE lo := hlo
  let : P.IsStrictlyLE hi := hhi
  refine (Set.finite_Icc lo hi).subset fun i hi' => Set.mem_Icc.mpr ⟨?_, ?_⟩ <;> by_contra h
  · exact hi' (CochainComplex.isZero_of_isStrictlyGE P lo i (by lia))
  · exact hi' (CochainComplex.isZero_of_isStrictlyLE P hi i (by lia))

private lemma signedTraceAt_support_subset (R : Type u) [Ring R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : finiteProjectiveComplex R P)
    (f : ∀ i : ℤ, P.X i ⟶ P.X i) :
    Function.support (fun i => signedTraceAt R P hP i (f i)) ⊆
      {i | ¬ CategoryTheory.Limits.IsZero (P.X i)} := by
  intro i hi
  change signedTraceAt R P hP i (f i) ≠ 0 at hi
  by_contra hz
  have hzero : CategoryTheory.Limits.IsZero (P.X i) := not_not.mp hz
  have htrace : traceAt R P hP i (f i) = 0 := traceAt_eq_zero_of_isZero R P hP i (f i) hzero
  simp [signedTraceAt, htrace] at hi

private lemma signedTerm_neg_next {R : Type u} [Ring R] (i : ℤ)
    (x : AdditiveCommutatorQuotient R) :
    (if Even i then x else -x) = -(if Even (i + 1) then x else -x) := by
  by_cases hi : Even i
  · have hnext : ¬Even (i + 1) := by simpa [Int.even_add_one] using hi
    simp [hi, hnext]
  · have hnext : Even (i + 1) := by simpa [Int.even_add_one] using hi
    simp [hi, hnext]

/-- The alternating sum of the traces of the components of an endomorphism of a bounded
complex of finite projective modules. -/
@[sga "4½ Rapport 4.3", sga "5 IIIB 5.7"]
public noncomputable def alternatingTrace (R : Type u) [Ring R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : finiteProjectiveComplex R P)
    (f : P ⟶ P) : AdditiveCommutatorQuotient R :=
  ∑ᶠ i : ℤ, by
    letI : Module.Projective R (P.X i) := (hP.2 i).1
    letI : Projective (P.X i) := inferInstance
    letI : Module.Finite R (P.X i) := (hP.2 i).2
    let t := Stacks.Trace.projectiveModuleTrace R (P.X i) (f.f i).hom
    exact if Even i then t else -t

private lemma alternatingTrace_eq_of_homotopy (R : Type u) [Ring R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : finiteProjectiveComplex R P) {f g : P ⟶ P}
    (H : Homotopy f g) : alternatingTrace R P hP f = alternatingTrace R P hP g := by
  classical
  let T (q : P ⟶ P) (i : ℤ) := signedDegreeTrace R P hP q i
  let A (i : ℤ) := signedTraceAt R P hP i (dNext i H.hom)
  let B (i : ℤ) := signedTraceAt R P hP i (prevD i H.hom)
  have hD := finite_nonzero_degrees R P hP
  let s := hD.toFinset
  have hbound (q : ∀ i : ℤ, P.X i ⟶ P.X i) :
      Function.support (fun i => signedTraceAt R P hP i (q i)) ⊆ s := by
    intro i hi
    exact (Set.Finite.mem_toFinset hD).2 ((signedTraceAt_support_subset R P hP q) hi)
  have hTf : Function.support (T f) ⊆ s := by
    simpa [T, signedDegreeTrace] using hbound (fun i => (f.f i))
  have hTg : Function.support (T g) ⊆ s := by
    simpa [T, signedDegreeTrace] using hbound (fun i => (g.f i))
  have hA : Function.support A ⊆ s := by
    simpa [A] using hbound (fun i => dNext i H.hom)
  have hB : Function.support B ⊆ s := by
    simpa [B] using hbound (fun i => prevD i H.hom)
  have hAB : (∑ᶠ i : ℤ, A i) = -(∑ᶠ i : ℤ, B i) := by
    calc
      (∑ᶠ i : ℤ, A i) = ∑ᶠ i : ℤ, -B (i + 1) := by
        apply finsum_congr
        intro i
        have hd : dNext i H.hom = P.d i (i + 1) ≫ H.hom (i + 1) i :=
          dNext_eq H.hom (ComplexShape.up_mk i (i + 1) rfl)
        have hp : prevD (i + 1) H.hom = H.hom (i + 1) i ≫ P.d i (i + 1) :=
          prevD_eq H.hom (ComplexShape.up_mk i (i + 1) rfl)
        have hcyc : traceAt R P hP i (P.d i (i + 1) ≫ H.hom (i + 1) i) =
            traceAt R P hP (i + 1) (H.hom (i + 1) i ≫ P.d i (i + 1)) := by
          let : Module.Projective R (P.X i) := (hP.2 i).1
          let : Module.Finite R (P.X i) := (hP.2 i).2
          let : Module.Projective R (P.X (i + 1)) := (hP.2 (i + 1)).1
          let : Module.Finite R (P.X (i + 1)) := (hP.2 (i + 1)).2
          simpa [traceAt] using projectiveModuleTrace_cyclic R (P.X i) (P.X (i + 1))
            (P.d i (i + 1)).hom (H.hom (i + 1) i).hom
        show (if Even i then traceAt R P hP i (dNext i H.hom)
          else -traceAt R P hP i (dNext i H.hom)) =
          -(if Even (i + 1) then traceAt R P hP (i + 1) (prevD (i + 1) H.hom)
            else -traceAt R P hP (i + 1) (prevD (i + 1) H.hom))
        rw [hd, hp, hcyc]
        exact signedTerm_neg_next i _
      _ = ∑ᶠ j : ℤ, -B j := finsum_eq_of_bijective _ (Equiv.addRight 1).bijective fun _ => rfl
      _ = -(∑ᶠ j : ℤ, B j) := finsum_neg_distrib B
  have hpoint : ∀ i, T f i = T g i + A i + B i := by
    intro i
    have htrace : traceAt R P hP i (f.f i) =
        traceAt R P hP i (g.f i) + traceAt R P hP i (dNext i H.hom) +
          traceAt R P hP i (prevD i H.hom) := by
      rw [H.comm i, add_assoc, traceAt_add, traceAt_add]
      abel
    by_cases hi : Even i
    · simpa [T, A, B, signedDegreeTrace, signedTraceAt, hi] using htrace
    · simp only [T, A, B, signedDegreeTrace, signedTraceAt, ite_eq_right hi]
      rw [htrace]
      rw [neg_add, neg_add]
  show (∑ᶠ i : ℤ, T f i) = ∑ᶠ i : ℤ, T g i
  rw [finsum_eq_finsetSum_of_support_subset _ hTf,
    finsum_eq_finsetSum_of_support_subset _ hTg]
  calc
    (∑ i ∈ s, T f i) = ∑ i ∈ s, (T g i + A i + B i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hpoint i
    _ = (∑ i ∈ s, T g i) + ((∑ i ∈ s, A i) + ∑ i ∈ s, B i) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      abel
    _ = (∑ i ∈ s, T g i) + ((∑ᶠ i : ℤ, A i) + ∑ᶠ i : ℤ, B i) := by
      rw [← finsum_eq_finsetSum_of_support_subset _ hA,
        ← finsum_eq_finsetSum_of_support_subset _ hB]
    _ = ∑ i ∈ s, T g i := by rw [hAB]; simp

@[sga "5 III 4.1" "4.1.5, special case",
  sga "5 IIIB 1.1" "partial",
  sga "5 IIIB 5.8" "special case"]
private lemma alternatingTrace_cyclic (R : Type u) [Ring R]
    (P Q : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : finiteProjectiveComplex R P)
    (hQ : finiteProjectiveComplex R Q)
    (a : P ⟶ Q) (b : Q ⟶ P) :
    alternatingTrace R P hP (a ≫ b) = alternatingTrace R Q hQ (b ≫ a) := by
  classical
  show (∑ᶠ i : ℤ, signedDegreeTrace R P hP (a ≫ b) i) =
    ∑ᶠ i : ℤ, signedDegreeTrace R Q hQ (b ≫ a) i
  apply finsum_congr
  intro i
  let : Module.Projective R (P.X i) := (hP.2 i).1
  let : Module.Finite R (P.X i) := (hP.2 i).2
  let : Module.Projective R (Q.X i) := (hQ.2 i).1
  let : Module.Finite R (Q.X i) := (hQ.2 i).2
  have hcyc : traceAt R P hP i (a.f i ≫ b.f i) =
      traceAt R Q hQ i (b.f i ≫ a.f i) := by
    simpa [traceAt] using projectiveModuleTrace_cyclic R (P.X i) (Q.X i)
      (a.f i).hom (b.f i).hom
  simp [signedDegreeTrace, signedTraceAt, hcyc]

/-- A bounded complex of finite projective modules is K-projective. -/
private lemma isKProjective_of_finiteProjectiveComplex (R : Type u) [Ring R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : finiteProjectiveComplex R P) : CochainComplex.IsKProjective P := by
  obtain ⟨⟨_, ⟨d, hd⟩⟩, hproj⟩ := hP
  let : P.IsStrictlyLE d := hd
  let (i : ℤ) : Module.Projective R (P.X i) := (hproj i).1
  let (i : ℤ) : Projective (P.X i) := inferInstance
  exact CochainComplex.isKProjective_of_projective P d

/-- The trace of an endomorphism of a perfect object of the derived category. -/
public noncomputable def perfectDerivedTrace (R : Type u) [Ring R]
    (K : PerfectDerivedCategory.{u, v} R) (f : K.obj ⟶ K.obj) :
    AdditiveCommutatorQuotient R := by
  let h := (isPerfect_iff R K.obj).mp K.property
  let P := h.choose
  let hP := h.choose_spec.1
  let e := h.choose_spec.2.some
  letI : CochainComplex.IsKProjective P := by
    obtain ⟨⟨_, ⟨d, hd⟩⟩, hproj⟩ := hP
    let : P.IsStrictlyLE d := hd
    let (i : ℤ) : Module.Projective R (P.X i) := (hproj i).1
    let (i : ℤ) : Projective (P.X i) := inferInstance
    exact CochainComplex.isKProjective_of_projective P d
  let qP := (HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).obj P
  let α : DerivedCategory.Qh.obj qP ≅ K.obj :=
    (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).app P ≪≫ e
  let gₕ : qP ⟶ qP :=
    (CochainComplex.IsKProjective.Qh_map_bijective P qP).surjective
      (α.hom ≫ f ≫ α.inv) |>.choose
  let g : P ⟶ P :=
    (HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).preimage gₕ
  exact alternatingTrace R P hP g

/-- The trace of an endomorphism of a perfect derived object is computed on any bounded
finite-projective representative, and hence is independent of the representative, the chosen
isomorphism, and the cochain map representing the endomorphism. -/
@[stacks 03TI]
public theorem perfectDerivedTrace_eq_alternatingTrace (R : Type u) [Ring R]
    (K : PerfectDerivedCategory.{u, v} R) (f : K.obj ⟶ K.obj)
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : finiteProjectiveComplex R P)
    (e : DerivedCategory.Q.obj P ≅ K.obj) (g : P ⟶ P)
    (hg : DerivedCategory.Q.map g = e.hom ≫ f ≫ e.inv) :
    perfectDerivedTrace R K f = alternatingTrace R P hP g := by
  classical
  let h := (isPerfect_iff R K.obj).mp K.property
  let P0 := h.choose
  let hP0 := h.choose_spec.1
  let e0 := h.choose_spec.2.some
  have : CochainComplex.IsKProjective P0 := isKProjective_of_finiteProjectiveComplex R P0 hP0
  have : CochainComplex.IsKProjective P := isKProjective_of_finiteProjectiveComplex R P hP
  let Q := HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)
  let q0 := Q.obj P0
  let q := Q.obj P
  let α0 : DerivedCategory.Qh.obj q0 ≅ K.obj :=
    (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).app P0 ≪≫ e0
  let α : DerivedCategory.Qh.obj q ≅ K.obj :=
    (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).app P ≪≫ e
  let g0H : q0 ⟶ q0 :=
    (CochainComplex.IsKProjective.Qh_map_bijective P0 q0).surjective
      (α0.hom ≫ f ≫ α0.inv) |>.choose
  have hg0H : (DerivedCategory.Qh).map g0H = α0.hom ≫ f ≫ α0.inv :=
    (CochainComplex.IsKProjective.Qh_map_bijective P0 q0).surjective
      (α0.hom ≫ f ≫ α0.inv) |>.choose_spec
  let g0 : P0 ⟶ P0 := Q.preimage g0H
  have hg0 : Q.map g0 = g0H := by simp [g0]
  obtain ⟨uH, huH⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P0 q).surjective
    (α0.hom ≫ α.inv)
  obtain ⟨vH, hvH⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P q0).surjective
    (α.hom ≫ α0.inv)
  have hconj : α.inv ≫ (DerivedCategory.Qh).map (Q.map g) ≫ α.hom = f := by
    show (e.inv ≫ (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).inv.app P) ≫
        (DerivedCategory.Qh).map (Q.map g) ≫
        ((DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).hom.app P ≫ e.hom) = f
    simp only [Category.assoc]
    rw [← DerivedCategory.quotientCompQhIso_inv_naturality_assoc, Iso.inv_hom_id_app_assoc, hg]
    simp
  have hconjH : uH ≫ Q.map g ≫ vH = g0H := by
    apply (CochainComplex.IsKProjective.Qh_map_bijective P0 q0).injective
    calc
      (DerivedCategory.Qh).map (uH ≫ Q.map g ≫ vH) =
          α0.hom ≫ (α.inv ≫ (DerivedCategory.Qh).map (Q.map g) ≫ α.hom) ≫ α0.inv := by
        simp [Functor.map_comp, huH, hvH, Category.assoc]
      _ = (DerivedCategory.Qh).map g0H := by rw [hconj, hg0H]
  have hVU : vH ≫ uH = 𝟙 q := by
    apply (CochainComplex.IsKProjective.Qh_map_bijective P q).injective
    simp only [Functor.map_comp, hvH, huH]
    rw [CategoryTheory.Functor.map_id]
    simp [Category.assoc]
  let u : P0 ⟶ P := Q.preimage uH
  let v : P ⟶ P0 := Q.preimage vH
  have hu : Q.map u = uH := by simp [u]
  have hv : Q.map v = vH := by simp [v]
  have h0 : Homotopy g0 (u ≫ g ≫ v) := HomotopyCategory.homotopyOfEq _ _ <| by
    show Q.map g0 = Q.map (u ≫ g ≫ v)
    rw [hg0, Q.map_comp, Q.map_comp, hu, hv, hconjH]
  have hHomVU : Homotopy (v ≫ u) (𝟙 P) := HomotopyCategory.homotopyOfEq _ _ <| by
    show Q.map (v ≫ u) = Q.map (𝟙 P)
    rw [Q.map_comp, Q.map_id, hv, hu, hVU]
  show alternatingTrace R P0 hP0 g0 = alternatingTrace R P hP g
  calc
    alternatingTrace R P0 hP0 g0 = alternatingTrace R P0 hP0 (u ≫ g ≫ v) :=
      alternatingTrace_eq_of_homotopy R P0 hP0 h0
    _ = alternatingTrace R P hP (v ≫ u ≫ g) := by
      simpa [Category.assoc] using alternatingTrace_cyclic R P0 P hP0 hP (u ≫ g) v
    _ = alternatingTrace R P hP g :=
      alternatingTrace_eq_of_homotopy R P hP (Homotopy.compRightId hHomVU g)

end CategoryTheory.FilteredDerived
