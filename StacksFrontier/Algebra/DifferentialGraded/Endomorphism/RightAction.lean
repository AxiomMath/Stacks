module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.RightModuleHom
public import StacksFrontier.Homology.HomComplex.Basic

/-!
# Right differential graded actions on a complex, their shifts, and Hom complexes

Let `R` be a commutative ring, `A` a differential graded `R`-algebra and `M` a cochain complex of
`R`-modules. A *right differential graded action* of `A` on `M` is the right-handed companion of
`DifferentialGradedAlgebra.LeftAction`: an `R`-linear map from each homogeneous piece `A^n` to the
degree-`n` cochains `M → M`, recorded in the signed presentation of Tag 0FQ5, so that a
homogeneous element of degree `n` acts on an element of degree `p` by `(-1)^{np}` times right
multiplication. Consequently its multiplicativity reverses the factors and carries the Koszul
sign, while its Leibniz rule carries none.

Both kinds of action can be shifted, and a right action on `M` induces a left action on the Hom
complex `Hom^•(M, N)`, by signed precomposition. These are the module structures of Section 22.26
of the Stacks project.

## Main definitions

* `DifferentialGradedAlgebra.RightAction`: a right differential graded action on a fixed complex.
* `DifferentialGradedAlgebra.LeftAction.shift` and `DifferentialGradedAlgebra.RightAction.shift`:
  the shift of a left, resp. right, differential graded action.
* `DifferentialGradedAlgebra.LeftAction.homAction`: the action of a homogeneous element of the
  algebra on a homogeneous cochain, for a left action on a Hom complex.
* `DifferentialGradedAlgebra.RightAction.homLeftActionComponent` and
  `DifferentialGradedAlgebra.RightAction.homLeftActionCochain`: signed precomposition with a right
  differential graded action, on homogeneous cochains and as a cochain of the Hom complex.
* `DifferentialGradedAlgebra.RightAction.homLeftAction`: the left differential graded action on
  `Hom^•(M, N)` induced by a right differential graded action on `M`.
* `DifferentialGradedAlgebra.Opposite.gradingEquiv`: the identification of the homogeneous parts
  of a graded opposite of `A` with those of `A`.
* `DifferentialGradedAlgebra.Opposite.rightAction`: the right differential graded action of `A`
  attached to a left differential graded action of a graded opposite of `A`.

## Main results

* `DifferentialGradedModule.exists_rightAction`: a right differential graded module gives a right
  differential graded action on any complex identified with its underlying complex, with the
  signed formula of Tag 0FQ5.
* `DifferentialGradedAlgebra.LeftAction.shift_action` and
  `DifferentialGradedAlgebra.RightAction.shift_action`: on homogeneous elements both shifts are
  the Koszul sign `(-1)^{pk}` times the given action.
* `DifferentialGradedAlgebra.RightAction.homLeftAction_homAction`: the induced left action on
  `Hom^•(M, N)` is `(-1)^{pq}` times precomposition with the signed right action.
* `CochainComplex.HomComplex.Cochain.shift_comp` and
  `CochainComplex.HomComplex.Cochain.shift_ofHom_id`: the degreewise shift of cochains is
  multiplicative, with no sign, and fixes the identity cochain.
* `DifferentialGradedAlgebra.Opposite.rightActionCochain_one`,
  `DifferentialGradedAlgebra.Opposite.rightActionCochain_mul` and
  `DifferentialGradedAlgebra.Opposite.rightActionCochain_d`: the three laws of that right action,
  where the Koszul sign of `RightAction.map_mul` comes from the graded opposite reversing the
  order twice.

## Implementation notes

*The sign of each shift is forced.* Definition 22.26.1 shifts a right module without signs, but
in the signed presentation of Tag 0FQ5 the factor `(-1)^{pk}` still appears, because the degree of
an element changes by `k` under the shift; shifting a left module inserts the Koszul factor
`(-1)^{pk}` outright. This is why `LeftAction.shift` and `RightAction.shift` are given by the same
formula. The computation that makes both well defined is that the shift of cochains is
multiplicative without signs (`Cochain.shift_comp`) and changes the Hom-complex differential by
exactly `(-1)^k` (`Cochain.δ_shift`), which is the sign the Leibniz rule absorbs.

*The left action on a Hom complex needs a sign.* A degree-`p` element acts on a degree-`q` cochain
by `(-1)^{pq}` times precomposition with the signed right action; this is the explicit formula of
Section 22.26, and it is what makes multiplicativity and the Leibniz rule come out. Because a
homogeneous piece of the Hom complex is itself a module of cochains, the action is read through
`LeftAction.homAction`, which applies the acting cochain to a cochain of the given degree.

*The bridge to right differential graded modules is Tag 0FQ5.* A right module structure on a
complex is the same as a homomorphism into the graded opposite of its endomorphism algebra, and
the cochain attached to a homogeneous element by such a homomorphism is
`DifferentialGradedModule.oppEndCochain`; the three laws of `RightAction` are then the
multiplicativity and differential compatibility already proved for it.

## References

* [Stacks Project, Tag 0FQ1](https://stacks.math.columbia.edu/tag/0FQ1)
* [Stacks Project, Tag 0FQ2](https://stacks.math.columbia.edu/tag/0FQ2)
* [Stacks Project, Tag 0FQ5](https://stacks.math.columbia.edu/tag/0FQ5)
-/

@[expose] public section

open CategoryTheory CochainComplex CochainComplex.HomComplex

universe u v

variable {R : Type u} [CommRing R]

namespace CochainComplex.HomComplex.Cochain

variable {C : Type*} [Category C] [Preadditive C]

/-- Shifting a composite of cochains is the composite of the shifts; no sign intervenes. -/
theorem shift_comp {K L M : CochainComplex C ℤ} {n₁ n₂ n₁₂ : ℤ}
    (z₁ : Cochain K L n₁) (z₂ : Cochain L M n₂) (h : n₁ + n₂ = n₁₂) (k : ℤ) :
    (z₁.comp z₂ h).shift k = (z₁.shift k).comp (z₂.shift k) h :=
  Cochain.ext _ _ fun p q hpq => by
    rw [Cochain.shift_v' _ k p q hpq,
      Cochain.comp_v _ _ h (p + k) (p + n₁ + k) (q + k) (by omega) (by omega),
      Cochain.comp_v _ _ h p (p + n₁) q rfl (by omega),
      Cochain.shift_v' z₁ k p (p + n₁) rfl, Cochain.shift_v' z₂ k (p + n₁) q (by omega)]

/-- Shifting the identity cochain gives the identity cochain. -/
theorem shift_ofHom_id (K : CochainComplex C ℤ) (k : ℤ) :
    (Cochain.ofHom (𝟙 K)).shift k = Cochain.ofHom (𝟙 (K⟦k⟧)) :=
  Cochain.ext _ _ fun p q hpq => by
    obtain rfl : q = p := by omega
    simp only [Cochain.shift_v', Cochain.ofHom_v, HomologicalComplex.id_f]
    rfl

end CochainComplex.HomComplex.Cochain

namespace DifferentialGradedAlgebra

/-- A right differential graded action of `A` on a fixed cochain complex `M` of `R`-modules,
expressed on homogeneous elements in the signed presentation of Tag 0FQ5: the element acting in
degree `n` is sent to the degree-`n` cochain which, on an element of degree `p`, is `(-1)^{np}`
times right multiplication. Multiplication is therefore reversed with the Koszul sign, while the
Leibniz rule carries none. -/
structure RightAction (A : DifferentialGradedAlgebra.{u, v} R)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) where
  /-- The signed right action of the degree-`n` part of `A`, by degree-`n` cochains. -/
  action (n : ℤ) : A.grading n →ₗ[R] Cochain M M n
  /-- The unit of `A` acts as the identity. -/
  map_one : action 0 ⟨1, SetLike.one_mem_graded A.grading⟩ = Cochain.ofHom (𝟙 M)
  /-- A product of homogeneous elements acts as the composite of their actions, in order, with
  the Koszul sign. -/
  map_mul (n m : ℤ) (a : A.grading n) (b : A.grading m) :
    action (n + m) ⟨(a : A.A) * (b : A.A), SetLike.mul_mem_graded a.property b.property⟩ =
      (n * m).negOnePow • (action n a).comp (action m b) rfl
  /-- The differential of `A` acts by the graded commutator differential on cochains. -/
  map_d (n : ℤ) (a : A.grading n) :
    action (n + 1) ⟨A.d a, A.d_mem n a a.property⟩ = δ n (n + 1) (action n a)

end DifferentialGradedAlgebra

namespace DifferentialGradedModule

/-- The components of `oppEndCochain` do not depend on the degree in which the homogeneous element
is presented. -/
private theorem oppEndCochain_v_congr (A : DifferentialGradedAlgebra.{u, v} R)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (τ : A.Hom (oppEndAlgebra M)) {d d' : ℤ} (hd : d = d')
    (x : A.A) (hx : x ∈ A.grading d) (hx' : x ∈ A.grading d') (p q : ℤ) (h : p + d = q)
    (h' : p + d' = q) :
    (oppEndCochain A M τ d ⟨x, hx⟩).v p q h = (oppEndCochain A M τ d' ⟨x, hx'⟩).v p q h' := by
  subst hd; rfl

/-- The signed cochains attached to a homomorphism into the graded opposite of the endomorphism
algebra form a right differential graded action. -/
private noncomputable def oppEndRightAction (A : DifferentialGradedAlgebra.{u, v} R)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (τ : A.Hom (oppEndAlgebra M)) :
    A.RightAction M where
  action n := oppEndCochainLinear A M τ n
  map_one := by
    have h : (⟨(oppEndOpposite M).equiv (τ.toAlgebraHom 1), by
          simpa using ((oppEndOpposite M).mem_grading_iff 0 (τ.toAlgebraHom 1)).mp
            (τ.map_grading 0 1 (SetLike.one_mem_graded A.grading))⟩ :
          (endomorphismDGA M).algebra.grading 0) =
        ⟨1, SetLike.one_mem_graded (endomorphismDGA M).algebra.grading⟩ :=
      Subtype.ext (by simp)
    change (endomorphismDGA M).cochainEquiv 0 _ = _
    rw [h]
    exact (endomorphismDGA M).map_one
  map_mul n m a b := by
    refine Cochain.ext _ _ fun p q hpq => ?_
    change (oppEndCochain A M τ (n + m)
        ⟨(a : A.A) * (b : A.A), SetLike.mul_mem_graded a.property b.property⟩).v p q hpq =
      ((n * m).negOnePow •
        (oppEndCochain A M τ n a).comp (oppEndCochain A M τ m b) rfl).v p q hpq
    rw [oppEndCochain_v_congr A M τ (add_comm n m) ((a : A.A) * (b : A.A))
      (SetLike.mul_mem_graded a.property b.property)
      (by simpa only [add_comm] using SetLike.mul_mem_graded a.property b.property)
      p q hpq (by omega)]
    rw [show (oppEndCochain A M τ (m + n) ⟨(a : A.A) * (b : A.A), by
          simpa only [add_comm] using SetLike.mul_mem_graded a.property b.property⟩) =
        (((n * m).negOnePow.val : ℤ) : R) •
          ((oppEndCochain A M τ n a).comp (oppEndCochain A M τ m b) (by omega)) from
      oppEndCochain_mul A M τ n m a b]
    rw [Cochain.units_smul_v, Cochain.smul_v,
      Cochain.comp_v _ _ (show n + m = n + m from rfl) p (p + n) q rfl (by omega),
      Cochain.comp_v _ _ (show n + m = m + n by omega) p (p + n) q rfl (by omega),
      Units.smul_def, ← Int.cast_smul_eq_zsmul R]
  map_d n a := oppEndCochain_map_d A M τ n a

/-- The signed formula of Tag 0FQ5 holds for `oppEndRightAction` as soon as the homomorphism
realizes the right module structure. -/
private theorem oppEndRightAction_apply (A : DifferentialGradedAlgebra.{u, v} R)
    (L : DifferentialGradedModule A) (M : CochainComplex (ModuleCat.{u} R) ℤ)
    (i : L.toCochainComplex ≅ M) (τ : A.Hom (oppEndAlgebra M)) (hτ : IsSignedAction A M L i τ)
    (n p : ℤ) (a : A.grading n) (x : L.grading p) :
    ((oppEndRightAction A M τ).action n a).v p (p + n) rfl (i.hom.f p x) =
      (n * p).negOnePow • i.hom.f (p + n)
        (⟨MulOpposite.op (a : A.A) • (x : L.M),
          L.smul_mem p n (x : L.M) (a : A.A) x.property a.property⟩ : L.grading (p + n)) :=
  hτ n p a x

/-- **Stacks 0FQ5.** A right differential graded `A`-module gives a right differential graded
action of `A` on any complex identified with its underlying complex: a homogeneous element of
degree `n` acts on one of degree `p` by `(-1)^{np}` times right multiplication. -/
theorem exists_rightAction (A : DifferentialGradedAlgebra.{u, v} R)
    (L : DifferentialGradedModule A) (M : CochainComplex (ModuleCat.{u} R) ℤ)
    (i : L.toCochainComplex ≅ M) :
    ∃ t : A.RightAction M,
      ∀ (n p : ℤ) (a : A.grading n) (x : L.grading p),
        (t.action n a).v p (p + n) rfl (i.hom.f p x) =
          (n * p).negOnePow • i.hom.f (p + n)
            (⟨MulOpposite.op (a : A.A) • (x : L.M),
              L.smul_mem p n (x : L.M) (a : A.A) x.property a.property⟩ : L.grading (p + n)) := by
  obtain ⟨τ, hτ, -⟩ := existsUnique_isSignedAction A M L i
  exact ⟨oppEndRightAction A M τ, oppEndRightAction_apply A L M i τ hτ⟩

end DifferentialGradedModule

namespace DifferentialGradedAlgebra

variable {A : DifferentialGradedAlgebra.{u, v} R} {M N : CochainComplex (ModuleCat.{u} R) ℤ}

/-- **Stacks 0FQ1.** The shift `M[k]` of a left differential graded module, as an action on the
shifted complex: a homogeneous element of degree `p` acts with the Koszul factor `(-1)^{pk}`. -/
noncomputable def LeftAction.shift (act : A.LeftAction M) (k : ℤ) : A.LeftAction (M⟦k⟧) where
  action p :=
    { toFun a := (p * k).negOnePow • Cochain.shiftLinearMap R M M p k (act.action p a)
      map_add' a b := by simp only [map_add, smul_add]
      map_smul' r a := by
        simp only [map_smul, RingHom.id_apply]
        exact smul_comm _ _ _ }
  map_one := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Cochain.shiftLinearMap_apply, act.map_one,
      zero_mul, Int.negOnePow_zero, one_smul, Cochain.shift_ofHom_id]
  map_mul n m a b := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Cochain.shiftLinearMap_apply, act.map_mul n m a b]
    rw [Cochain.units_smul_comp, Cochain.comp_units_smul, smul_smul, ← Int.negOnePow_add,
      Cochain.shift_comp]
    congr 2
    ring
  map_d n a := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Cochain.shiftLinearMap_apply, act.map_d n a]
    rw [δ_units_smul, (act.action n a).δ_shift k (n + 1), smul_smul, ← Int.negOnePow_add]
    congr 2
    ring

/-- On homogeneous elements, the shifted left action is the Koszul sign `(-1)^{pk}` times the
given action. -/
theorem LeftAction.shift_action (act : A.LeftAction M) (k p : ℤ) (a : A.grading p) :
    (act.shift k).action p a = (p * k).negOnePow • (act.action p a).shift k :=
  rfl

/-- **Stacks 0FQ1.** The shift `M[k]` of a right differential graded module, as an action on the
shifted complex. Definition 22.26.1 shifts a right module without signs, but in the signed
presentation of Tag 0FQ5 the factor `(-1)^{pk}` appears, because the degree of an element changes
by `k` under the shift. -/
noncomputable def RightAction.shift (t : A.RightAction M) (k : ℤ) : A.RightAction (M⟦k⟧) where
  action p :=
    { toFun a := (p * k).negOnePow • Cochain.shiftLinearMap R M M p k (t.action p a)
      map_add' a b := by simp only [map_add, smul_add]
      map_smul' r a := by
        simp only [map_smul, RingHom.id_apply]
        exact smul_comm _ _ _ }
  map_one := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Cochain.shiftLinearMap_apply, t.map_one,
      zero_mul, Int.negOnePow_zero, one_smul, Cochain.shift_ofHom_id]
  map_mul n m a b := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Cochain.shiftLinearMap_apply, t.map_mul n m a b]
    rw [Cochain.shift_units_smul, Cochain.units_smul_comp, Cochain.comp_units_smul,
      Cochain.shift_comp, smul_smul, smul_smul, smul_smul, ← Int.negOnePow_add,
      ← Int.negOnePow_add, ← Int.negOnePow_add]
    congr 2
    ring
  map_d n a := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Cochain.shiftLinearMap_apply, t.map_d n a]
    rw [δ_units_smul, (t.action n a).δ_shift k (n + 1), smul_smul, ← Int.negOnePow_add]
    congr 2
    ring

/-- On homogeneous elements, the shifted right action is `(-1)^{pk}` times the given action. -/
theorem RightAction.shift_action (t : A.RightAction M) (k p : ℤ) (a : A.grading p) :
    (t.shift k).action p a = (p * k).negOnePow • (t.action p a).shift k :=
  rfl

/-- Two morphisms between homogeneous pieces of a Hom complex agree as soon as they agree on
every homogeneous cochain. This is `ModuleCat.hom_ext` with the source read as a module of
cochains, which is what keeps the cochain lemmas applicable to the resulting goal. -/
theorem homComplexR_hom_ext {M N : CochainComplex (ModuleCat.{u} R) ℤ} {q r : ℤ}
    {f g : (HomComplexR R M N).X q ⟶ (HomComplexR R M N).X r}
    (h : ∀ z : Cochain M N q, f.hom z = g.hom z) : f = g :=
  ModuleCat.hom_ext (LinearMap.ext h)

/-- The action of a homogeneous element of degree `p` on a homogeneous cochain of degree `q`, for
a left differential graded action on a Hom complex. -/
noncomputable def LeftAction.homAction (s : A.LeftAction (HomComplexR R M N)) (p q r : ℤ)
    (h : q + p = r) (a : A.grading p) (z : Cochain M N q) : Cochain M N r :=
  ((s.action p a).v q r h).hom z

/-- **Stacks 0FQ2.** Signed precomposition with a right differential graded action: a homogeneous
element of degree `p` sends a cochain of degree `q` to `(-1)^{pq}` times its precomposite with the
signed right action. -/
noncomputable def RightAction.homLeftActionComponent (t : A.RightAction M)
    (N : CochainComplex (ModuleCat.{u} R) ℤ) (p q r : ℤ) (h : q + p = r) (a : A.grading p) :
    Cochain M N q →ₗ[R] Cochain M N r where
  toFun z := (p * q).negOnePow • (t.action p a).comp z (by omega)
  map_add' z z' := by simp [Cochain.comp_add]
  map_smul' c z := by
    simp only [Cochain.comp_smul]
    exact smul_comm _ _ _

/-- **Stacks 0FQ2.** Signed precomposition with a right differential graded action, assembled into
a degree-`p` cochain of the Hom complex `Hom^•(M, N)`. -/
noncomputable def RightAction.homLeftActionCochain (t : A.RightAction M)
    (N : CochainComplex (ModuleCat.{u} R) ℤ) (p : ℤ) (a : A.grading p) :
    Cochain (HomComplexR R M N) (HomComplexR R M N) p :=
  Cochain.mk fun q r h => ModuleCat.ofHom (t.homLeftActionComponent N p q r h a)

/-- **Stacks 0FQ2.** The components of the signed precomposition cochain. -/
theorem RightAction.homLeftActionCochain_v_apply (t : A.RightAction M)
    (N : CochainComplex (ModuleCat.{u} R) ℤ) (p q r : ℤ) (h : q + p = r) (a : A.grading p)
    (z : Cochain M N q) :
    ((t.homLeftActionCochain N p a).v q r h).hom z =
      (p * q).negOnePow • (t.action p a).comp z (by omega) :=
  rfl

/-- **Stacks 0FQ2.** The left differential graded action on `Hom^•(M, N)` induced by a right
differential graded action on `M`: a homogeneous element of degree `p` acts on a cochain of degree
`q` by `(-1)^{pq}` times precomposition with the signed right action. -/
noncomputable def RightAction.homLeftAction (t : A.RightAction M)
    (N : CochainComplex (ModuleCat.{u} R) ℤ) : A.LeftAction (HomComplexR R M N) where
  action p :=
    { toFun := t.homLeftActionCochain N p
      map_add' a b := by
        refine Cochain.ext _ _ fun q r h => homComplexR_hom_ext fun z => ?_
        change (p * q).negOnePow • (t.action p (a + b)).comp z (show p + q = r by omega) =
          (p * q).negOnePow • (t.action p a).comp z (show p + q = r by omega) +
            (p * q).negOnePow • (t.action p b).comp z (show p + q = r by omega)
        rw [(t.action p).map_add a b, Cochain.add_comp, smul_add]
      map_smul' c a := by
        refine Cochain.ext _ _ fun q r h => homComplexR_hom_ext fun z => ?_
        change (p * q).negOnePow • (t.action p (c • a)).comp z (show p + q = r by omega) =
          c • ((p * q).negOnePow • (t.action p a).comp z (show p + q = r by omega))
        rw [(t.action p).map_smul c a, Cochain.smul_comp]
        exact smul_comm _ _ _ }
  map_one := by
    refine Cochain.ext _ _ fun q r h => homComplexR_hom_ext fun z => ?_
    obtain rfl : q = r := by omega
    change ((0 : ℤ) * q).negOnePow •
      (t.action 0 ⟨1, SetLike.one_mem_graded A.grading⟩).comp z (show 0 + q = q by omega) = z
    rw [t.map_one, Cochain.id_comp]
    simp
  map_mul n m a b := by
    refine Cochain.ext _ _ fun q r h => homComplexR_hom_ext fun z => ?_
    change ((n + m) * q).negOnePow •
        (t.action (n + m)
          ⟨(a : A.A) * (b : A.A), SetLike.mul_mem_graded a.property b.property⟩).comp
          z (show n + m + q = r by omega) =
      (n * (q + m)).negOnePow • (t.action n a).comp
        ((m * q).negOnePow • (t.action m b).comp z (show m + q = q + m by omega))
        (show n + (q + m) = r by omega)
    rw [t.map_mul n m a b, Cochain.units_smul_comp, Cochain.comp_units_smul, smul_smul, smul_smul,
      Cochain.comp_assoc (t.action n a) (t.action m b) z rfl
        (show m + q = q + m by omega) (show n + m + q = r by omega)]
    congr 1
    rw [← Int.negOnePow_add, ← Int.negOnePow_add]
    congr 1
    ring
  map_d n a := by
    refine Cochain.ext _ _ fun q r h => homComplexR_hom_ext fun z => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [δ_v n (n + 1) rfl (t.homLeftActionCochain N n a) q r h (q + n) (q + 1) (by omega) rfl]
    change ((n + 1) * q).negOnePow •
        (t.action (n + 1) ⟨A.d (a : A.A), A.d_mem n (a : A.A) a.property⟩).comp z
          (show n + 1 + q = r by omega) =
      δ (q + n) r ((n * q).negOnePow • (t.action n a).comp z (show n + q = q + n by omega)) +
        (n + 1).negOnePow • ((n * (q + 1)).negOnePow •
          (t.action n a).comp (δ q (q + 1) z) (show n + (q + 1) = r by omega))
    have hδcomp : δ (q + n) r ((t.action n a).comp z (show n + q = q + n by omega)) =
        (t.action n a).comp (δ q (q + 1) z) (show n + (q + 1) = r by omega) +
          q.negOnePow • (δ n (n + 1) (t.action n a)).comp z (show n + 1 + q = r by omega) :=
      δ_comp (t.action n a) z (show n + q = q + n by omega) (n + 1) (q + 1) r
        (show q + n + 1 = r by omega) rfl rfl
    rw [t.map_d n a, δ_units_smul, hδcomp, smul_add, smul_smul, smul_smul]
    have hδsign : (n * q).negOnePow * q.negOnePow = ((n + 1) * q).negOnePow := by
      rw [← Int.negOnePow_add]
      congr 1
      ring
    have hcancel : (n + 1).negOnePow * (n * (q + 1)).negOnePow = -(n * q).negOnePow := by
      rw [← Int.negOnePow_add, show (n + 1) + n * (q + 1) = n * q + 1 + 2 * n by ring,
        Int.negOnePow_add, Int.negOnePow_two_mul, Int.negOnePow_succ]
      simp
    rw [hδsign, hcancel, Units.neg_smul]
    abel

/-- The signed formula for the left action induced on a Hom complex. -/
theorem RightAction.homLeftAction_homAction (t : A.RightAction M)
    (N : CochainComplex (ModuleCat.{u} R) ℤ) (p q r : ℤ) (h : q + p = r) (a : A.grading p)
    (z : Cochain M N q) :
    (t.homLeftAction N).homAction p q r h a z =
      (p * q).negOnePow • (t.action p a).comp z (by omega) :=
  rfl

/-! ### Right actions from left actions of the graded opposite -/

/-- The identification of the degree-`n` part of a graded opposite of `A` with the degree-`n` part
of `A`. -/
def Opposite.gradingEquiv (O : Opposite R A) (n : ℤ) :
    O.toDifferentialGradedAlgebra.grading n ≃ₗ[R] A.grading n where
  toFun x := ⟨O.equiv x, (O.mem_grading_iff n (x : O.toDifferentialGradedAlgebra.A)).mp x.property⟩
  map_add' x y := Subtype.ext (map_add O.equiv _ _)
  map_smul' r x := Subtype.ext (map_smul O.equiv r _)
  invFun y := ⟨O.equiv.symm y, (O.mem_grading_iff n _).mpr (by simp)⟩
  left_inv x := Subtype.ext (O.equiv.symm_apply_apply _)
  right_inv y := Subtype.ext (O.equiv.apply_symm_apply _)

/-- The element of `A` underlying the image of `x` under `O.gradingEquiv n` is `O.equiv x`. -/
@[simp] theorem Opposite.gradingEquiv_coe (O : Opposite R A) (n : ℤ)
    (x : O.toDifferentialGradedAlgebra.grading n) :
    ((O.gradingEquiv n x : A.grading n) : A.A) = O.equiv (x : O.toDifferentialGradedAlgebra.A) :=
  rfl

/-- The element underlying the image of `y` under the inverse of `O.gradingEquiv n` is
`O.equiv.symm y`. -/
@[simp] theorem Opposite.gradingEquiv_symm_coe (O : Opposite R A) (n : ℤ) (y : A.grading n) :
    (((O.gradingEquiv n).symm y : O.toDifferentialGradedAlgebra.grading n) :
      O.toDifferentialGradedAlgebra.A) = O.equiv.symm (y : A.A) :=
  rfl

/-- A family of cochains indexed by the homogeneous parts of `A` takes the same value on a given
element however its degree is written. -/
theorem gradedCochainFamily_v_congr (act : ∀ n : ℤ, A.grading n →ₗ[R] Cochain M M n)
    {d d' : ℤ} (hd : d = d') (x : A.A) (hx : x ∈ A.grading d) (hx' : x ∈ A.grading d')
    (p q : ℤ) (h : p + d = q) (h' : p + d' = q) :
    (act d ⟨x, hx⟩).v p q h = (act d' ⟨x, hx'⟩).v p q h' := by
  subst hd; rfl

/-- The cochains of a left differential graded action of a graded opposite of `A`, read as a
family indexed by the homogeneous parts of `A` itself. -/
noncomputable def Opposite.rightActionCochain (O : Opposite R A)
    (act : O.toDifferentialGradedAlgebra.LeftAction M) (n : ℤ) :
    A.grading n →ₗ[R] Cochain M M n :=
  (act.action n) ∘ₗ (O.gradingEquiv n).symm.toLinearMap

/-- The cochain attached to `a` is the action of the corresponding element of the graded
opposite. -/
@[simp] theorem Opposite.rightActionCochain_apply (O : Opposite R A)
    (act : O.toDifferentialGradedAlgebra.LeftAction M) (n : ℤ) (a : A.grading n) :
    O.rightActionCochain act n a = act.action n ((O.gradingEquiv n).symm a) :=
  rfl

/-- The unit of `A` acts as the identity. -/
theorem Opposite.rightActionCochain_one (O : Opposite R A)
    (act : O.toDifferentialGradedAlgebra.LeftAction M) :
    O.rightActionCochain act 0 ⟨1, SetLike.one_mem_graded A.grading⟩ = Cochain.ofHom (𝟙 M) := by
  have h1 : (O.gradingEquiv 0).symm ⟨1, SetLike.one_mem_graded A.grading⟩ =
      ⟨1, SetLike.one_mem_graded O.toDifferentialGradedAlgebra.grading⟩ := by
    refine Subtype.ext ?_
    change O.equiv.symm (1 : A.A) = 1
    rw [← O.map_one, LinearEquiv.symm_apply_apply]
  rw [Opposite.rightActionCochain_apply, h1, act.map_one]

/-- A product of homogeneous elements of `A` acts as the composite of their actions, in order,
with the Koszul sign: the order is reversed twice, once by the graded opposite and once by the
left action. -/
theorem Opposite.rightActionCochain_mul (O : Opposite R A)
    (act : O.toDifferentialGradedAlgebra.LeftAction M) (n m : ℤ) (a : A.grading n)
    (b : A.grading m) :
    O.rightActionCochain act (n + m)
        ⟨(a : A.A) * (b : A.A), SetLike.mul_mem_graded a.property b.property⟩ =
      (n * m).negOnePow •
        (O.rightActionCochain act n a).comp (O.rightActionCochain act m b) rfl := by
  have hmem' := SetLike.mul_mem_graded ((O.gradingEquiv m).symm b).property
    ((O.gradingEquiv n).symm a).property
  have hmem : (((O.gradingEquiv m).symm b : O.toDifferentialGradedAlgebra.A) *
      ((O.gradingEquiv n).symm a : O.toDifferentialGradedAlgebra.A)) ∈
      O.toDifferentialGradedAlgebra.grading (n + m) := by
    simpa only [add_comm] using hmem'
  have hmul : (O.gradingEquiv (n + m)).symm
      ⟨(a : A.A) * (b : A.A), SetLike.mul_mem_graded a.property b.property⟩ =
      (m * n).negOnePow •
        (⟨((O.gradingEquiv m).symm b : O.toDifferentialGradedAlgebra.A) *
          ((O.gradingEquiv n).symm a : O.toDifferentialGradedAlgebra.A), hmem⟩ :
          O.toDifferentialGradedAlgebra.grading (n + m)) := by
    refine Subtype.ext (O.equiv.injective ?_)
    rw [Opposite.gradingEquiv_symm_coe, LinearEquiv.apply_symm_apply]
    change _ = O.equiv (((m * n).negOnePow : ℤ) •
      (((O.gradingEquiv m).symm b : O.toDifferentialGradedAlgebra.A) *
        ((O.gradingEquiv n).symm a : O.toDifferentialGradedAlgebra.A)))
    rw [map_zsmul, O.map_mul_of_mem m n _ _ ((O.gradingEquiv m).symm b).property
      ((O.gradingEquiv n).symm a).property]
    simp only [Opposite.gradingEquiv_symm_coe, LinearEquiv.apply_symm_apply, Units.smul_def,
      smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]
  rw [Opposite.rightActionCochain_apply, hmul, Units.smul_def, map_zsmul, ← Units.smul_def,
    mul_comm n m]
  congr 1
  simp only [Opposite.rightActionCochain_apply]
  refine Cochain.ext _ _ fun s t hst => ?_
  rw [gradedCochainFamily_v_congr act.action (add_comm n m) _ hmem hmem' s t _ (by omega),
    act.map_mul m n ((O.gradingEquiv m).symm b) ((O.gradingEquiv n).symm a),
    Cochain.comp_v _ _ (show n + m = m + n by omega) s (s + n) t rfl (by omega),
    Cochain.comp_v _ _ (show n + m = n + m from rfl) s (s + n) t rfl (by omega)]

/-- The differential of `A` acts by the graded commutator differential on cochains. -/
theorem Opposite.rightActionCochain_d (O : Opposite R A)
    (act : O.toDifferentialGradedAlgebra.LeftAction M) (n : ℤ) (a : A.grading n) :
    O.rightActionCochain act (n + 1) ⟨A.d a, A.d_mem n a a.property⟩ =
      δ n (n + 1) (O.rightActionCochain act n a) := by
  have hd : (O.gradingEquiv (n + 1)).symm ⟨A.d (a : A.A), A.d_mem n _ a.property⟩ =
      ⟨O.toDifferentialGradedAlgebra.d ((O.gradingEquiv n).symm a),
        O.toDifferentialGradedAlgebra.d_mem n _ ((O.gradingEquiv n).symm a).property⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext (by simp [O.map_d])
  rw [Opposite.rightActionCochain_apply, hd, act.map_d n ((O.gradingEquiv n).symm a),
    Opposite.rightActionCochain_apply]

/-- **Stacks 0FQ5.** A left differential graded action of a graded opposite of `A` on `M` is the
same thing as a right differential graded action of `A` on `M`, through the identification of the
underlying graded modules. -/
noncomputable def Opposite.rightAction (O : Opposite R A)
    (act : O.toDifferentialGradedAlgebra.LeftAction M) : A.RightAction M where
  action := O.rightActionCochain act
  map_one := O.rightActionCochain_one act
  map_mul := O.rightActionCochain_mul act
  map_d := O.rightActionCochain_d act

/-- On homogeneous elements, the right action attached to a left action of the graded opposite is
the given action. -/
theorem Opposite.rightAction_action (O : Opposite R A)
    (act : O.toDifferentialGradedAlgebra.LeftAction M) (n : ℤ) (a : A.grading n) :
    (O.rightAction act).action n a = act.action n ((O.gradingEquiv n).symm a) :=
  rfl

end DifferentialGradedAlgebra
