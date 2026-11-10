module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksFrontier.Algebra.Homology.ShortComplex.AdditiveEndomorphism
public import StacksFrontier.RingTheory.Cech.Reindex
public import StacksFrontier.RingTheory.Derivation.Localization

/-!
# A derivation of the base ring acting on the extended alternating Čech complex

Let `A` be a commutative ring, `θ : A → A` a derivation — modelled as `Derivation ℤ A A` — and
`f : Fin r → A`. Every term of the extended alternating Čech complex `C^•(f₁, …, f_r; A)` of the
regular module is a finite direct sum of localizations of `A`, and `θ` has a unique extension to
each of them, acting on fractions by the quotient rule
`θ (a / t) = (t * θ a - a * θ t) / t²`. Those extensions are compatible with the transition maps
of the complex, hence assemble to an additive — not `A`-linear — chain endomorphism of
`C^•(f₁, …, f_r; A)`, and therefore to additive endomorphisms of its cycles and of its
cohomology, each satisfying the twisted Leibniz rule for `θ`.

The quotient rule determines the chain endomorphism completely: `Cech.DerivationAction` packages
the data together with the quotient rule and the commutation with the differential, and
`Cech.DerivationAction.ext` shows there is at most one such operator.
`Cech.derivationAction` is the one there is.

## Main definitions

* `Cech.cechModAction` — the extension of `θ` to a single localization appearing in the complex.
* `Cech.cechTermAction` — the induced additive endomorphism of a term of the complex.
* `Cech.cechChainAction` — the induced additive chain endomorphism of the whole complex.
* `Cech.cechCyclesAction`, `Cech.cechHomologyAction` — the induced operators on cycles and on
  cohomology.
* `Cech.DerivationAction` — an additive chain endomorphism acting on fractions by the quotient
  rule.
* `Cech.derivationAction` — the localization extensions, assembled.

## Main results

* `Cech.cechModAction_mk`, `Cech.cechTermAction_mk` — **the quotient rule.**
* `Cech.cechModAction_leibniz`, `Cech.cechTermAction_leibniz`,
  `Cech.cechHomologyAction_leibniz` — the twisted Leibniz rule, on a localization, on a term and
  on cohomology.
* `Cech.DerivationAction.ext` — the quotient rule determines the operator.
* `Cech.cechHomologyAction_naturality` — a chain map commuting with the term operators commutes
  with the operators on cohomology.
* `Cech.cechTermRestrict_action` — restriction to a subfamily of the generators commutes with the
  operators.

## References

* [Stacks Project, Tag 07PE](https://stacks.math.columbia.edu/tag/07PE)
* [Stacks Project, Tag 0EC5](https://stacks.math.columbia.edu/tag/0EC5)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.DerivationExtension
open ExtendedAlternatingCech (Idx cechRing mlocREquiv mlocREquiv_mk_one mlocREquiv_cechι ιRing)

namespace Cech

universe u

variable {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)

/-! ### The action on a single localization -/

/-- **The extension of `θ` to one of the localizations appearing in the Čech complex**, as an
additive endomorphism. It is the unique derivation of `A_{f_S}` extending `θ`, read through the
identification of the module localization of `A` with the ring localization. -/
def cechModAction (θ : Derivation ℤ A A) (S : Finset (Fin r)) :
    cechMod f A S →+ cechMod f A S where
  toFun x :=
    (mlocREquiv f S).symm (locDeriv θ (cechSub f S) (cechRing f S) (mlocREquiv f S x))
  map_zero' := by simp
  map_add' x y := by simp

/-- Under the identification of the module localization with the ring localization, the operator
is the canonical extension of `θ`. -/
theorem mlocREquiv_cechModAction (θ : Derivation ℤ A A) (S : Finset (Fin r))
    (x : cechMod f A S) :
    mlocREquiv f S (cechModAction f θ S x) =
      locDeriv θ (cechSub f S) (cechRing f S) (mlocREquiv f S x) :=
  (mlocREquiv f S).apply_symm_apply _

/-- The identification of the module localization of `A` with the ring localization sends the
fraction `a / t` to the fraction `a / t`. -/
theorem mlocREquiv_mk (S : Finset (Fin r)) (a : A) (t : cechSub f S) :
    mlocREquiv f S (LocalizedModule.mk a t) = IsLocalization.mk' (cechRing f S) a t := by
  rw [IsLocalization.eq_mk'_iff_mul_eq, mul_comm, ← Algebra.smul_def, ← map_smul,
    LocalizedModule.smul'_mk,
    show LocalizedModule.mk ((t : A) • a) t = LocalizedModule.mk a 1 from
      LocalizedModule.mk_cancel t a, mlocREquiv_mk_one]

/-- **The quotient rule on one localization.** -/
theorem cechModAction_mk (θ : Derivation ℤ A A) (S : Finset (Fin r)) (a : A)
    (t : cechSub f S) :
    cechModAction f θ S (LocalizedModule.mk a t) =
      LocalizedModule.mk ((t : A) * θ a - a * θ (t : A)) (t * t) := by
  refine (mlocREquiv f S).injective ?_
  rw [mlocREquiv_cechModAction, mlocREquiv_mk, mlocREquiv_mk, locDeriv_mk']

/-- The operators on the localizations are compatible with the transition maps of the complex. -/
theorem cechModAction_naturality (θ : Derivation ℤ A A) {S T : Finset (Fin r)} (h : S ⊆ T)
    (x : cechMod f A S) :
    cechModAction f θ T (cechι f A h x) = cechι f A h (cechModAction f θ S x) := by
  refine (mlocREquiv f T).injective ?_
  rw [mlocREquiv_cechModAction, mlocREquiv_cechι, mlocREquiv_cechι, mlocREquiv_cechModAction]
  exact (algHom_locDeriv θ _ _ (ιRing f S T h) _).symm

/-- **The twisted Leibniz rule on one localization.** -/
theorem cechModAction_leibniz (θ : Derivation ℤ A A) (S : Finset (Fin r)) (a : A)
    (x : cechMod f A S) :
    cechModAction f θ S (a • x) = θ a • x + a • cechModAction f θ S x := by
  -- Pin the `ℤ`-algebra structure of the ring localization to the one in the type of
  -- `Stacks.DerivationExtension.locDeriv`; instance search would otherwise produce the
  -- `OreLocalization` one, which is not definitionally equal to it.
  let _ : Algebra ℤ (cechRing f S) := Ring.toIntAlgebra (cechRing f S)
  refine (mlocREquiv f S).injective ?_
  rw [mlocREquiv_cechModAction]
  simp only [map_add, map_smul, mlocREquiv_cechModAction]
  simp only [Algebra.smul_def]
  rw [Derivation.leibniz, locDeriv_algebraMap]
  simp only [smul_eq_mul]
  ring

/-! ### The action on the complex -/

/-- **The induced additive endomorphism of a term of the Čech complex**: the direct sum of the
operators on the localizations. -/
def cechTermAction (θ : Derivation ℤ A A) (p : ℕ) : cechTerm f A p →+ cechTerm f A p :=
  DirectSum.map fun S => cechModAction f θ S.1

/-- On the summand indexed by `S`, the operator is the one on that localization. -/
theorem cechTermAction_lof (θ : Derivation ℤ A A) (p : ℕ) (S : Idx r p)
    (y : cechMod f A S.1) :
    cechTermAction f θ p
        (DirectSum.lof A _ (fun S : Idx r p => cechMod f A S.1) S y) =
      DirectSum.lof A _ (fun S : Idx r p => cechMod f A S.1) S (cechModAction f θ S.1 y) := by
  unfold cechTermAction
  rw [DirectSum.lof_eq_of A, DirectSum.map_of, DirectSum.lof_eq_of]

/-- **The quotient rule on a term of the Čech complex.** -/
theorem cechTermAction_mk (θ : Derivation ℤ A A) (p : ℕ) (S : Idx r p) (a : A)
    (t : cechSub f S.1) :
    cechTermAction f θ p (DirectSum.lof A _ (fun S : Idx r p => cechMod f A S.1) S
        (LocalizedModule.mk a t)) =
      DirectSum.lof A _ (fun S : Idx r p => cechMod f A S.1) S
        (LocalizedModule.mk ((t : A) * θ a - a * θ (t : A)) (t * t)) := by
  rw [cechTermAction_lof, cechModAction_mk]

/-- **The twisted Leibniz rule on a term of the Čech complex.** -/
theorem cechTermAction_leibniz (θ : Derivation ℤ A A) (p : ℕ) (a : A) (x : cechTerm f A p) :
    cechTermAction f θ p (a • x) = θ a • x + a • cechTermAction f θ p x := by
  induction x using DirectSum.induction_on with
  | zero => simp [cechTermAction]
  | of S y =>
    rw [← DirectSum.lof_eq_of A]
    simp only [← map_smul, cechTermAction_lof]
    rw [cechModAction_leibniz]
    simp only [map_add, map_smul]
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]; abel

/-- **The operators on the terms commute with the Čech differential.** -/
theorem cechTermAction_comm_d (θ : Derivation ℤ A A) (p : ℕ) (x : cechTerm f A p) :
    cechTermAction f θ (p + 1) (cechD f A p x) = cechD f A p (cechTermAction f θ p x) := by
  induction x using DirectSum.induction_on with
  | zero => simp [cechTermAction]
  | of S y =>
    rw [← DirectSum.lof_eq_of A, cechD_lof]
    simp only [map_sum, map_zsmul, cechTermAction_lof]
    rw [cechD_lof]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cechTermAction_lof]
    exact congrArg
      (fun q : cechMod f A (insert i.1 S.1) =>
        cechSign S.1 i.1 •
          DirectSum.lof A _ (fun T : Idx r (p + 1) => cechMod f A T.1)
            ⟨insert i.1 S.1, by
              rw [Finset.card_insert_of_notMem (by simpa using Finset.mem_compl.1 i.2), S.2]⟩ q)
      (cechModAction_naturality f θ (Finset.subset_insert i.1 S.1) y)
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **The induced additive chain endomorphism of the Čech complex**, viewed as a complex of
abelian groups — which is where an additive but not `A`-linear operator lives. -/
def cechChainAction (θ : Derivation ℤ A A) :
    ((forget₂ (ModuleCat.{u} A) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (cechComplex f A) ⟶
      ((forget₂ (ModuleCat.{u} A) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (cechComplex f A) where
  f p := AddCommGrpCat.ofHom (cechTermAction f θ p)
  comm' p q hpq := by
    change p + 1 = q at hpq
    subst q
    ext x
    simp only [Functor.mapHomologicalComplex_obj_d, ModuleCat.forget₂_map, cechComplex,
      CochainComplex.of_d]
    change cechD f A p (cechTermAction f θ p x) = cechTermAction f θ (p + 1) (cechD f A p x)
    exact (cechTermAction_comm_d f θ p x).symm

/-- **The induced additive endomorphism of the Čech cycles.** -/
def cechCyclesAction (θ : Derivation ℤ A A) (i : ℕ) :
    (cechComplex f A).cycles i →+ (cechComplex f A).cycles i :=
  ShortComplex.additiveCyclesMap ((cechComplex f A).sc i)
    ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (.up ℕ) i).map (cechChainAction f θ))

/-- **The induced additive endomorphism of the Čech cohomology.** -/
def cechHomologyAction (θ : Derivation ℤ A A) (i : ℕ) :
    (cechComplex f A).homology i →+ (cechComplex f A).homology i :=
  ShortComplex.additiveHomologyMap ((cechComplex f A).sc i)
    ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (.up ℕ) i).map (cechChainAction f θ))

/-- The operator on cycles is computed by the operator on the term, through the inclusion of
cycles. -/
theorem cechCyclesAction_i (θ : Derivation ℤ A A) (i : ℕ) (z : (cechComplex f A).cycles i) :
    (cechComplex f A).iCycles i (cechCyclesAction f θ i z) =
      cechTermAction f θ i ((cechComplex f A).iCycles i z) :=
  ShortComplex.additiveCyclesMap_i _ _ z

/-- The operator on cohomology sends the class of a cycle to the class of its image under the
operator on cycles. -/
theorem cechHomologyAction_π (θ : Derivation ℤ A A) (i : ℕ) (z : (cechComplex f A).cycles i) :
    cechHomologyAction f θ i ((cechComplex f A).homologyπ i z) =
      (cechComplex f A).homologyπ i (cechCyclesAction f θ i z) :=
  ShortComplex.additiveHomologyMap_π _ _ z

/-- **The twisted Leibniz rule on Čech cohomology.** -/
theorem cechHomologyAction_leibniz (θ : Derivation ℤ A A) (i : ℕ) (a : A)
    (x : (cechComplex f A).homology i) :
    cechHomologyAction f θ i (a • x) = θ a • x + a • cechHomologyAction f θ i x :=
  ShortComplex.additiveHomologyMap_leibniz _ _ θ (cechTermAction f θ i) (fun _ => rfl)
    (cechTermAction_leibniz f θ i) a x

/-- **Naturality on cohomology.** A chain map of Čech complexes commuting with the term operators
commutes with the operators on cohomology. -/
theorem cechHomologyAction_naturality {s : ℕ} (g : Fin s → A) (θ : Derivation ℤ A A)
    (k : cechComplex f A ⟶ cechComplex g A)
    (hk : ∀ (p : ℕ) (x : cechTerm f A p),
      k.f p (cechTermAction f θ p x) = cechTermAction g θ p (k.f p x))
    (i : ℕ) (x : (cechComplex f A).homology i) :
    cechHomologyAction g θ i (HomologicalComplex.homologyMap k i x) =
      HomologicalComplex.homologyMap k i (cechHomologyAction f θ i x) := by
  have hchain : cechChainAction f θ ≫
      ((forget₂ (ModuleCat.{u} A) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).map k =
      ((forget₂ (ModuleCat.{u} A) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).map k ≫ cechChainAction g θ := by
    refine HomologicalComplex.Hom.ext (funext fun p => AddCommGrpCat.hom_ext
      (AddMonoidHom.ext fun z => ?_))
    exact hk p z
  have hsc := congrArg
    ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (.up ℕ) i).map) hchain
  simp only [Functor.map_comp] at hsc
  exact ShortComplex.additiveHomologyMap_naturality _ _ _ _
    ((HomologicalComplex.shortComplexFunctor (ModuleCat A) (.up ℕ) i).map k) hsc x

/-! ### Uniqueness -/

/-- **An additive chain endomorphism of the Čech complex acting on fractions by the quotient
rule.** The data is an additive endomorphism of each term; the conditions are the quotient rule
on fractions and the commutation with the differential. -/
structure DerivationAction (f : Fin r → A) (θ : Derivation ℤ A A) where
  /-- The additive endomorphism of the degree-`p` term. -/
  toAddMonoidHom (p : ℕ) : cechTerm f A p →+ cechTerm f A p
  /-- **The quotient rule** on the fraction `a / t` of the summand indexed by `S`. -/
  map_mk (p : ℕ) (S : Idx r p) (a : A) (t : cechSub f S.1) :
    toAddMonoidHom p (DirectSum.lof A _ (fun S : Idx r p => cechMod f A S.1) S
        (LocalizedModule.mk a t)) =
      DirectSum.lof A _ (fun S : Idx r p => cechMod f A S.1) S
        (LocalizedModule.mk ((t : A) * θ a - a * θ (t : A)) (t * t))
  /-- Commutation with the Čech differential. -/
  comm_d (p : ℕ) (x : cechTerm f A p) :
    toAddMonoidHom (p + 1) (cechD f A p x) = cechD f A p (toAddMonoidHom p x)

/-- **The quotient rule determines the operator**: every term is a sum of fractions. -/
theorem DerivationAction.ext {θ : Derivation ℤ A A} (D E : DerivationAction f θ) : D = E := by
  have h : D.toAddMonoidHom = E.toAddMonoidHom := by
    refine funext fun p => AddMonoidHom.ext fun x => ?_
    induction x using DirectSum.induction_on with
    | zero => simp
    | of S y =>
      induction y using LocalizedModule.induction_on with
      | _ a t => rw [← DirectSum.lof_eq_of A, D.map_mk, E.map_mk]
    | add x y hx hy => simp only [map_add, hx, hy]
  cases D
  cases E
  cases h
  rfl

/-- The zero derivation acts by zero. -/
def DerivationAction.zero (f : Fin r → A) : DerivationAction f (0 : Derivation ℤ A A) where
  toAddMonoidHom _ := 0
  map_mk _ _ _ _ := by simp
  comm_d _ _ := by simp

/-- **The localization extensions assemble to an operator satisfying the quotient rule.** -/
def derivationAction (θ : Derivation ℤ A A) : DerivationAction f θ where
  toAddMonoidHom := cechTermAction f θ
  map_mk := cechTermAction_mk f θ
  comm_d := cechTermAction_comm_d f θ

/-! ### Compatibility with restriction to a subfamily -/

variable {s : ℕ} (g : Fin s → A) (e : Fin r ↪o Fin s) (he : ∀ i, g (e i) = f i)

include he in
/-- The identification of localizations attached to a subfamily of the generators commutes with
the operators. -/
theorem reindexLoc_action (θ : Derivation ℤ A A) (S : Finset (Fin r))
    (x : cechMod g A (S.map e.toEmbedding)) :
    reindexLoc f A g e he S (cechModAction g θ (S.map e.toEmbedding) x) =
      cechModAction f θ S (reindexLoc f A g e he S x) := by
  induction x using LocalizedModule.induction_on with
  | _ a t =>
    rw [cechModAction_mk, reindexLoc_mk, reindexLoc_mk, cechModAction_mk]
    rfl

include he in
/-- **Restriction to a subfamily of the generators commutes with the operators.** -/
theorem cechTermRestrict_action (θ : Derivation ℤ A A) (p : ℕ) (x : cechTerm g A p) :
    cechTermRestrict f A g e he p (cechTermAction g θ p x) =
      cechTermAction f θ p (cechTermRestrict f A g e he p x) := by
  refine DirectSum.ext_component A fun S => ?_
  change (cechTermRestrict f A g e he p (cechTermAction g θ p x)) S =
    (cechTermAction f θ p (cechTermRestrict f A g e he p x)) S
  simp only [cechTermRestrict_apply, cechTermAction, DirectSum.map_apply]
  exact reindexLoc_action f g e he θ S.1 (x (reindexIdx e S))

end Cech

end
