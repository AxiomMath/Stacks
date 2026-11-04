module

public import StacksFrontier.AlgebraicGeometry.Curves.InseparableFrobeniusFactorization
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Iterated
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Purely inseparable morphisms of curves are iterated relative Frobenius morphisms

Let `k` be a field of characteristic `p > 0` and let `f : X ⟶ Y` be a nonconstant morphism of
proper nonsingular curves over `k` with `X` smooth, whose extension of function fields is
purely inseparable. Factoring `f` into steps of degree `p` -- which is the content of
[Stacks, Tag 0CCX] -- each step is a relative Frobenius by [Stacks, Tag 0CCY], and the composite
of the steps is the `n`-fold relative Frobenius by [Stacks, Tag 0CCG]. The present file performs
that assembly and the uniqueness arguments, from the chain and from the degree of a single
relative Frobenius; both of those are supplied, and [Stacks, Tag 0CCZ] is registered, in
`StacksFrontier/AlgebraicGeometry/Curves/InseparableFrobeniusChainAssembly.lean`.

## Main results

* `AlgebraicGeometry.existsUnique_iso_nFoldFrobeniusTwist_of_inseparable_chain`:
  for a chain of `n` inseparable steps of degree `p` composing to `f`, there is a unique
  isomorphism of the `n`-fold Frobenius twist of `X` with `Y` carrying the `n`-fold relative
  Frobenius to `f`.
* `AlgebraicGeometry.eq_of_iso_nFoldFrobeniusTwist`: the number of iterations is unique.
* `AlgebraicGeometry.existsUnique_nat_existsUnique_iso_nFoldFrobeniusTwist_of_inseparable_chain`:
  the combination of the two, in the shape of the source.
* `exists_iso_nFoldFrobeniusTwist_of_relativeFrobenius_chain` in the auxiliary namespace
  `AlgebraicGeometry.InseparableFrobeniusIteration`: the purely formal assembly step, that a
  chain of relative Frobenius morphisms composes to the iterated relative Frobenius.

## Implementation notes

The factorization of `f` enters in the shape of a family `C : ℕ → Over k` of curves together
with edges `g i : C i ⟶ C (i + 1)`; only the first `n` edges are constrained, so the family may
be continued arbitrarily (by identities, say) past the index `n`, and the endpoints of the first
`n` edges are identified with `X` and `Y` by given isomorphisms over `k`. This is exactly the
data produced by the factorization statement, and none of the constraints imposed on an edge
mentions the Frobenius: an edge carries only its degree at the generic point, pure
inseparability of the induced residue field extension, and nonconstancy.

Smoothness of the intermediate curves is not assumed: it is propagated along the chain from
smoothness of `X`, since each step is identified with a Frobenius twist of its source and the
Frobenius twist is a base change.

## References

* [Stacks Project, Tag 0CCZ](https://stacks.math.columbia.edu/tag/0CCZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

namespace InseparableFrobeniusIteration

/-- The composite of the first `n` edges of a chain of morphisms `g i : C i ⟶ C (i + 1)`. -/
def chainComp {S : Scheme.{u}} (C : ℕ → Over S) (g : ∀ i, C i ⟶ C (i + 1)) :
    (n : ℕ) → (C 0 ⟶ C n)
  | 0 => 𝟙 _
  | n + 1 => chainComp C g n ≫ g n

/-- The composite of the first zero edges of a chain is the identity. -/
@[simp]
theorem chainComp_zero {S : Scheme.{u}} (C : ℕ → Over S) (g : ∀ i, C i ⟶ C (i + 1)) :
    chainComp C g 0 = 𝟙 _ := rfl

/-- The composite of the first `n + 1` edges of a chain is the composite of the first `n` edges
followed by the edge `g n`. -/
@[simp]
theorem chainComp_succ {S : Scheme.{u}} (C : ℕ → Over S) (g : ∀ i, C i ⟶ C (i + 1)) (n : ℕ) :
    chainComp C g (n + 1) = chainComp C g n ≫ g n := rfl

/-- Transport of the first projection of a fibre product along an equality of the second
morphism. -/
theorem eqToHom_pullback_fst {A B D : Scheme.{u}} (f : A ⟶ D) {g h : B ⟶ D} (e : g = h) :
    eqToHom (show pullback f g = pullback f h from by cases e; rfl) ≫
      pullback.fst f h = pullback.fst f g := by
  cases e
  simp

/-- Transport of the second projection of a fibre product along an equality of the second
morphism. -/
theorem eqToHom_pullback_snd {A B D : Scheme.{u}} (f : A ⟶ D) {g h : B ⟶ D} (e : g = h) :
    eqToHom (show pullback f g = pullback f h from by cases e; rfl) ≫
      pullback.snd f h = pullback.snd f g := by
  cases e
  simp

/-- The zero-fold Frobenius twist is the scheme itself, by an isomorphism which is the
zero-fold relative Frobenius. -/
theorem exists_zeroTwistIso (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (X : Over S) :
    ∃ e : X ≅ nFoldFrobeniusTwist S p hS 0 X,
      e.hom = nFoldRelativeFrobenius S p hS 0 X := by
  have hpowS : absoluteFrobeniusPow S p hS 0 = 𝟙 S := by
    simp [absoluteFrobeniusPow]
  have h0 : nFoldFrobeniusTwist S p hS 0 X = (Over.pullback (𝟙 S)).obj X := by
    show (Over.pullback (absoluteFrobeniusPow S p hS 0)).obj X = _
    rw [hpowS]
  refine ⟨(Over.pullbackId.app X).symm ≪≫ (eqToIso h0).symm, ?_⟩
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · calc
      ((Over.pullbackId.app X).symm ≪≫ (eqToIso h0).symm).hom.left ≫
            pullback.fst X.hom (absoluteFrobeniusPow S p hS 0) = 𝟙 X.left := by
        dsimp
        rw [Category.assoc, Over.eqToHom_left, eqToHom_pullback_fst X.hom hpowS.symm]
        simp [Over.pullbackId, Category.assoc, pullback.lift_fst]
      _ = (nFoldRelativeFrobenius S p hS 0 X).left ≫
          pullback.fst X.hom (absoluteFrobeniusPow S p hS 0) := by
        rw [nFoldRelativeFrobenius_fst]
        simp
  · calc
      ((Over.pullbackId.app X).symm ≪≫ (eqToIso h0).symm).hom.left ≫
            pullback.snd X.hom (absoluteFrobeniusPow S p hS 0) = X.hom := by
        dsimp
        rw [Category.assoc, Over.eqToHom_left, eqToHom_pullback_snd X.hom hpowS.symm]
        simp [Over.pullbackId, Category.assoc, pullback.lift_snd]
      _ = (nFoldRelativeFrobenius S p hS 0 X).left ≫
          pullback.snd X.hom (absoluteFrobeniusPow S p hS 0) := by
        rw [nFoldRelativeFrobenius_snd]

/-- The one-fold Frobenius twist is the Frobenius twist. -/
@[sga "3 VIIA 4.1.3" "partial"]
theorem nFoldFrobeniusTwist_one (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (X : Over S) :
    (frobeniusTwist S p hS).obj X = nFoldFrobeniusTwist S p hS 1 X := by
  show (Over.pullback (absoluteFrobenius S p hS)).obj X =
    (Over.pullback (absoluteFrobeniusPow S p hS 1)).obj X
  congr 1

/-- The one-fold relative Frobenius is the relative Frobenius. -/
@[sga "3 VIIA 4.1.3" "partial"]
theorem nFoldRelativeFrobenius_one (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (X : Over S)
    (h : (frobeniusTwist S p hS).obj X = nFoldFrobeniusTwist S p hS 1 X) :
    nFoldRelativeFrobenius S p hS 1 X = relativeFrobenius S p hS X ≫ eqToHom h := by
  rw [nFoldRelativeFrobenius_eq_successiveRelativeFrobenius]
  rfl

/-- The iterated relative Frobenius is the iterated relative Frobenius of the previous stage
followed by the relative Frobenius of the twist. -/
@[sga "3 VIIA 4.1.3" "partial"]
theorem nFoldRelativeFrobenius_succ_succ (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (n : ℕ) (X : Over S) :
    nFoldRelativeFrobenius S p hS (n + 1) X ≫
        relativeFrobenius S p hS (nFoldFrobeniusTwist S p hS (n + 1) X) ≫
          (successiveTwistIso S p hS (n + 1) X).hom =
      nFoldRelativeFrobenius S p hS (n + 2) X := by
  rw [nFoldRelativeFrobenius_eq_successiveRelativeFrobenius S p hS (n + 1) X,
    nFoldRelativeFrobenius_eq_successiveRelativeFrobenius S p hS n X]
  rfl

/-- The iterated absolute Frobenius is natural. -/
@[ega "0 21.2.6" "more general"]
theorem absoluteFrobeniusPow_naturality {V W : Scheme.{u}} (h : V ⟶ W) (p n : ℕ) [Fact p.Prime]
    (hV : IsInCharacteristic V p) (hW : IsInCharacteristic W p) :
    absoluteFrobeniusPow V p hV n ≫ h = h ≫ absoluteFrobeniusPow W p hW n := by
  induction n with
  | zero => simp [absoluteFrobeniusPow]
  | succ n ih =>
      simp only [absoluteFrobeniusPow, pow_succ, End.mul_def]
      show (absoluteFrobenius V p hV ≫ absoluteFrobeniusPow V p hV n) ≫ h =
        h ≫ (absoluteFrobenius W p hW ≫ absoluteFrobeniusPow W p hW n)
      rw [Category.assoc, ih, ← Category.assoc, absoluteFrobenius_naturality h p hV hW,
        Category.assoc]

/-- The iterated relative Frobenius is natural in the `S`-scheme. -/
@[sga "3 VIIA 4.1" "special case",
  sga "3 VIIA 4.1.3" "partial",
  sga "4½ Rapport 1.3" "more general",
  sga "5 XV 1.Proposition1" "At n = 1"]
theorem nFoldRelativeFrobenius_naturality (S : Scheme.{u}) (p n : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) {U V : Over S} (f : U ⟶ V) :
    nFoldRelativeFrobenius S p hS n U ≫
        (Over.pullback (absoluteFrobeniusPow S p hS n)).map f =
      f ≫ nFoldRelativeFrobenius S p hS n V := by
  have hU : IsInCharacteristic U.left p := isInCharacteristic_of_hom U.hom p hS
  have hV : IsInCharacteristic V.left p := isInCharacteristic_of_hom V.hom p hS
  ext
  apply pullback.hom_ext
  · show (nFoldRelativeFrobenius S p hS n U).left ≫
        pullback.lift (pullback.fst U.hom (absoluteFrobeniusPow S p hS n) ≫ f.left)
          (pullback.snd U.hom (absoluteFrobeniusPow S p hS n)) _ ≫
          pullback.fst V.hom (absoluteFrobeniusPow S p hS n) =
      f.left ≫ (nFoldRelativeFrobenius S p hS n V).left ≫
        pullback.fst V.hom (absoluteFrobeniusPow S p hS n)
    calc
      _ = (nFoldRelativeFrobenius S p hS n U).left ≫
          pullback.fst U.hom (absoluteFrobeniusPow S p hS n) ≫ f.left := by
            simp only [pullback.lift_fst]
      _ = absoluteFrobeniusPow U.left p hU n ≫ f.left := by
            rw [← Category.assoc, nFoldRelativeFrobenius_fst]
      _ = f.left ≫ absoluteFrobeniusPow V.left p hV n :=
            absoluteFrobeniusPow_naturality f.left p n hU hV
      _ = f.left ≫ (nFoldRelativeFrobenius S p hS n V).left ≫
          pullback.fst V.hom (absoluteFrobeniusPow S p hS n) := by
            rw [← nFoldRelativeFrobenius_fst]
  · show (nFoldRelativeFrobenius S p hS n U).left ≫
        pullback.lift (pullback.fst U.hom (absoluteFrobeniusPow S p hS n) ≫ f.left)
          (pullback.snd U.hom (absoluteFrobeniusPow S p hS n)) _ ≫
          pullback.snd V.hom (absoluteFrobeniusPow S p hS n) =
      f.left ≫ (nFoldRelativeFrobenius S p hS n V).left ≫
        pullback.snd V.hom (absoluteFrobeniusPow S p hS n)
    simp [pullback.lift_snd, nFoldRelativeFrobenius_snd, Over.w]

/-- **The formal assembly step.** A chain of `n` morphisms, each of which is the relative
Frobenius of its source up to an isomorphism with the Frobenius twist, composes to the
`n`-fold relative Frobenius of its starting object, up to an isomorphism with the `n`-fold
Frobenius twist. -/
@[sga "3 VIIA 4.1.3" "partial"]
theorem exists_iso_nFoldFrobeniusTwist_of_relativeFrobenius_chain
    (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p)
    (C : ℕ → Over S) (g : ∀ i, C i ⟶ C (i + 1)) :
    ∀ n : ℕ,
      (∀ i, i < n → ∃ a : C (i + 1) ≅ (frobeniusTwist S p hS).obj (C i),
          g i ≫ a.hom = relativeFrobenius S p hS (C i)) →
        ∃ e : C n ≅ nFoldFrobeniusTwist S p hS n (C 0),
          chainComp C g n ≫ e.hom = nFoldRelativeFrobenius S p hS n (C 0) := by
  intro n
  induction n with
  | zero =>
      intro _
      obtain ⟨e, he⟩ := exists_zeroTwistIso S p hS (C 0)
      exact ⟨e, by simpa using he⟩
  | succ m ih =>
      cases m with
      | zero =>
          intro hedge
          obtain ⟨a, ha⟩ := hedge 0 (by omega)
          refine ⟨a ≪≫ eqToIso (nFoldFrobeniusTwist_one S p hS (C 0)), ?_⟩
          rw [nFoldRelativeFrobenius_one S p hS (C 0)
            (nFoldFrobeniusTwist_one S p hS (C 0))]
          calc
            chainComp C g 1 ≫ (a ≪≫ eqToIso (nFoldFrobeniusTwist_one S p hS (C 0))).hom =
                (g 0 ≫ a.hom) ≫ eqToHom (nFoldFrobeniusTwist_one S p hS (C 0)) := by
              simp [Iso.trans_hom, Category.assoc]
            _ = relativeFrobenius S p hS (C 0) ≫
                eqToHom (nFoldFrobeniusTwist_one S p hS (C 0)) := by
              rw [ha]
      | succ l =>
          intro hedge
          obtain ⟨e, he⟩ := ih (fun i hi => hedge i (by omega))
          obtain ⟨a, ha⟩ := hedge (l + 1) (by omega)
          refine ⟨a ≪≫ (frobeniusTwist S p hS).mapIso e ≪≫
            successiveTwistIso S p hS (l + 1) (C 0), ?_⟩
          rw [← nFoldRelativeFrobenius_succ_succ S p hS l (C 0), ← he]
          calc
            chainComp C g (l + 2) ≫
                  (a ≪≫ (frobeniusTwist S p hS).mapIso e ≪≫
                    successiveTwistIso S p hS (l + 1) (C 0)).hom =
                chainComp C g (l + 1) ≫ (g (l + 1) ≫ a.hom) ≫
                  (frobeniusTwist S p hS).map e.hom ≫
                    (successiveTwistIso S p hS (l + 1) (C 0)).hom := by
              simp [Iso.trans_hom, Category.assoc]
            _ = chainComp C g (l + 1) ≫ (relativeFrobenius S p hS (C (l + 1)) ≫
                  (frobeniusTwist S p hS).map e.hom) ≫
                    (successiveTwistIso S p hS (l + 1) (C 0)).hom := by
              rw [ha, Category.assoc]
            _ = chainComp C g (l + 1) ≫ (e.hom ≫
                  relativeFrobenius S p hS (nFoldFrobeniusTwist S p hS (l + 1) (C 0))) ≫
                    (successiveTwistIso S p hS (l + 1) (C 0)).hom := by
              rw [relativeFrobenius_naturality]
            _ = (chainComp C g (l + 1) ≫ e.hom) ≫
                  relativeFrobenius S p hS (nFoldFrobeniusTwist S p hS (l + 1) (C 0)) ≫
                    (successiveTwistIso S p hS (l + 1) (C 0)).hom := by
              simp [Category.assoc]

/-- A purely inseparable extension of degree greater than one is not separable. -/
theorem not_isSeparable_of_isPurelyInseparable
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsPurelyInseparable K L]
    (hlarge : 1 < Module.finrank K L) : ¬ Algebra.IsSeparable K L := by
  intro hsep
  have hsurj : Function.Surjective (algebraMap K L) :=
    IsPurelyInseparable.surjective_algebraMap_of_isSeparable K L
  have hdim : Module.finrank K L = 1 := by
    have e : K ≃ₐ[K] L :=
      AlgEquiv.ofBijective (Algebra.ofId K L) ⟨(algebraMap K L).injective, hsurj⟩
    rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]
  omega

/-- One step of the factorization is a relative Frobenius: a nonconstant morphism of proper
nonsingular curves over `k`, with smooth source, whose residue field extension at the generic
point is purely inseparable of degree `p`, identifies its target with the Frobenius twist of
its source, carrying the morphism to the relative Frobenius. This is the application of
[Stacks, Tag 0CCY] to one edge of the chain. -/
theorem exists_relativeFrobeniusIso_of_edge
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hS : IsInCharacteristic (Spec (.of k)) p)
    (U V : Over (Spec (.of k))) (hUcurve : IsCurve k U.hom) (hVcurve : IsCurve k V.hom)
    (hUproper : IsProper U.hom) (hVproper : IsProper V.hom) (hUsmooth : Smooth U.hom)
    (hUreg : IsRegular U.left) (hVreg : IsRegular V.left) (e : U ⟶ V)
    (hnc : (Set.range e.left).Nontrivial)
    (hdeg : e.left.residueDegree (genericPoint U.left) = p)
    (hpure : (e.left.residueFieldMap (genericPoint U.left)).hom.IsPurelyInseparable) :
    ∃ a : V ≅ (frobeniusTwist (Spec (.of k)) p hS).obj U,
      e ≫ a.hom = relativeFrobenius (Spec (.of k)) p hS U := by
  let := (e.left.residueFieldMap (genericPoint U.left)).hom.toAlgebra
  have hnotsep :
      ¬ Algebra.IsSeparable (V.left.residueField (e.left (genericPoint U.left)))
        (U.left.residueField (genericPoint U.left)) := by
    have : IsPurelyInseparable (V.left.residueField (e.left (genericPoint U.left)))
        (U.left.residueField (genericPoint U.left)) := hpure
    have : 1 < e.left.residueDegree (genericPoint U.left) := hdeg ▸ (Fact.out : p.Prime).one_lt
    exact not_isSeparable_of_isPurelyInseparable this
  obtain ⟨a, ha, -⟩ := existsUnique_iso_frobeniusTwist_of_inseparable_degree_prime
    p U.hom V.hom hUreg hVreg e.left (Over.w e) hnc hdeg hnotsep
  exact ⟨a, Over.OverMorphism.ext ha⟩

/-- The left component of an isomorphism in an over category is an isomorphism. -/
private instance isIso_left_of_isIso {S : Scheme.{u}} {A B : Over S} (f : A ⟶ B) [IsIso f] :
    IsIso f.left :=
  Functor.map_isIso (Over.forget S) f

/-- Smoothness of the structure morphism transfers backwards along an isomorphism in an over
category. -/
private theorem smooth_hom_of_iso {S : Scheme.{u}} {A B : Over S} (a : A ≅ B)
    (h : Smooth B.hom) : Smooth A.hom := by
  have hw : a.hom.left ≫ B.hom = A.hom := Over.w a.hom
  rw [← hw]
  infer_instance

/-- Smoothness propagates along the chain: each step is identified with the Frobenius twist of
its source, which is a base change of the source. -/
theorem smooth_of_inseparable_chain
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hS : IsInCharacteristic (Spec (.of k)) p)
    (C : ℕ → Over (Spec (.of k))) (g : ∀ i, C i ⟶ C (i + 1))
    (hcurve : ∀ i, IsCurve k (C i).hom) (hproper : ∀ i, IsProper (C i).hom)
    (hreg : ∀ i, IsRegular (C i).left) (hsmooth0 : Smooth (C 0).hom) (n : ℕ)
    (hnc : ∀ i, i < n → (Set.range (g i).left).Nontrivial)
    (hdeg : ∀ i, i < n → (g i).left.residueDegree (genericPoint (C i).left) = p)
    (hpure : ∀ i, i < n →
      ((g i).left.residueFieldMap (genericPoint (C i).left)).hom.IsPurelyInseparable) :
    ∀ i, i ≤ n → Smooth (C i).hom := by
  intro i
  induction i with
  | zero => exact fun _ => hsmooth0
  | succ m ih =>
      intro hm
      have hsm : Smooth (C m).hom := ih (by omega)
      obtain ⟨a, -⟩ := exists_relativeFrobeniusIso_of_edge p hS (C m) (C (m + 1))
        (hcurve m) (hcurve (m + 1)) (hproper m) (hproper (m + 1)) hsm (hreg m)
        (hreg (m + 1)) (g m) (hnc m (by omega)) (hdeg m (by omega)) (hpure m (by omega))
      have : Smooth ((frobeniusTwist (Spec (.of k)) p hS).obj (C m)).hom := by
        show Smooth (pullback.snd (C m).hom (absoluteFrobenius (Spec (.of k)) p hS))
        infer_instance
      exact smooth_hom_of_iso a this

/-- The `n`-fold Frobenius twist of a smooth scheme over a field is reduced: it is smooth,
hence geometrically reduced and flat, over a reduced locally noetherian base. -/
theorem isReduced_nFoldFrobeniusTwist
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hS : IsInCharacteristic (Spec (.of k)) p) (n : ℕ)
    (X : Over (Spec (.of k))) (hX : Smooth X.hom) :
    IsReduced (nFoldFrobeniusTwist (Spec (.of k)) p hS n X).left := by
  have hsmooth : Smooth (nFoldFrobeniusTwist (Spec (.of k)) p hS n X).hom := by
    show Smooth (pullback.snd X.hom (absoluteFrobeniusPow (Spec (.of k)) p hS n))
    infer_instance
  have : GeometricallyReduced (nFoldFrobeniusTwist (Spec (.of k)) p hS n X).hom :=
    geometricallyReduced_of_smooth _
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
    (nFoldFrobeniusTwist (Spec (.of k)) p hS n X).hom

/-- The iterated relative Frobenius is a homeomorphism on underlying spaces: the relative
Frobenius is a universal homeomorphism, and the iterate is a composite of such up to
isomorphism. -/
theorem isHomeomorph_nFoldRelativeFrobenius (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (X : Over S) :
    ∀ n : ℕ, IsHomeomorph (nFoldRelativeFrobenius S p hS n X).left := by
  have hrel : ∀ Z : Over S, IsHomeomorph (relativeFrobenius S p hS Z).left := fun Z =>
    (relativeFrobenius_universalHomeomorphism S p hS Z).universally_isHomeomorph
      _ _ _ IsPullback.of_id_snd
  intro n
  induction n with
  | zero =>
      obtain ⟨e, he⟩ := exists_zeroTwistIso S p hS X
      rw [← he]
      exact e.hom.left.homeomorph.isHomeomorph
  | succ m ih =>
      cases m with
      | zero =>
          rw [nFoldRelativeFrobenius_one S p hS X (nFoldFrobeniusTwist_one S p hS X)]
          show IsHomeomorph ((relativeFrobenius S p hS X).left ≫
            (eqToHom (nFoldFrobeniusTwist_one S p hS X)).left)
          exact (eqToHom (nFoldFrobeniusTwist_one S p hS X)).left.homeomorph.isHomeomorph.comp
            (hrel X)
      | succ l =>
          rw [← nFoldRelativeFrobenius_succ_succ S p hS l X]
          show IsHomeomorph ((nFoldRelativeFrobenius S p hS (l + 1) X).left ≫
            (relativeFrobenius S p hS (nFoldFrobeniusTwist S p hS (l + 1) X)).left ≫
              (successiveTwistIso S p hS (l + 1) X).hom.left)
          exact ((successiveTwistIso S p hS (l + 1) X).hom.left.homeomorph.isHomeomorph.comp
            (hrel (nFoldFrobeniusTwist S p hS (l + 1) X))).comp ih

/-- An isomorphism has residue degree one at every point. -/
theorem residueDegree_of_isIso {A B : Scheme.{u}} (h : A ⟶ B) [IsIso h] (x : A) :
    h.residueDegree x = 1 := by
  have hc := residueDegree_comp h (inv h) x
  rw [IsIso.hom_inv_id, Scheme.Hom.residueDegree_id] at hc
  exact Nat.eq_one_of_mul_eq_one_left hc.symm

/-- A surjective morphism of irreducible schemes takes the generic point to the generic
point. -/
theorem genericPoint_map_of_surjective {A B : Scheme.{u}} [IrreducibleSpace A]
    [IrreducibleSpace B] (h : A ⟶ B) (hs : Function.Surjective h) :
    h (genericPoint A) = genericPoint B := by
  apply ((genericPoint_spec B).eq _).symm
  simpa [Set.image_univ, Set.range_eq_univ.mpr hs] using
    (genericPoint_spec A).image h.continuous

/-- The `n`-fold Frobenius twist of a smooth `S`-scheme is smooth, being a base change. -/
theorem smooth_nFoldFrobeniusTwist (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (n : ℕ) (X : Over S) (hX : Smooth X.hom) :
    Smooth (nFoldFrobeniusTwist S p hS n X).hom := by
  show Smooth (pullback.snd X.hom (absoluteFrobeniusPow S p hS n))
  infer_instance

/-- The `n`-fold Frobenius twist of a smooth curve over a field is again a curve: it is
reduced, and the iterated relative Frobenius is a homeomorphism onto it. -/
theorem isCurve_nFoldFrobeniusTwist
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hS : IsInCharacteristic (Spec (.of k)) p) (n : ℕ) (X : Over (Spec (.of k)))
    (hXcurve : IsCurve k X.hom) (hXsmooth : Smooth X.hom) :
    IsCurve k (nFoldFrobeniusTwist (Spec (.of k)) p hS n X).hom := by
  have hh := isHomeomorph_nFoldRelativeFrobenius (Spec (.of k)) p hS X n
  have : IsReduced (nFoldFrobeniusTwist (Spec (.of k)) p hS n X).left :=
    isReduced_nFoldFrobeniusTwist p hS n X hXsmooth
  have : IrreducibleSpace (nFoldFrobeniusTwist (Spec (.of k)) p hS n X).left :=
    Function.Surjective.irreducibleSpace hh.continuous hh.surjective
  have : IsIntegral (nFoldFrobeniusTwist (Spec (.of k)) p hS n X).left :=
    isIntegral_of_irreducibleSpace_of_isReduced _
  have : IsSeparated (nFoldFrobeniusTwist (Spec (.of k)) p hS n X).hom := by
    show IsSeparated (pullback.snd X.hom (absoluteFrobeniusPow (Spec (.of k)) p hS n))
    infer_instance
  have : LocallyOfFiniteType (nFoldFrobeniusTwist (Spec (.of k)) p hS n X).hom := by
    show LocallyOfFiniteType
      (pullback.snd X.hom (absoluteFrobeniusPow (Spec (.of k)) p hS n))
    infer_instance
  have : QuasiCompact (nFoldFrobeniusTwist (Spec (.of k)) p hS n X).hom := by
    show QuasiCompact (pullback.snd X.hom (absoluteFrobeniusPow (Spec (.of k)) p hS n))
    infer_instance
  refine { topologicalKrullDim_eq_one := ?_ }
  exact (hh.topologicalKrullDim_eq _).symm.trans (IsCurve.topologicalKrullDim_eq_one X.hom)

/-- The `n`-fold relative Frobenius of a smooth curve has residue degree `p ^ n` at the
generic point, the degree of a single relative Frobenius entering through `hdegFrob`; that is
[Stacks, Tag 0CCF], `AlgebraicGeometry.residueDegree_relativeFrobenius_isCurve`. -/
theorem residueDegree_nFoldRelativeFrobenius
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hS : IsInCharacteristic (Spec (.of k)) p)
    (hdegFrob : ∀ (Z : Over (Spec (.of k))) [IsCurve k Z.hom] [Smooth Z.hom],
      (relativeFrobenius (Spec (.of k)) p hS Z).left.residueDegree
        (genericPoint Z.left) = p)
    (X : Over (Spec (.of k))) (hXcurve : IsCurve k X.hom) (hXsmooth : Smooth X.hom) :
    ∀ n : ℕ, (nFoldRelativeFrobenius (Spec (.of k)) p hS n X).left.residueDegree
      (genericPoint X.left) = p ^ n := by
  intro n
  induction n with
  | zero =>
      obtain ⟨e, he⟩ := exists_zeroTwistIso (Spec (.of k)) p hS X
      rw [← he]
      simpa using residueDegree_of_isIso e.hom.left (genericPoint X.left)
  | succ m ih =>
      cases m with
      | zero =>
          rw [nFoldRelativeFrobenius_one (Spec (.of k)) p hS X
            (nFoldFrobeniusTwist_one (Spec (.of k)) p hS X)]
          show ((relativeFrobenius (Spec (.of k)) p hS X).left ≫
            (eqToHom (nFoldFrobeniusTwist_one (Spec (.of k)) p hS X)).left).residueDegree
              (genericPoint X.left) = p ^ 1
          rw [residueDegree_comp, residueDegree_of_isIso, one_mul, pow_one]
          exact hdegFrob X
      | succ l =>
          rw [← nFoldRelativeFrobenius_succ_succ (Spec (.of k)) p hS l X]
          have hTcurve : IsCurve k
              (nFoldFrobeniusTwist (Spec (.of k)) p hS (l + 1) X).hom :=
            isCurve_nFoldFrobeniusTwist p hS (l + 1) X hXcurve hXsmooth
          have hTsmooth : Smooth
              (nFoldFrobeniusTwist (Spec (.of k)) p hS (l + 1) X).hom :=
            smooth_nFoldFrobeniusTwist (Spec (.of k)) p hS (l + 1) X hXsmooth
          have hTred : IsReduced
              (nFoldFrobeniusTwist (Spec (.of k)) p hS (l + 1) X).left :=
            isReduced_nFoldFrobeniusTwist p hS (l + 1) X hXsmooth
          have hh := isHomeomorph_nFoldRelativeFrobenius (Spec (.of k)) p hS X (l + 1)
          show ((nFoldRelativeFrobenius (Spec (.of k)) p hS (l + 1) X).left ≫
            (relativeFrobenius (Spec (.of k)) p hS
                (nFoldFrobeniusTwist (Spec (.of k)) p hS (l + 1) X)).left ≫
              (successiveTwistIso (Spec (.of k)) p hS (l + 1) X).hom.left).residueDegree
                (genericPoint X.left) = p ^ (l + 2)
          rw [residueDegree_comp, residueDegree_comp, residueDegree_of_isIso, one_mul,
            genericPoint_map_of_surjective _ hh.surjective, hdegFrob _, ih]
          exact (pow_succ' p (l + 1)).symm

/-- The iterated relative Frobenius is dominant. -/
theorem isDominant_nFoldRelativeFrobenius (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (n : ℕ) (X : Over S) :
    IsDominant (nFoldRelativeFrobenius S p hS n X).left :=
  ⟨(isHomeomorph_nFoldRelativeFrobenius S p hS X n).surjective.denseRange⟩

end InseparableFrobeniusIteration

open InseparableFrobeniusIteration in
/-- The assembly step for [Stacks, Tag 0CCZ]: existence and uniqueness of the isomorphism from a
given chain. Let `f : X ⟶ Y` be a nonconstant morphism of proper nonsingular curves over a field
`k` of characteristic `p`, with `X` smooth and the induced extension of function fields purely
inseparable. Suppose `f` is the composite of a chain of `n` morphisms of proper nonsingular curves
over `k`, each purely inseparable of degree `p` at the generic point and nonconstant, with the two
endpoints of the chain identified with `X` and `Y` over `k`. Then there is a unique isomorphism
over `k` of the `n`-fold Frobenius twist of `X` with `Y` which carries the `n`-fold relative
Frobenius of `X` to `f`.

The number `n` of steps is here the given length of the chain. The chain itself is produced by
[Stacks, Tag 0CCX], and the tag is registered on
`AlgebraicGeometry.existsUnique_nat_existsUnique_iso_nFoldFrobeniusTwist` in
`StacksFrontier/AlgebraicGeometry/Curves/InseparableFrobeniusChainAssembly.lean`, where that chain is
supplied and the number of steps is shown unique. -/
theorem existsUnique_iso_nFoldFrobeniusTwist_of_inseparable_chain
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hS : IsInCharacteristic (Spec (.of k)) p)
    {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [IsCurve k pX] [IsCurve k pY] [IsProper pX] [IsProper pY] [Smooth pX]
    (_hXreg : IsRegular X) (_hYreg : IsRegular Y)
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (_hnonconstant : (Set.range f).Nontrivial)
    (_hpure : (f.residueFieldMap (genericPoint X)).hom.IsPurelyInseparable)
    (n : ℕ) (C : ℕ → Over (Spec (.of k))) (g : ∀ i, C i ⟶ C (i + 1))
    (hcurve : ∀ i, IsCurve k (C i).hom) (hproper : ∀ i, IsProper (C i).hom)
    (hreg : ∀ i, IsRegular (C i).left)
    (hnc : ∀ i, i < n → (Set.range (g i).left).Nontrivial)
    (hdeg : ∀ i, i < n → (g i).left.residueDegree (genericPoint (C i).left) = p)
    (hpure : ∀ i, i < n →
      ((g i).left.residueFieldMap (genericPoint (C i).left)).hom.IsPurelyInseparable)
    (iX : C 0 ≅ Over.mk pX) (iY : C n ≅ Over.mk pY)
    (hpath : iX.inv ≫ chainComp C g n ≫ iY.hom = Over.homMk f hf) :
    ∃! e : nFoldFrobeniusTwist (Spec (.of k)) p hS n (Over.mk pX) ≅ Over.mk pY,
      nFoldRelativeFrobenius (Spec (.of k)) p hS n (Over.mk pX) ≫ e.hom =
        Over.homMk f hf := by
  have hsmooth0 : Smooth (C 0).hom := smooth_hom_of_iso iX (inferInstanceAs (Smooth pX))
  have hsm := smooth_of_inseparable_chain p hS C g hcurve hproper hreg hsmooth0 n hnc hdeg hpure
  have hedge : ∀ i, i < n →
      ∃ a : C (i + 1) ≅ (frobeniusTwist (Spec (.of k)) p hS).obj (C i),
        g i ≫ a.hom = relativeFrobenius (Spec (.of k)) p hS (C i) := fun i hi =>
    exists_relativeFrobeniusIso_of_edge p hS (C i) (C (i + 1)) (hcurve i) (hcurve (i + 1))
      (hproper i) (hproper (i + 1)) (hsm i (by omega)) (hreg i) (hreg (i + 1)) (g i)
      (hnc i hi) (hdeg i hi) (hpure i hi)
  obtain ⟨eChain, heChain⟩ :=
    exists_iso_nFoldFrobeniusTwist_of_relativeFrobenius_chain (Spec (.of k)) p hS C g n hedge
  let tw : Over (Spec (.of k)) ⥤ Over (Spec (.of k)) :=
    Over.pullback (absoluteFrobeniusPow (Spec (.of k)) p hS n)
  let iXtw : tw.obj (C 0) ≅ tw.obj (Over.mk pX) := tw.mapIso iX
  have htransport : nFoldRelativeFrobenius (Spec (.of k)) p hS n (Over.mk pX) ≫ iXtw.inv =
      iX.inv ≫ nFoldRelativeFrobenius (Spec (.of k)) p hS n (C 0) :=
    nFoldRelativeFrobenius_naturality (Spec (.of k)) p n hS iX.inv
  have hmain : nFoldRelativeFrobenius (Spec (.of k)) p hS n (Over.mk pX) ≫
      (iXtw.symm ≪≫ eChain.symm ≪≫ iY).hom = Over.homMk f hf := by
    calc
      nFoldRelativeFrobenius (Spec (.of k)) p hS n (Over.mk pX) ≫
            (iXtw.symm ≪≫ eChain.symm ≪≫ iY).hom =
          (nFoldRelativeFrobenius (Spec (.of k)) p hS n (Over.mk pX) ≫ iXtw.inv) ≫
            eChain.inv ≫ iY.hom := by
        simp [Category.assoc]
      _ = iX.inv ≫ (nFoldRelativeFrobenius (Spec (.of k)) p hS n (C 0) ≫ eChain.inv) ≫
            iY.hom := by
        rw [htransport]
        simp [Category.assoc]
      _ = iX.inv ≫ chainComp C g n ≫ iY.hom := by
        rw [← heChain]
        simp
      _ = Over.homMk f hf := hpath
  refine ⟨iXtw.symm ≪≫ eChain.symm ≪≫ iY, hmain, fun e' he' => ?_⟩
  have hred : IsReduced (nFoldFrobeniusTwist (Spec (.of k)) p hS n (Over.mk pX)).left :=
    isReduced_nFoldFrobeniusTwist p hS n (Over.mk pX) (inferInstanceAs (Smooth pX))
  have hdom : IsDominant
      (nFoldRelativeFrobenius (Spec (.of k)) p hS n (Over.mk pX)).left :=
    isDominant_nFoldRelativeFrobenius (Spec (.of k)) p hS n (Over.mk pX)
  have hsep : IsSeparated (Over.mk pY).hom := inferInstanceAs (IsSeparated pY)
  apply Iso.ext
  apply overHom_ext_of_isDominant
    (nFoldRelativeFrobenius (Spec (.of k)) p hS n (Over.mk pX)).left
  simpa using congrArg Over.Hom.left (he'.trans hmain.symm)

open InseparableFrobeniusIteration in
/-- **Stacks Project, Tag 0CCZ**, uniqueness of the number of iterations. If a morphism `f`
from a smooth curve `X` over `k` is the `m`-fold relative Frobenius of `X` up to an
isomorphism of its target with the `m`-fold Frobenius twist, and also the `n`-fold relative
Frobenius up to such an isomorphism, then `m = n`: both numbers are read off the residue
degree of `f` at the generic point, which is `p ^ m` and `p ^ n`.

The degree of a single relative Frobenius of a smooth curve, which is [Stacks, Tag 0CCF], enters
through `hdegFrob`; it is supplied by
`AlgebraicGeometry.residueDegree_relativeFrobenius_isCurve` in
`StacksFrontier/AlgebraicGeometry/Curves/InseparableFrobeniusChainAssembly.lean`, where the tag is
registered on
`AlgebraicGeometry.existsUnique_nat_existsUnique_iso_nFoldFrobeniusTwist`. -/
theorem eq_of_iso_nFoldFrobeniusTwist
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hS : IsInCharacteristic (Spec (.of k)) p)
    (hdegFrob : ∀ (Z : Over (Spec (.of k))) [IsCurve k Z.hom] [Smooth Z.hom],
      (relativeFrobenius (Spec (.of k)) p hS Z).left.residueDegree
        (genericPoint Z.left) = p)
    {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [IsCurve k pX] [Smooth pX] (f : X ⟶ Y) (hf : f ≫ pY = pX) (m n : ℕ)
    (e : nFoldFrobeniusTwist (Spec (.of k)) p hS m (Over.mk pX) ≅ Over.mk pY)
    (he : nFoldRelativeFrobenius (Spec (.of k)) p hS m (Over.mk pX) ≫ e.hom =
      Over.homMk f hf)
    (e' : nFoldFrobeniusTwist (Spec (.of k)) p hS n (Over.mk pX) ≅ Over.mk pY)
    (he' : nFoldRelativeFrobenius (Spec (.of k)) p hS n (Over.mk pX) ≫ e'.hom =
      Over.homMk f hf) :
    m = n := by
  have key : ∀ (r : ℕ)
      (a : nFoldFrobeniusTwist (Spec (.of k)) p hS r (Over.mk pX) ≅ Over.mk pY),
      nFoldRelativeFrobenius (Spec (.of k)) p hS r (Over.mk pX) ≫ a.hom = Over.homMk f hf →
        f.residueDegree (genericPoint X) = p ^ r := by
    intro r a ha
    have hcurve : IsCurve k (Over.mk pX).hom := inferInstanceAs (IsCurve k pX)
    have hsmooth : Smooth (Over.mk pX).hom := inferInstanceAs (Smooth pX)
    have h := congrArg (fun t : Over.mk pX ⟶ Over.mk pY =>
      t.left.residueDegree (genericPoint X)) ha
    change ((nFoldRelativeFrobenius (Spec (.of k)) p hS r (Over.mk pX)).left ≫
      a.hom.left).residueDegree (genericPoint X) =
        f.residueDegree (genericPoint X) at h
    rw [residueDegree_comp, residueDegree_of_isIso, one_mul] at h
    rw [← h]
    exact residueDegree_nFoldRelativeFrobenius p hS hdegFrob (Over.mk pX) hcurve hsmooth r
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le
    ((key m e he).symm.trans (key n e' he'))

open InseparableFrobeniusIteration in
/-- **Stacks Project, Tag 0CCZ**, in its full shape. Let `f : X ⟶ Y` be a nonconstant
morphism of proper nonsingular curves over a field `k` of characteristic `p`, with `X` smooth
and the induced extension of function fields purely inseparable. Suppose `f` is the composite
of a chain of `n` morphisms of proper nonsingular curves over `k`, each nonconstant and purely
inseparable of degree `p` at the generic point, with the endpoints of the chain identified with
`X` and `Y` over `k`. Then there is a unique number of iterations and, for it, a unique
isomorphism over `k` of the correspondingly iterated Frobenius twist of `X` with `Y` carrying
the iterated relative Frobenius of `X` to `f`.

The two inputs of the source's proof enter as the chain and as `hdegFrob`: they are supplied by
[Stacks, Tag 0CCX], `AlgebraicGeometry.exists_chain_isInseparableDegreePrime`, and by
[Stacks, Tag 0CCF], `AlgebraicGeometry.residueDegree_relativeFrobenius_isCurve`, in
`StacksFrontier/AlgebraicGeometry/Curves/InseparableFrobeniusChainAssembly.lean`, where the tag is
registered on
`AlgebraicGeometry.existsUnique_nat_existsUnique_iso_nFoldFrobeniusTwist`. -/
theorem existsUnique_nat_existsUnique_iso_nFoldFrobeniusTwist_of_inseparable_chain
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hS : IsInCharacteristic (Spec (.of k)) p)
    (hdegFrob : ∀ (Z : Over (Spec (.of k))) [IsCurve k Z.hom] [Smooth Z.hom],
      (relativeFrobenius (Spec (.of k)) p hS Z).left.residueDegree
        (genericPoint Z.left) = p)
    {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [IsCurve k pX] [IsCurve k pY] [IsProper pX] [IsProper pY] [Smooth pX]
    (hXreg : IsRegular X) (hYreg : IsRegular Y)
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (hnonconstant : (Set.range f).Nontrivial)
    (hpuref : (f.residueFieldMap (genericPoint X)).hom.IsPurelyInseparable)
    (n : ℕ) (C : ℕ → Over (Spec (.of k))) (g : ∀ i, C i ⟶ C (i + 1))
    (hcurve : ∀ i, IsCurve k (C i).hom) (hproper : ∀ i, IsProper (C i).hom)
    (hreg : ∀ i, IsRegular (C i).left)
    (hnc : ∀ i, i < n → (Set.range (g i).left).Nontrivial)
    (hdeg : ∀ i, i < n → (g i).left.residueDegree (genericPoint (C i).left) = p)
    (hpure : ∀ i, i < n →
      ((g i).left.residueFieldMap (genericPoint (C i).left)).hom.IsPurelyInseparable)
    (iX : C 0 ≅ Over.mk pX) (iY : C n ≅ Over.mk pY)
    (hpath : iX.inv ≫ chainComp C g n ≫ iY.hom = Over.homMk f hf) :
    ∃! m : ℕ, ∃! e : nFoldFrobeniusTwist (Spec (.of k)) p hS m (Over.mk pX) ≅ Over.mk pY,
      nFoldRelativeFrobenius (Spec (.of k)) p hS m (Over.mk pX) ≫ e.hom =
        Over.homMk f hf := by
  have hiso := existsUnique_iso_nFoldFrobeniusTwist_of_inseparable_chain p hS pX pY hXreg
    hYreg f hf hnonconstant hpuref n C g hcurve hproper hreg hnc hdeg hpure iX iY hpath
  refine ⟨n, hiso, ?_⟩
  rintro m ⟨e', he', -⟩
  obtain ⟨e, he, -⟩ := hiso
  exact eq_of_iso_nFoldFrobeniusTwist p hS hdegFrob pX pY f hf m n e' he' e he

end AlgebraicGeometry

end
