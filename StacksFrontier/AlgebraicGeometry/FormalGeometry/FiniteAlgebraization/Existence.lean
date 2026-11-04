module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FiniteAlgebraization.AdicSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FiniteAlgebraization.AlgebraTransfer
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.GrothendieckExistenceProper

/-!
# Grothendieck existence for finite sheaves of algebras

Let `A` be a Noetherian ring complete with respect to an ideal `I` and `f : X ⟶ Spec A` proper.
This file proves `AlgebraicGeometry.AdicFiniteAlgebraAlgebraization A I f`, the hypothesis of the
library's Stacks 09ZT: every compatible system of finite quasi-coherent algebras on the adic
thickenings of `X` is the system of pullbacks of one finite quasi-coherent algebra on `X`, whose
relative spectrum is proper over `Spec A`.

The proof is the one the source gives for 09ZT (with 088E/088F for the module): the pushforwards
of the algebras form a coherent adic system (`AdicFiniteAlgebra.sysAdic`), Grothendieck existence
(Stacks 088C) writes it as the completion of a coherent module `M`, and full faithfulness together
with `Stacks.Algebraization.completionHomLimitEquiv` makes morphisms from coherent modules into
`M` the same as compatible families into the system (`exists_hom_comp_κ`, `eq_of_comp_κ`). That
is exactly the input of `AdicFiniteAlgebra.LiftData`, which produces the algebra; its pullbacks are
identified with the given algebras on sections over affine opens
(`nonempty_algebraPullback_iso_of_sections`).

## Main results

* `AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_isEquivalence` — from the equivalence of
  Stacks 088C, in the form of `Stacks.Algebraization.isEquivalence_completionFunctor_of_isProper`.
* `AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_isProper` — unconditionally.

## References

* [Stacks Project, Tag 09ZT](https://stacks.math.columbia.edu/tag/09ZT)
* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open Stacks.AffineAlgebraEquivalence Stacks.Algebraization
open Stacks.RelativeSpec (AlgebraSheaf)
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf)

universe u

namespace AlgebraicGeometry.AdicFiniteAlgebra

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {A : Type u} [CommRing A] {I : Ideal A} {X : Scheme.{u}} {f : X ⟶ Spec (.of A)}
variable (B : ∀ n : ℕ, AlgebraSheaf (adicBaseChange A I f n))
  [hqc : ∀ n, AlgebraSheaf.IsQuasicoherent (B n)]
  (e : ∀ n, (algebraPullback (adicBaseChangeSucc A I f n)).obj (B (n + 1)) ≅ B n)
  [hfin : ∀ n, IsFinite (sysy B n)] [IsLocallyNoetherian X]
  (M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
  (ε : (completionFunctor X (baseIdealSheaf A I f)).obj M ≅ sysAdic B e)

/-- Pasting two commutative squares, in an abstract category. -/
public theorem comp_comp_eq_of_comm {C : Type*} [Category C] {a b c d e : C} (π' : a ⟶ b)
    (T : b ⟶ c) (π : a ⟶ c) (ε' : b ⟶ d) (ε : c ⟶ e) (S : d ⟶ e) (h3 : π' ≫ T = π)
    (h1 : T ≫ ε = ε' ≫ S) : (π' ≫ ε') ≫ S = π ≫ ε := by
  rw [Category.assoc, ← h1, ← Category.assoc, h3]

/-- Cancelling an isomorphism out of a factorization, in an abstract category. -/
public theorem comp_eq_of_factor {C : Type*} [Category C] {a b c d c' : C} (φ : a ⟶ b)
    (πM : b ⟶ c) (πG : a ⟶ d) (H : d ⟶ c') (Ei : c' ⟶ c) (Eh : c ⟶ c') (gn : a ⟶ c')
    (h1 : πG ≫ (H ≫ Ei) = φ ≫ πM) (h2 : πG ≫ H = gn) (h4 : Ei ≫ Eh = 𝟙 _) :
    φ ≫ (πM ≫ Eh) = gn := by
  rwa [← Category.assoc, ← h1, Category.assoc, Category.assoc, h4, Category.comp_id]

/-- Two maps out of the target of an epimorphism agreeing after a common factorization. -/
public theorem comp_eq_comp_of_epi {C : Type*} [Category C] {a b c d m : C} (pG : a ⟶ b)
    [Epi pG] (Fφ Fψ : b ⟶ c) (E : c ⟶ d) (φ ψ : a ⟶ m) (pM : m ⟶ c)
    (h1 : pG ≫ Fφ = φ ≫ pM) (h2 : pG ≫ Fψ = ψ ≫ pM) (h : φ ≫ (pM ≫ E) = ψ ≫ (pM ≫ E)) :
    Fφ ≫ E = Fψ ≫ E := by
  rwa [← cancel_epi pG, ← Category.assoc, h1, ← Category.assoc, h2, Category.assoc,
    Category.assoc]

/-- The projection `M ⟶ Nₙ`. -/
public def κ (n : ℕ) : M.obj ⟶ sysN B n :=
  completionProjection X (baseIdealSheaf A I f) M n ≫ ε.hom.hom.app (op n)

/-- The projections `M ⟶ Nₙ` are compatible with the transition morphisms. -/
public theorem κ_comp_sysNτ (n : ℕ) : κ B e M ε (n + 1) ≫ sysNτ B e n = κ B e M ε n := by
  have h1 := ε.hom.hom.naturality (homOfLE (Nat.le_succ n)).op
  have h2 := sysNSystem_map_succ B e n
  have h3 := completionProjection_transition X (baseIdealSheaf A I f) M n
  change (sysAdic B e).obj.map (homOfLE (Nat.le_succ n)).op = sysNτ B e n at h2
  exact comp_comp_eq_of_comm _ _ _ _ _ _ h3 (h1.trans (congrArg _ h2))


/-- The cone on `(Nₙ)` given by a compatible family of morphisms `G ⟶ Nₙ`. -/
public def familyCone {G : X.Modules} (g : ∀ n, G ⟶ sysN B n)
    (hg : ∀ n, g (n + 1) ≫ sysNτ B e n = g n) : Cone (sysAdic B e).obj where
  pt := G
  π := NatTrans.ofOpSequence (F := (Functor.const ℕᵒᵖ).obj G) (G := (sysAdic B e).obj)
    (fun n => g n) (fun n => by
      change 𝟙 G ≫ g n = g (n + 1) ≫ (sysNSystem B e).map (homOfLE (Nat.le_add_right n 1)).op
      rw [Category.id_comp]
      exact ((congrArg (g (n + 1) ≫ ·) (sysNSystem_map_succ B e n)).trans (hg n)).symm)

/-- **Existence of lifts.** A compatible family of morphisms from a coherent module into the
`Nₙ` comes from a morphism into `M`. -/
public theorem exists_hom_comp_κ [(completionFunctor X (baseIdealSheaf A I f)).Full]
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (g : ∀ n, G.obj ⟶ sysN B n) (hg : ∀ n, g (n + 1) ≫ sysNτ B e n = g n) :
    ∃ φ : G ⟶ M, ∀ n, φ.hom ≫ κ B e M ε n = g n := by
  let ℓ : coherentObj G ⟶ limit (sysAdic B e).obj := limit.lift _ (familyCone B e g hg)
  let ψ := homToAdicSystem G (sysAdic B e) ℓ ≫ ε.inv
  refine ⟨(completionFunctor X (baseIdealSheaf A I f)).preimage ψ, fun n => ?_⟩
  have h1 := completionFunctor_map_quotient X (baseIdealSheaf A I f)
    ((completionFunctor X (baseIdealSheaf A I f)).preimage ψ) n
  rw [Functor.map_preimage] at h1
  have h2 := completionProjection_homToAdicSystem G (sysAdic B e) ℓ (op n)
  have h3 : ℓ ≫ limit.π (sysAdic B e).obj (op n) = g n := limit.lift_π _ _
  have h4 : ε.inv.hom.app (op n) ≫ ε.hom.hom.app (op n) = 𝟙 _ := by
    rw [← NatTrans.comp_app]
    exact congrArg (fun φ => NatTrans.app φ (op n)) (congrArg InducedCategory.Hom.hom ε.inv_hom_id)
  exact comp_eq_of_factor _ _ _ _ _ _ _ h1 (h2.trans h3) h4

/-- **Uniqueness of lifts.** Two morphisms from a coherent module into `M` agreeing after every
projection `M ⟶ Nₙ` are equal. -/
public theorem eq_of_comp_κ [(completionFunctor X (baseIdealSheaf A I f)).Faithful]
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (φ ψ : G ⟶ M)
    (h : ∀ n, φ.hom ≫ κ B e M ε n = ψ.hom ≫ κ B e M ε n) : φ = ψ := by
  apply (completionFunctor X (baseIdealSheaf A I f)).map_injective
  refine (cancel_mono ε.hom).1 ?_
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun n => ?_))
  obtain ⟨n⟩ := n
  have := epi_completionProjection X (baseIdealSheaf A I f) G n
  exact @comp_eq_comp_of_epi X.Modules _ _ _ _ _ _
    (completionProjection X (baseIdealSheaf A I f) G n) this _ _ _ _ _ _
    (completionFunctor_map_quotient X (baseIdealSheaf A I f) φ n)
    (completionFunctor_map_quotient X (baseIdealSheaf A I f) ψ n) (h n)

/-- **The lifting data**: `M` with its projections to the system `(Nₙ)`. -/
public def liftData [(completionFunctor X (baseIdealSheaf A I f)).Full]
    [(completionFunctor X (baseIdealSheaf A I f)).Faithful] : LiftData X where
  F := M.obj
  hF := M.property
  D := sysD B
  τ := sysτ B e
  p := κ B e M ε
  hp := κ_comp_sysNτ B e M ε
  hex G hG g hg :=
    let ⟨φ, hφ⟩ := exists_hom_comp_κ B e M ε ⟨G, hG⟩ g hg
    ⟨φ.hom, hφ⟩
  huniq G hG φ ψ h :=
    congrArg (fun χ => χ.hom) (eq_of_comp_κ B e M ε ⟨G, hG⟩ (ObjectProperty.homMk φ)
      (ObjectProperty.homMk ψ) h)

/-- An isomorphism of sheaves of modules is bijective on sections. -/
public theorem bijective_iso_app {Z : Scheme.{u}} {P Q : Z.Modules} (E : P ≅ Q) (U : Z.Opens) :
    Function.Bijective (E.hom.val.app (op U)) :=
  ⟨Function.LeftInverse.injective (g := E.inv.val.app (op U)) fun x =>
      congrArg (fun ψ : P ⟶ P => ψ.val.app (op U) x) E.hom_inv_id,
    Function.RightInverse.surjective (g := E.inv.val.app (op U)) fun x =>
      congrArg (fun ψ : Q ⟶ Q => ψ.val.app (op U) x) E.inv_hom_id⟩

/-- The component of `ε` at `n`, as an isomorphism of modules. -/
public def εApp (n : ℕ) :
    ((completionFunctor X (baseIdealSheaf A I f)).obj M).obj.obj (op n) ≅ sysN B n where
  hom := ε.hom.hom.app (op n)
  inv := ε.inv.hom.app (op n)
  hom_inv_id := congrArg (fun φ => NatTrans.app φ (op n))
    (congrArg InducedCategory.Hom.hom ε.hom_inv_id)
  inv_hom_id := congrArg (fun φ => NatTrans.app φ (op n))
    (congrArg InducedCategory.Hom.hom ε.inv_hom_id)

/-- The projections `M ⟶ Nₙ` are surjective on sections over affine opens. -/
public theorem κ_surjective (n : ℕ) (U : X.affineOpens) :
    Function.Surjective ((κ B e M ε n).val.app (op U.1)) := fun y => by
  obtain ⟨z, hz⟩ := (bijective_iso_app (εApp B e M ε n) U.1).2 y
  obtain ⟨x, hx⟩ := completionProjection_app_surjective X (baseIdealSheaf A I f) M n U z
  exact ⟨x, (congrArg ((εApp B e M ε n).hom.val.app (op U.1)) hx).trans hz⟩

/-- The kernel of `M ⟶ Nₙ` on sections over an affine open `U` is `I(U)^(n+1) • M(U)`. -/
public theorem κ_ker (n : ℕ) (U : X.affineOpens) (x : Γ(coherentObj M, U.1))
    (hx : (κ B e M ε n).val.app (op U.1) x = 0) :
    x ∈ (baseIdealSheaf A I f).ideal U ^ (n + 1) •
      (⊤ : Submodule Γ(X, U.1) Γ(coherentObj M, U.1)) := by
  have hk := completionProjection_app_ker X (baseIdealSheaf A I f) M n U
  have h0 : (completionProjection X (baseIdealSheaf A I f) M n).val.app (op U.1) x = 0 :=
    (bijective_iso_app (εApp B e M ε n) U.1).1 (hx.trans (map_zero _).symm)
  have h1 : x ∈ LinearMap.ker ((completionProjection X (baseIdealSheaf A I f) M n).val.app
      (op U.1)).hom := h0
  exact hk ▸ h1

end AlgebraicGeometry.AdicFiniteAlgebra

namespace AlgebraicGeometry

open AdicFiniteAlgebra

/-- **Grothendieck existence for finite sheaves of algebras, from Grothendieck existence for
coherent modules.** For `f : X ⟶ Spec A` proper over a Noetherian ring, if completion along
`I 𝒪_X` is an equivalence `Coh(𝒪_X) ⥤ Coh(X, I 𝒪_X)` (Stacks 088C), then every compatible system
of finite quasi-coherent algebras on the adic thickenings `Xₙ` is the system of pullbacks of a
single finite quasi-coherent algebra on `X`, whose relative spectrum is proper over `Spec A`.

The proof is that of Stacks 09ZT: the pushforwards to `X` of the algebras form a coherent adic
system, which is the completion of a coherent module `F`; full faithfulness of completion,
applied to `F ⊗ F`, `(F ⊗ F) ⊗ F` and `𝒪_X ⊗ F`, lifts the multiplications to a commutative
algebra structure on `F`, and the identification of its pullbacks with the given algebras is
read on sections over affine opens. -/
public theorem adicFiniteAlgebraAlgebraization_of_isEquivalence
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (hEquiv : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      (completionFunctor X (baseIdealSheaf A I f)).IsEquivalence) :
    AdicFiniteAlgebraAlgebraization A I f := by
  intro B hqc hBfin hBtrans _
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : (completionFunctor X (baseIdealSheaf A I f)).IsEquivalence := hEquiv
  have := hqc
  have e : ∀ n, (algebraPullback (adicBaseChangeSucc A I f n)).obj (B (n + 1)) ≅ B n :=
    fun n => (hBtrans n).some
  have hfin : ∀ n, IsFinite (sysy B n) := fun n => isFinite_relativeSpecToBase (B n) (hBfin n)
  obtain ⟨M, ⟨ε⟩⟩ := Functor.EssSurj.mem_essImage
    (F := completionFunctor X (baseIdealSheaf A I f)) (sysAdic B e)
  let L := liftData B e M ε
  have hC := L.isQuasicoherent_algebra
  refine ⟨L.algebra, hC, L.isFinite_algebra, ?_, fun n => ?_⟩
  · have : IsFinite (relativeSpecToBase L.algebra) :=
      isFinite_relativeSpecToBase L.algebra L.isFinite_algebra
    infer_instance
  · obtain ⟨E⟩ := nonempty_algebraPullback_iso_of_sections
      (pullback.fst f (adicThickeningι A I n)) L.algebra (sysy B n) (L.c n)
      (fun U => L.c_surjective n (op U.1) (κ_surjective B e M ε n U))
      (fun U => by
        rw [ker_adicBaseChange_fst, Scheme.IdealSheafData.ideal_pow]
        exact L.ker_c_le n U.1 _ (κ_ker B e M ε n U))
    exact ⟨E ≪≫ pushforwardAlgebraIso (B n)⟩

/-- **Grothendieck existence for finite sheaves of algebras over a proper base.** Let `A` be a
Noetherian ring complete with respect to an ideal `I` and `f : X ⟶ Spec A` proper. Every
compatible system of finite quasi-coherent algebras on the adic thickenings
`Xₙ = X ×_{Spec A} Spec(A / I^(n+1))` is the system of pullbacks of a single finite
quasi-coherent algebra on `X`, whose relative spectrum is proper over `Spec A`.

This is `adicFiniteAlgebraAlgebraization_of_isEquivalence` with Grothendieck's existence theorem
for coherent modules, Stacks 088C
(`Stacks.Algebraization.isEquivalence_completionFunctor_of_isProper`), as its input. -/
public theorem adicFiniteAlgebraAlgebraization_of_isProper
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] :
    AdicFiniteAlgebraAlgebraization A I f :=
  adicFiniteAlgebraAlgebraization_of_isEquivalence A I f
    (isEquivalence_completionFunctor_of_isProper A I f)

end AlgebraicGeometry


end
