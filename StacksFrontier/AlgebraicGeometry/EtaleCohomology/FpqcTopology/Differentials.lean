module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.DedekindDomain.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.Surjective
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.DifferentialSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FpqcTopology.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Relative differentials do not descend along fpqc coverings

The presheaf sending a scheme over `S` to the global sections of its sheaf of relative
differentials is a Zariski sheaf, but it is not a sheaf for the fpqc topology. The failure is
witnessed over the prime field `𝔽ₚ` by the Frobenius endomorphism of the affine line: the
morphism `Spec 𝔽ₚ[v] ⟶ Spec 𝔽ₚ[u]` sending `u` to `v ^ p` is a singleton fpqc covering, yet the
induced map on global differentials kills the generator `du`, because `d(v ^ p) = p v ^ (p - 1) dv`
vanishes.

## Main results

* `AlgebraicGeometry.relativeDifferentialsPresheaf_not_isSheaf_fpqc` is the failure of the fpqc
  sheaf condition for the presheaf of relative differentials over `Spec (ZMod p)`.

## Implementation notes

The counterexample is exhibited, not merely asserted: the proof produces the nonzero global
differential `du` of `Spec 𝔽ₚ[u]` over `Spec 𝔽ₚ`, shows that the Frobenius covering sends it to
zero, and so contradicts even the separatedness half of the sheaf condition. Nonvanishing of
`du` is checked by transporting the derivative of the polynomial ring along the canonical
identification of the sections of the structure sheaf of an affine scheme with its ring.

## References

* [Stacks Project, Tag 03O2](https://stacks.math.columbia.edu/tag/03O2)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The derivative of the polynomial ring in one variable, transported along ring equivalences
identifying an algebra with a polynomial algebra in one variable over its base. -/
private noncomputable def polynomialDerivation {A B k : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [CommRing k] [Nontrivial k] (eA : A ≃+* k) (eB : B ≃+* Polynomial k)
    (hbase : ∀ r : A, eB (algebraMap A B r) = algebraMap k (Polynomial k) (eA r)) :
    Derivation A B B where
  toLinearMap :=
    { toFun := fun x => eB.symm (Polynomial.derivative' (eB x))
      map_add' := by intro x y; simp
      map_smul' := by
        intro r x
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, Algebra.smul_def]
        apply eB.injective
        simp only [eB.apply_symm_apply]
        rw [map_mul, hbase r, Polynomial.derivative'.leibniz,
          Polynomial.derivative'.map_algebraMap, map_mul, hbase r, eB.apply_symm_apply]
        ring }
  map_one_eq_zero' := by simp
  leibniz' := by
    intro x y
    apply eB.injective
    calc
      eB (eB.symm (Polynomial.derivative' (eB (x * y)))) =
          Polynomial.derivative' (eB x * eB y) := by
        rw [eB.apply_symm_apply, map_mul]
      _ = eB x * Polynomial.derivative' (eB y) + eB y * Polynomial.derivative' (eB x) :=
        Polynomial.derivative'.leibniz _ _
      _ = eB (x • eB.symm (Polynomial.derivative' (eB y)) +
            y • eB.symm (Polynomial.derivative' (eB x))) := by
        simp [smul_eq_mul]

/-- In an algebra identified with a polynomial algebra in one variable over its base, the
universal differential of the variable is nonzero. -/
private theorem kaehlerDifferential_D_ne_zero {A B k : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [CommRing k] [Nontrivial k] (eA : A ≃+* k) (eB : B ≃+* Polynomial k)
    (hbase : ∀ r : A, eB (algebraMap A B r) = algebraMap k (Polynomial k) (eA r)) :
    KaehlerDifferential.D A B (eB.symm Polynomial.X) ≠ 0 := by
  intro hzero
  have h := congrArg (polynomialDerivation eA eB hbase).liftKaehlerDifferential hzero
  rw [map_zero, Derivation.liftKaehlerDifferential_comp_D] at h
  have hone : (1 : B) = 0 := by simpa [polynomialDerivation] using h
  exact one_ne_zero (α := Polynomial k) (by rw [← map_one eB, hone, map_zero])

/-- The Frobenius endomorphism of a principal ideal domain of prime characteristic `p` is
faithfully flat: it is injective, so the domain is torsion-free over itself along it, and it
induces the identity on the prime spectrum. -/
private theorem faithfullyFlat_frobenius (R : Type u) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (p : ℕ) [ExpChar R p] (hp : 0 < p) :
    (frobenius R p).FaithfullyFlat := by
  let : Algebra R R := RingHom.toAlgebra (frobenius R p)
  let : Module R R := Algebra.toModule
  let : IsDedekindDomain R := IsPrincipalIdealRing.isDedekindDomain R
  let : Module.IsTorsionFree R R :=
    { isSMulRegular := by
        intro r hr
        have hr0 : r ≠ 0 := by
          intro hrz
          exact zero_ne_one (α := R) (hr.left (by simp [hrz]))
        have hfr0 : frobenius R p r ≠ 0 := by
          intro hz
          exact hr0 ((frobenius_inj R p) (by simpa using hz))
        change Function.Injective (fun x : R => (algebraMap R R r) * x)
        exact fun _ _ hxy => mul_left_cancel₀ hfr0 hxy }
  let : Module.Flat R R := Module.Flat.instOfIsDedekindDomainOfIsTorsionFree
  refine (RingHom.faithfullyFlat_algebraMap_iff (R := R) (S := R)).2
    (Module.FaithfullyFlat.of_comap_surjective fun q => ⟨q, PrimeSpectrum.ext ?_⟩)
  ext x
  change frobenius R p x ∈ q.asIdeal ↔ x ∈ q.asIdeal
  rw [frobenius_def]
  exact q.isPrime.pow_mem_iff_mem p hp

/-- A section of a sheaf of abelian groups which restricts to zero along a morphism generating a
covering sieve is zero. -/
private theorem _root_.CategoryTheory.Presheaf.IsSheaf.eq_zero_of_map_eq_zero {C : Type*}
    [Category C] {J : GrothendieckTopology C} {F : Cᵒᵖ ⥤ AddCommGrpCat.{0}}
    (hF : Presheaf.IsSheaf J F) {X Y : C} {g : Y ⟶ X}
    (hg : Sieve.generate (Presieve.singleton g) ∈ J X)
    {t : F.obj (Opposite.op X)} (ht : F.map g.op t = 0) : t = 0 := by
  let A := AddCommGrpCat.of ℤ
  have hT : Presieve.IsSheafFor (F ⋙ coyoneda.obj (Opposite.op A)) (Presieve.singleton g) :=
    (hF A).isSheafFor _ hg
  let α : A ⟶ F.obj (Opposite.op X) := AddCommGrpCat.ofHom
    { toFun := fun n => n • t
      map_zero' := zero_smul ℤ t
      map_add' := fun m n => add_smul m n t }
  have hα : α = 0 := by
    refine hT.isSeparatedFor.ext (t₁ := α) (t₂ := (0 : A ⟶ F.obj (Opposite.op X))) ?_
    rintro _ _ ⟨⟩
    change ((coyoneda.obj (Opposite.op A)).map (F.map g.op)) α =
      ((coyoneda.obj (Opposite.op A)).map (F.map g.op)) (0 : A ⟶ F.obj (Opposite.op X))
    dsimp [coyoneda, yoneda]
    ext
    simp [α, ht]
  simpa [α] using congrArg (fun q : A ⟶ F.obj (Opposite.op X) => q.hom 1) hα

/-- The map on global sections of relative differentials induced by a morphism `g` over `S` kills
the universal differential of a global function `a` whenever it kills that of the pullback of
`a` along `g`. -/
private theorem differentialSectionsMap_d_eq_zero {S : Scheme.{u}} {X Y : Over S} (g : X ⟶ Y)
    {a : Γ(Y.left, ⊤)}
    (ha : (Scheme.Hom.universalRelativeDerivation X.hom).d (g.left.appTop.hom a) = 0) :
    differentialSectionsMap g ((Scheme.Hom.universalRelativeDerivation Y.hom).d a) = 0 := by
  have hcomm : g.left ≫ Y.hom = X.hom ≫ 𝟙 S := by simp [Over.w g]
  have hzero := ((Scheme.Hom.isRelativeDifferentialsMap_iff_eq g.left Y.hom X.hom (𝟙 S) hcomm
    _).mpr rfl ⊤ a).trans ha
  let N : Y.left.Modules := Scheme.Hom.relativeDifferentials Y.hom
  let M : X.left.Modules := Scheme.Hom.relativeDifferentials X.hom
  let adj := Scheme.Modules.pullbackPushforwardAdjunction g.left
  change (((adj.homEquiv N M
    (Scheme.Hom.relativeDifferentialsMap g.left Y.hom X.hom (𝟙 S) hcomm)).val.app
      (Opposite.op ⊤)).hom ((Scheme.Hom.universalRelativeDerivation Y.hom).d a)) = 0 at hzero
  unfold differentialSectionsMap differentialsSectionMorphism
  change (M.presheaf.map (eqToHom (by simp)).op).hom
    (((adj.homEquiv N M _).val.app (Opposite.op ⊤)).hom
      ((Scheme.Hom.universalRelativeDerivation Y.hom).d a)) = 0
  rw [hzero]
  exact (M.presheaf.map (eqToHom (by simp)).op).hom.map_zero

/-- The relative differential `du` of the affine line `Spec 𝔽ₚ[u]` over `Spec 𝔽ₚ` is nonzero. -/
private theorem universalRelativeDerivation_d_X_ne_zero (p : ℕ) [Fact p.Prime] :
    (Scheme.Hom.universalRelativeDerivation
      (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (Polynomial (ZMod p)))))).d
        ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial (ZMod p)))).commRingCatIsoToRingEquiv.symm
          Polynomial.X) ≠ 0 := by
  let P := Polynomial (ZMod p)
  let S : Scheme := Spec (.of (ZMod p))
  let X : Scheme := Spec (.of P)
  let b : X ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) P))
  have hUV : (⊤ : X.Opens) ≤ b ⁻¹ᵁ (⊤ : S.Opens) := by simp
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := (b.appLE ⊤ ⊤ hUV).hom.toAlgebra
  obtain ⟨e, he⟩ :=
    Stacks.AlgebraicGeometry.AffineDifferentialsIso.existsUnique_affineDifferentialsIso b
      (isAffineOpen_top X) hUV (isAffineOpen_top S)
  let eS : Γ(S, ⊤) ≃+* ZMod p :=
    (Scheme.ΓSpecIso (CommRingCat.of (ZMod p))).commRingCatIsoToRingEquiv
  let eX : Γ(X, ⊤) ≃+* P := (Scheme.ΓSpecIso (CommRingCat.of P)).commRingCatIsoToRingEquiv
  let a : Γ(X, ⊤) := eX.symm Polynomial.X
  have halg (r : Γ(S, ⊤)) :
      eX (algebraMap Γ(S, ⊤) Γ(X, ⊤) r) = algebraMap (ZMod p) P (eS r) := by
    change (Scheme.ΓSpecIso (CommRingCat.of P)).hom.hom (b.appTop.hom r) =
      (algebraMap (ZMod p) P) ((Scheme.ΓSpecIso (CommRingCat.of (ZMod p))).hom.hom r)
    exact congrArg (fun f : CommRingCat.Hom _ _ => f.hom r)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap (ZMod p) P)))
  have hΩd : CommRingCat.KaehlerDifferential.d (f := b.appLE ⊤ ⊤ hUV) a ≠ 0 :=
    kaehlerDifferential_D_ne_zero eS eX halg
  intro hz
  refine hΩd ?_
  rw [← he.1 a, show (Scheme.Hom.universalRelativeDerivation b).d a = 0 from hz, map_zero]
  rfl

/-- The Frobenius endomorphism of the affine line `Spec 𝔽ₚ[u]` over `Spec 𝔽ₚ` kills the relative
differential `du`, since it sends `u` to `u ^ p` and `d(u ^ p) = p u ^ (p - 1) du = 0`. -/
private theorem universalRelativeDerivation_d_frobenius_X (p : ℕ) [Fact p.Prime] :
    (Scheme.Hom.universalRelativeDerivation
      (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (Polynomial (ZMod p)))))).d
        ((Spec.map (CommRingCat.ofHom (frobenius (Polynomial (ZMod p)) p))).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial (ZMod p)))).commRingCatIsoToRingEquiv.symm
            Polynomial.X)) = 0 := by
  let P := Polynomial (ZMod p)
  let S : Scheme := Spec (.of (ZMod p))
  let X : Scheme := Spec (.of P)
  let φ : X ⟶ X := Spec.map (CommRingCat.ofHom (frobenius P p))
  let b : X ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) P))
  have hUV : (⊤ : X.Opens) ≤ b ⁻¹ᵁ (⊤ : S.Opens) := by simp
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := (b.appLE ⊤ ⊤ hUV).hom.toAlgebra
  obtain ⟨e, he⟩ :=
    Stacks.AlgebraicGeometry.AffineDifferentialsIso.existsUnique_affineDifferentialsIso b
      (isAffineOpen_top X) hUV (isAffineOpen_top S)
  let eX : Γ(X, ⊤) ≃+* P := (Scheme.ΓSpecIso (CommRingCat.of P)).commRingCatIsoToRingEquiv
  let a : Γ(X, ⊤) := eX.symm Polynomial.X
  change (Scheme.Hom.universalRelativeDerivation b).d ((φ.appTop).hom a) = 0
  have hphi : (φ.appTop).hom a = a ^ p := by
    apply eX.injective
    rw [show eX ((φ.appTop).hom a) = (frobenius P p) (eX a) from
      congrArg (fun f : CommRingCat.Hom _ _ => f.hom a)
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (frobenius P p))), map_pow, frobenius_def]
  have hp : (p : Γ(X, ⊤)) = 0 := eX.injective (by simp)
  have hΩphi :
      CommRingCat.KaehlerDifferential.d (f := b.appLE ⊤ ⊤ hUV) ((φ.appTop).hom a) = 0 := by
    rw [hphi]
    change KaehlerDifferential.D Γ(S, ⊤) Γ(X, ⊤) (a ^ p) = 0
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul (Γ(X, ⊤)), hp, zero_smul]
  have hleft : Function.LeftInverse e.inv.hom e.hom.hom :=
    fun z => congrArg (fun f => f z) e.hom_inv_id
  exact hleft.injective (by rw [he.1, map_zero]; exact hΩphi)

/-- **Stacks Project, Tag 03O2.** The presheaf on schemes over `Spec (ZMod p)` sending a scheme
to the global sections of its sheaf of relative differentials is not a sheaf for the fpqc
topology. -/
@[stacks 03O2 "not_fpqc_sheaf"]
theorem relativeDifferentialsPresheaf_not_isSheaf_fpqc (p : ℕ) [Fact p.Prime] :
    ¬ Presheaf.IsSheaf (Scheme.fpqcTopology.over (Spec (.of (ZMod p))))
      (relativeDifferentialsPresheaf (Spec (.of (ZMod p)))).functor := by
  let P := Polynomial (ZMod p)
  let S : Scheme := Spec (.of (ZMod p))
  let X : Scheme := Spec (.of P)
  let φ : X ⟶ X := Spec.map (CommRingCat.ofHom (frobenius P p))
  let b : X ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) P))
  have hbase : φ ≫ b = b := by
    simpa only [CommRingCat.ofHom_comp, Spec.map_comp, φ, b] using
      congrArg Spec.map (congrArg CommRingCat.ofHom (RingHom.ext_zmod
        ((frobenius P p).comp (algebraMap (ZMod p) P)) (algebraMap (ZMod p) P)))
  let Xover : Over S := Over.mk b
  let g : Xover ⟶ Xover := Over.homMk φ hbase
  have hcover : Presieve.singleton φ ∈ Scheme.fpqcPrecoverage X :=
    (singleton_specMap_mem_fpqcPrecoverage_iff_faithfullyFlat (frobenius P p)).2
      (faithfullyFlat_frobenius P p (Fact.out : p.Prime).pos)
  have hC : Sieve.ofArrows (X := Xover) (I := PUnit.{1}) (fun _ => Xover) (fun _ => g) ∈
      (Scheme.fpqcTopology.over S) Xover := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    simpa [Xover, g, φ, Sieve.ofArrows, Presieve.ofArrows_pUnit] using
      Precoverage.generate_mem_toGrothendieck hcover
  have hg : Sieve.generate (Presieve.singleton g) ∈ (Scheme.fpqcTopology.over S) Xover := by
    simpa [Sieve.ofArrows, Presieve.ofArrows_pUnit] using hC
  let F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{0} := (relativeDifferentialsPresheaf S).functor
  intro hF
  let i := (relativeDifferentialsPresheaf S).objIso (Opposite.op Xover)
  let tΓ : Γ(Scheme.Hom.relativeDifferentials b, ⊤) :=
    (Scheme.Hom.universalRelativeDerivation b).d
      ((Scheme.ΓSpecIso (CommRingCat.of P)).commRingCatIsoToRingEquiv.symm Polynomial.X)
  have hdiff : differentialSectionsMap g tΓ = 0 :=
    differentialSectionsMap_d_eq_zero g (universalRelativeDerivation_d_frobenius_X p)
  have hEq : i.hom (F.map g.op (i.inv tΓ)) = differentialSectionsMap g tΓ := by
    simpa [i, Opposite.unop_op] using
      congrArg (fun f => f tΓ) ((relativeDifferentialsPresheaf S).map_objIso g.op)
  have hEq' : i.hom (F.map g.op (i.inv tΓ)) = 0 := hEq.trans hdiff
  have hmapzero : F.map g.op (i.inv tΓ) = 0 := by simpa [i] using congrArg i.inv.hom hEq'
  have htΓ : tΓ = 0 := by
    simpa [i] using congrArg i.hom.hom (hF.eq_zero_of_map_eq_zero hg hmapzero)
  exact universalRelativeDerivation_d_X_ne_zero p htΓ

end AlgebraicGeometry

end
