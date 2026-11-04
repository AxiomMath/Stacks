module

public import Mathlib.RingTheory.Ideal.GoingUp
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.LocalizedFlatness
public import StacksFrontier.RingTheory.Flat.HenselianFlattening

/-!
# A finite change of the local algebra does not change the flat-at-a-point functor

In the situation of Stacks Tag 05MK, let `B → C` be a finite local homomorphism of local
`A`-algebras and let `N` be a `C`-module which is isomorphic to `M` as a `B`-module. Then the
functor `F_lf` attached to the pair `(C, N)` is the functor attached to `(B, M)`.

The reason is that `m_C` is the radical of `m_B C`, so the closed fibre of `Spec C' → Spec A'`
is the preimage of the closed fibre of `Spec B' → Spec A'` for every base change `A'`; and over
a point of the latter, flatness of `M'` is flatness of `N'` at every prime of `C'` above it,
because `B' → C'` is finite, so those primes are exactly the maximal ideals of the localization.

## Main results

* `Module.FlatAtPointSituation.flatAtPointFunctor_eq_of_finite`: **Stacks Tag 05P4**.

## Implementation notes

The second local algebra is presented by an algebra homomorphism `f : B →ₐ[A] C` over the common
base, and the module isomorphism is recorded with the `B`-action on `N` obtained by restricting
scalars along `f`. The base-changed comparison of modules is
`Module.FlatAtPointSituation.tensorBaseChangeEquiv`, built from the two cancellations of base
change over `A` and transported to a `B ⊗[A] A'`-linear equivalence.

## References

* [Stacks Project, Tag 05P4](https://stacks.math.columbia.edu/tag/05P4)
-/

@[expose] public section

open CategoryTheory IsLocalRing
open scoped TensorProduct

universe u v w x y z

namespace Module.FlatAtPointSituation

/-- Along an integral local homomorphism of local rings the maximal ideal of the target is the
radical of the extension of the maximal ideal of the source. -/
private theorem radical_map_maximalIdeal_of_isIntegral {B C : Type*} [CommRing B] [CommRing C]
    [IsLocalRing B] [IsLocalRing C] (f : B →+* C) [IsLocalHom f] (hf : f.IsIntegral) :
    (Ideal.map f (maximalIdeal B)).radical = maximalIdeal C := by
  refine le_antisymm ((maximalIdeal.isMaximal C).isPrime.radical_le_iff.mpr
    (IsLocalRing.map_maximalIdeal_le f)) ?_
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun Q hQ ↦ ?_
  have _ : Q.IsPrime := hQ.2
  have heq : Ideal.comap f Q = maximalIdeal B :=
    le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.comap_isPrime f Q).ne_top)
      (Ideal.map_le_iff_le_comap.mp hQ.1)
  have hm : (Ideal.comap f Q).IsMaximal := heq.symm ▸ maximalIdeal.isMaximal B
  exact (IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' f hf Q hm)).ge

/-- A prime of the target of an integral local homomorphism of local rings contains the maximal
ideal exactly when its contraction does. -/
private theorem maximalIdeal_le_iff_le_comap {B C : Type*} [CommRing B] [CommRing C]
    [IsLocalRing B] [IsLocalRing C] (f : B →+* C) [IsLocalHom f] (hf : f.IsIntegral) (Q : Ideal C)
    [Q.IsPrime] : maximalIdeal C ≤ Q ↔ maximalIdeal B ≤ Q.comap f := by
  refine ⟨fun h ↦ (Ideal.map_le_iff_le_comap.mp (IsLocalRing.map_maximalIdeal_le f)).trans
    (Ideal.comap_mono h), fun h ↦ ?_⟩
  rw [← radical_map_maximalIdeal_of_isIntegral f hf]
  exact ‹Q.IsPrime›.radical_le_iff.mpr (Ideal.map_le_iff_le_comap.mpr h)

/-- In a commuting square of ring maps whose left-hand side is integral and local, a prime of
the lower right corner contains the closed-fibre ideal exactly when its contraction to the
lower left corner does. -/
private theorem closedFiber_le_iff_le_comap {B C R D E : Type*} [CommRing B] [CommRing C]
    [CommRing R] [CommRing D] [CommRing E] [IsLocalRing B] [IsLocalRing C] [IsLocalRing R]
    (f : B →+* C) [IsLocalHom f] (hf : f.IsIntegral) (bD : B →+* D) (cE : C →+* E) (rD : R →+* D)
    (rE : R →+* E) (g : D →+* E) (hB : g.comp bD = cE.comp f) (hR : g.comp rD = rE) (q : Ideal E)
    [q.IsPrime] :
    Ideal.map rE (maximalIdeal R) ⊔ Ideal.map cE (maximalIdeal C) ≤ q ↔
      Ideal.map rD (maximalIdeal R) ⊔ Ideal.map bD (maximalIdeal B) ≤ q.comap g := by
  have _ : (q.comap cE).IsPrime := Ideal.comap_isPrime _ q
  simp only [sup_le_iff, Ideal.map_le_iff_le_comap]
  refine and_congr ?_ ?_
  · rw [show (q.comap g).comap rD = q.comap rE by rw [Ideal.comap_comap, hR]]
  · rw [show (q.comap g).comap bD = (q.comap cE).comap f by
      rw [Ideal.comap_comap, Ideal.comap_comap, hB]]
    exact maximalIdeal_le_iff_le_comap f hf (q.comap cE)

/-- Base change along `R` of a map of `A`-algebras commutes with the maps from `R`. -/
private theorem map_id_comp_algebraMap_rightAlgebra {A B C R : Type*} [CommRing A] [CommRing B]
    [CommRing C] [CommRing R] [Algebra A B] [Algebra A C] [Algebra A R] (f : B →ₐ[A] C) :
    letI : Algebra R (B ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra R (C ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
    (Algebra.TensorProduct.map f (AlgHom.id A R)).toRingHom.comp (algebraMap R (B ⊗[A] R)) =
      algebraMap R (C ⊗[A] R) := by
  ext r
  show Algebra.TensorProduct.map f (AlgHom.id A R) ((1 : B) ⊗ₜ[A] r) = (1 : C) ⊗ₜ[A] r
  simp

/-- Base change along `R` of a map `f` of `A`-algebras commutes with the maps from the source and
target of `f`. -/
private theorem map_id_comp_algebraMap {A B C R : Type*} [CommRing A] [CommRing B] [CommRing C]
    [CommRing R] [Algebra A B] [Algebra A C] [Algebra A R] (f : B →ₐ[A] C) :
    (Algebra.TensorProduct.map f (AlgHom.id A R)).toRingHom.comp (algebraMap B (B ⊗[A] R)) =
      (algebraMap C (C ⊗[A] R)).comp f.toRingHom := by
  ext b
  show Algebra.TensorProduct.map f (AlgHom.id A R) (b ⊗ₜ[A] (1 : R)) = f b ⊗ₜ[A] (1 : R)
  simp

/-- For an integral algebra `D → E` and a module `N` over `E`, flatness over the base of the
localization of `N` at a prime `p` of `D` is the flatness of its localizations at the primes of
`E` over `p`: those primes are the maximal ideals of the localization of `E` at `p`. -/
theorem flat_localizedModule_atPrime_iff_forall_primesOver {R B C N : Type*} [CommRing R]
    [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]
    [Algebra.IsIntegral B C] [AddCommGroup N] [Module R N] [Module B N] [Module C N]
    [IsScalarTower R B N] [IsScalarTower B C N] [IsScalarTower R C N] (p : Ideal B) [p.IsPrime] :
    Module.Flat R (LocalizedModule.AtPrime p N) ↔
      ∀ (q : Ideal C) [q.IsPrime], q.comap (algebraMap B C) = p →
        Module.Flat R (LocalizedModule.AtPrime q N) := by
  let T := Algebra.algebraMapSubmonoid C p.primeCompl
  let Cp := Localization T
  let Bp := Localization.AtPrime p
  have _ : Algebra.IsIntegral Bp Cp := ⟨isIntegral_localization⟩
  let L := LocalizedModule T N
  let _ : Module B L :=
    OreLocalization.instModuleOfIsScalarTower (R := C) (S := T) (X := N) (R₀ := B)
  let _ : Module R L :=
    OreLocalization.instModuleOfIsScalarTower (R := C) (S := T) (X := N) (R₀ := R)
  have _ : LinearMap.CompatibleSMul N L B C := LinearMap.IsScalarTower.compatibleSMul
  have _ : LinearMap.CompatibleSMul (LocalizedModule.AtPrime p N) L R B :=
    LinearMap.IsScalarTower.compatibleSMul
  have e : LocalizedModule.AtPrime p N ≃ₗ[R] L :=
    have _ : IsLocalizedModule p.primeCompl
        ((LocalizedModule.mkLinearMap T N).restrictScalars B) :=
      IsLocalizedModule.restrictScalars p.primeCompl _
    (IsLocalizedModule.linearEquiv p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl N)
      ((LocalizedModule.mkLinearMap T N).restrictScalars B)).restrictScalars R
  have flatQ (Q : Ideal Cp) [Q.IsPrime] :
      Module.Flat R (LocalizedModule.AtPrime Q L) ↔
        Module.Flat R (LocalizedModule.AtPrime (Q.comap (algebraMap C Cp)) N) := by
    let eQ := IsLocalizedModule.mapEquiv Q.primeCompl
      (LocalizedModule.mkLinearMap Q.primeCompl L)
      (LocalizedModule.mkLinearMap Q.primeCompl (Cp ⊗[C] N)) (Localization.AtPrime Q)
      (LocalizedModule.equivTensorProduct T N)
    exact (Module.Flat.equiv_iff (eQ.restrictScalars R)).trans
      (Module.flat_localizedModule_atPrime_comap_iff (R := R) T Q).symm
  refine ⟨fun h q _ hqp ↦ ?_, fun h ↦ ?_⟩
  · have _ : q.LiesOver p := ⟨hqp.symm⟩
    let Q : Ideal Cp := q.map (algebraMap C Cp)
    have _ : Q.IsPrime := IsLocalization.AtPrime.isPrime_map_of_liesOver C p Cp q
    have hqback : Q.comap (algebraMap C Cp) = q :=
      IsLocalization.under_map_of_isPrime_disjoint T Cp ‹q.IsPrime›
        (Ideal.disjoint_primeCompl_of_liesOver q p)
    have _ : Module.Flat R L := (Module.Flat.equiv_iff e).mp h
    have hQflat := (flatQ Q).mp
      (Module.Flat.localizedModule_of_isScalarTower (R := R) (A := Cp) (M := L) Q.primeCompl)
    change Module.Flat R (LocalizedModule (Q.comap (algebraMap C Cp)).primeCompl N) at hQflat
    show Module.Flat R (LocalizedModule q.primeCompl N)
    rwa [show (Q.comap (algebraMap C Cp)).primeCompl = q.primeCompl by
      ext; simp [Ideal.mem_primeCompl_iff, hqback]] at hQflat
  · refine (Module.Flat.equiv_iff e).mpr
      ((Module.flat_iff_forall_flat_localizedModule_isMaximal (R := R) (A := Cp)
        (M := L)).mpr fun Q hQ ↦ ?_)
    have _ : Q.IsPrime := hQ.isPrime
    have _ : Q.LiesOver (maximalIdeal Bp) :=
      (IsLocalization.AtPrime.mem_primesOver_of_isPrime Bp Cp (Q := Q)).2
    have _ : (Q.comap (algebraMap C Cp)).IsPrime := Ideal.comap_isPrime _ Q
    exact (flatQ Q).mpr (h (Q.comap (algebraMap C Cp))
      (IsLocalization.AtPrime.liesOver_comap_of_liesOver p Bp Q).over.symm)

/-- The base change to `R` of a module over `B` compared with the base change to `R` of an
isomorphic module over a `B`-algebra `C`, as an equivalence linear over `B ⊗[A] R`. -/
noncomputable def tensorBaseChangeEquiv {A B C R M N : Type*} [CommRing A] [CommRing B]
    [CommRing C] [CommRing R] [Algebra A B] [Algebra A C] [Algebra A R] (f : B →ₐ[A] C)
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module C N]
    (e : letI : Module B N := Module.compHom N f.toRingHom
      M ≃ₗ[B] N) :
    let D := B ⊗[A] R
    let E := C ⊗[A] R
    letI : Semiring D := Algebra.TensorProduct.instCommSemiring.toSemiring
    letI : Semiring E := Algebra.TensorProduct.instCommSemiring.toSemiring
    letI : Algebra R D := Algebra.TensorProduct.rightAlgebra
    letI : Algebra R E := Algebra.TensorProduct.rightAlgebra
    let g : D →ₐ[A] E := Algebra.TensorProduct.map f (AlgHom.id A R)
    letI : Algebra D E := g.toRingHom.toAlgebra
    letI : Module D (E ⊗[C] N) := Module.compHom _ g.toRingHom
    D ⊗[B] M ≃ₗ[D] E ⊗[C] N := by
  letI : Algebra B C := f.toRingHom.toAlgebra
  letI : Module B N := Module.compHom N f.toRingHom
  have _ : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun a ↦ (f.commutes a).symm
  letI : Module A M := Module.compHom M (algebraMap A B)
  letI : Module A N := Module.compHom N (algebraMap A C)
  have _ : IsScalarTower A B M := IsScalarTower.of_compHom A B M
  have _ : IsScalarTower A C N := IsScalarTower.of_compHom A C N
  have _ : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul fun a n ↦ by
    change f (algebraMap A B a) • n = algebraMap A C a • n
    rw [f.commutes]
  let D := B ⊗[A] R
  let E := C ⊗[A] R
  letI : Algebra R D := Algebra.TensorProduct.rightAlgebra
  letI : Algebra R E := Algebra.TensorProduct.rightAlgebra
  letI : Algebra C E := Algebra.TensorProduct.leftAlgebra
  let g : D →ₐ[A] E := Algebra.TensorProduct.map f (AlgHom.id A R)
  letI : Algebra D E := g.toRingHom.toAlgebra
  have _ : IsScalarTower A R D := inferInstance
  have _ : IsScalarTower A R E := inferInstance
  let eM : D ⊗[B] M ≃ₗ[R] R ⊗[A] M := Algebra.IsPushout.cancelBaseChange A R B D M
  let eN : E ⊗[C] N ≃ₗ[R] R ⊗[A] N := Algebra.IsPushout.cancelBaseChange A R C E N
  let eMid : R ⊗[A] M ≃ₗ[R] R ⊗[A] N :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R R) (e.restrictScalars A)
  let eR : D ⊗[B] M ≃ₗ[R] E ⊗[C] N := eM.trans (eMid.trans eN.symm)
  have _ : IsScalarTower B D E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have _ : IsScalarTower B E (E ⊗[C] N) := inferInstance
  have _ : IsScalarTower C E (E ⊗[C] N) := inferInstance
  let k : M →ₗ[B] E ⊗[C] N :=
    { toFun := fun m ↦ (1 : E) ⊗ₜ[C] e m
      map_add' := fun m n ↦ by simp [map_add, TensorProduct.tmul_add]
      map_smul' := by
        intro b m
        rw [e.map_smul]
        change (1 : E) ⊗ₜ[C] (f b • e m) = b • ((1 : E) ⊗ₜ[C] e m)
        rw [← IsScalarTower.algebraMap_smul (R := B) (A := E) b ((1 : E) ⊗ₜ[C] e m)]
        simp only [TensorProduct.tmul_smul]
        change f b • ((1 : E) ⊗ₜ[C] e m) = (algebraMap B E b) • ((1 : E) ⊗ₜ[C] e m)
        rw [show algebraMap B E b = algebraMap C E (f b) from rfl]
        exact (IsScalarTower.algebraMap_smul (R := C) (A := E) (f b)
          ((1 : E) ⊗ₜ[C] e m)).symm }
  let l : D ⊗[B] M →ₗ[D] E ⊗[C] N := k.liftBaseChange D
  have hl : (l : D ⊗[B] M → E ⊗[C] N) = eR := by
    funext z
    obtain ⟨t, rfl⟩ := eM.symm.surjective z
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add t u ht hu => simpa only [map_add] using congrArg₂ (· + ·) ht hu
    | tmul r m =>
      simp only [eR, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
      change l ((Algebra.IsPushout.cancelBaseChange A R B D M).symm (r ⊗ₜ[A] m)) =
        eN.symm (eMid (r ⊗ₜ[A] m))
      rw [Algebra.IsPushout.cancelBaseChange_symm_tmul]
      simp only [eMid, TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
        LinearEquiv.restrictScalars_apply]
      rw [show eN.symm (r ⊗ₜ[A] e m) = (algebraMap R E r) ⊗ₜ[C] e m from by
        simpa only [eN] using Algebra.IsPushout.cancelBaseChange_symm_tmul A R C E N r (e m)]
      change g ((algebraMap R D) r) • ((1 : E) ⊗ₜ[C] e m) = (algebraMap R E r) ⊗ₜ[C] e m
      rw [show g ((algebraMap R D) r) = algebraMap R E r from by
        change g ((1 : B) ⊗ₜ[A] r) = (1 : C) ⊗ₜ[A] r
        rw [Algebra.TensorProduct.map_tmul f (AlgHom.id A R) (1 : B) r]
        simp]
      simp [TensorProduct.smul_tmul', Algebra.smul_def]
  exact LinearEquiv.ofBijective l (by rw [hl]; exact eR.bijective)

/-- **Stacks Project, Tag 05P4.** Replacing the local algebra of a flat-at-a-point situation by
a finite local extension, and its module by an isomorphic module over that extension, does not
change the flat-at-a-point functor. -/
@[stacks 05P4]
public theorem flatAtPointFunctor_eq_of_finite (S : FlatAtPointSituation.{u, v, w})
    {C : Type x} [CommRing C] [IsLocalRing C] [Algebra S.A C] [IsLocalHom (algebraMap S.A C)]
    {N : Type y} [AddCommGroup N] [Module C N] (f : S.B →ₐ[S.A] C)
    (hf : IsLocalHom f.toRingHom) (hfinite : f.toRingHom.Finite)
    (e : letI : Module S.B N := Module.compHom N f.toRingHom
      S.M ≃ₗ[S.B] N) :
    flatAtPointFunctor.{u, v, w, z} S =
      flatAtPointFunctor.{u, x, y, z} ({ A := S.A, B := C, M := N } :
        FlatAtPointSituation.{u, x, y}) := by
  apply CategoryTheory.Functor.ext (fun R ↦ ?_)
  simp only [flatAtPointFunctor]
  refine congrArg PLift (propext ?_)
  let D := S.B ⊗[S.A] R
  let E := C ⊗[S.A] R
  let : Algebra R D := Algebra.TensorProduct.rightAlgebra
  let : Algebra R E := Algebra.TensorProduct.rightAlgebra
  let g : D →ₐ[S.A] E := Algebra.TensorProduct.map f (AlgHom.id S.A R)
  let : Algebra D E := g.toRingHom.toAlgebra
  let : Algebra S.B C := f.toRingHom.toAlgebra
  have _ : IsScalarTower S.A S.B C := IsScalarTower.of_algebraMap_eq fun a ↦ (f.commutes a).symm
  have hR : g.toRingHom.comp (algebraMap R D) = algebraMap R E :=
    map_id_comp_algebraMap_rightAlgebra f
  have _ : IsScalarTower R D E :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (congrArg (fun φ : R →+* E ↦ φ r) hR).symm
  have _ : Algebra.IsIntegral D E :=
    ⟨(RingHom.Finite.tensorProductMap hfinite (AlgHom.Finite.id S.A R)).to_isIntegral⟩
  let : Module E (E ⊗[C] N) := TensorProduct.leftModule
  let eD : D ⊗[S.B] S.M ≃ₗ[D] E ⊗[C] N := tensorBaseChangeEquiv f e
  let : Module D (E ⊗[C] N) := Module.compHom (E ⊗[C] N) g.toRingHom
  have _ : IsScalarTower D E (E ⊗[C] N) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hB : g.toRingHom.comp (algebraMap S.B D) = (algebraMap C E).comp f.toRingHom :=
    map_id_comp_algebraMap f
  let hJ (q : Ideal E) [q.IsPrime] :=
    closedFiber_le_iff_le_comap f.toRingHom hfinite.to_isIntegral (algebraMap S.B D)
      (algebraMap C E) (algebraMap R D) (algebraMap R E) g.toRingHom hB hR q
  let : Module D (D ⊗[S.B] S.M) := TensorProduct.leftModule
  have towerE : IsScalarTower R D (E ⊗[C] N) :=
    IsScalarTower.of_algebraMap_smul fun r n ↦ by
      show g ((algebraMap R D) r) • n = (algebraMap R E r) • n
      rw [IsScalarTower.algebraMap_apply R D E r]
      rfl
  have hlocal (p : Ideal D) [p.IsPrime] :=
    @Module.flat_localizedModule_atPrime_congr R D (D ⊗[S.B] S.M) (E ⊗[C] N) _ _ _ _
      (inferInstance : Module D (D ⊗[S.B] S.M)) (inferInstance : Module R (D ⊗[S.B] S.M))
      inferInstance _ (inferInstance : Module D (E ⊗[C] N))
      (inferInstance : Module R (E ⊗[C] N)) towerE eD p inferInstance
  have hintegral (p : Ideal D) [p.IsPrime] :=
    @flat_localizedModule_atPrime_iff_forall_primesOver R D E (E ⊗[C] N) _ _ _ _ _ _ _ _ _
      (inferInstance : Module R (E ⊗[C] N)) (inferInstance : Module D (E ⊗[C] N))
      (inferInstance : Module E (E ⊗[C] N)) towerE
      (inferInstance : IsScalarTower D E (E ⊗[C] N))
      (inferInstance : IsScalarTower R E (E ⊗[C] N)) p inferInstance
  constructor <;> intro h
  · intro q hq hqcond
    have _ : q.IsPrime := hq
    exact (hintegral (q.comap g.toRingHom)).mp
      ((hlocal _).mp (h _ (Ideal.comap_isPrime g.toRingHom q) ((hJ q).mp hqcond))) q rfl
  · intro p hp hpcond
    have _ : p.IsPrime := hp
    exact (hlocal p).mpr ((hintegral p).mpr fun q hq hqp ↦
      h q hq ((hJ q).mpr (hqp ▸ hpcond)))

end Module.FlatAtPointSituation
