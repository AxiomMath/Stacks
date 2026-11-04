module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.LinearAlgebra.Matrix.Dual
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.LinearAlgebra.Matrix.DeterminantalRank
public import StacksFrontier.LinearAlgebra.Matrix.MinorIdeal
public import StacksFrontier.RingTheory.Fitting.Basic

/-!
# A nonzero map from a finitely presented module

On an affine scheme, a nonzero quasi-coherent module whose support is contained in the support
of a finitely presented module receives a nonzero map from that finitely presented module.

## Main results

* `AlgebraicGeometry.exists_nonzero_hom_of_supp_subset`: the sheaf statement, [Stacks, Tag
  0GPF].
* `Module.exists_nonzero_linearMap_of_support_subset`: its module-theoretic heart, for a
  finitely presented module over a commutative ring.

## Implementation notes

The module-theoretic statement is proved by reducing to a cyclic submodule `R ∙ x ≅ R ⧸ I` of
the target and producing a nonzero map into `R ⧸ I`.  Over `R ⧸ I` the zeroth Fitting ideal of
the source becomes an ideal with a nonzero annihilator, so the transpose of a relation matrix
of the source has a nonzero kernel vector, and that vector is the required functional.

The sheaf statement is transported along `X.isoSpec` to `Spec Γ(X, ⊤)` and then across the
equivalence between quasi-coherent modules on an affine scheme and modules over its ring of
global sections.

## References

* [Stacks Project, Lemma 56.2.1 (Tag 0GPF)](https://stacks.math.columbia.edu/tag/0GPF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

section Algebra

private theorem minorIdeal_transpose_eq {R : Type u} [CommRing R]
    {m n : ℕ} (A : Matrix (Fin n) (Fin m) R) (r : ℕ) :
    minorIdeal A.transpose r = minorIdeal A r := by
  have key : ∀ {m n : ℕ} (B : Matrix (Fin n) (Fin m) R),
      minorIdeal B.transpose r ≤ minorIdeal B r := by
    intro m n B
    rw [minorIdeal, Ideal.span_le]
    rintro x ⟨f, g, rfl⟩
    apply Ideal.subset_span
    refine ⟨g, f, ?_⟩
    rw [← Matrix.det_transpose (B.submatrix g f), Matrix.transpose_submatrix]
  exact le_antisymm (key A) (by simpa using key A.transpose)

/-- A finitely presented module whose support contains every prime containing a proper ideal
`I` admits a nonzero map to `R ⧸ I`. -/
private theorem exists_nonzero_linearMap_to_quotient
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] (I : Ideal R) (hI : I ≠ ⊤)
    (hsupp : ∀ p : PrimeSpectrum R, I ≤ p.asIdeal → p ∈ Module.support R M) :
    ∃ f : M →ₗ[R] (R ⧸ I), f ≠ 0 := by
  classical
  let S := R ⧸ I
  let q : R →+* S := Ideal.Quotient.mk I
  -- Choose a finite presentation and its relation matrix.
  obtain ⟨n, m, f, g, hf, hgf⟩ := Module.FinitePresentation.exists_fin' R M
  let A : Matrix (Fin n) (Fin m) R := LinearMap.toMatrix' g
  have hg : g = A.mulVecLin := by
    simpa [A, Matrix.toLin'_apply'] using (Matrix.toLin'_toMatrix' g).symm
  have hrange : LinearMap.range g = LinearMap.ker f := (LinearMap.exact_iff.mp hgf).symm
  have hspan : Submodule.span R (Set.range fun j : Fin m => fun i : Fin n => A i j) =
      LinearMap.ker f := by
    rw [← hrange, hg, Matrix.range_mulVecLin]
    rfl
  let eQ : ((Fin n → R) ⧸ Submodule.span R
      (Set.range fun j : Fin m => fun i : Fin n => A i j)) ≃ₗ[R] M :=
    (Submodule.quotEquivOfEq _ _ hspan).trans (f.quotKerEquivOfSurjective hf)
  have hfit : fittingIdeal (R := R) (M := M) 0 = minorIdeal A n :=
    fittingIdeal_eq_minorIdeal_of_presentation A 0 eQ
  let F : Ideal R := fittingIdeal (R := R) (M := M) 0
  have hprops := fittingIdeal_basic_properties.{u, u, u, u} (R := R) (M := M)
  rcases hprops with ⟨_, _, _, hfg, _, _, hsuppM, _⟩
  have hFfg : F.FG := by exact hfg inferInstance 0
  -- Every element of `Fitt₀(M)` is nilpotent modulo `I`.
  have hrad : F ≤ I.radical := by
    rw [Ideal.radical_eq_sInf]
    apply le_sInf
    rintro P ⟨hP, hIP⟩
    let p : PrimeSpectrum R := ⟨P, hIP⟩
    have hpM : p ∈ Module.support R M := hsupp p hP
    rw [← hsuppM] at hpM
    exact (PrimeSpectrum.mem_zeroLocus p (F : Set R)).mp hpM
  obtain ⟨k₀, hk₀⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hFfg
  have hpow : ∃ n : ℕ, F ^ n ≤ I := ⟨k₀, hk₀⟩
  let k := Nat.find hpow
  have hk : F ^ k ≤ I := Nat.find_spec hpow
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    have h1 : (1 : R) ∈ I := by
      have h := hk
      rw [hk0, pow_zero] at h
      exact h (by simp)
    exact hI (I.eq_top_iff_one.mpr h1)
  have hprev : ¬ F ^ (k - 1) ≤ I := by
    intro hprev'
    have hmin := Nat.find_min' hpow hprev'
    omega
  obtain ⟨a, haF, haI⟩ := SetLike.not_le_iff_exists.mp hprev
  have hqa : q a ∈ (Ideal.map q F).annihilator := by
    rw [Submodule.mem_annihilator]
    intro y hy
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective q q.surjective).mp hy
    show q a * q b = 0
    rw [← map_mul]
    apply (Ideal.Quotient.eq_zero_iff_mem).2
    have hab : a * b ∈ F ^ k := by
      rw [← Nat.sub_add_cancel hkpos, pow_succ]
      exact Ideal.mul_mem_mul haF hb
    exact hk hab
  have hqa_ne : q a ≠ 0 := by
    intro hzero
    exact haI ((Ideal.Quotient.eq_zero_iff_mem).mp hzero)
  let B : Matrix (Fin m) (Fin n) S := (A.map q).transpose
  let : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hI
  have hdet_of_rank (hr : Stacks.DeterminantalRank.exteriorRank B = n) :
      Stacks.DeterminantalRank.detIdeal B = Ideal.map q F := by
    calc
      Stacks.DeterminantalRank.detIdeal B =
          minorIdeal B (Stacks.DeterminantalRank.exteriorRank B) := rfl
      _ = minorIdeal B n := by rw [hr]
      _ = Ideal.map q F := by
        rw [minorIdeal_transpose_eq]
        show minorIdeal (A.map q) n = Ideal.map q (fittingIdeal (R := R) (M := M) 0)
        rw [hfit]
        exact (minorIdeal_map q A n).symm
  have hnotinj : ¬ Function.Injective B.mulVecLin := by
    intro hinj
    have hrank := Stacks.DeterminantalRank.rank_eq_and_annihilator_eq_bot_of_injective B hinj
    have hqa' : q a ∈ (Stacks.DeterminantalRank.detIdeal B).annihilator := by
      rw [hdet_of_rank hrank.1]
      exact hqa
    rw [hrank.2] at hqa'
    exact hqa_ne (by simpa using hqa')
  have hker : LinearMap.ker B.mulVecLin ≠ ⊥ := by
    intro hzero
    exact hnotinj (LinearMap.ker_eq_bot.mp hzero)
  obtain ⟨v, hvker, hv⟩ := (LinearMap.ker B.mulVecLin).ne_bot_iff.mp hker
  -- A nonzero vector in the kernel of the transposed relation matrix is a nonzero functional
  -- on the presented module.
  let qPi (ι : Type) : (ι → R) →ₗ[R] (ι → S) := {
    toFun := fun z i => q (z i)
    map_add' := by intro z w; ext i; simp
    map_smul' := by
      intro r z
      ext i
      show q (r * z i) = algebraMap R S r * q (z i)
      rw [map_mul]
      rfl }
  let ell : Module.Dual S (Fin n → S) := dotProductEquiv S (Fin n) v
  let h₀ : (Fin n → R) →ₗ[R] S := (ell.restrictScalars R).comp (qPi (Fin n))
  have hqg : ∀ z, qPi (Fin n) (g z) = (A.map q).mulVecLin (qPi (Fin m) z) := by
    intro z
    ext i
    rw [hg]
    show q (∑ j : Fin m, A i j * z j) = ∑ j : Fin m, q (A i j) * q (z j)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_mul]
  have hcomp : h₀.comp g = 0 := by
    apply LinearMap.ext
    intro z
    show ell (qPi (Fin n) (g z)) = 0
    rw [hqg z]
    show dotProduct v ((A.map q).mulVec (qPi (Fin m) z)) = 0
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose (A.map q) v]
    have hv0 : B.mulVec v = 0 := by simpa [Matrix.mulVecLin_apply] using hvker
    exact (by simpa using congrArg (fun t => dotProduct t (qPi (Fin m) z)) hv0)
  have hkerf : LinearMap.ker f ≤ LinearMap.ker h₀ := by
    rw [← hrange]
    exact LinearMap.range_le_ker_iff.mpr hcomp
  let hQ := (LinearMap.ker f).liftQ h₀ hkerf
  let e := f.quotKerEquivOfSurjective hf
  let h : M →ₗ[R] S := hQ.comp e.symm.toLinearMap
  have hcomp' : h.comp f = h₀ := by
    ext z
    simp [h, hQ, e]
  have hnonzero : h ≠ 0 := by
    intro hz
    have hz' : h₀ = 0 := by rw [← hcomp', hz]; simp
    have hell0 : ell = 0 := by
      apply LinearMap.ext
      intro y
      obtain ⟨z, hz⟩ : ∃ z : Fin n → R, qPi (Fin n) z = y := by
        choose z hz using fun i => q.surjective (y i)
        refine ⟨z, ?_⟩
        ext i
        exact hz i
      rw [← hz]
      show h₀ z = 0
      exact congrArg (fun φ : (Fin n → R) →ₗ[R] S => φ z) hz'
    have hvzero : v = 0 := by
      apply (dotProductEquiv S (Fin n)).injective
      simpa [ell] using hell0
    exact hv hvzero
  exact ⟨h, hnonzero⟩

namespace Module

/-- **Stacks Project, Tag 0GPF**, module form.  A nonzero module whose support is contained in
the support of a finitely presented module receives a nonzero linear map from it. -/
theorem exists_nonzero_linearMap_of_support_subset
    {R M N : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.FinitePresentation R M]
    (hN : ¬ Subsingleton N)
    (hsupp : Module.support R N ⊆ Module.support R M) :
    ∃ f : M →ₗ[R] N, f ≠ 0 := by
  classical
  have : Nontrivial N := not_subsingleton_iff_nontrivial.mp hN
  obtain ⟨x, hx⟩ := exists_ne (0 : N)
  let I : Ideal R := Ideal.torsionOf R N x
  have hAnn : (R ∙ x).annihilator = I := Ideal.annihilator_span_singleton_eq_torsionOf x
  have hI : I ≠ ⊤ := fun htop =>
    hx (by simpa using (Ideal.mem_torsionOf_iff x 1).mp (I.eq_top_iff_one.mp htop))
  have hprimeSupp : ∀ p : PrimeSpectrum R, I ≤ p.asIdeal → p ∈ Module.support R M := by
    intro p hp
    apply hsupp
    rw [Module.mem_support_iff_exists_annihilator]
    exact ⟨x, by simpa [hAnn] using hp⟩
  obtain ⟨f, hf⟩ := exists_nonzero_linearMap_to_quotient I hI hprimeSupp
  let e := Ideal.quotTorsionOfEquivSpanSingleton R N x
  refine ⟨(R ∙ x).subtype.comp (e.toLinearMap.comp f), fun hzero => hf ?_⟩
  ext1 m
  exact e.injective (Subtype.ext (by simpa using LinearMap.congr_fun hzero m))

end Module

end Algebra

namespace AlgebraicGeometry

section Transport

/-- Pushforward along an isomorphism of schemes is restriction along the inverse. -/
private noncomputable def pushforwardIsoRestrictInv {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    Scheme.Modules.pushforward f ≅ Scheme.Modules.restrictFunctor (inv f) :=
  (Scheme.Modules.restrictAdjunction f).rightAdjointUniq
    (CategoryTheory.Equivalence.mk (Scheme.Modules.restrictFunctor f)
      (Scheme.Modules.restrictFunctor (inv f))
      ((Scheme.Modules.restrictFunctorId (X := Y)).symm ≪≫
        (Scheme.Modules.restrictFunctorCongr (IsIso.inv_hom_id f)).symm ≪≫
        Scheme.Modules.restrictFunctorComp (inv f) f)
      ((Scheme.Modules.restrictFunctorComp f (inv f)).symm ≪≫
        Scheme.Modules.restrictFunctorCongr (IsIso.hom_inv_id f) ≪≫
        Scheme.Modules.restrictFunctorId)).toAdjunction

/-- Direct image along an isomorphism of schemes preserves finite presentation.

This is the special case of [Stacks, Tag 05B4] at an isomorphism, which is the only case the
proof of [Stacks, Tag 0GPF] below uses.  Delete it once tag 05B4 lands and use that instead. -/
private theorem isFinitePresentation_pushforward_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] (F : X.Modules) [F.IsFinitePresentation] :
    ((Scheme.Modules.pushforward f).obj F).IsFinitePresentation := by
  have hp : ((Scheme.Modules.pullback (inv f)).obj F).IsFinitePresentation :=
    @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _
      (inv f).toLRSHom.toShHom F ‹F.IsFinitePresentation›
  have hr : ((Scheme.Modules.restrictFunctor (inv f)).obj F).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback (inv f)).app F).symm hp
  exact (SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso
    ((pushforwardIsoRestrictInv f).app F).symm hr

private theorem finitePresentation_globalSections {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] [M.IsFinitePresentation] :
    Module.FinitePresentation R (AlgebraicGeometry.moduleSpecΓFunctor.obj M) := by
  let N := AlgebraicGeometry.moduleSpecΓFunctor.obj M
  have htilde : (AlgebraicGeometry.tilde N).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf).prop_of_iso
      (CategoryTheory.asIso M.fromTildeΓ).symm inferInstance
  exact (AlgebraicGeometry.tilde_isFinitePresentation_iff N).mp htilde

private noncomputable def addEquivOfIso {A B : AddCommGrpCat} (i : A ≅ B) : (↑A) ≃+ ↑B :=
  AddEquiv.ofBijective (ConcreteCategory.hom i.hom)
    (ConcreteCategory.bijective_of_isIso i.hom)

/-- An additive equivalence transports the existence of a nonzero element. -/
private theorem exists_ne_zero_iff_of_addEquiv {A B : Type*} [AddZeroClass A] [AddZeroClass B]
    (e : A ≃+ B) : (∃ a : A, a ≠ 0) ↔ ∃ b : B, b ≠ 0 := by
  rw [← nontrivial_iff_exists_ne (0 : A), ← nontrivial_iff_exists_ne (0 : B)]
  exact e.toEquiv.nontrivial_congr

/-- Stalks are unchanged by direct image along an isomorphism. -/
private theorem stalk_support_pushforward_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] (M : X.Modules) (x : X) :
    (∃ a : M.presheaf.stalk x, a ≠ 0) ↔
      (∃ a : ((Scheme.Modules.pushforward f).obj M).presheaf.stalk (f x), a ≠ 0) := by
  let i : (X : TopCat) ⟶ (Y : TopCat) := f.toLRSHom.base
  have hi : Topology.IsInducing (ConcreteCategory.hom i) := by
    show Topology.IsInducing ⇑(f.toLRSHom.base)
    convert f.homeomorph.isInducing using 1
    funext z
    rfl
  have hst : IsIso (TopCat.Presheaf.stalkPushforward Ab i M.presheaf x) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing Ab hi M.presheaf x
  let e : M.presheaf.stalk x ≃+
      ((Scheme.Modules.pushforward f).obj M).presheaf.stalk (f x) := by
    show M.presheaf.stalk x ≃+
      ((TopCat.Presheaf.pushforward Ab i).obj M.presheaf).stalk (i x)
    exact addEquivOfIso (asIso (TopCat.Presheaf.stalkPushforward Ab i M.presheaf x)).symm
  exact exists_ne_zero_iff_of_addEquiv e

/-- An iso of abelian groups transports the existence of a nonzero element. -/
lemma exists_nonzero_iff_of_addCommGrpCat_iso {A B : AddCommGrpCat.{u}} (i : A ≅ B) :
    (∃ a : A, a ≠ 0) ↔ ∃ b : B, b ≠ 0 := by
  exact exists_ne_zero_iff_of_addEquiv (addEquivOfIso i)

/-- A prime lies in the support of a module exactly when the associated quasi-coherent sheaf
has a nonzero stalk there. -/
private theorem mem_module_support_iff_tilde_stalk (R : CommRingCat.{u})
    (M : ModuleCat.{u} R) (x : PrimeSpectrum R) :
    x ∈ Module.support R M ↔
      ∃ a : (AlgebraicGeometry.tilde M).presheaf.stalk x, a ≠ 0 := by
  rw [Module.mem_support_iff, ← nontrivial_iff_exists_ne (0 : _)]
  exact Equiv.nontrivial_congr
    (IsLocalizedModule.iso x.asIdeal.primeCompl
      (AlgebraicGeometry.tilde.toStalk M x).hom).toEquiv

/-- For a quasi-coherent module on an affine scheme, the support of its module of global
sections is the set of points with nonzero stalk. -/
private theorem mem_support_moduleSpecΓ_iff {R : CommRingCat.{u}} (N : (Spec R).Modules)
    [N.IsQuasicoherent] (x : PrimeSpectrum R) :
    x ∈ Module.support R (AlgebraicGeometry.moduleSpecΓFunctor.obj N) ↔
      ∃ a : N.presheaf.stalk x, a ≠ 0 := by
  rw [mem_module_support_iff_tilde_stalk]
  exact exists_nonzero_iff_of_addCommGrpCat_iso
    ((Scheme.Modules.toPresheaf (Spec R) ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso (asIso N.fromTildeΓ))

end Transport

/-- **Stacks Project, Tag 0GPF.** If the support of a nonzero quasi-coherent module on an
affine scheme is contained in that of a finitely presented module, then there is a nonzero
morphism from the latter to the former. -/
@[stacks 0GPF, sga "2 VII 1.3" "affine case"]
theorem exists_nonzero_hom_of_supp_subset
    (X : Scheme.{u}) [IsAffine X]
    (F E : X.Modules) [F.IsFinitePresentation] [E.IsQuasicoherent]
    (hE : ¬ IsZero E)
    (hsupp : SheafOfModules.supp E ⊆ SheafOfModules.supp F) :
    ∃ f : F ⟶ E, f ≠ 0 := by
  classical
  let g := X.isoSpec.hom
  let PF := (Scheme.Modules.pushforward g).obj F
  let PE := (Scheme.Modules.pushforward g).obj E
  let : F.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F
  have : PF.IsQuasicoherent := inferInstanceAs
    (((Scheme.Modules.pushforward g).obj F).IsQuasicoherent)
  have : PE.IsQuasicoherent := inferInstanceAs
    (((Scheme.Modules.pushforward g).obj E).IsQuasicoherent)
  have : PF.IsFinitePresentation := isFinitePresentation_pushforward_of_isIso g F
  let MF := AlgebraicGeometry.moduleSpecΓFunctor.obj PF
  let ME := AlgebraicGeometry.moduleSpecΓFunctor.obj PE
  have : Module.FinitePresentation (Γ(X, ⊤)) MF := finitePresentation_globalSections PF
  have hPE : ¬ IsZero PE := by
    intro hzero
    have hmap : (Scheme.Modules.pushforward g).map (𝟙 E) =
        (Scheme.Modules.pushforward g).map (0 : E ⟶ E) := by
      calc
        _ = 𝟙 ((Scheme.Modules.pushforward g).obj E) :=
          (Scheme.Modules.pushforward g).map_id E
        _ = 0 := by simpa [PE] using (IsZero.iff_id_eq_zero PE).mp hzero
        _ = (Scheme.Modules.pushforward g).map 0 := by simp
    have hfaith : (Scheme.Modules.pushforward g).Faithful := by infer_instance
    have : (𝟙 E : E ⟶ E) = 0 := hfaith.map_injective hmap
    exact hE ((IsZero.iff_id_eq_zero E).mpr this)
  have hME : ¬ Subsingleton ME := by
    intro hsub
    have hzero : IsZero ME := ModuleCat.isZero_iff_subsingleton.mpr hsub
    have htilde : IsZero ((AlgebraicGeometry.tilde.functor
        (R := Γ(X, ⊤))).obj ME) := Functor.map_isZero _ hzero
    have hPEzero : IsZero PE := IsZero.of_iso htilde (asIso PE.fromTildeΓ).symm
    exact hPE hPEzero
  let R := Γ(X, ⊤)
  have hmodSupp : Module.support R ME ⊆ Module.support R MF := by
    intro p hp
    have hstalkE : ∃ a : PE.presheaf.stalk p, a ≠ 0 :=
      (mem_support_moduleSpecΓ_iff PE p).1 hp
    let x : X := g.homeomorph.symm p
    have hxp : g x = p := g.homeomorph.apply_symm_apply p
    have hstalkOrigE : ∃ a : E.presheaf.stalk x, a ≠ 0 := by
      apply (stalk_support_pushforward_iff g E x).mpr
      rw [hxp]
      exact hstalkE
    have hstalkOrigF : ∃ a : F.presheaf.stalk x, a ≠ 0 := hsupp hstalkOrigE
    have hstalkF : ∃ a : PF.presheaf.stalk p, a ≠ 0 := by
      rw [← hxp]
      exact (stalk_support_pushforward_iff g F x).1 hstalkOrigF
    exact (mem_support_moduleSpecΓ_iff PF p).2 hstalkF
  obtain ⟨φ, hφ⟩ := Module.exists_nonzero_linearMap_of_support_subset hME hmodSupp
  have : IsIso PF.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent PF
  have : IsIso PE.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent PE
  let SF := AlgebraicGeometry.moduleSpecΓFunctor.obj PF
  let SE := AlgebraicGeometry.moduleSpecΓFunctor.obj PE
  let rawF := (AlgebraicGeometry.modulesSpecToSheaf.obj PF).presheaf.obj (.op ⊤)
  let rawE := (AlgebraicGeometry.modulesSpecToSheaf.obj PE).presheaf.obj (.op ⊤)
  let : Module (Γ(X, ⊤)) rawF := SF.isModule
  let : Module (Γ(X, ⊤)) rawE := SE.isModule
  have hSF : SF = ModuleCat.of (Γ(X, ⊤)) rawF := rfl
  have hSE : SE = ModuleCat.of (Γ(X, ⊤)) rawE := rfl
  let iF0 := CategoryTheory.asIso PF.fromTildeΓ
  let iE0 := CategoryTheory.asIso PE.fromTildeΓ
  let iF : tilde SF ≅ PF :=
    (AlgebraicGeometry.tilde.functor (R := Γ(X, ⊤))).mapIso (eqToIso hSF) ≪≫ iF0
  let iE : tilde SE ≅ PE :=
    (AlgebraicGeometry.tilde.functor (R := Γ(X, ⊤))).mapIso (eqToIso hSE) ≪≫ iE0
  let φ' : (↑SF) →ₗ[Γ(X, ⊤)] (↑SE) := φ
  let htildeMap := AlgebraicGeometry.tilde.map (ModuleCat.ofHom φ')
  let ψ : PF ⟶ PE := iF.inv ≫ htildeMap ≫ iE.hom
  have hψ : ψ ≠ 0 := by
    intro hzero
    have hm : htildeMap = 0 := by
      have hc := congrArg (fun q => iF.hom ≫ q) hzero
      have hc' : htildeMap ≫ iE.hom = 0 := by
        change iF.hom ≫ (iF.inv ≫ htildeMap ≫ iE.hom) = iF.hom ≫ 0 at hc
        simpa [Category.assoc, iF.hom_inv_id, zero_comp] using hc
      exact (cancel_mono iE.hom).1 (by simpa [zero_comp] using hc')
    have hm' : (AlgebraicGeometry.tilde.functor (R := Γ(X, ⊤))).map
        (ModuleCat.ofHom φ') = 0 := by
      show AlgebraicGeometry.tilde.map (ModuleCat.ofHom φ') = 0
      exact hm
    have hlin : ModuleCat.ofHom φ' = 0 :=
      (AlgebraicGeometry.tilde.functor (R := Γ(X, ⊤))).map_injective <| by
        let T := AlgebraicGeometry.tilde.functor (R := Γ(X, ⊤))
        calc
          _ = 0 := hm'
          _ = T.map 0 := (T.map_zero SF SE).symm
    apply hφ
    simpa [φ'] using congrArg ModuleCat.Hom.hom hlin
  have : (Scheme.Modules.pushforward g).Full := by infer_instance
  have : (Scheme.Modules.pushforward g).Faithful := by infer_instance
  let f := (Scheme.Modules.pushforward g).preimage ψ
  have hf : f ≠ 0 := by
    intro hzero
    apply hψ
    have hmap := congrArg ((Scheme.Modules.pushforward g).map) hzero
    simpa [f] using hmap
  exact ⟨f, hf⟩

end AlgebraicGeometry
