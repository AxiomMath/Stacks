module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FiniteAlgebraization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalClosedSubschemeAlgebraization
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PrincipalPowerSubscheme
public import StacksFrontier.AlgebraicGeometry.KerDetected.IdealComap
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Adjunction
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.AffineOpenSections
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.SupportSeparation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientMap
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.LocalSections
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.AlgebraIso

/-!
# The coherent adic system of a compatible system of finite algebras

Let `A` be a ring, `I ⊆ A` an ideal and `f : X ⟶ Spec A`, and write
`Xₙ = X ×_{Spec A} Spec(A / I^(n+1))` with `pₙ : Xₙ ⟶ X`. A system of finite quasi-coherent
algebras `Bₙ` on the `Xₙ` with `iₙ^* B_{n+1} ≅ Bₙ` along the transitions `iₙ : Xₙ ⟶ X_{n+1}` is
the input of Grothendieck existence for sheaves of algebras (the hypothesis
`AlgebraicGeometry.AdicFiniteAlgebraAlgebraization` of Stacks 09ZT). This file turns such a system
into a coherent adic system along `I 𝒪_X` on `X` itself — the "unwinding" of Stacks 088F, for
systems of algebras — which is the shape Stacks 088C consumes.

The route is geometric. The relative spectra `Yₙ = Spec_{Xₙ}(Bₙ)` form a cartesian system of
finite schemes over the `Xₙ` (`isPullback_syst`), hence also over `X`, where
`Yₙ = Y_{n+1} ×_X Xₙ` (`isPullback_syst_sysq`). The modules `Nₙ = (Yₙ ⟶ X)_* 𝒪_{Yₙ}` are coherent,
killed by `(I 𝒪_X)^(n+1)` because `Xₙ` is cut out by that ideal (`ker_adicBaseChange_fst`), and on
an affine open the transition `N_{n+1} ⟶ Nₙ` is the quotient by `I(U)^(n+1)`, because a base
change of a closed immersion of affine schemes is cut out by the extended ideal
(`app_surjective_ker_of_isPullback`).

The file also proves the converse recognition principle used at the end of the proof of
Grothendieck existence for algebras: a morphism of affine schemes over `S` which on sections
over affine opens realizes the quotient by the ideal of a closed immersion `T ⟶ S` is the base
change along it (`isPullback_of_appLE`), and its algebraic form for the pullback of an algebra
sheaf (`nonempty_algebraPullback_iso_of_sections`).

## Main results

* `AlgebraicGeometry.AdicFiniteAlgebra.ker_adicBaseChange_fst` — `Xₙ ⊆ X` is cut out by
  `(I 𝒪_X)^(n+1)`.
* `AlgebraicGeometry.AdicFiniteAlgebra.isPullback_of_appLE` — a morphism of affine schemes over
  `S` realizing, on sections over affine opens, the quotient by the ideal of a closed immersion
  `T ⟶ S` is the base change along it.
* `AlgebraicGeometry.AdicFiniteAlgebra.nonempty_algebraPullback_iso_of_sections` — the same
  recognition for the pullback of a quasi-coherent algebra along a closed immersion.
* `AlgebraicGeometry.AdicFiniteAlgebra.isCoherentAdicSystem_sysNSystem` — the system `(Nₙ)` is a
  coherent adic system along `I 𝒪_X`.

## References

* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
* [Stacks Project, Tag 09ZT](https://stacks.math.columbia.edu/tag/09ZT)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AffineAlgebraEquivalence
open Stacks.RelativeSpec (AlgebraSheaf)
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf baseIdealSheaf_pow)
open Stacks.AlgebraicGeometry.HigherDirectImageCoherent
  (idealPowerMultiple_eq_bot_of_forall_smul_eq_zero)

universe u

namespace AlgebraicGeometry.AdicFiniteAlgebra

variable (A : Type u) [CommRing A] (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- The structure morphism of an adic thickening is a closed immersion. -/
public instance isClosedImmersion_adicThickeningι (n : ℕ) :
    IsClosedImmersion (adicThickeningι A I n) :=
  IsClosedImmersion.spec_of_quotient_mk (R := .of A) (I ^ (n + 1))

/-- The projection of an adic base change to `X` is a closed immersion. -/
public instance isClosedImmersion_adicBaseChange_fst (n : ℕ) :
    IsClosedImmersion (pullback.fst f (adicThickeningι A I n)) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback f (adicThickeningι A I n)).flip inferInstance

/-- The ideal sheaf cutting out `Xₙ = X ×_{Spec A} Spec(A / I^(n+1))` in `X` is `(I 𝒪_X)^(n+1)`. -/
public theorem ker_adicBaseChange_fst (n : ℕ) :
    (pullback.fst f (adicThickeningι A I n)).ker = baseIdealSheaf A I f ^ (n + 1) := by
  rw [← baseIdealSheaf_pow, Stacks.PuncturedSpectrumPicard.baseIdealSheaf_eq_ker_pullback_fst]
  rfl

/-- A section of `I 𝒪_X` to the power `n + 1` over an affine open dies in `Xₙ`. -/
public theorem app_adicBaseChange_fst_eq_zero (n : ℕ) (U : X.affineOpens) (r : Γ(X, U.1))
    (hr : r ∈ (baseIdealSheaf A I f).ideal U ^ (n + 1)) :
    ((pullback.fst f (adicThickeningι A I n)).app U.1).hom r = 0 := by
  have h : r ∈ (pullback.fst f (adicThickeningι A I n)).ker.ideal U := by
    rwa [ker_adicBaseChange_fst]
  rwa [Scheme.Hom.ker_apply] at h

/-- `Xₙ` is the fibre product `X_{n+1} ×_X Xₙ`, because `X_{n+1} ⟶ X` is a monomorphism. -/
public theorem isPullback_adicBaseChangeSucc_fst (n : ℕ) :
    IsPullback (adicBaseChangeSucc A I f n) (𝟙 _)
      (pullback.fst f (adicThickeningι A I (n + 1))) (pullback.fst f (adicThickeningι A I n)) := by
  refine IsPullback.of_isLimit' ⟨by simp [adicBaseChangeSucc_fst]⟩ ?_
  refine PullbackCone.IsLimit.mk _ (fun s => s.snd) (fun s => ?_) (fun s => by simp)
    (fun s m _ h2 => by simpa using h2)
  apply (cancel_mono (pullback.fst f (adicThickeningι A I (n + 1)))).1
  rw [Category.assoc, adicBaseChangeSucc_fst, ← s.condition]



/-! ### Sections of a base change of a closed immersion over an affine open -/

/-- Restriction along an equality of opens is bijective on sections. -/
public theorem bijective_presheaf_map_of_eq {Y : Scheme.{u}} {V W : Y.Opens} (h : V = W) :
    Function.Bijective (Y.presheaf.map (homOfLE h.le).op).hom := by
  subst h
  have : (homOfLE (le_refl V)).op = 𝟙 (op V) := rfl
  rw [this, CategoryTheory.Functor.map_id]
  exact Function.bijective_id

/-- The kernel of the base change `t` of a closed immersion `ι` is the inverse image of `ker ι`. -/
private theorem ker_eq_comap_of_isPullback {P Y T S : Scheme.{u}} {t : P ⟶ Y} {a : P ⟶ T}
    {g : Y ⟶ S} {ι : T ⟶ S} (h : IsPullback t a g ι) [IsClosedImmersion ι] :
    t.ker = ι.ker.comap g := by
  rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

/-- **Sections of a base change of a closed immersion.** For a cartesian square
`P = Y ×_S T` with `ι : T ⟶ S` a closed immersion and `g : Y ⟶ S` affine, over an affine open
`U` of `S` the map `Γ(Y, g⁻¹U) ⟶ Γ(P, t⁻¹g⁻¹U)` is surjective with kernel generated by the
ideal of `T` over `U`. -/
public theorem app_surjective_ker_of_isPullback {P Y T S : Scheme.{u}} {t : P ⟶ Y} {a : P ⟶ T}
    {g : Y ⟶ S} {ι : T ⟶ S} (h : IsPullback t a g ι) [IsClosedImmersion ι] [IsAffineHom g]
    (U : S.affineOpens) :
    Function.Surjective (t.app (g ⁻¹ᵁ U.1)) ∧
      RingHom.ker (t.app (g ⁻¹ᵁ U.1)).hom = Ideal.map (g.app U.1).hom (ι.ker.ideal U) := by
  have : IsClosedImmersion t :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback h.flip inferInstance
  let V : Y.affineOpens := ⟨g ⁻¹ᵁ U.1, U.2.preimage g⟩
  refine ⟨t.app_surjective V.1 V.2, ?_⟩
  have h1 := Scheme.Hom.ker_apply t V
  rw [ker_eq_comap_of_isPullback h, Stacks.IdealSheaf.ideal_comap_appLE ι.ker g U V le_rfl,
    Scheme.Hom.appLE_eq_app] at h1
  exact h1.symm


/-- An element of the extension `𝔞 S` of an ideal along a ring map `φ : R ⟶ S` lies in
`𝔞 • M` after any additive map `g : S ⟶ M` to an `R`-module with `r • g s = g (φ r * s)`. -/
public theorem mem_smul_top_of_mem_map {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] (φ : R →+* S) (𝔞 : Ideal R) (g : S →+ M)
    (hsmul : ∀ (r : R) (s : S), r • g s = g (φ r * s)) {x : S} (hx : x ∈ Ideal.map φ 𝔞) :
    g x ∈ 𝔞 • (⊤ : Submodule R M) := by
  let P : Ideal S :=
    { carrier := {y | ∀ c : S, g (c * y) ∈ 𝔞 • (⊤ : Submodule R M)}
      add_mem' := fun {a b} ha hb c => by
        rw [mul_add, map_add]
        exact add_mem (ha c) (hb c)
      zero_mem' := fun c => by
        rw [mul_zero, map_zero]
        exact zero_mem _
      smul_mem' := fun d y hy c => by
        rw [smul_eq_mul, ← mul_assoc]
        exact hy (c * d) }
  have hle : Ideal.map φ 𝔞 ≤ P := by
    refine Ideal.map_le_iff_le_comap.2 fun a ha c => ?_
    rw [mul_comm, ← hsmul]
    exact Submodule.smul_mem_smul ha trivial
  simpa only [one_mul] using hle hx 1

/-! ### A criterion for the quotient by `I^k M` to map isomorphically -/

/-- Let `φ : M ⟶ N` be a morphism of quasi-coherent modules which is surjective on affine sections
and whose kernel on an affine open `U` is `I(U)^k M(U)`. Then any factorization of `φ` through
`M / I^k M` is an isomorphism. -/
public theorem isIso_cokernelDesc_of_affine {Z : Scheme.{u}} (J : Z.IdealSheafData) (k : ℕ)
    (M N : Z.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N)
    (d : Stacks.Algebraization.idealPowerQuotient J k M ⟶ N)
    (hd : cokernel.π (C := Z.Modules) (Stacks.Algebraization.idealPowerMultiple J k M).ι ≫ d = φ)
    (hsurj : ∀ U : Z.affineOpens, Function.Surjective (φ.val.app (op U.1)))
    (hker : ∀ (U : Z.affineOpens) (s : Γ(M, U.1)), φ.val.app (op U.1) s = 0 →
      s ∈ J.ideal U ^ k • (⊤ : Submodule Γ(Z, U.1) Γ(M, U.1))) :
    IsIso d := by
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_bijective_app_of_isOpenCover
    d (fun U : Z.affineOpens => U.1) (iSup_affineOpens_eq_top Z) (fun U => U.2) fun U => ?_
  let π := cokernel.π (C := Z.Modules) (Stacks.Algebraization.idealPowerMultiple J k M).ι
  have hπ : Function.Surjective (π.app U.1) := surjective_app_of_epi_of_isAffineOpen π U.2
  have hcomp : ∀ s, d.val.app (op U.1) (π.val.app (op U.1) s) = φ.val.app (op U.1) s :=
    fun s => congrArg (fun ψ : M ⟶ N => ψ.val.app (op U.1) s) hd
  refine ⟨?_, fun y => ?_⟩
  · refine (injective_iff_map_eq_zero (d.val.app (op U.1)).hom).2 fun y hy => ?_
    obtain ⟨s, rfl⟩ := hπ y
    refine (Stacks.Algebraization.cokernel_π_app_eq_zero_iff _ _ _ s).2 ?_
    rw [Stacks.Algebraization.idealPowerMultiple_toSubmodule_obj_affine]
    exact hker U s ((hcomp s).symm.trans hy)
  · obtain ⟨s, hs⟩ := hsurj U y
    exact ⟨π.val.app (op U.1) s, (hcomp s).trans hs⟩


/-- The version of `isIso_cokernelDesc_of_affine` for the morphism of underlying modules of a
morphism of algebra sheaves out of a pushed-forward structure sheaf, with the hypotheses read on
the rings of sections. -/
public theorem isIso_cokernelDesc_of_affine_algebra {Z W : Scheme.{u}} (J : Z.IdealSheafData)
    (k : ℕ) (q : W ⟶ Z) [IsAffineHom q] (Q : AlgebraSheaf Z) [Q.IsQuasicoherent]
    (ψ : pushforwardAlgebra q ⟶ Q)
    (d : Stacks.Algebraization.idealPowerQuotient J k
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra q)) ⟶ AlgebraSheaf.underlyingModule Q)
    (hd : cokernel.π (C := Z.Modules) (Stacks.Algebraization.idealPowerMultiple J k
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra q))).ι ≫ d =
        AlgebraSheaf.underlyingModuleMap ψ)
    (hsurj : ∀ U : Z.affineOpens, Function.Surjective (ψ.right.hom.app (op U.1)))
    (hker : ∀ U : Z.affineOpens, RingHom.ker (ψ.right.hom.app (op U.1)).hom ≤
      Ideal.map (q.app U.1).hom (J.ideal U ^ k)) :
    IsIso d := by
  have : (AlgebraSheaf.underlyingModule (pushforwardAlgebra q)).IsQuasicoherent :=
    isQuasicoherent_pushforwardAlgebra q
  refine isIso_cokernelDesc_of_affine J k _ _ _ d hd (fun U y => ?_) (fun U s hs => ?_)
  · exact hsurj U y
  · let g : Γ(W, q ⁻¹ᵁ U.1) →+ Γ(AlgebraSheaf.underlyingModule (pushforwardAlgebra q), U.1) :=
      { toFun := fun x => x, map_zero' := rfl, map_add' := fun _ _ => rfl }
    obtain ⟨s', rfl⟩ : ∃ s', g s' = s := ⟨s, rfl⟩
    have h1 : s' ∈ RingHom.ker (ψ.right.hom.app (op U.1)).hom := hs
    exact mem_smul_top_of_mem_map (q.app U.1).hom (J.ideal U ^ k) g (fun r x => rfl)
      (hker U h1)


/-! ### Recognizing a base change of a closed immersion from sections -/

/-- `appLE` only depends on the morphism, not on the proof of the inclusion. -/
public theorem appLE_of_eq {Y Z : Scheme.{u}} {g h : Z ⟶ Y} (e : g = h) (U : Y.Opens)
    (V : Z.Opens) (hg : V ≤ g ⁻¹ᵁ U) (hh : V ≤ h ⁻¹ᵁ U) : g.appLE U V hg = h.appLE U V hh := by
  subst e
  rfl

/-- A morphism of schemes affine over `S` is an isomorphism as soon as it is bijective on the
sections over the preimages of the affine opens of `S`. -/
public theorem isIso_of_bijective_appLE {S Y Z : Scheme.{u}} (y : Y ⟶ S) (z : Z ⟶ S)
    [IsAffineHom y] [IsAffineHom z] (c : Z ⟶ Y) (hc : c ≫ y = z)
    (hb : ∀ U : S.affineOpens, Function.Bijective
      (c.appLE (y ⁻¹ᵁ U.1) (z ⁻¹ᵁ U.1) (by rw [← hc]; exact le_rfl))) :
    IsIso c := by
  let cO : Over.mk z ⟶ Over.mk y := Over.homMk c hc
  have hφ : IsIso (pushforwardAlgebraMap cO) := by
    refine Stacks.AlgebraPullbackQcoh.isIso_of_isIso_moduleMap _ ?_
    have : SheafOfModules.IsQuasicoherent
        (AlgebraSheaf.underlyingModule (pushforwardAlgebra (Over.mk y).hom)) :=
      isQuasicoherent_pushforwardAlgebra y
    have : SheafOfModules.IsQuasicoherent
        (AlgebraSheaf.underlyingModule (pushforwardAlgebra (Over.mk z).hom)) :=
      isQuasicoherent_pushforwardAlgebra z
    refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_bijective_app_of_isOpenCover
      _ (fun U : S.affineOpens => U.1) (iSup_affineOpens_eq_top S) (fun U => U.2) fun U => ?_
    have h := pushforwardAlgebraMap_app cO U.1 (preimage_le_preimage_preimage cO U.1)
    have hU := hb U
    have h' : (pushforwardAlgebraMap cO).right.hom.app (op U.1) =
        c.appLE (y ⁻¹ᵁ U.1) (z ⁻¹ᵁ U.1) (by rw [← hc]; exact le_rfl) := h
    rw [← h'] at hU
    exact hU
  let E := Stacks.AlgebraPullbackQcoh.overHomEquiv (Over.mk y) (Over.mk z)
  let c' : Over.mk y ⟶ Over.mk z := E.symm (inv (pushforwardAlgebraMap cO))
  have h1 : cO ≫ c' = 𝟙 _ := by
    apply (Stacks.AlgebraPullbackQcoh.overHomEquiv (Over.mk z) (Over.mk z)).injective
    change pushforwardAlgebraMap (cO ≫ c') = pushforwardAlgebraMap (𝟙 _)
    rw [pushforwardAlgebraMap_comp, pushforwardAlgebraMap_id]
    change E (E.symm _) ≫ _ = _
    rw [Equiv.apply_symm_apply, IsIso.inv_hom_id]
  have h2 : c' ≫ cO = 𝟙 _ := by
    apply (Stacks.AlgebraPullbackQcoh.overHomEquiv (Over.mk y) (Over.mk y)).injective
    change pushforwardAlgebraMap (c' ≫ cO) = pushforwardAlgebraMap (𝟙 _)
    rw [pushforwardAlgebraMap_comp, pushforwardAlgebraMap_id]
    change _ ≫ E (E.symm _) = _
    rw [Equiv.apply_symm_apply, IsIso.hom_inv_id]
  exact ⟨c'.left, congrArg CommaMorphism.left h1, congrArg CommaMorphism.left h2⟩

/-- **A morphism realizing the quotient by the ideal of a closed immersion is its base change.**
Let `ι : T ⟶ S` be a closed immersion, `w : W ⟶ S` and `z : Z ⟶ S` affine, and `k : Z ⟶ W`,
`y : Z ⟶ T` over `S`. If over every affine open `U` of `S` the map `Γ(W, w⁻¹U) ⟶ Γ(Z, z⁻¹U)` is
surjective with kernel inside the ideal generated by that of `T`, then `Z = W ×_S T`. -/
public theorem isPullback_of_appLE {T W Z S : Scheme.{u}} (ι : T ⟶ S) [IsClosedImmersion ι]
    (w : W ⟶ S) [IsAffineHom w] (z : Z ⟶ S) [IsAffineHom z] (y : Z ⟶ T) (k : Z ⟶ W)
    (hy : y ≫ ι = z) (hk : k ≫ w = z)
    (hsurj : ∀ U : S.affineOpens, Function.Surjective
      (k.appLE (w ⁻¹ᵁ U.1) (z ⁻¹ᵁ U.1) (by rw [← hk]; exact le_rfl)))
    (hker : ∀ U : S.affineOpens,
      RingHom.ker (k.appLE (w ⁻¹ᵁ U.1) (z ⁻¹ᵁ U.1) (by rw [← hk]; exact le_rfl)).hom ≤
        Ideal.map (w.app U.1).hom (ι.ker.ideal U)) :
    IsPullback k y w ι := by
  have hw : k ≫ w = y ≫ ι := hk.trans hy.symm
  let c : Z ⟶ pullback w ι := pullback.lift k y hw
  have hct : c ≫ pullback.fst w ι = k := pullback.lift_fst _ _ _
  have hcz : c ≫ (pullback.fst w ι ≫ w) = z := by rw [← Category.assoc, hct, hk]
  have : IsIso c := by
    refine isIso_of_bijective_appLE (pullback.fst w ι ≫ w) z c hcz fun U => ?_
    obtain ⟨hts, htk⟩ := app_surjective_ker_of_isPullback (IsPullback.of_hasPullback w ι) U
    have hcomp : ∀ x, k.appLE (w ⁻¹ᵁ U.1) (z ⁻¹ᵁ U.1) (by rw [← hk]; exact le_rfl) x =
        c.appLE ((pullback.fst w ι ≫ w) ⁻¹ᵁ U.1) (z ⁻¹ᵁ U.1) (by rw [← hcz]; exact le_rfl)
          ((pullback.fst w ι).app (w ⁻¹ᵁ U.1) x) := by
      intro x
      have h1 := appLE_of_eq hct.symm (w ⁻¹ᵁ U.1) (z ⁻¹ᵁ U.1)
        (by rw [← hk]; exact le_rfl) (by rw [hct, ← hk]; exact le_rfl)
      rw [Scheme.Hom.comp_appLE] at h1
      exact congrArg (fun φ => φ.hom x) h1
    refine ⟨?_, fun v => ?_⟩
    · refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
      obtain ⟨x, rfl⟩ := hts v
      have hx : x ∈ RingHom.ker ((pullback.fst w ι).app (w ⁻¹ᵁ U.1)).hom := by
        rw [htk]
        exact hker U (by rw [RingHom.mem_ker, hcomp]; exact hv)
      exact hx
    · obtain ⟨x, hx⟩ := hsurj U v
      exact ⟨_, (hcomp x).symm.trans hx⟩
  exact IsPullback.of_iso_pullback ⟨hw⟩ (asIso c) hct (pullback.lift_snd _ _ _)


/-- The preimage along a composite is contained in the iterated preimage. -/
public theorem preimage_le_of_comp {Z W S : Scheme.{u}} {g : Z ⟶ W} {w : W ⟶ S} {z : Z ⟶ S}
    (e : g ≫ w = z) (U : S.Opens) : z ⁻¹ᵁ U ≤ g ⁻¹ᵁ (w ⁻¹ᵁ U) := by
  subst e
  exact le_rfl

/-- The inverse of an isomorphism of algebra sheaves undoes it on sections. -/
public theorem iso_inv_hom_app {S : Scheme.{u}} {P Q : AlgebraSheaf S} (E : P ≅ Q) (U : S.Opens)
    (x : P.right.obj.obj (op U)) :
    E.inv.right.hom.app (op U) (E.hom.right.hom.app (op U) x) = x :=
  congrArg (fun ψ : P ⟶ P => (ψ.right.hom.app (op U)).hom x) E.hom_inv_id

/-- An isomorphism of algebra sheaves undoes its inverse on sections. -/
public theorem iso_hom_inv_app {S : Scheme.{u}} {P Q : AlgebraSheaf S} (E : P ≅ Q) (U : S.Opens)
    (x : Q.right.obj.obj (op U)) :
    E.hom.right.hom.app (op U) (E.inv.right.hom.app (op U) x) = x :=
  congrArg (fun ψ : Q ⟶ Q => (ψ.right.hom.app (op U)).hom x) E.inv_hom_id

/-- **The pullback of an algebra along a closed immersion, from sections.** Let `ι : T ⟶ S` be
a closed immersion, `C` a quasi-coherent algebra on `S`, `y : Z ⟶ T` with `y ≫ ι` affine, and
`φ : C ⟶ (y ≫ ι)_* 𝒪_Z` a morphism of algebras which over every affine open `U` is surjective
with kernel inside the ideal generated by that of `T`. Then `ι^* C ≅ y_* 𝒪_Z`. -/
public theorem nonempty_algebraPullback_iso_of_sections {T Z S : Scheme.{u}} (ι : T ⟶ S)
    [IsClosedImmersion ι] (C : AlgebraSheaf S) [AlgebraSheaf.IsQuasicoherent C]
    (y : Z ⟶ T) [IsAffineHom y] (φ : C ⟶ pushforwardAlgebra (y ≫ ι))
    (hsurj : ∀ U : S.affineOpens, Function.Surjective (φ.right.hom.app (op U.1)))
    (hker : ∀ U : S.affineOpens, RingHom.ker (φ.right.hom.app (op U.1)).hom ≤
      Ideal.map (C.hom.hom.app (op U.1)).hom (ι.ker.ideal U)) :
    Nonempty ((algebraPullback ι).obj C ≅ pushforwardAlgebra y) := by
  let w := relativeSpecToBase C
  let P := pushforwardAlgebraIso C
  let kO : Over.mk (y ≫ ι) ⟶ Over.mk w :=
    (Stacks.AlgebraPullbackQcoh.overHomEquiv (Over.mk (y ≫ ι)) (Over.mk w)).symm (P.hom ≫ φ)
  have hkO : pushforwardAlgebraMap kO = P.hom ≫ φ :=
    (Stacks.AlgebraPullbackQcoh.overHomEquiv (Over.mk (y ≫ ι)) (Over.mk w)).apply_symm_apply _
  have hk : kO.left ≫ w = y ≫ ι := Over.w kO
  have happ : ∀ U : S.affineOpens,
      kO.left.appLE (w ⁻¹ᵁ U.1) ((y ≫ ι) ⁻¹ᵁ U.1) (preimage_le_of_comp hk U.1) =
        P.hom.right.hom.app (op U.1) ≫ φ.right.hom.app (op U.1) := by
    intro U
    have h := pushforwardAlgebraMap_app kO U.1 (preimage_le_preimage_preimage kO U.1)
    rw [hkO] at h
    exact h.symm
  have hPb : ∀ U : S.affineOpens, Function.Bijective (P.hom.right.hom.app (op U.1)) := fun U =>
    ⟨Function.LeftInverse.injective (iso_inv_hom_app P U.1),
      Function.RightInverse.surjective (iso_hom_inv_app P U.1)⟩
  have hpb : IsPullback kO.left y w ι := by
    refine isPullback_of_appLE ι w (y ≫ ι) y kO.left rfl hk (fun U => ?_) (fun U => ?_)
    · rw [happ U]
      exact (hsurj U).comp (hPb U).2
    · intro x hx
      rw [happ U, RingHom.mem_ker] at hx
      have h1 : P.hom.right.hom.app (op U.1) x ∈ RingHom.ker (φ.right.hom.app (op U.1)).hom := hx
      have h2 := Ideal.mem_map_of_mem (P.inv.right.hom.app (op U.1)).hom (hker U h1)
      rw [iso_inv_hom_app P U.1 x] at h2
      have h4 : C.hom.hom.app (op U.1) ≫ P.inv.right.hom.app (op U.1) = w.app U.1 :=
        congrArg (fun ψ => ψ.hom.app (op U.1)) (Under.w P.inv)
      have h5 := Ideal.map_map (C.hom.hom.app (op U.1)).hom (P.inv.right.hom.app (op U.1)).hom
        (I := ι.ker.ideal U)
      have h7 : Ideal.map (P.inv.right.hom.app (op U.1)).hom
          (Ideal.map (C.hom.hom.app (op U.1)).hom (ι.ker.ideal U)) =
            Ideal.map (w.app U.1).hom (ι.ker.ideal U) :=
        h5.trans (congrArg (fun φ => Ideal.map φ (ι.ker.ideal U)) (congrArg CommRingCat.Hom.hom h4))
      exact h7 ▸ h2
  exact ⟨(algebraPullback ι).mapIso P.symm ≪≫
    algebraPullback_pushforwardAlgebra_iso_of_isPullback hpb⟩

/-! ### The geometric system attached to a compatible system of algebras -/

section System

variable {A I f}
variable (B : ∀ n : ℕ, AlgebraSheaf (adicBaseChange A I f n))
  [hqc : ∀ n, AlgebraSheaf.IsQuasicoherent (B n)]

/-- The relative spectrum `Yₙ = Spec_{Xₙ}(Bₙ)`. -/
public abbrev sysY (n : ℕ) : Scheme.{u} := relativeSpec (B n)

/-- The structure morphism `Yₙ ⟶ Xₙ`. -/
public abbrev sysy (n : ℕ) : sysY B n ⟶ adicBaseChange A I f n := relativeSpecToBase (B n)

/-- The composite `Yₙ ⟶ Xₙ ⟶ X`. -/
public abbrev sysq (n : ℕ) : sysY B n ⟶ X :=
  sysy B n ≫ pullback.fst f (adicThickeningι A I n)

variable (e : ∀ n, (algebraPullback (adicBaseChangeSucc A I f n)).obj (B (n + 1)) ≅ B n)

/-- The base change of `Y_{n+1}` to `Xₙ`, identified with `Yₙ` over `Xₙ`. -/
public def sysE (n : ℕ) :
    (Over.pullback (adicBaseChangeSucc A I f n)).obj (Over.mk (sysy B (n + 1))) ≅
      Over.mk (sysy B n) :=
  relativeSpecBaseChangeIso (adicBaseChangeSucc A I f n) (B (n + 1)) ≪≫ relativeSpecOverIso (e n)

/-- The transition map `Yₙ ⟶ Y_{n+1}`. -/
public def syst (n : ℕ) : sysY B n ⟶ sysY B (n + 1) :=
  (sysE B e n).inv.left ≫ pullback.fst (sysy B (n + 1)) (adicBaseChangeSucc A I f n)

/-- The identification `sysE` is a morphism over `Xₙ`. -/
public theorem sysE_inv_left_snd (n : ℕ) :
    (sysE B e n).inv.left ≫ pullback.snd (sysy B (n + 1)) (adicBaseChangeSucc A I f n) =
      sysy B n :=
  Over.w (sysE B e n).inv

/-- The squares of the system are cartesian. -/
public theorem isPullback_syst (n : ℕ) :
    IsPullback (syst B e n) (sysy B n) (sysy B (n + 1)) (adicBaseChangeSucc A I f n) := by
  have hiso : IsIso (sysE B e n).inv.left := by
    have h' : IsIso ((Over.forget (adicBaseChange A I f n)).map (sysE B e n).inv) :=
      inferInstance
    rwa [Over.forget_map] at h'
  refine IsPullback.of_iso_pullback ⟨?_⟩ (asIso (sysE B e n).inv.left) rfl
    (sysE_inv_left_snd B e n)
  rw [syst, Category.assoc, pullback.condition, ← Category.assoc, sysE_inv_left_snd]

/-- The transition map `Yₙ ⟶ Y_{n+1}` is a morphism over `X`. -/
@[reassoc]
public theorem syst_sysq (n : ℕ) : syst B e n ≫ sysq B (n + 1) = sysq B n := by
  rw [sysq, ← Category.assoc, (isPullback_syst B e n).w, Category.assoc, adicBaseChangeSucc_fst]

/-- The squares over `X` are cartesian too: `Yₙ = Y_{n+1} ×_X Xₙ`. -/
public theorem isPullback_syst_sysq (n : ℕ) :
    IsPullback (syst B e n) (sysy B n) (sysq B (n + 1))
      (pullback.fst f (adicThickeningι A I n)) := by
  simpa using (isPullback_syst B e n).paste_vert (isPullback_adicBaseChangeSucc_fst A I f n)

/-- The transition map `Yₙ ⟶ Y_{n+1}` is a closed immersion. -/
public instance isClosedImmersion_syst (n : ℕ) : IsClosedImmersion (syst B e n) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (isPullback_syst_sysq B e n).flip
    inferInstance

/-- The ideal sheaf cutting out `Yₙ` in `Y_{n+1}` is the inverse image of `(I 𝒪_X)^(n+1)`. -/
public theorem ker_syst (n : ℕ) :
    (syst B e n).ker = (baseIdealSheaf A I f ^ (n + 1)).comap (sysq B (n + 1)) := by
  rw [ker_eq_comap_of_isPullback (isPullback_syst_sysq B e n), ker_adicBaseChange_fst]


/-! ### The module system on `X` -/

/-- The `𝒪_X`-algebra `qₙ_* 𝒪_{Yₙ}`. -/
public abbrev sysD (n : ℕ) : AlgebraSheaf X := pushforwardAlgebra (sysq B n)

/-- Its underlying `𝒪_X`-module. -/
public abbrev sysN (n : ℕ) : X.Modules := AlgebraSheaf.underlyingModule (sysD B n)

/-- The morphism of pushed-forward structure sheaves induced by a morphism `t` over the base,
with the structure morphism of the source given separately. -/
public def pushforwardAlgebraHomOfEq {Y Y' S : Scheme.{u}} (q : Y ⟶ S) (q' : Y' ⟶ S)
    (t : Y ⟶ Y') (h : t ≫ q' = q) : pushforwardAlgebra q' ⟶ pushforwardAlgebra q :=
  pushforwardAlgebraMapAux q' t ≫ eqToHom (congrArg pushforwardAlgebra h)

/-- The sections of `pushforwardAlgebraHomOfEq` are the canonical maps `appLE`. -/
public theorem pushforwardAlgebraHomOfEq_app {Y Y' S : Scheme.{u}} (q : Y ⟶ S) (q' : Y' ⟶ S)
    (t : Y ⟶ Y') (h : t ≫ q' = q) (U : S.Opens) :
    (pushforwardAlgebraHomOfEq q q' t h).right.hom.app (op U) =
      t.appLE (q' ⁻¹ᵁ U) (q ⁻¹ᵁ U) (by rw [← h]; exact le_rfl) :=
  pushforwardAlgebraMapAux_app q' t q h U _

/-- The transition morphism of algebras `D_{n+1} ⟶ Dₙ`. -/
public def sysτ (n : ℕ) : sysD B (n + 1) ⟶ sysD B n :=
  pushforwardAlgebraHomOfEq (sysq B n) (sysq B (n + 1)) (syst B e n) (syst_sysq B e n)

/-- The preimage of an open of `X` in `Yₙ` is its preimage in `Y_{n+1}` pulled back to `Yₙ`. -/
public theorem sysq_preimage (n : ℕ) (U : X.Opens) :
    sysq B n ⁻¹ᵁ U = syst B e n ⁻¹ᵁ (sysq B (n + 1) ⁻¹ᵁ U) := by
  rw [← syst_sysq B e n, Scheme.Hom.comp_preimage]

/-- The sections of the transition morphism of algebras. -/
public theorem sysτ_app (n : ℕ) (U : X.Opens) :
    (sysτ B e n).right.hom.app (op U) =
      (syst B e n).appLE (sysq B (n + 1) ⁻¹ᵁ U) (sysq B n ⁻¹ᵁ U)
        (sysq_preimage B e n U).le :=
  pushforwardAlgebraHomOfEq_app _ _ _ _ U

/-- Over an affine open, the transition on sections is surjective with kernel generated by
`I(U)^(n+1)`. -/
public theorem sysτ_app_surjective_ker (n : ℕ) (U : X.affineOpens) :
    Function.Surjective ((sysτ B e n).right.hom.app (op U.1)) ∧
      RingHom.ker ((sysτ B e n).right.hom.app (op U.1)).hom =
        Ideal.map ((sysq B (n + 1)).app U.1).hom ((baseIdealSheaf A I f).ideal U ^ (n + 1)) := by
  obtain ⟨hs, hk⟩ := app_surjective_ker_of_isPullback (isPullback_syst_sysq B e n) U
  rw [ker_adicBaseChange_fst] at hk
  have hb := bijective_presheaf_map_of_eq (Y := sysY B n) (sysq_preimage B e n U.1)
  rw [sysτ_app, Scheme.Hom.appLE]
  refine ⟨fun y => ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hb.2 y
    obtain ⟨w, hw⟩ := hs z
    exact ⟨w, (congrArg (fun x => ((sysY B n).presheaf.map
      (homOfLE (sysq_preimage B e n U.1).le).op).hom x) hw).trans hz⟩
  · have key : ∀ x : Γ(sysY B (n + 1), sysq B (n + 1) ⁻¹ᵁ U.1),
        ((sysY B n).presheaf.map (homOfLE (sysq_preimage B e n U.1).le).op).hom
          (((syst B e n).app (sysq B (n + 1) ⁻¹ᵁ U.1)).hom x) = 0 ↔
        x ∈ Ideal.map ((sysq B (n + 1)).app U.1).hom
          ((baseIdealSheaf A I f).ideal U ^ (n + 1)) := by
      intro x
      rw [map_eq_zero_iff _ hb.1, ← RingHom.mem_ker, hk]
      rfl
    ext x
    exact key x


/-- The identification of the sections of `Yₙ` over `qₙ⁻¹U` with the sections of `Nₙ` over `U`,
as an additive map. -/
public def sysNAddHom (n : ℕ) (U : X.Opens) :
    Γ(sysY B n, sysq B n ⁻¹ᵁ U) →+ Γ(sysN B n, U) where
  toFun s := s
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The scalar action on the sections of `Nₙ = qₙ_* 𝒪_{Yₙ}` is multiplication through `qₙ`. -/
public theorem sysN_smul (n : ℕ) (U : X.Opens) (r : Γ(X, U))
    (s : Γ(sysY B n, sysq B n ⁻¹ᵁ U)) :
    r • sysNAddHom B n U s = sysNAddHom B n U (((sysq B n).app U).hom r * s) :=
  rfl

/-- The transition morphism of modules `N_{n+1} ⟶ Nₙ`. -/
public abbrev sysNτ (n : ℕ) : sysN B (n + 1) ⟶ sysN B n :=
  AlgebraSheaf.underlyingModuleMap (sysτ B e n)

/-- On sections, the morphism of underlying modules is the morphism of algebras. -/
public theorem underlyingModuleMap_val_app {Z : Scheme.{u}} {P Q : AlgebraSheaf Z} (φ : P ⟶ Q)
    (U : Z.Opens) (s : Γ(AlgebraSheaf.underlyingModule P, U)) :
    (AlgebraSheaf.underlyingModuleMap φ).val.app (op U) s = φ.right.hom.app (op U) s :=
  rfl

variable [hfin : ∀ n, IsFinite (sysy B n)]

/-- The composite `Yₙ ⟶ Xₙ ⟶ X` is finite. -/
public instance isFinite_sysq (n : ℕ) : IsFinite (sysq B n) := by
  have := hfin n
  infer_instance

/-- The module `Nₙ` is quasi-coherent, `qₙ` being affine. -/
public instance isQuasicoherent_sysN (n : ℕ) : (sysN B n).IsQuasicoherent :=
  isQuasicoherent_pushforwardAlgebra (sysq B n)

/-- The sections of `Nₙ` over an affine open are a finite module. -/
public theorem moduleFinite_sysN (n : ℕ) (U : X.affineOpens) :
    Module.Finite Γ(X, U.1) Γ(sysN B n, U.1) :=
  IsFinite.finite_app (sysq B n) U.1 U.2

/-- The module `Nₙ` is coherent. -/
public theorem isCoherent_sysN [IsLocallyNoetherian X] (n : ℕ) :
    SheafOfModules.IsCoherent.{u} (sysN B n) :=
  Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteTildeOn _ fun U hU =>
    Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isFiniteTildeOn_of_moduleFinite_sections
      _ ⟨U, hU⟩ (moduleFinite_sysN B n ⟨U, hU⟩)

omit hfin in
/-- `(I 𝒪_X)^(n+1)` annihilates `Nₙ`. -/
public theorem idealPowerMultiple_sysN_eq_bot (n : ℕ) :
    Stacks.Algebraization.idealPowerMultiple (baseIdealSheaf A I f) (n + 1) (sysN B n) = ⊥ := by
  refine idealPowerMultiple_eq_bot_of_forall_smul_eq_zero
    _ _ _ fun U a ha m => ?_
  obtain ⟨m', rfl⟩ : ∃ m', sysNAddHom B n U.1 m' = m := ⟨m, rfl⟩
  rw [sysN_smul]
  have h0 := app_adicBaseChange_fst_eq_zero A I f n U a ha
  have h1 : ((sysq B n).app U.1).hom a = 0 := by
    have hc : ((sysq B n).app U.1).hom a = ((sysy B n).app _).hom
        (((pullback.fst f (adicThickeningι A I n)).app U.1).hom a) := rfl
    rw [hc, h0, map_zero]
    rfl
  rw [h1, zero_mul, map_zero]

/-- The comparison `N_{n+1} / (I 𝒪_X)^(n+1) N_{n+1} ⟶ Nₙ`. -/
public def sysQuot (n : ℕ) :
    Stacks.Algebraization.idealPowerQuotient (baseIdealSheaf A I f) (n + 1) (sysN B (n + 1)) ⟶
      sysN B n :=
  cokernel.desc (C := X.Modules) _ (sysNτ B e n)
    (Stacks.Algebraization.comp_eq_zero_of_idealPowerMultiple_eq_bot _ _ _
      (idealPowerMultiple_sysN_eq_bot B n))

omit hfin in
/-- The comparison `sysQuot` factors the transition morphism through the quotient. -/
public theorem π_sysQuot (n : ℕ) :
    cokernel.π (C := X.Modules) (Stacks.Algebraization.idealPowerMultiple
      (baseIdealSheaf A I f) (n + 1) (sysN B (n + 1))).ι ≫ sysQuot B e n = sysNτ B e n :=
  cokernel.π_desc (C := X.Modules) _ _ _

/-- The comparison `N_{n+1} / (I 𝒪_X)^(n+1) N_{n+1} ⟶ Nₙ` is an isomorphism. -/
public instance isIso_sysQuot (n : ℕ) : IsIso (sysQuot B e n) :=
  isIso_cokernelDesc_of_affine_algebra _ _ (sysq B (n + 1)) (sysD B n) (sysτ B e n) _
    (π_sysQuot B e n) (fun U => (sysτ_app_surjective_ker B e n U).1)
    (fun U => (sysτ_app_surjective_ker B e n U).2.le)


/-- The inverse system `(Nₙ)` of `𝒪_X`-modules. -/
public def sysNSystem : ℕᵒᵖ ⥤ X.Modules := Functor.ofOpSequence (sysNτ B e)

omit hfin in
/-- The transition maps of the system `(Nₙ)` are the morphisms `sysNτ`. -/
public theorem sysNSystem_map_succ (n : ℕ) :
    (sysNSystem B e).map (homOfLE (Nat.le_succ n)).op = sysNτ B e n :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- **The system `(Nₙ)` is a coherent adic system along `I 𝒪_X`.** -/
public theorem isCoherentAdicSystem_sysNSystem [IsLocallyNoetherian X] :
    Stacks.Coherent.IsCoherentAdicSystem (baseIdealSheaf A I f) (sysNSystem B e) :=
  ⟨fun n => isCoherent_sysN B n, fun n => idealPowerMultiple_sysN_eq_bot B n,
    fun n => ⟨@asIso _ _ _ _ (sysQuot B e n) (isIso_sysQuot B e n),
      (π_sysQuot B e n).trans (sysNSystem_map_succ B e n).symm⟩⟩

/-- The system `(Nₙ)` as an object of `Coh(X, I 𝒪_X)`. -/
public def sysAdic [IsLocallyNoetherian X] :
    Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f) :=
  ⟨sysNSystem B e, isCoherentAdicSystem_sysNSystem B e⟩

end System

end AlgebraicGeometry.AdicFiniteAlgebra

end
