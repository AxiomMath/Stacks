module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.RingTheory.Polynomial.Quotient
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.BaseChange
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PuncturedSpectrumSectionsDepthTwo
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.Universal
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.SectionsColimit.Basic
public import StacksFrontier.Examples.QuasiCoherentPushforward.NotQuasiSeparated
public import StacksFrontier.RingTheory.Depth.Criteria

/-!
# Direct image of a quasi-coherent module does not commute with base change

Let `A` be a Noetherian ring, `I ⊆ A` a finitely generated proper ideal whose `I`-depth is at
least two, and `U = Spec A ∖ V(I)` with `j : U ⟶ Spec A` its open immersion.  Base change along
the closed immersion `g : Spec (A/I) ⟶ Spec A` gives the cartesian square

```
U ×_{Spec A} Spec (A/I) --g'--> U
   |j'                          |j
   v                            v
 Spec (A/I) ------g-----------> Spec A
```

in which `j` is quasi-compact and quasi-separated and `𝒪_U` is quasi-coherent, and yet the
canonical base-change morphism `g^*(j_*𝒪_U) ⟶ j'_*((g')^*𝒪_U)` is **not** an isomorphism.  The
reason is depth: `Γ(U, 𝒪_U) = A` because `H⁰_{V(I)}(A) = H¹_{V(I)}(A) = 0`, so the source has
`(A/I) ⊗_A A = A/I ≠ 0` global sections, while the fibre `U ×_{Spec A} Spec (A/I)` is empty, so
the target has none.

This is the obstruction behind [Stacks, Tag 03LC] part (2).  The source's example is the punctured
affine plane `𝐀²_k ∖ {0} ⟶ 𝐀²_k` base changed along the origin; the example instantiated here is
the punctured spectrum of `k[t][X]` at the ideal `(X, t)`, the same phenomenon with the Hartogs
computation supplied by the depth-two vanishing of local cohomology rather than by a Čech
computation.

Part (2) has a second half, the remark that the statement cannot even be made precise in
general because `f_*` need not preserve quasi-coherence.  That is already in the library, as
`exists_quasiCompact_not_quasiSeparated_pushforward_not_isQuasicoherent` of
`StacksFrontier/Examples/QuasiCoherentPushforward/NotQuasiSeparated.lean`.

Part (2) itself, that `f_{big, *}(𝓕^a)` and `(f_*𝓕)^a` differ, is
`Stacks.Examples.QcohPushforward.exists_isEmpty_iso_bigPushforward_associatedModule` of
`StacksFrontier/Examples/QuasiCoherentPushforward/BigSitePushforward.lean`, which evaluates both
sides at the base change exhibited here; it carries the tag, and neither statement of this
file does, each being an ingredient of the source's explanation rather than the part itself.

## Main definitions

* `Stacks.Examples.QcohPushforward.puncturedScheme`, `puncturedUnit` and `puncturedPushforward`:
  the open `U = Spec A ∖ V(I)`, its structure sheaf as a module over itself, and `j_*𝒪_U`.
* `Stacks.Examples.QcohPushforward.quotientSpecMap`: the closed immersion
  `g : Spec (A/I) ⟶ Spec A` along which base change is taken.
* `Stacks.Examples.QcohPushforward.puncturedSectionsIso`: **Hartogs as an `A`-linear
  identification**, `Γ(j_*𝒪_U, ⊤) ≅ A`, from bijectivity of `A ⟶ Γ(U, 𝒪_U)`.
* `Stacks.Examples.QcohPushforward.counterexampleRing` and `counterexampleIdeal`: the concrete
  witnesses `k[t][X]` and `(X, t)`, with `k = ULift ℚ`.

## Main results

* `Stacks.Examples.QcohPushforward.preimage_complementZeroLocus_eq_bot` and
  `isEmpty_puncturedFibre`: the fibre of `U` over `Spec (A/I)` is empty.
* `Stacks.Examples.QcohPushforward.nontrivial_pullback_puncturedPushforward_sections`: the
  source of the comparison has nonzero global sections, `(A/I) ⊗_A A`.
* `Stacks.Examples.QcohPushforward.not_isIso_baseChangeNatTrans`: **the comparison is not an
  isomorphism**, for any such `A` and `I`.
* `Stacks.Examples.QcohPushforward.two_le_depth_counterexampleIdeal`: the concrete ideal has
  depth at least two, `X` and `t` being a regular sequence.
* `Stacks.Examples.QcohPushforward.exists_not_isIso_baseChangeNatTrans`: **the base-change
  obstruction behind Stacks 03LC part (2)**, the existential statement with the concrete witness
  substituted.

## Implementation notes

The Hartogs input is `Stacks.LocalCohomology.bijective_complementTopScalars_of_depth_ge_two`,
which needs only `I ≠ ⊤` and `2 ≤ depth_I(A)`; the depth is produced from the regular sequence
`X, t` by `Stacks.Depth.ModNonzerodivisor.length_le_depth_of_isWeaklyRegular`.  The second term
of that sequence is handled by `isSMulRegular_C_of_quotSMulTop_X`, which computes in `R[X]/(X)`
through `Polynomial.X_dvd_iff` rather than through the quotient isomorphism `R[X]/(X) ≅ R`.

The comparison whose failure is proved is
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans`, the same natural transformation
whose invertibility under a *flat* base change is
`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat`,
[Stacks, Tag 02KH] in degree zero.  The closed immersion `g` here is not flat, and that is the
whole point.

The base field is `ULift ℚ` rather than `ℚ` so that the counterexample lives in the universe
`Scheme.{u}` that the existential statement quantifies over.

## References

* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.LocalCohomology
open Polynomial RingTheory.Sequence
open scoped Pointwise

universe u

namespace Stacks.Examples.QcohPushforward

section General

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- The open complement `U = Spec A ∖ V(I)`, as a scheme. -/
abbrev puncturedScheme : Scheme.{u} := (complementZeroLocus A I : Scheme)

/-- The structure sheaf of `U = Spec A ∖ V(I)` as a module over itself. -/
abbrev puncturedUnit : (puncturedScheme A I).Modules :=
  SheafOfModules.unit (puncturedScheme A I).ringCatSheaf

/-- The closed immersion `g : Spec (A/I) ⟶ Spec A`, the base change along which fails. -/
abbrev quotientSpecMap : Spec (CommRingCat.of (A ⧸ I)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

/-- The direct image `j_*𝒪_U` along the open immersion `j : U ⟶ Spec A`. -/
abbrev puncturedPushforward : (Spec (CommRingCat.of A)).Modules :=
  (Scheme.Modules.pushforward (complementZeroLocus A I).ι).obj (puncturedUnit A I)

/-- A prime of `A/I` contracts to a prime of `A` containing `I`. -/
theorem mem_comap_of_mem (x : PrimeSpectrum (A ⧸ I)) (a : A) (ha : a ∈ I) :
    a ∈ (PrimeSpectrum.comap (Ideal.Quotient.mk I) x).asIdeal := by
  show (Ideal.Quotient.mk I) a ∈ x.asIdeal
  rw [Ideal.Quotient.eq_zero_iff_mem.2 ha]
  exact x.asIdeal.zero_mem

/-- **The fibre of `U` over `Spec (A/I)` is empty**, as an open of `Spec (A/I)`: every prime of
`A/I` contracts into `V(I)`, the complement of `U`. -/
theorem preimage_complementZeroLocus_eq_bot :
    (quotientSpecMap A I ⁻¹ᵁ complementZeroLocus A I) = ⊥ := by
  ext x
  simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro hx
  refine (hx : (quotientSpecMap A I).base x ∈ (complementZeroLocus A I).1) ?_
  show (I : Set A) ⊆ (PrimeSpectrum.comap (Ideal.Quotient.mk I) x).asIdeal
  exact fun a ha => mem_comap_of_mem A I x a ha

/-- The fibre of `U` over `Spec (A/I)` is the empty scheme. -/
instance isEmpty_puncturedFibre :
    IsEmpty ((quotientSpecMap A I ⁻¹ᵁ complementZeroLocus A I) : Scheme.{u}) := by
  constructor
  rintro ⟨x, hx⟩
  rwa [preimage_complementZeroLocus_eq_bot A I] at hx

/-- **Hartogs, as an `A`-linear identification.**  When `A ⟶ Γ(U, 𝒪_U)` is bijective, the
`A`-module of global sections of `j_*𝒪_U` is `A` itself: those sections are `Γ(U, 𝒪_U)` and the
`A`-module structure on them is multiplication through that very map. -/
def puncturedSectionsIso (hb : Function.Bijective (complementTopScalars I)) :
    ModuleCat.of A A ≅ moduleSpecΓFunctor.obj (puncturedPushforward A I) :=
  (LinearEquiv.ofBijective
    ({ toFun := fun a => (complementTopScalars I a : moduleSpecΓFunctor.obj
          (puncturedPushforward A I))
       map_add' := fun a b => (complementTopScalars I).map_add a b
       map_smul' := fun a b => (complementTopScalars I).map_mul a b } :
      ModuleCat.of A A →ₗ[A] moduleSpecΓFunctor.obj (puncturedPushforward A I)) hb).toModuleIso

/-- For a finitely generated `I` the open `U = Spec A ∖ V(I)` is retrocompact in `Spec A`, so
the open immersion `j : U ⟶ Spec A` is quasi-compact. -/
theorem quasiCompact_punctured_ι (hI : I.FG) : QuasiCompact (complementZeroLocus A I).ι :=
  quasiCompact_iff_isSpectralMap.mpr (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp
    (PrimeSpectrum.isRetrocompact_zeroLocus_compl_of_fg hI))

/-- `j_*𝒪_U` is quasi-coherent: `j` is quasi-compact because `I` is finitely generated and
quasi-separated because it is an immersion, so [Stacks, Tag 01LC] applies. -/
theorem isQuasicoherent_puncturedPushforward (hI : I.FG) :
    (puncturedPushforward A I).IsQuasicoherent :=
  have := quasiCompact_punctured_ι A I hI
  AlgebraicGeometry.pushforward_isQuasicoherent (complementZeroLocus A I).ι
    (puncturedUnit A I)

/-- **The source of the base-change comparison has nonzero global sections.**  They are
`(A/I) ⊗_A Γ(U, 𝒪_U) = (A/I) ⊗_A A = A/I`, which is nonzero because `I` is proper. -/
theorem nontrivial_pullback_puncturedPushforward_sections (hI : I.FG) (hIne : I ≠ ⊤)
    (hb : Function.Bijective (complementTopScalars I)) :
    Nontrivial (moduleSpecΓFunctor.obj
      ((Scheme.Modules.pullback (quotientSpecMap A I)).obj (puncturedPushforward A I))) := by
  let := isQuasicoherent_puncturedPushforward A I hI
  let : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  let φ : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
  let e : (ModuleCat.extendScalars φ.hom).obj (ModuleCat.of A A) ≅
      moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (quotientSpecMap A I)).obj
        (puncturedPushforward A I)) :=
    (ModuleCat.extendScalars φ.hom).mapIso (puncturedSectionsIso A I hb) ≪≫
      quasicoherentPullbackSectionsIso (CommRingCat.of A) (CommRingCat.of (A ⧸ I)) φ
        (puncturedPushforward A I)
  obtain ⟨x, y, hxy⟩ : Nontrivial ((ModuleCat.extendScalars φ.hom).obj (ModuleCat.of A A)) :=
    (TensorProduct.rid A (A ⧸ I)).toEquiv.nontrivial
  exact ⟨e.hom x, e.hom y, fun h =>
    hxy ((ConcreteCategory.bijective_of_isIso e.hom).injective h)⟩

/-- **The target of the base-change comparison is zero.**  The base change of `U` is empty, so
every module on it has only the zero section. -/
theorem subsingleton_baseChanged_sections
    (N : ((quotientSpecMap A I ⁻¹ᵁ complementZeroLocus A I) : Scheme.{u}).Modules) :
    Subsingleton (moduleSpecΓFunctor.obj
      ((Scheme.Modules.pushforward
        (quotientSpecMap A I ⁻¹ᵁ complementZeroLocus A I).ι).obj N)) :=
  Stacks.Modules.subsingleton_sections_of_isEmpty _ N _

/-- **The base-change comparison fails.**  For `j : U ⟶ Spec A` the inclusion of
`U = Spec A ∖ V(I)`, with `I` finitely generated and proper and `A ⟶ Γ(U, 𝒪_U)` bijective, the
canonical morphism `g^*(j_*𝒪_U) ⟶ j'_*((g')^*𝒪_U)` along the closed immersion
`g : Spec (A/I) ⟶ Spec A` is **not** an isomorphism, although `j` is quasi-compact and
quasi-separated and `𝒪_U` is quasi-coherent.

Its source has global sections `(A/I) ⊗_A A = A/I ≠ 0` and its target has none at all, the
fibre `U ×_{Spec A} Spec (A/I)` being empty. -/
theorem not_isIso_baseChangeNatTrans (hI : I.FG) (hIne : I ≠ ⊤)
    (hb : Function.Bijective (complementTopScalars I)) :
    ¬ IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
        (isPullback_morphismRestrict (quotientSpecMap A I) (complementZeroLocus A I)).w).app
      (puncturedUnit A I)) := by
  intro hiso
  have hsub := subsingleton_baseChanged_sections A I
    ((Scheme.Modules.pullback (quotientSpecMap A I ∣_ complementZeroLocus A I)).obj
      (puncturedUnit A I))
  obtain ⟨x, y, hxy⟩ := nontrivial_pullback_puncturedPushforward_sections A I hI hIne hb
  exact hxy (((ConcreteCategory.bijective_of_isIso
    (moduleSpecΓFunctor.map ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
        (isPullback_morphismRestrict (quotientSpecMap A I)
          (complementZeroLocus A I)).w).app (puncturedUnit A I)))).injective)
    (hsub.elim _ _))

end General

/-! ### A concrete ring of depth two: `k[t][X]` at the ideal `(X, t)` -/

/-- The base field, `ℚ` lifted to the universe of the schemes. -/
abbrev counterexampleField : Type u := ULift.{u} ℚ

/-- The coefficient ring `k[t]`. -/
abbrev counterexampleCoeffs : Type u := Polynomial counterexampleField.{u}

/-- The ring `k[t][X]` of the counterexample. -/
abbrev counterexampleRing : Type u := Polynomial counterexampleCoeffs.{u}

/-- The ideal `(X, t)` of `k[t][X]`, generated by a regular sequence of length two. -/
def counterexampleIdeal : Ideal counterexampleRing.{u} :=
  Ideal.span {(X : counterexampleRing.{u}), C (X : counterexampleCoeffs.{u})}

/-- The submodule `X · R[X]` of `R[X]` is the ideal generated by `X`. -/
theorem smul_top_X_eq_span (R : Type u) [CommRing R] :
    (X : R[X]) • (⊤ : Submodule R[X] R[X]) = Ideal.span {(X : R[X])} := by
  rw [← Submodule.ideal_span_singleton_smul]
  simp

/-- **A nonzero constant is a nonzerodivisor modulo `X`.**  For `R` a domain and `c ≠ 0` in `R`,
multiplication by `C c` is injective on `R[X]/XR[X]`: a polynomial lies in `XR[X]` exactly when
its constant coefficient vanishes, and the constant coefficient of `C c * p` is `c * p(0)`. -/
theorem isSMulRegular_C_of_quotSMulTop_X (R : Type u) [CommRing R] [IsDomain R] (c : R)
    (hc : c ≠ 0) : IsSMulRegular (QuotSMulTop (X : R[X]) R[X]) (C c) := by
  intro a b hab
  obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  have key (r : R[X]) : r ∈ (X : R[X]) • (⊤ : Submodule R[X] R[X]) ↔ r.coeff 0 = 0 := by
    rw [smul_top_X_eq_span, Ideal.mem_span_singleton, X_dvd_iff]
  have hab' : (C c * p - C c * q).coeff 0 = 0 :=
    (key _).mp ((Submodule.Quotient.eq _).mp hab)
  refine (Submodule.Quotient.eq _).mpr ((key _).mpr ?_)
  rw [← mul_sub, coeff_C_mul] at hab'
  exact (mul_eq_zero.mp hab').resolve_left hc

/-- `X, t` is a weakly regular sequence on `k[t][X]`. -/
theorem isWeaklyRegular_counterexamplePair :
    IsWeaklyRegular counterexampleRing.{u}
      [(X : counterexampleRing.{u}), C (X : counterexampleCoeffs.{u})] := by
  rw [isWeaklyRegular_cons_iff]
  refine ⟨fun p q h => mul_left_cancel₀ (X_ne_zero (R := counterexampleCoeffs.{u})) h, ?_⟩
  rw [isWeaklyRegular_cons_iff]
  exact ⟨isSMulRegular_C_of_quotSMulTop_X counterexampleCoeffs.{u}
    (X : counterexampleCoeffs.{u}) X_ne_zero, by simp⟩

/-- The ideal `(X, t)` of `k[t][X]` has depth at least two. -/
theorem two_le_depth_counterexampleIdeal :
    (2 : ℕ∞) ≤ Module.depth counterexampleRing.{u} counterexampleIdeal.{u}
      counterexampleRing.{u} := by
  have h := Stacks.Depth.ModNonzerodivisor.length_le_depth_of_isWeaklyRegular
    (M := counterexampleRing.{u}) counterexampleIdeal.{u}
    (rs := [(X : counterexampleRing.{u}), C (X : counterexampleCoeffs.{u})])
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Ideal.subset_span (by simp))
    isWeaklyRegular_counterexamplePair
  simpa using h

/-- Evaluation of `k[t][X]` at `X = 0` and then at `t = 0`. -/
def evalAtOrigin : counterexampleRing.{u} →+* counterexampleField.{u} :=
  (evalRingHom (0 : counterexampleField.{u})).comp
    (evalRingHom (0 : counterexampleCoeffs.{u}))

/-- The ideal `(X, t)` of `k[t][X]` is proper: both generators vanish at the origin. -/
theorem counterexampleIdeal_ne_top : counterexampleIdeal.{u} ≠ ⊤ := by
  have hle : counterexampleIdeal.{u} ≤ RingHom.ker evalAtOrigin.{u} := by
    rw [counterexampleIdeal, Ideal.span_le]
    rintro r (rfl | rfl) <;> simp [RingHom.mem_ker, evalAtOrigin]
  intro h
  have h1 : (1 : counterexampleRing.{u}) ∈ RingHom.ker evalAtOrigin.{u} :=
    hle (h ▸ Submodule.mem_top)
  rw [RingHom.mem_ker, map_one] at h1
  exact one_ne_zero h1

/-- The ideal `(X, t)` of `k[t][X]` is finitely generated. -/
theorem counterexampleIdeal_fg : counterexampleIdeal.{u}.FG :=
  Submodule.fg_span (Set.toFinite _)

/-- **Hartogs for `k[t][X]`**: the restriction `k[t][X] ⟶ Γ(U, 𝒪_U)` to the complement of
`V(X, t)` is bijective, the depth of `(X, t)` being at least two. -/
theorem bijective_complementTopScalars_counterexample :
    Function.Bijective (complementTopScalars counterexampleIdeal.{u}) :=
  bijective_complementTopScalars_of_depth_ge_two counterexampleRing.{u} counterexampleIdeal.{u}
    counterexampleIdeal_ne_top two_le_depth_counterexampleIdeal

/-! ### The base-change obstruction behind Stacks 03LC part (2) -/

/-- **The base-change obstruction behind Stacks 03LC part (2).**  The equivalences of
[Stacks, Tag 03DX] are *not* compatible with pushforward in general, and the source explains why
by this: there is a cartesian square of schemes

```
X' --g'--> X
|f'        |f
S' --g-->  S
```

with `f` quasi-compact and quasi-separated and a quasi-coherent module `𝓕` on `X` for which the
canonical base-change morphism `g^*(f_*𝓕) ⟶ f'_*((g')^*𝓕)` is not an isomorphism.  Were the
association `𝓕 ↦ 𝓕^a` of [Stacks, Tag 03DX] compatible with pushforward over the big sites,
formation of `f_*𝓕` would commute with every base change, which this forbids.

The witness is the complement `U` of `V(X, t)` in `Spec k[t][X]` with `k = ULift ℚ`, its
structure sheaf, and base change along the closed immersion
`Spec k[t][X]/(X, t) ⟶ Spec k[t][X]` — the punctured affine plane over a point of its puncture,
which is the source's example.  The morphism `g` is a closed immersion, hence not flat; under a
*flat* base change the comparison is an isomorphism by [Stacks, Tag 02KH] in degree zero.

Part (2) itself is
`Stacks.Examples.QcohPushforward.exists_isEmpty_iso_bigPushforward_associatedModule`
(`StacksFrontier/Examples/QuasiCoherentPushforward/BigSitePushforward.lean`). -/
theorem exists_not_isIso_baseChangeNatTrans :
    ∃ (X S X' S' : Scheme.{u}) (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
      (H : IsPullback g' f' f g) (F : X.Modules),
        QuasiCompact f ∧ QuasiSeparated f ∧ F.IsQuasicoherent ∧
          ¬ IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans H.w).app F) := by
  refine ⟨puncturedScheme counterexampleRing.{u} counterexampleIdeal.{u},
    Spec (CommRingCat.of counterexampleRing.{u}),
    (quotientSpecMap counterexampleRing.{u} counterexampleIdeal.{u} ⁻¹ᵁ
      complementZeroLocus counterexampleRing.{u} counterexampleIdeal.{u} : Scheme.{u}),
    Spec (CommRingCat.of (counterexampleRing.{u} ⧸ counterexampleIdeal.{u})),
    (complementZeroLocus counterexampleRing.{u} counterexampleIdeal.{u}).ι,
    quotientSpecMap counterexampleRing.{u} counterexampleIdeal.{u},
    (quotientSpecMap counterexampleRing.{u} counterexampleIdeal.{u} ⁻¹ᵁ
      complementZeroLocus counterexampleRing.{u} counterexampleIdeal.{u}).ι,
    quotientSpecMap counterexampleRing.{u} counterexampleIdeal.{u} ∣_
      complementZeroLocus counterexampleRing.{u} counterexampleIdeal.{u},
    isPullback_morphismRestrict _ _,
    puncturedUnit counterexampleRing.{u} counterexampleIdeal.{u},
    quasiCompact_punctured_ι counterexampleRing.{u} counterexampleIdeal.{u}
      counterexampleIdeal_fg, inferInstance, inferInstance, ?_⟩
  exact not_isIso_baseChangeNatTrans counterexampleRing.{u} counterexampleIdeal.{u}
    counterexampleIdeal_fg counterexampleIdeal_ne_top
    bijective_complementTopScalars_counterexample

end Stacks.Examples.QcohPushforward

end
