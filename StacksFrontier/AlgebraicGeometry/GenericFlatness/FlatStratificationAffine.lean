module

public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningStratification.AffineFlatness
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatStratificationQcqs
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineIdealSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The flattening stratification of an affine base, read on ideals

Let `A → B` be a ring homomorphism of finite presentation and let `M` be a finitely presented
`B`-module. Stacks 0ASY stratifies `Spec A` so that `M` becomes flat over each stratum; this file
states that stratification as a statement about ideals of `A` and modules over quotients and
localizations of `A`, and derives it from the geometric statement
`AlgebraicGeometry.exists_flat_stratification`.

The chain of closed subschemes and the three side conditions on it convert through the dictionary
of `StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineIdealSheaf`, which turns
`(Spec A).IdealSheafData` into `Ideal A`. The flatness clause does not convert that way, because
the stratum is only a *quasi-affine* open of the closed subscheme `Spec (A ⧸ K)`: it is the
complement of the zero locus of the next ideal `J`, and that complement has no ring of its own.
What it does have is an affine open cover, by the basic opens `D(a)` for `a ∈ J`, and `D(a)`
inside `Spec (A ⧸ K)` is the spectrum of the localization `(A ⧸ K)_a`. So the flatness clause is
read on those basic opens, one element `a ∈ J` at a time, which loses nothing: those basic opens
cover the stratum.

## Main results

* `AlgebraicGeometry.exists_specStratum_point`: the spectrum of `(A ⧸ K)_a` maps to the stratum
  cut out by `K` and `J`, for any `a ∈ J`, and its composite down to `Spec A` is the spectrum of
  `A → (A ⧸ K)_a`.
* `AlgebraicGeometry.flat_of_isFlatOver_specStratum`: the flatness of a quasi-coherent module
  over such a stratum, read as flatness of an extension of scalars to `(A ⧸ K)_a`.
* `AlgebraicGeometry.exists_flat_stratification_ideals`: **Stacks 0ASY, read
  ring-theoretically.** The tag itself is carried by the geometric statement
  `AlgebraicGeometry.exists_flat_stratification`; this is that statement transported along the
  dictionary, so it carries no attribute of its own.
* `AlgebraicGeometry.flat_tensorQuotient_of_flat_tensor`: base change from `A` to a localization
  of `A ⧸ K` is base change of the reduction `M ⧸ K M` from `A ⧸ K`.
* `AlgebraicGeometry.exists_flat_stratification_ideals_quotient`: the same chain with the
  flatness clause stated over `A ⧸ K i`, which is the shape
  `Stacks.flat_of_least_flattening_of_flat_away` asks of its hypothesis `hU`.

## Implementation notes

The localization `(A ⧸ K)_a` is not named but quantified over: the conclusion holds for every
ring `L` which is an `A`-algebra through `A ⧸ K` and a localization of `A ⧸ K` away from the
image of `a`. That is the `IsLocalization` idiom, and it is what lets a consumer use its own
model of the localization — `Localization.Away (Ideal.Quotient.mk K a)`, say, which is the shape
`Stacks.flat_of_least_flattening_of_flat_away` asks for.

The passage from the stratum to its basic open is `AlgebraicGeometry.exists_specStratum_point`
together with `AlgebraicGeometry.isFlatOver_pullback_snd_comp_of_isFlatOver`: flatness over a
stratum is inherited by any further base change of it, so a morphism *into* the stratum is all
that is needed and the basic open need not be identified with the stratum's own structure. The
morphism is produced by the universal property of the open immersion
`AlgebraicGeometry.IsOpenImmersion.lift`; the hypothesis it asks for, that the image lies in the
open, holds because the image of `a` is a unit in `L` and a unit lies in no prime.

Flatness over the affine stratum is then read on modules by
`AlgebraicGeometry.isFlatOver_affine_baseChange_iff`, and the sections of the associated sheaf of
`M` are `M` again by Mathlib's `AlgebraicGeometry.tilde.toTildeΓNatIso`.

The two rings `A`, `B` and the localization `L` share one universe, because the spectrum of each
has to be an object of a single `Scheme.{u}`; that is the constraint recorded in the
implementation notes of `StacksFrontier.RingTheory.Flat.EtaleLocalizationProjectiveBaseChange`,
where `AlgebraicGeometry.tilde` of a module over `R : CommRingCat.{u}` is a `Scheme.{u}`-module
only for a module in `Type u`. The *module* does not join them. It is replaced at the top of the
proof of `AlgebraicGeometry.exists_flat_stratification_ideals` by Mathlib's
`Module.Finite.repr B M`, a model of `M` in the universe of `B` — a finite module over `B` is a
quotient of some `Bⁿ`, which is where that model comes from — and the flatness conclusion
travels back along `Module.Finite.reprEquiv` by base change, since `L ⊗[A] -` carries an
`A`-linear equivalence to an `L`-linear one. So `M` keeps its own universe, which is what the
proof of Stacks 05U9 needs: there the base is the local ring of Situation 0AT0 and the module is
one over a localized polynomial algebra over it, in a larger universe.

## References

* [Stacks Project, Tag 0ASY](https://stacks.math.columbia.edu/tag/0ASY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct
open Stacks.LocalCohomology (specIdealSheaf coe_support_specIdealSheaf)

universe u v

namespace AlgebraicGeometry

/-! ### The locally closed strata of an affine base -/

/-- The stratum of `Spec A` cut out by a pair of ideals `K` and `J`: the open complement of the
zero locus of `J` inside the closed subscheme cut out by `K`, together with its morphism down to
`Spec A`. This is the stratum `S_i ∖ S_{i+1}` of `AlgebraicGeometry.exists_flat_stratification`
when `S_i` and `S_{i+1}` are cut out by `K` and `J`. -/
noncomputable def specStratumι (A : Type u) [CommRing A] (K J : Ideal A) :
    ((specIdealSheaf A K).subschemeι ⁻¹ᵁ (specIdealSheaf A J).support.compl).toScheme ⟶
      Spec (CommRingCat.of A) :=
  ((specIdealSheaf A K).subschemeι ⁻¹ᵁ (specIdealSheaf A J).support.compl).ι ≫
    (specIdealSheaf A K).subschemeι

/-- **The basic opens of the closed subscheme cover the stratum.** For `a ∈ J` and `L` a
localization of `A ⧸ K` away from the image of `a`, the spectrum of `L` maps to the stratum cut
out by `K` and `J`, and its composite down to `Spec A` is the spectrum of the structure map
`A → L`.

Geometrically: `Spec L` is the basic open `D(a)` of the closed subscheme `Spec (A ⧸ K)`, and `a`
lies in `J`, so `D(a)` misses the zero locus of `J` and therefore lands in the stratum. -/
theorem exists_specStratum_point {A : Type u} [CommRing A] {K J : Ideal A} {a : A} (ha : a ∈ J)
    (L : Type u) [CommRing L] [Algebra A L] [Algebra (A ⧸ K) L]
    [IsScalarTower A (A ⧸ K) L] [IsLocalization.Away (Ideal.Quotient.mk K a) L] :
    ∃ b : Spec (CommRingCat.of L) ⟶
        ((specIdealSheaf A K).subschemeι ⁻¹ᵁ (specIdealSheaf A J).support.compl).toScheme,
      b ≫ specStratumι A K J = Spec.map (CommRingCat.ofHom (algebraMap A L)) := by
  obtain ⟨e, he⟩ := exists_subschemeIso_specIdealSheaf (A := A) K
  have hcomp : (Spec.map (CommRingCat.ofHom (algebraMap (A ⧸ K) L)) ≫ e.inv) ≫
      (specIdealSheaf A K).subschemeι = Spec.map (CommRingCat.ofHom (algebraMap A L)) := by
    rw [he, Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp]
    congr 1
    ext x
    exact (IsScalarTower.algebraMap_apply A (A ⧸ K) L x).symm
  set g := Spec.map (CommRingCat.ofHom (algebraMap (A ⧸ K) L)) ≫ e.inv
  have hunit : IsUnit (algebraMap A L a) := by
    rw [IsScalarTower.algebraMap_apply A (A ⧸ K) L a]
    exact IsLocalization.map_units L
      (⟨Ideal.Quotient.mk K a, Submonoid.mem_powers _⟩ :
        Submonoid.powers (Ideal.Quotient.mk K a))
  have hrange : Set.range g.base ⊆
      Set.range ((specIdealSheaf A K).subschemeι ⁻¹ᵁ
        (specIdealSheaf A J).support.compl).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change _ ∈ (((specIdealSheaf A K).subschemeι ⁻¹ᵁ (specIdealSheaf A J).support.compl :
      (specIdealSheaf A K).subscheme.Opens) : Set (specIdealSheaf A K).subscheme)
    rw [Scheme.Hom.coe_preimage]
    have hx : (specIdealSheaf A K).subschemeι.base (g.base x) =
        (Spec.map (CommRingCat.ofHom (algebraMap A L))).base x := by
      conv_rhs => rw [← hcomp]
      rfl
    change (specIdealSheaf A K).subschemeι.base _ ∈
      (((specIdealSheaf A J).support.compl : (Spec (CommRingCat.of A)).Opens) :
        Set (Spec (CommRingCat.of A)))
    rw [hx, TopologicalSpace.Closeds.coe_compl, coe_support_specIdealSheaf]
    intro hmem
    exact x.isPrime.ne_top
      (x.asIdeal.eq_top_of_isUnit_mem ((PrimeSpectrum.mem_zeroLocus _ _).mp hmem ha) hunit)
  refine ⟨IsOpenImmersion.lift _ _ hrange, ?_⟩
  rw [specStratumι, ← Category.assoc, IsOpenImmersion.lift_fac, hcomp]

/-! ### Flatness over a stratum, read on modules -/

/-- **Flatness over a stratum of an affine base, read on modules.** Let `φ : A → B` be a ring
homomorphism, let `F` be a quasi-coherent module on `Spec B`, and suppose `F` is flat over the
stratum of `Spec A` cut out by a pair of ideals `K` and `J`. Then for every `a ∈ J` and every
localization `L` of `A ⧸ K` away from the image of `a`, the extension of scalars of the sections
of `F` to `L` is a flat `L`-module.

This restricts the flatness clause of `AlgebraicGeometry.exists_flat_stratification` to the
affine basic opens of the stratum, where
`AlgebraicGeometry.isFlatOver_affine_baseChange_iff` reads it on modules. -/
theorem flat_of_isFlatOver_specStratum {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : (Spec (CommRingCat.of B)).Modules) [F.IsQuasicoherent]
    {K J : Ideal A} {a : A} (ha : a ∈ J)
    (L : Type u) [CommRing L] [Algebra A L] [Algebra (A ⧸ K) L]
    [IsScalarTower A (A ⧸ K) L] [IsLocalization.Away (Ideal.Quotient.mk K a) L]
    (hflat : IsFlatOver
        (pullback.snd (Spec.map (CommRingCat.ofHom φ)) (specStratumι A K J)).toLRSHom.toShHom
      ((Scheme.Modules.pullback
        (pullback.fst (Spec.map (CommRingCat.ofHom φ)) (specStratumι A K J))).obj F)) :
    Module.Flat L ((ModuleCat.extendScalars (algebraMap A L)).obj
      ((ModuleCat.restrictScalars φ).obj (moduleSpecΓFunctor.obj F))) := by
  obtain ⟨b, hb⟩ := exists_specStratum_point (K := K) (J := J) ha L
  have key := isFlatOver_pullback_snd_comp_of_isFlatOver (Spec.map (CommRingCat.ofHom φ)) F
    (specStratumι A K J) b hflat
  rw [hb] at key
  exact (isFlatOver_affine_baseChange_iff (CommRingCat.ofHom φ)
    (CommRingCat.ofHom (algebraMap A L)) F).mp key

/-! ### The stratification, read on ideals -/

/-- The morphism of affine schemes attached to an algebra of finite presentation is of finite
presentation. -/
theorem finitePresentation_specMap_algebraMap (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.FinitePresentation A B] :
    FinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
  FinitePresentation.mk
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2
      (RingHom.finitePresentation_algebraMap.2 ‹_›))
    inferInstance inferInstance

/-- The extension of scalars to `L` of the sections of the associated sheaf of `M`, restricted
along `A → B`, is the base change `L ⊗[A] M`. This is Mathlib's
`AlgebraicGeometry.tilde.toTildeΓNatIso` — the sections of the associated sheaf of `M` are `M`
— together with the identification of the action of `A` on `M` through `B` with its own
action. -/
private theorem flat_tensor_of_flat_extendScalars_tilde {A B L : Type u} [CommRing A]
    [CommRing B] [CommRing L] [Algebra A B] [Algebra A L] (M : Type u) [AddCommGroup M]
    [Module B M] [Module A M] [IsScalarTower A B M]
    (h : Module.Flat L ((ModuleCat.extendScalars (algebraMap A L)).obj
      ((ModuleCat.restrictScalars (algebraMap A B)).obj
        ((moduleSpecΓFunctor (R := CommRingCat.of B)).obj (tilde (ModuleCat.of B M)))))) :
    Module.Flat L (L ⊗[A] M) := by
  have hobj : (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B M) =
      ModuleCat.of A M :=
    congrArg (fun i : Module A M => @ModuleCat.of A _ M _ i)
      (Module.compHom_algebraMap A B M)
  have eΓ : (ModuleCat.restrictScalars (algebraMap A B)).obj
      ((moduleSpecΓFunctor (R := CommRingCat.of B)).obj (tilde (ModuleCat.of B M))) ≅
        ModuleCat.of A M :=
    (ModuleCat.restrictScalars (algebraMap A B)).mapIso
        ((tilde.toTildeΓNatIso (R := CommRingCat.of B)).app (ModuleCat.of B M)).symm ≪≫
      eqToIso hobj
  exact (Module.Flat.equiv_iff
    (((ModuleCat.extendScalars (algebraMap A L)).mapIso eΓ ≪≫
      extendScalarsAlgebraMapLinearIso (A := A) (B := L) (ModuleCat.of A M)).toLinearEquiv)).mp h

/-- **Stacks 0ASY, read ring-theoretically.** Let `A → B` be an algebra of finite presentation
and let `M` be a finitely presented `B`-module. Then `A` carries a finite ascending chain of
finitely generated ideals

`K 0 ⊆ K 1 ⊆ ⋯ ⊆ K t = (1)`

whose first term is contained in the nilradical, such that for every `i` and every `a ∈ K (i+1)`
the base change of `M` to any localization `L` of `A ⧸ K i` away from the image of `a` is a flat
`L`-module.

The ideal `K i` cuts out the closed subscheme `S_i` of
`AlgebraicGeometry.exists_flat_stratification`: the chain being ascending is the chain of
subschemes being descending, `K 0 ⊆ nilradical A` is `S₀ ⊆ Spec A` a thickening, and
`K t = (1)` is `S_t = ∅`. The spectra of the localizations `(A ⧸ K i)_a` for `a ∈ K (i+1)` are
the affine basic opens covering the locally closed stratum `S_i ∖ S_{i+1}`, so the flatness
clause here is the flatness clause there.

The module is in its own universe: only the rings `A`, `B` and the localization `L` are tied to
one universe, by the scheme category their spectra live in. See the implementation notes.

This carries no tag: 0ASY is carried by `AlgebraicGeometry.exists_flat_stratification`, of which
this is a restatement. -/
@[ega "IV 6.9.3" "special case",
  ega "IV 8.9.5" "Affine source and base",
  sga "6 XIII 1.13" "(i) ⇒ (ii), special case"]
theorem exists_flat_stratification_ideals {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FinitePresentation A B] (M : Type v) [AddCommGroup M] [Module B M] [Module A M]
    [IsScalarTower A B M] [Module.FinitePresentation B M] :
    ∃ (t : ℕ) (K : Fin (t + 1) → Ideal A),
      K 0 ≤ nilradical A ∧
      (∀ i, (K i).FG) ∧
      (∀ i : Fin t, K (Fin.castSucc i) ≤ K (Fin.succ i)) ∧
      K (Fin.last t) = ⊤ ∧
      ∀ (i : Fin t) (a : A), a ∈ K (Fin.succ i) →
        ∀ (L : Type u) [CommRing L] [Algebra A L] [Algebra (A ⧸ K (Fin.castSucc i)) L]
          [IsScalarTower A (A ⧸ K (Fin.castSucc i)) L]
          [IsLocalization.Away (Ideal.Quotient.mk (K (Fin.castSucc i)) a) L],
          Module.Flat L (L ⊗[A] M) := by
  classical
  have : Module.FinitePresentation B (Module.Finite.repr B M) :=
    Module.FinitePresentation.of_equiv (Module.Finite.reprEquiv B M).symm
  have hM := (tilde_isFinitePresentation_iff (R := CommRingCat.of B)
    (ModuleCat.of B (Module.Finite.repr B M))).2 ‹_›
  obtain ⟨t, I, hthick, hft, hmono, htop, hflat⟩ :=
    exists_flat_stratification (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (finitePresentation_specMap_algebraMap A B)
      (tilde (ModuleCat.of B (Module.Finite.repr B M)))
  choose K hK using fun i => exists_eq_specIdealSheaf A (I i)
  refine ⟨t, K, ?_, fun i => ?_, fun i => ?_, ?_, fun i a ha L _ _ _ _ _ => ?_⟩
  · exact isThickening_subschemeι_specIdealSheaf_iff.mp (hK 0 ▸ hthick)
  · exact isFiniteType_specIdealSheaf_iff.mp (hK i ▸ hft i)
  · exact specIdealSheaf_le_iff.mp (hK (Fin.castSucc i) ▸ hK (Fin.succ i) ▸ hmono i)
  · exact specIdealSheaf_eq_top_iff.mp (hK (Fin.last t) ▸ htop)
  · have hstratum := hflat i
    rw [hK (Fin.castSucc i), hK (Fin.succ i)] at hstratum
    have := flat_tensor_of_flat_extendScalars_tilde (Module.Finite.repr B M)
      (flat_of_isFlatOver_specStratum (algebraMap A B)
        (tilde (ModuleCat.of B (Module.Finite.repr B M)))
        (K := K (Fin.castSucc i)) (J := K (Fin.succ i)) ha L hstratum)
    exact Module.Flat.of_linearEquiv (AlgebraTensorModule.congr (LinearEquiv.refl L L)
      ((Module.Finite.reprEquiv B M).restrictScalars A)).symm

/-- **The base change of `M` to a localization of `A ⧸ K` is the base change of the reduction
`M ⧸ K M`.** Tensoring up from `A` factors through `A ⧸ K`, and `(A ⧸ K) ⊗[A] M` is `M ⧸ K M`. -/
theorem flat_tensorQuotient_of_flat_tensor {A L : Type u} [CommRing A] [CommRing L]
    (K : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] [Algebra A L]
    [Algebra (A ⧸ K) L] [IsScalarTower A (A ⧸ K) L] (h : Module.Flat L (L ⊗[A] M)) :
    Module.Flat L (L ⊗[A ⧸ K] (M ⧸ (K • (⊤ : Submodule A M)))) := by
  have e₁ : ((A ⧸ K) ⊗[A] M) ≃ₗ[A ⧸ K] (M ⧸ (K • (⊤ : Submodule A M))) :=
    (TensorProduct.quotTensorEquivQuotSMul M K).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  exact (Module.Flat.equiv_iff
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange A (A ⧸ K) L L M).symm.trans
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl L L) e₁))).mp h

/-- **Stacks 0ASY, read ring-theoretically over the quotients.** The chain of
`AlgebraicGeometry.exists_flat_stratification_ideals` with the flatness clause stated over the
quotient `A ⧸ K i` rather than over `A`: the reduction `M ⧸ (K i) M` becomes flat after
localizing `A ⧸ K i` away from the image of any `a ∈ K (i+1)`.

This is the shape `Stacks.flat_of_least_flattening_of_flat_away` asks of its hypothesis `hU`,
with base ring `A ⧸ K i`, module `M ⧸ (K i) M` and the family of elements the images of
generators of `K (i+1)`. Only an `A ⧸ K i`-algebra structure on `L` is required, so
`Localization.Away (Ideal.Quotient.mk (K i) a)` may be used directly.

This carries no tag: 0ASY is carried by `AlgebraicGeometry.exists_flat_stratification`. -/
theorem exists_flat_stratification_ideals_quotient {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.FinitePresentation A B] (M : Type v) [AddCommGroup M] [Module B M]
    [Module A M] [IsScalarTower A B M] [Module.FinitePresentation B M] :
    ∃ (t : ℕ) (K : Fin (t + 1) → Ideal A),
      K 0 ≤ nilradical A ∧
      (∀ i, (K i).FG) ∧
      (∀ i : Fin t, K (Fin.castSucc i) ≤ K (Fin.succ i)) ∧
      K (Fin.last t) = ⊤ ∧
      ∀ (i : Fin t) (a : A), a ∈ K (Fin.succ i) →
        ∀ (L : Type u) [CommRing L] [Algebra (A ⧸ K (Fin.castSucc i)) L]
          [IsLocalization.Away (Ideal.Quotient.mk (K (Fin.castSucc i)) a) L],
          Module.Flat L (L ⊗[A ⧸ K (Fin.castSucc i)]
            (M ⧸ (K (Fin.castSucc i) • (⊤ : Submodule A M)))) := by
  obtain ⟨t, K, h0, hfg, hmono, htop, hflat⟩ :=
    exists_flat_stratification_ideals (A := A) (B := B) M
  refine ⟨t, K, h0, hfg, hmono, htop, fun i a ha L _ _ _ => ?_⟩
  let : Algebra A L := ((algebraMap (A ⧸ K (Fin.castSucc i)) L).comp
    (algebraMap A (A ⧸ K (Fin.castSucc i)))).toAlgebra
  have : IsScalarTower A (A ⧸ K (Fin.castSucc i)) L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact flat_tensorQuotient_of_flat_tensor _ M (hflat i a ha L)

end AlgebraicGeometry

end
