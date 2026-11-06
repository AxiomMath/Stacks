module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.MapsToAlgebraicSpaceTruncations
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SectionsFiniteProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartCoverDensity

/-!
# Sections of an algebraic space over a finite algebra over a complete local ring

Let `R` be a Noetherian complete local ring and `A` a finite `R`-algebra. **Stacks 0AQH**, read on
truncations (`AlgebraicGeometry.FormalSpace.existsUnique_section_of_compatible_truncations`), says
that a section of an algebraic space over `Spec` of a complete local ring is the same thing as a
compatible family of sections over the truncations. This file extends that to `Spec A`, with the
truncations `Spec (A ⧸ 𝔪 ^ (n + 1) A)` cut out by the powers of the maximal ideal of `R`.

By **Stacks 0325** `A` is a finite product `Π i, A i` of Noetherian complete local rings, each
finite over `R`; the ideals `𝔪 ^ (n + 1) A i` are cofinal with the powers of the maximal ideal of
`A i`, because the closed fibre `A i ⧸ 𝔪 A i` is Artinian; and a section over the spectrum of a
finite product is a family of sections over the spectra of the factors
(`AlgebraicGeometry.BigFppfOver.existsUnique_section_of_pi`).

This is what the descent step of **Stacks 07X8** needs: a finite étale extension `R ⊆ R'` makes
`R' ⊗_R R'` and `R' ⊗_R R' ⊗_R R'` finite `R`-algebras which are not local.

## Main results

* `AlgebraicGeometry.FormalSpace.existsUnique_section_of_compatible_truncations_of_finite`: a
  compatible family of sections over the truncations `Spec (A ⧸ 𝔪 ^ (n + 1) A)` comes from a
  unique section over `Spec A`.

## References

* [Stacks Project, Tag 0325](https://stacks.math.columbia.edu/tag/0325)
* [Stacks Project, Tag 0AQH](https://stacks.math.columbia.edu/tag/0AQH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- In a finite product of rings, an element of the extension of an ideal of a ring `R` mapping to
the product, supported on a single factor, lies in the extension. -/
private lemma single_mem_map_of_mem {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι]
    {T : ι → Type u} [∀ i, CommRing (T i)] (f : R →+* Π i, T i) (I : Ideal R) (i : ι) {x : T i}
    (hx : x ∈ I.map ((Pi.evalRingHom T i).comp f)) : Pi.single i x ∈ I.map f := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r, hr, rfl⟩ := hy
    have : Pi.single i (((Pi.evalRingHom T i).comp f) r) = f r * Pi.single i 1 := by
      ext j
      by_cases hij : j = i
      · subst hij
        simp
      · simp [Pi.single_eq_of_ne hij]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem f hr)
  | zero => simp
  | add y z _ _ hy hz =>
    rw [Pi.single_add]
    exact Ideal.add_mem _ hy hz
  | smul c y _ hy =>
    rw [smul_eq_mul, Pi.single_mul]
    exact Ideal.mul_mem_left _ _ hy

/-- The extension of an ideal of `R` to a finite product of `R`-algebras is the product of its
extensions to the factors. -/
private lemma mem_map_iff_forall {R : Type u} [CommRing R] {ι : Type u} [Finite ι]
    {T : ι → Type u} [∀ i, CommRing (T i)] (f : R →+* Π i, T i) (I : Ideal R)
    (a : Π i, T i) : a ∈ I.map f ↔ ∀ i, a i ∈ I.map ((Pi.evalRingHom T i).comp f) := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨fun ha i => ?_, fun ha => ?_⟩
  · rw [← Ideal.map_map]
    exact Ideal.mem_map_of_mem _ ha
  · rw [← Finset.univ_sum_single a]
    exact Ideal.sum_mem _ fun i _ => single_mem_map_of_mem f I i (ha i)

/-- Transporting the `i`-th projection of a ring equivalence `A ≃+* Π i, Ai i` along an
identification of a scheme with `Spec A` gives the `i`-th projection of `Spec (Π i, Ai i)`. -/
private lemma spec_map_comp_inv_comp_spec_mapIso_hom {Z : Scheme.{u}} {A : Type u} [CommRing A]
    {ι : Type u} {Ai : ι → Type u} [∀ i, CommRing (Ai i)] (e : Z ≅ Spec (.of A))
    (ε : A ≃+* Π i, Ai i) (i : ι) :
    (Spec.map (CommRingCat.ofHom ((Pi.evalRingHom Ai i).comp ε.toRingHom)) ≫ e.inv) ≫
      (e ≪≫ Scheme.Spec.mapIso ε.symm.toCommRingCatIso.op).hom =
    Spec.map (CommRingCat.ofHom (Pi.evalRingHom Ai i)) := by
  change _ ≫ e.hom ≫ Spec.map (CommRingCat.ofHom ε.symm.toRingHom) = _
  rw [Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a
  simp

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **Stacks 0AQH, read on truncations, over a finite algebra.** Let `R` be a Noetherian complete
local ring, `A` a finite `R`-algebra and `X` an algebraic space over `S`. Let `T` be an object of
the site whose scheme is identified with `Spec A`, and `W n` objects whose schemes are identified
with `Spec (A ⧸ 𝔪 ^ (n + 1) A)`, mapping to `T` by the quotient maps and to each other
compatibly. Then a compatible family of sections of `X` over the `W n` is the restriction of a
unique section over `T`. -/
public theorem existsUnique_section_of_compatible_truncations_of_finite
    {R : Type u} [CommRing R] [IsLocalRing R] (hR : IsNoetherianCompleteLocalRing R)
    {A : Type u} [CommRing A] [Algebra R A] [Module.Finite R A]
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (T : BigFppfOver B S hS) (eT : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of A))
    (W : ℕ → BigFppfOver B S hS)
    (eW : ∀ n, (BigFppfOver.toScheme B S hS).obj (W n) ≅
      Spec (.of (A ⧸ (maximalIdeal R ^ (n + 1)).map (algebraMap R A))))
    (ι : ∀ n, W n ⟶ T)
    (hι : ∀ n, (BigFppfOver.toScheme B S hS).map (ι n) ≫ eT.hom =
      (eW n).hom ≫ Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk ((maximalIdeal R ^ (n + 1)).map (algebraMap R A)))))
    (τ : ∀ n, W n ⟶ W (n + 1)) (hτ : ∀ n, τ n ≫ ι (n + 1) = ι n)
    (x : ∀ n, X.obj (op (W n))) (hx : ∀ n, X.map (τ n).op (x (n + 1)) = x n) :
    ∃! y : X.obj (op T), ∀ n, X.map (ι n).op y = x n := by
  classical
  -- the product decomposition of `A`
  obtain ⟨m, A₀, _, hA₀, ⟨e₀⟩⟩ := finite_isProduct_isNoetherianCompleteLocalRing (S := A) hR
  let ιt : Type u := ULift.{u} (Fin m)
  let Ai : ιt → Type u := fun i => A₀ i.down
  let e : A ≃+* Π i, Ai i := e₀.trans (RingEquiv.piCongrLeft A₀ Equiv.ulift).symm
  have hAi : ∀ i, IsNoetherianCompleteLocalRing (Ai i) := fun i => hA₀ i.down
  have : ∀ i, IsLocalRing (Ai i) := fun i => (hAi i).isLocal
  let pr : ∀ i, A →+* Ai i := fun i => (Pi.evalRingHom Ai i).comp e.toRingHom
  have hpr : ∀ i, Function.Surjective (pr i) := fun i =>
    (Function.surjective_eval i).comp e.surjective
  let : ∀ i, Algebra R (Ai i) := fun i => ((pr i).comp (algebraMap R A)).toAlgebra
  have : ∀ i, Module.Finite R (Ai i) := fun i => by
    let : Algebra A (Ai i) := (pr i).toAlgebra
    have : IsScalarTower R A (Ai i) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have : Module.Finite A (Ai i) := Module.Finite.of_surjective
      (Algebra.linearMap A (Ai i)) (hpr i)
    exact Module.Finite.trans A (Ai i)
  have : ∀ i, IsLocalHom (algebraMap R (Ai i)) := fun i =>
    ((IsLocalRing.local_hom_TFAE (algebraMap R (Ai i))).out 1 5).mpr
      (IsLocalRing.eq_maximalIdeal
        (Ideal.IsMaximal.under R (IsLocalRing.maximalIdeal (Ai i))))
  -- the ideals of the truncations
  let J : ℕ → Ideal A := fun n => (maximalIdeal R ^ (n + 1)).map (algebraMap R A)
  let Ji : ∀ i, ℕ → Ideal (Ai i) := fun i n => (maximalIdeal R ^ (n + 1)).map (algebraMap R (Ai i))
  have hJm : ∀ i n, Ji i n ≤ maximalIdeal (Ai i) := fun i n =>
    le_trans (Ideal.map_mono (Ideal.pow_le_self n.succ_ne_zero)) (IsLocalRing.map_maximalIdeal_le _)
  have hJmono : ∀ i n, Ji i (n + 1) ≤ Ji i n := fun i n =>
    Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ _))
  have hJ₂ : ∀ i k, ∃ n, Ji i n ≤ maximalIdeal (Ai i) ^ k := fun i k => ⟨k, by
    refine le_trans ?_ (Ideal.pow_le_pow_right (Nat.le_succ k))
    show (maximalIdeal R ^ (k + 1)).map (algebraMap R (Ai i)) ≤ _
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le _) _⟩
  have hJ₁ : ∀ i n, ∃ k, maximalIdeal (Ai i) ^ k ≤ Ji i n := fun i n => by
    -- the closed fibre is Artinian, so its maximal ideal is nilpotent
    have hart := isArtinianRing_quotient_map_maximalIdeal (R := R) (S := Ai i)
    let N := (maximalIdeal R).map (algebraMap R (Ai i))
    have hN : N ≤ maximalIdeal (Ai i) := by
      simpa [N, Ji, pow_one] using hJm i 0
    have : IsLocalRing (Ai i ⧸ N) := IsLocalRing.of_surjective' (Ideal.Quotient.mk N)
      Ideal.Quotient.mk_surjective
    obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := Ai i ⧸ N)
    have hjac :
        (⊥ : Ideal (Ai i ⧸ N)).jacobson = (maximalIdeal (Ai i)).map (Ideal.Quotient.mk N) := by
      rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      exact (IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm
    have hk' : maximalIdeal (Ai i) ^ k ≤ N := by
      intro a ha
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have : Ideal.Quotient.mk N a ∈ ((maximalIdeal (Ai i)).map (Ideal.Quotient.mk N)) ^ k := by
        rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ ha
      rw [← hjac, hk] at this
      simpa using this
    refine ⟨k * (n + 1), ?_⟩
    rw [pow_mul]
    refine le_trans (Ideal.pow_right_mono hk' _) ?_
    simp [N, Ji, Ideal.map_pow]
  -- the quotients of `A` are the products of the quotients of the factors
  have hqJ : ∀ n i, (J n).map (pr i) = Ji i n := fun n i => by
    rw [Ideal.map_map]
    rfl
  let qi : ∀ n i, A ⧸ J n →+* Ai i ⧸ Ji i n := fun n i =>
    Ideal.quotientMap (Ji i n) (pr i) (Ideal.map_le_iff_le_comap.1 (hqJ n i).le)
  let qe : ∀ n, A ⧸ J n ≃+* Π i, Ai i ⧸ Ji i n := fun n =>
    RingEquiv.ofBijective (Pi.ringHom (qi n)) (by
      constructor
      · rw [injective_iff_map_eq_zero]
        intro a ha
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        rw [Ideal.Quotient.eq_zero_iff_mem]
        have hmem : e a ∈ (maximalIdeal R ^ (n + 1)).map (e.toRingHom.comp (algebraMap R A)) := by
          rw [mem_map_iff_forall]
          intro i
          have := congrFun ha i
          change Ideal.Quotient.mk (Ji i n) (pr i a) = 0 at this
          rw [Ideal.Quotient.eq_zero_iff_mem] at this
          exact this
        rw [← Ideal.map_map] at hmem
        exact Ideal.apply_mem_of_equiv_iff.1 hmem
      · intro b
        refine ⟨Ideal.Quotient.mk _ (e.symm fun i => (Ideal.Quotient.mk_surjective (b i)).choose),
          ?_⟩
        ext i
        show Ideal.Quotient.mk (Ji i n) (e (e.symm _) i) = b i
        rw [RingEquiv.apply_symm_apply]
        exact (Ideal.Quotient.mk_surjective (b i)).choose_spec)

  -- the factors and their truncations as objects of the site
  have hTA : B.Contains (Spec (.of A)) := by
    show (Spec (.of A)).size < B.cutoff
    rw [← Scheme.size_congr eT]
    exact T.left.2
  have hTi : ∀ i, B.Contains (Spec (.of (Ai i))) := fun i => by
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (pr i))) :=
      IsClosedImmersion.spec_of_surjective _ (hpr i)
    exact Scheme.size_lt_of_isClosedImmersion (Spec.map (CommRingCat.ofHom (pr i))) hTA
  have hWi : ∀ i n, B.Contains (Spec (.of (Ai i ⧸ Ji i n))) := fun i n => by
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ji i n)))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    exact Scheme.size_lt_of_isClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ji i n)))) (hTi i)
  let sT : Spec (.of A) ⟶ S := eT.inv ≫ B.inclusion.map T.hom
  let Ti : ιt → BigFppfOver B S hS := fun i =>
    siteObject B S hS (hTi i) (Spec.map (CommRingCat.ofHom (pr i)) ≫ sT)
  let Wi : ιt → ℕ → BigFppfOver B S hS := fun i n =>
    siteObject B S hS (hWi i n) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ji i n))) ≫
      Spec.map (CommRingCat.ofHom (pr i)) ≫ sT)
  have hWhom : ∀ n, B.inclusion.map (W n).hom =
      (eW n).hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J n))) ≫ sT := fun n => by
    rw [← Over.w (ι n), Functor.map_comp]
    show (BigFppfOver.toScheme B S hS).map (ι n) ≫ _ = _
    rw [← Category.comp_id ((BigFppfOver.toScheme B S hS).map (ι n)), ← eT.hom_inv_id,
      ← Category.assoc, hι n]
    simp [sT]
  let ji : ∀ i, Ti i ⟶ T := fun i => Space.siteHomOfSchemeHom B S hS
    (Spec.map (CommRingCat.ofHom (pr i)) ≫ eT.inv) (by simp [Ti, sT])
  let ιi : ∀ i n, Wi i n ⟶ Ti i := fun i n => Space.siteHomOfSchemeHom B S hS
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ji i n)))) rfl
  let τi : ∀ i n, Wi i n ⟶ Wi i (n + 1) := fun i n => Space.siteHomOfSchemeHom B S hS
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (hJmono i n)))) (by
      show _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ _
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        Ideal.Quotient.factor_comp_mk])
  have hqi : ∀ n i, (qi n i).comp (Ideal.Quotient.mk (J n)) =
      (Ideal.Quotient.mk (Ji i n)).comp (pr i) := fun n i => Ideal.quotientMap_comp_mk _
  let wi : ∀ i n, Wi i n ⟶ W n := fun i n => Space.siteHomOfSchemeHom B S hS
    (Spec.map (CommRingCat.ofHom (qi n i)) ≫ (eW n).inv) (by
      rw [hWhom n, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, hqi, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      rfl)
  have hji : ∀ i, (BigFppfOver.toScheme B S hS).map (ji i) =
      Spec.map (CommRingCat.ofHom (pr i)) ≫ eT.inv := fun i =>
    Space.siteHomOfSchemeHom_map B S hS _ _
  have hιi : ∀ i n, (BigFppfOver.toScheme B S hS).map (ιi i n) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ji i n))) := fun i n =>
    Space.siteHomOfSchemeHom_map B S hS _ _
  have hτi : ∀ i n, (BigFppfOver.toScheme B S hS).map (τi i n) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (hJmono i n))) := fun i n =>
    Space.siteHomOfSchemeHom_map B S hS _ _
  have hwi : ∀ i n, (BigFppfOver.toScheme B S hS).map (wi i n) =
      Spec.map (CommRingCat.ofHom (qi n i)) ≫ (eW n).inv := fun i n =>
    Space.siteHomOfSchemeHom_map B S hS _ _
  have hιeq : ∀ n, (BigFppfOver.toScheme B S hS).map (ι n) =
      (eW n).hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J n))) ≫ eT.inv := fun n => by
    rw [← cancel_mono eT.hom, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact hι n
  -- the basic squares
  have K1 : ∀ i n, ιi i n ≫ ji i = wi i n ≫ ι n := fun i n => by
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp, Functor.map_comp, hιi, hji, hwi, hιeq, Category.assoc,
      Iso.inv_hom_id_assoc, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hqi]
  have K2 : ∀ i n, τi i n ≫ ιi i (n + 1) = ιi i n := fun i n => by
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp, hτi, hιi, hιi, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      Ideal.Quotient.factor_comp_mk]
  have hmonoι : ∀ n, Mono (ι n) := fun n => by
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J n)))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have : Mono ((BigFppfOver.toScheme B S hS).map (ι n)) := by
      rw [hιeq]
      infer_instance
    exact (BigFppfOver.toScheme B S hS).mono_of_mono_map this
  have K3 : ∀ i n, τi i n ≫ wi i (n + 1) = wi i n ≫ τ n := fun i n => by
    rw [← cancel_mono (ι (n + 1)), Category.assoc, ← K1, ← Category.assoc, K2, K1,
      Category.assoc, hτ]
  -- the sections over the factors
  have hloc : ∀ i, ∃! yi : X.obj (op (Ti i)),
      ∀ n, X.map (ιi i n).op yi = X.map (wi i n).op (x n) := fun i =>
    existsUnique_section_of_compatible_truncations (hAi i) (Ji i) (hJm i) (hJmono i) (hJ₁ i)
      (hJ₂ i) hX (Ti i) (Iso.refl _) (Wi i) (fun _ => Iso.refl _) (ιi i)
      (fun n => by rw [hιi]; simp) (τi i) (K2 i)
      (fun n => X.map (wi i n).op (x n)) (fun n => by
        rw [← Functor.map_comp_apply, ← op_comp, K3, op_comp,
          Functor.map_comp_apply, hx])
  choose yi hyi huniq using hloc
  -- the identification of `T` with the spectrum of the product
  let eU : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of (Π i, Ai i)) :=
    eT ≪≫ Scheme.Spec.mapIso e.symm.toCommRingCatIso.op
  have hj : ∀ i, (BigFppfOver.toScheme B S hS).map (ji i) ≫ eU.hom =
      (Iso.refl _).hom ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom Ai i)) := fun i => by
    rw [hji, Iso.refl_hom, Category.id_comp]
    exact spec_map_comp_inv_comp_spec_mapIso_hom eT e i
  obtain ⟨y, hy, hyuniq⟩ := BigFppfOver.existsUnique_section_of_pi hX.isSheaf Ai T eU Ti
    (fun _ => Iso.refl _) ji hj yi
  -- the restrictions over the truncations
  have hrestr : ∀ n, X.map (ι n).op y = x n := fun n => by
    let eUn : (BigFppfOver.toScheme B S hS).obj (W n) ≅ Spec (.of (Π i, Ai i ⧸ Ji i n)) :=
      eW n ≪≫ Scheme.Spec.mapIso (qe n).symm.toCommRingCatIso.op
    have hjn : ∀ i, (BigFppfOver.toScheme B S hS).map (wi i n) ≫ eUn.hom =
        (Iso.refl _).hom ≫
          Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun i => Ai i ⧸ Ji i n) i)) :=
      fun i => by
        rw [hwi, Iso.refl_hom, Category.id_comp]
        exact spec_map_comp_inv_comp_spec_mapIso_hom (eW n) (qe n) i
    obtain ⟨z, -, hzuniq⟩ := BigFppfOver.existsUnique_section_of_pi hX.isSheaf
      (fun i => Ai i ⧸ Ji i n) (W n) eUn (fun i => Wi i n) (fun _ => Iso.refl _) (fun i => wi i n)
      hjn (fun i => X.map (wi i n).op (x n))
    refine (hzuniq _ fun i => ?_).trans (hzuniq _ fun i => rfl).symm
    rw [← Functor.map_comp_apply, ← op_comp, ← K1, op_comp, Functor.map_comp_apply,
      hy, hyi]
  refine ⟨y, hrestr, fun y' hy' => hyuniq y' fun i => huniq i _ fun n => ?_⟩
  rw [← Functor.map_comp_apply, ← op_comp, K1, op_comp, Functor.map_comp_apply, hy']

end AlgebraicGeometry.FormalSpace

end
