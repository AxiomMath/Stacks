module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import StacksFrontier.Algebra.Homology.HomologyFunctorLinear
public import StacksFrontier.Algebra.Homology.QuasiIsoOfShortExact
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.RingTheory.LocalCohomology.BaseChange
public import StacksFrontier.RingTheory.LocalCohomology.ModelComparison.DerivedTorsion

/-!
# Over a Noetherian ring the two models of local cohomology agree

Let `I` be a finitely generated ideal of a commutative ring `A` and `Z = V(I)`. The library
carries two derived torsion functors on `D(A)`: derived `I`-power torsion `RΓ_I`, the total
right derived functor of the `I`-power-torsion submodule functor, and local cohomology `RΓ_Z`,
the right adjoint of the inclusion of the objects with `I`-power-torsion cohomology. The
canonical comparison `RΓ_I ⟶ RΓ_Z` is not invertible over an arbitrary ring — that is
[Stacks, Tag 0A6P] — and the module docstring of
`StacksFrontier.RingTheory.LocalCohomology.ModelComparison.DerivedTorsion` records what was
missing:

> **What is still missing, and exactly what it is.** `compareSectionsWithSupportLocalCohomology`
> is invertible when `A` is Noetherian — [Stacks, Tag 0955] — and that statement is not proved
> anywhere in this library.

This file proves it. The three assertions of [Stacks, Tag 0955] are: the counit `RΓ_I(K) ⟶ K`
is invertible at every `K` with `I`-power-torsion cohomology; the comparison
`D(I^∞-torsion) ⥤ D_{I^∞-torsion}(A)` is an equivalence; and `RΓ_I ⟶ RΓ_Z` is invertible at
every object of `D(A)`.

The key statement about complexes is that over a Noetherian ring the degreewise `I`-power-torsion
subcomplex of a complex of injective modules with `I`-power-torsion cohomology is already the
whole complex up to quasi-isomorphism. For a single generator this is the computation of the
first paragraph of the proof of Tag 0955: the termwise torsion submodule of an injective module
is injective ([Stacks, Tag 08XW]), the quotient of an injective module by it has no torsion, so
multiplication by the generator is invertible on the quotient complex, and an `I`-power-torsion
cohomology module on which a generator acts invertibly vanishes. A finite set of generators is
handled by induction, because iterating the construction over two ideals computes it for their
sum.

Given that, the counit is invertible at every object of `D_{I^∞-torsion}(A)`: choose a
K-injective resolution with injective terms, which exists functorially
(`Stacks.Injectives.kInjectiveResolutionFunctor`), and apply the criterion
`Dualizing.TorsionCounit.isIso_derivedPowerTorsionCounit_app_Q_iff_quasiIso`. Parts (2) and (3)
follow by the formal arguments the source omits: part (2) is
`Dualizing.isEquivalence_powerTorsionComparison_of_isIso_counit`, and part (3) is obtained by
evaluating the naturality square of the comparison at the local cohomology counit
`ι(RΓ_Z(K)) ⟶ K`, whose source is a torsion object.

## Main results

* `Dualizing.TorsionCounit.quasiIso_powerTorsionSubcomplexι_app_of_injective` — the degreewise
  torsion inclusion of a complex of injectives with torsion cohomology is a quasi-isomorphism.
* `Dualizing.TorsionCounit.isIso_derivedPowerTorsionCounit_app` — **part (1)**: the counit
  `RΓ_I(K) ⟶ K` is invertible at every object with `I`-power-torsion cohomology.
* `Dualizing.TorsionCounit.isEquivalence_powerTorsionComparison` — **part (2)**: the comparison
  `D(I^∞-torsion) ⥤ D_{I^∞-torsion}(A)` is an equivalence.
* `Dualizing.TorsionCounit.isIso_compareTorsionFunctors_app` — **part (3)**: the
  comparison `RΓ_I ⟶ RΓ_Z` is invertible at every object of `D(A)`.
* `Stacks.LocalCohomology.isIso_compareSectionsWithSupportLocalCohomology_app` and
  `Stacks.LocalCohomology.isIso_compareSectionsWithSupportLocalCohomology` — the same for the
  `RΓ_{V(I)} ⟶ RΓ_Z` spelling, objectwise and as a natural transformation.

## Implementation notes

The universe convention is the one forced by `Dualizing.derivedPowerTorsion`: the ring lives in
`Type u` and the modules in `Type (max u v)`.

The `@[stacks 0955]` attributes carry one clause per enumerated assertion of the source. The
statement about complexes carries none: it is the first two paragraphs of the proof, not one of
the three assertions.

## References

* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
* [Stacks Project, Tag 08XW](https://stacks.math.columbia.edu/tag/08XW)
* [Stacks Project, Tag 0A6P](https://stacks.math.columbia.edu/tag/0A6P)
* [Stacks Project, Tag 0A6U](https://stacks.math.columbia.edu/tag/0A6U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Dualizing.TorsionCounit

attribute [local instance] HasDerivedCategory.standard

/-! ### The degreewise torsion subcomplex -/

/-- The termwise `I`-power-torsion subcomplex of a complex of `A`-modules. -/
private abbrev torsionComplex (A : Type u) [CommRing A] (I : Ideal A)
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    CochainComplex (ModuleCat.{max u v} A) ℤ :=
  ((powerTorsionFunctor.{u, v} A I).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    Functor.mapHomologicalComplex
      (ObjectProperty.ι (fun M : ModuleCat.{max u v} A ↦ IsIPowerTorsion A M I))
      (ComplexShape.up ℤ)).obj K

/-- The degreewise inclusion of the termwise `I`-power-torsion subcomplex. -/
private def torsionInclusion (A : Type u) [CommRing A] (I : Ideal A)
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) : torsionComplex.{u, v} A I K ⟶ K :=
  (powerTorsionSubcomplexι.{u, v} A I).app K

private lemma torsionInclusion_f (A : Type u) [CommRing A] (I : Ideal A)
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) (i : ℤ) :
    (torsionInclusion.{u, v} A I K).f i =
      ModuleCat.ofHom (Ideal.primaryComponent (K.X i) I).subtype := rfl

private lemma torsionInclusion_f_mono (A : Type u) [CommRing A] (I : Ideal A)
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) (i : ℤ) :
    Mono ((torsionInclusion.{u, v} A I K).f i) := by
  rw [torsionInclusion_f]
  exact (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective

private lemma torsionInclusion_mono (A : Type u) [CommRing A] (I : Ideal A)
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    Mono (torsionInclusion.{u, v} A I K) :=
  HomologicalComplex.mono_of_mono_f _ (torsionInclusion_f_mono.{u, v} A I K)

private lemma torsionComplex_injective (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (K : CochainComplex (ModuleCat.{max u v} A) ℤ)
    [∀ i, Injective (K.X i)] (i : ℤ) : Injective ((torsionComplex.{u, v} A I K).X i) := by
  let := Module.injective_module_of_injective_object A (K.X i)
  let := Module.injective_primaryComponent (K.X i) I
  exact Module.injective_object_of_injective_module A _

/-! ### The case of a single generator -/

/-- An injective object on which a monic scalar acts has that scalar acting invertibly. -/
private lemma isIso_smul_id_of_injective {R : Type*} [CommRing R] {M : ModuleCat.{v} R}
    [Injective M] (r : R) [Mono (r • 𝟙 M)] : IsIso (r • 𝟙 M) := by
  let g := Injective.factorThru (𝟙 M) (r • 𝟙 M)
  have hg : (r • 𝟙 M) ≫ g = 𝟙 M := Injective.comp_factorThru _ _
  exact ⟨⟨g, hg, by simpa only [Linear.smul_comp, Linear.comp_smul,
    Category.id_comp, Category.comp_id] using hg⟩⟩

/-- Scalar multiplication by `r` is monic on a module exactly when it is injective. -/
private lemma mono_smul_id_iff_injective {R : Type*} [CommRing R] {M : ModuleCat.{v} R} (r : R) :
    Mono (r • 𝟙 M) ↔ Function.Injective (fun x : M => r • x) :=
  ModuleCat.mono_iff_injective _

/-- Conjugating the scalar `r • 𝟙` by an isomorphism gives the scalar `r • 𝟙` again. -/
private lemma iso_hom_comp_smul_id_comp_inv {R : Type*} [CommRing R] {C : Type*} [Category C]
    [Preadditive C] [Linear R C] {X Y : C} (e : X ≅ Y) (r : R) :
    e.hom ≫ (r • 𝟙 Y) ≫ e.inv = r • 𝟙 X := by
  simp only [Linear.comp_smul, Linear.smul_comp, Category.id_comp, Iso.hom_inv_id]

/-- The cokernel of a monomorphism between injective objects is injective. -/
private lemma injective_cokernel_of_injective {C : Type*} [Category C] [Abelian C] {X Y : C}
    [Injective X] [Injective Y] (f : X ⟶ Y) [Mono f] : Injective (cokernel f) := by
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  let s := ShortComplex.Splitting.ofExactOfRetraction S
    (S.exact_of_g_is_cokernel (cokernelIsCokernel f))
    (Injective.factorThru (𝟙 X) f) (Injective.comp_factorThru _ _) inferInstance
  refine ⟨fun g i _ => ?_⟩
  obtain ⟨l, hl⟩ := Injective.factors (g ≫ s.s) i
  exact ⟨l ≫ cokernel.π f, by rw [← Category.assoc, hl, Category.assoc, s.s_g,
    Category.comp_id]⟩

private lemma mono_smul_quotient_primaryComponent {A : Type u} [CommRing A] (f : A)
    (M : ModuleCat.{max u v} A) :
    Mono (f • 𝟙 (ModuleCat.of A (M ⧸ Ideal.primaryComponent M (Ideal.span {f})))) := by
  rw [mono_smul_id_iff_injective]
  suffices hz : ∀ x : M ⧸ Ideal.primaryComponent M (Ideal.span {f}), f • x = 0 → x = 0 by
    intro x y h
    exact sub_eq_zero.mp (hz _ (by rw [smul_sub]; exact sub_eq_zero.mpr h))
  intro x hx'
  have hmem : x ∈ Submodule.torsionBySet A
      (M ⧸ Ideal.primaryComponent M (Ideal.span {f})) (Ideal.span {f} : Set A) := by
    rw [Submodule.mem_torsionBySet_iff]
    rintro ⟨a, ha⟩
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp ha
    simpa [mul_smul, smul_comm f b] using congrArg (b • ·) hx'
  rw [torsionBySet_quotient_primaryComponent_eq_bot _ (Submodule.fg_span_singleton f) M] at hmem
  exact hmem

/-- On the quotient of an injective module by its `f`-power torsion, multiplication by `f` is
invertible: the quotient has no `f`-power torsion and is injective. -/
private lemma isIso_smul_cokernel_torsion (A : Type u) [CommRing A] [IsNoetherianRing A] (f : A)
    (M : ModuleCat.{max u v} A) [Injective M] :
    IsIso (f • 𝟙 (cokernel (ModuleCat.ofHom
      (Ideal.primaryComponent M (Ideal.span {f})).subtype))) := by
  let i := ModuleCat.ofHom (Ideal.primaryComponent M (Ideal.span {f})).subtype
  have : Mono i := (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  let := Module.injective_module_of_injective_object A M
  let := Module.injective_primaryComponent M (Ideal.span {f})
  let := Module.injective_object_of_injective_module A
    (Ideal.primaryComponent M (Ideal.span {f}))
  have : Injective (cokernel i) := injective_cokernel_of_injective i
  let e : cokernel i ≅ ModuleCat.of A (M ⧸ Ideal.primaryComponent M (Ideal.span {f})) :=
    ModuleCat.cokernelIsoRangeQuotient i ≪≫ LinearEquiv.toModuleIso
      (Submodule.quotEquivOfEq _ _ (Submodule.range_subtype _))
  have : Mono (f • 𝟙 (ModuleCat.of A (M ⧸ Ideal.primaryComponent M (Ideal.span {f})))) :=
    mono_smul_quotient_primaryComponent.{u, v} f M
  have : Mono (f • 𝟙 (cokernel i)) := by
    rw [← iso_hom_comp_smul_id_comp_inv e f]
    infer_instance
  exact isIso_smul_id_of_injective f

private lemma torsionInclusion_quasiIso_principal (A : Type u) [CommRing A] [IsNoetherianRing A]
    (f : A) (K : CochainComplex (ModuleCat.{max u v} A) ℤ) [∀ i, Injective (K.X i)]
    (hK : ∀ i, IsIPowerTorsion A (K.homology i) (Ideal.span {f})) :
    QuasiIso (torsionInclusion.{u, v} A (Ideal.span {f}) K) := by
  let I : Ideal A := Ideal.span {f}
  let P : ObjectProperty (ModuleCat.{max u v} A) := fun M => IsIPowerTorsion A M I
  let : P.IsSerreClass := isSerreClass_isIPowerTorsion I (Submodule.fg_span_singleton f)
  let i := torsionInclusion.{u, v} A I K
  have : Mono i := torsionInclusion_mono.{u, v} A I K
  let Q := cokernel i
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact := { exact := S.exact_of_g_is_cokernel (cokernelIsCokernel i) }
  apply CategoryTheory.quasiIso_of_shortExact_of_isZero_homology hS
  intro n
  have hT (j : ℤ) : P ((torsionComplex.{u, v} A I K).homology j) := by
    apply P.prop_of_epi ((torsionComplex.{u, v} A I K).homologyπ j)
    apply P.prop_of_mono ((torsionComplex.{u, v} A I K).iCycles j)
    exact ((powerTorsionFunctor.{u, v} A I).obj (K.X j)).property
  have hQ : P (Q.homology n) := P.prop_X₂_of_exact
    (hS.homology_exact₃ n (n + 1) (by rfl)) (hK n) (hT (n + 1))
  have hcomp (j : ℤ) : IsIso ((f • 𝟙 Q).f j) := by
    let E := HomologicalComplex.eval (ModuleCat.{max u v} A) (ComplexShape.up ℤ) j
    let e := PreservesCokernel.iso E i
    have : IsIso (f • 𝟙 (cokernel (E.map i))) :=
      isIso_smul_cokernel_torsion.{u, v} A f (K.X j)
    rw [HomologicalComplex.smul_f_apply, HomologicalComplex.id_f]
    have h : IsIso (e.hom ≫ (f • 𝟙 _) ≫ e.inv) := inferInstance
    rwa [iso_hom_comp_smul_id_comp_inv] at h
  have : IsIso (f • 𝟙 Q) := HomologicalComplex.Hom.isIso_of_components _
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{max u v} A) (ComplexShape.up ℤ) n
  have : H.Linear A := HomologicalComplex.homologyFunctor_linear (ComplexShape.up ℤ) n
  have h : IsIso (H.map (f • 𝟙 Q)) := inferInstance
  have : IsIso (f • 𝟙 (Q.homology n)) := by
    rw [H.map_smul, H.map_id] at h
    exact h
  rw [ModuleCat.isZero_iff_subsingleton]
  apply (subsingleton_iff_forall_eq 0).mpr
  intro x
  obtain ⟨k, -, hk⟩ := hQ x
  have hkx := hk (f ^ k) (Ideal.pow_mem_pow (Ideal.subset_span (by simp)) k)
  have hinj : Function.Injective (fun x : Q.homology n => f • x) :=
    (mono_smul_id_iff_injective f).mp inferInstance
  have hpow : Function.Injective (fun x : Q.homology n => f ^ k • x) := by
    simpa only [smul_iterate] using hinj.iterate k
  exact hpow (by simpa only [smul_zero] using hkx)

/-! ### Passing from one generator to finitely many -/

private lemma mem_primaryComponent_sup {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M]
    [Module A M] (I J : Ideal A) (x : M) :
    x ∈ Ideal.primaryComponent M (I ⊔ J) ↔
      x ∈ Ideal.primaryComponent M I ∧ x ∈ Ideal.primaryComponent M J := by
  simp only [Ideal.primaryComponent_mem, Submodule.mem_torsionBySet_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨⟨n, fun a => hn ⟨a, Ideal.pow_right_mono le_sup_left n a.property⟩⟩,
      ⟨n, fun a => hn ⟨a, Ideal.pow_right_mono le_sup_right n a.property⟩⟩⟩
  · rintro ⟨⟨n, hn⟩, ⟨m, hm⟩⟩
    refine ⟨n + m, fun a => ?_⟩
    obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.mp
      (Ideal.sup_pow_add_le_pow_sup_pow a.property)
    show (a : A) • x = 0
    rw [← hbc, add_smul, hn ⟨b, hb⟩, hm ⟨c, hc⟩, add_zero]

private lemma mem_primaryComponent_submodule {A : Type*} [CommRing A] {M : Type*}
    [AddCommGroup M] [Module A M] (I : Ideal A) (N : Submodule A M) (x : N) :
    x ∈ Ideal.primaryComponent N I ↔ (x : M) ∈ Ideal.primaryComponent M I := by
  simp only [Ideal.primaryComponent_mem, Submodule.mem_torsionBySet_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, fun a => congrArg Subtype.val (hn a)⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, fun a => Subtype.ext (hn a)⟩

private lemma primaryComponent_submodule_eq_comap {A : Type*} [CommRing A] (I J : Ideal A)
    (M : Type*) [AddCommGroup M] [Module A M] :
    Ideal.primaryComponent (Ideal.primaryComponent M I) J =
      (Ideal.primaryComponent M (I ⊔ J)).comap (Ideal.primaryComponent M I).subtype := by
  ext x
  show x ∈ Ideal.primaryComponent (Ideal.primaryComponent M I) J ↔
    (x : M) ∈ Ideal.primaryComponent M (I ⊔ J)
  rw [mem_primaryComponent_submodule, mem_primaryComponent_sup]
  exact ⟨fun h => ⟨x.property, h⟩, fun h => h.2⟩

/-- Iterating the torsion submodule over `I` and then over `J` computes it for `I ⊔ J`. -/
private def primaryComponentSupLinearEquiv {A : Type*} [CommRing A] (I J : Ideal A)
    (M : Type*) [AddCommGroup M] [Module A M] :
    Ideal.primaryComponent (Ideal.primaryComponent M I) J ≃ₗ[A]
      Ideal.primaryComponent M (I ⊔ J) :=
  (LinearEquiv.ofEq _ _ (primaryComponent_submodule_eq_comap I J M)).trans
    (Submodule.comapSubtypeEquivOfLe (fun x hx => (mem_primaryComponent_sup I J x).mp hx |>.1))

private lemma ofEq_trans_comapSubtypeEquivOfLe_comp_subtype (A : Type u) [CommRing A]
    (M : ModuleCat.{max u v} A) {N T : Submodule A M} {S : Submodule A N}
    (hST : S = T.comap N.subtype) (hTN : T ≤ N) :
    ((LinearEquiv.ofEq S (T.comap N.subtype) hST).trans
          (Submodule.comapSubtypeEquivOfLe hTN)).toModuleIso.hom ≫
        ModuleCat.ofHom T.subtype =
      ModuleCat.ofHom S.subtype ≫ ModuleCat.ofHom N.subtype := by
  ext x
  rfl

private def torsionComplexSupComponent (A : Type u) [CommRing A] (I J : Ideal A)
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) (n : ℤ) :
    (torsionComplex.{u, v} A J (torsionComplex.{u, v} A I K)).X n ≅
      (torsionComplex.{u, v} A (I ⊔ J) K).X n :=
  (primaryComponentSupLinearEquiv I J (K.X n)).toModuleIso

private lemma torsionComplexSupComponent_hom_comp_inclusion (A : Type u) [CommRing A]
    (I J : Ideal A) (K : CochainComplex (ModuleCat.{max u v} A) ℤ) (n : ℤ) :
    (torsionComplexSupComponent.{u, v} A I J K n).hom ≫
        (torsionInclusion.{u, v} A (I ⊔ J) K).f n =
      (torsionInclusion.{u, v} A J (torsionComplex.{u, v} A I K)).f n ≫
        (torsionInclusion.{u, v} A I K).f n := by
  rw [torsionInclusion_f, torsionInclusion_f, torsionInclusion_f]
  exact ofEq_trans_comapSubtypeEquivOfLe_comp_subtype.{u, v} A (K.X n)
    (primaryComponent_submodule_eq_comap I J (K.X n))
    (fun x hx => (mem_primaryComponent_sup I J x).mp hx |>.1)

private lemma torsionComplexSupComponent_comm (A : Type u) [CommRing A] (I J : Ideal A)
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) (i j : ℤ) :
    (torsionComplexSupComponent.{u, v} A I J K i).hom ≫
        (torsionComplex.{u, v} A (I ⊔ J) K).d i j =
      (torsionComplex.{u, v} A J (torsionComplex.{u, v} A I K)).d i j ≫
        (torsionComplexSupComponent.{u, v} A I J K j).hom := by
  have : Mono ((torsionInclusion.{u, v} A (I ⊔ J) K).f j) :=
    torsionInclusion_f_mono.{u, v} A (I ⊔ J) K j
  rw [← cancel_mono ((torsionInclusion.{u, v} A (I ⊔ J) K).f j), Category.assoc, Category.assoc,
    ← (torsionInclusion.{u, v} A (I ⊔ J) K).comm i j,
    torsionComplexSupComponent_hom_comp_inclusion, ← Category.assoc,
    torsionComplexSupComponent_hom_comp_inclusion, ← Category.assoc,
    ← (torsionInclusion.{u, v} A J (torsionComplex.{u, v} A I K)).comm i j, Category.assoc,
    (torsionInclusion.{u, v} A I K).comm i j, Category.assoc]

private def torsionComplexSupIso (A : Type u) [CommRing A] (I J : Ideal A)
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    torsionComplex.{u, v} A J (torsionComplex.{u, v} A I K) ≅
      torsionComplex.{u, v} A (I ⊔ J) K :=
  HomologicalComplex.Hom.isoOfComponents (torsionComplexSupComponent.{u, v} A I J K)
    (fun i j _ => torsionComplexSupComponent_comm.{u, v} A I J K i j)

private lemma torsionComplexSupIso_hom_inclusion (A : Type u) [CommRing A] (I J : Ideal A)
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    (torsionComplexSupIso.{u, v} A I J K).hom ≫ torsionInclusion.{u, v} A (I ⊔ J) K =
      torsionInclusion.{u, v} A J (torsionComplex.{u, v} A I K) ≫
        torsionInclusion.{u, v} A I K :=
  HomologicalComplex.hom_ext _ _ fun n =>
    torsionComplexSupComponent_hom_comp_inclusion.{u, v} A I J K n

/-- An `I`-power-torsion module is power torsion for every smaller ideal. -/
theorem isIPowerTorsion_of_le {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M]
    [Module A M] {I J : Ideal A} (h : I ≤ J) (hM : IsIPowerTorsion A M J) :
    IsIPowerTorsion A M I := by
  intro x
  obtain ⟨n, hn, hx⟩ := hM x
  exact ⟨n, hn, fun a ha => hx a (Ideal.pow_right_mono h n ha)⟩

private lemma torsionInclusion_quasiIso (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (K : CochainComplex (ModuleCat.{max u v} A) ℤ) [∀ i, Injective (K.X i)]
    (hK : ∀ i, IsIPowerTorsion A (K.homology i) I) :
    QuasiIso (torsionInclusion.{u, v} A I K) := by
  classical
  obtain ⟨s, rfl⟩ := Ideal.fg_of_isNoetherianRing I
  induction s using Finset.induction_on generalizing K with
  | empty =>
    have hi : IsIso (torsionInclusion.{u, v} A (Ideal.span (↑(∅ : Finset A) : Set A)) K) := by
      have hn (n : ℤ) : IsIso ((torsionInclusion.{u, v} A
          (Ideal.span (↑(∅ : Finset A) : Set A)) K).f n) := by
        apply (ConcreteCategory.isIso_iff_bijective _).mpr
        rw [torsionInclusion_f]
        refine ⟨Subtype.val_injective, fun x => ⟨⟨x, ?_⟩, rfl⟩⟩
        rw [Ideal.primaryComponent_mem]
        exact ⟨1, by simp⟩
      exact HomologicalComplex.Hom.isIso_of_components _
    infer_instance
  | @insert f s hf ih =>
    have heq : Ideal.span (↑(insert f s) : Set A) =
        Ideal.span (↑s : Set A) ⊔ Ideal.span {f} := by
      simp only [Finset.coe_insert, Ideal.span_insert, sup_comm]
    rw [heq] at hK ⊢
    let J := Ideal.span (↑s : Set A)
    have hi : QuasiIso (torsionInclusion.{u, v} A J K) :=
      ih K (fun n => isIPowerTorsion_of_le le_sup_left (hK n))
    have : ∀ n, Injective ((torsionComplex.{u, v} A J K).X n) :=
      torsionComplex_injective.{u, v} A J K
    let P : ObjectProperty (ModuleCat.{max u v} A) :=
      fun M => IsIPowerTorsion A M (Ideal.span {f})
    let : P.IsSerreClass := isSerreClass_isIPowerTorsion _ (Submodule.fg_span_singleton f)
    have ht : ∀ n, P ((torsionComplex.{u, v} A J K).homology n) := fun n =>
      P.prop_of_iso (asIso (HomologicalComplex.homologyMap
        (torsionInclusion.{u, v} A J K) n)).symm (isIPowerTorsion_of_le le_sup_right (hK n))
    have : QuasiIso (torsionInclusion.{u, v} A (Ideal.span {f})
        (torsionComplex.{u, v} A J K)) :=
      torsionInclusion_quasiIso_principal.{u, v} A f (torsionComplex.{u, v} A J K) ht
    have hcomp : QuasiIso ((torsionComplexSupIso.{u, v} A J (Ideal.span {f}) K).hom ≫
        torsionInclusion.{u, v} A (J ⊔ Ideal.span {f}) K) := by
      rw [torsionComplexSupIso_hom_inclusion]
      infer_instance
    exact quasiIso_of_comp_left (torsionComplexSupIso.{u, v} A J (Ideal.span {f}) K).hom
      (torsionInclusion.{u, v} A (J ⊔ Ideal.span {f}) K)

/-- **The degreewise torsion inclusion of a complex of injectives with torsion cohomology is a
quasi-isomorphism.** Let `A` be a Noetherian ring, `I ⊆ A` an ideal, and `J` a complex of
injective `A`-modules all of whose cohomology modules are `I`-power torsion. Then the inclusion
`Γ_I(J) ⟶ J` of the termwise `I`-power-torsion subcomplex is a quasi-isomorphism. This is the
computation of the first two paragraphs of the proof of [Stacks, Tag 0955]. -/
theorem quasiIso_powerTorsionSubcomplexι_app_of_injective (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (J : CochainComplex (ModuleCat.{max u v} A) ℤ)
    [∀ i, Injective (J.X i)] (hJ : ∀ i, IsIPowerTorsion A (J.homology i) I) :
    QuasiIso ((powerTorsionSubcomplexι.{u, v} A I).app J) :=
  torsionInclusion_quasiIso.{u, v} A I J hJ

/-! ### The three assertions of Stacks 0955 -/

section Main

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)

/-- **Stacks 0955, part (1).** Let `A` be a Noetherian ring and `I ⊆ A` a finitely generated
ideal. The counit `RΓ_I(K) ⟶ K` of [Stacks, Tag 0A6L] is an isomorphism at every object `K` of
`D(A)` whose cohomology modules are `I`-power torsion.

The object is represented by a K-injective complex with injective terms, where the counit is the
degreewise torsion inclusion. -/
@[stacks 0955 "part (1)"]
theorem isIso_derivedPowerTorsionCounit_app
    (K : PowerTorsionDerivedCategory.{u, max u v} A I hI) :
    IsIso ((derivedPowerTorsionCounit.{u, v} A I hI).app K.obj) := by
  let : AB5 (ModuleCat.{max u v} A) :=
    { ofShape := fun J _ _ => HasExactColimitsOfShape.domain_of_functor J
        (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat) }
  let : IsGrothendieckAbelian.{max u v} (ModuleCat.{max u v} A) := {}
  let P : ObjectProperty (ModuleCat.{max u v} A) := fun M => IsIPowerTorsion A M I
  let : P.IsSerreClass := isSerreClass_isIPowerTorsion I hI
  let L := DerivedCategory.Q.objPreimage K.obj
  let J := (Stacks.Injectives.kInjectiveResolutionFunctor (ModuleCat.{max u v} A)).obj L
  let q := (Stacks.Injectives.kInjectiveResolutionInclusion (ModuleCat.{max u v} A)).app L
  have : QuasiIso q := inferInstance
  have hJK : J.IsKInjective := inferInstance
  have : ∀ n, Injective (J.X n) := fun n => inferInstance
  let e : DerivedCategory.Q.obj J ≅ K.obj :=
    (asIso (DerivedCategory.Q.map q)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso K.obj
  have hJtors (n : ℤ) : IsIPowerTorsion A (J.homology n) I :=
    P.prop_of_iso (((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).mapIso e).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} A) n).app J) (K.property n)
  have hQ : IsIso ((derivedPowerTorsionCounit.{u, v} A I hI).app (DerivedCategory.Q.obj J)) := by
    rw [isIso_derivedPowerTorsionCounit_app_Q_iff_quasiIso.{u, v} A I hI J hJK]
    exact quasiIso_powerTorsionSubcomplexι_app_of_injective.{u, v} A I J hJtors
  exact isIso_derivedPowerTorsionCounit_app_of_iso.{u, v} A I hI e hQ

/-- **Stacks 0955, part (2).** For a Noetherian ring the comparison functor
`D(I^∞-torsion) ⥤ D_{I^∞-torsion}(A)` of [Stacks, Tag 0A6N] is an equivalence. -/
@[stacks 0955 "part (2)"]
theorem isEquivalence_powerTorsionComparison :
    (powerTorsionComparison.{u, max u v} A I hI).IsEquivalence :=
  isEquivalence_powerTorsionComparison_of_isIso_counit A I hI
    (derivedPowerTorsionAdjunction.{u, v} A I hI)
    (fun K => isIso_derivedPowerTorsionCounit_app.{u, v} A I hI K)

/-- The comparison `RΓ_I ⟶ RΓ_Z` of [Stacks, Tag 0A6U] is invertible at an object with
`I`-power-torsion cohomology: there both sides compute the object itself. -/
theorem isIso_compareTorsionFunctors_app_obj
    (K : PowerTorsionDerivedCategory.{u, max u v} A I hI) :
    IsIso ((compareTorsionFunctors.{u, v} A I hI).app K.obj) :=
  (isIso_derivedPowerTorsionCounit_app_iff_isIso_compareTorsionFunctors.{u, v} A I hI K).mp
    (isIso_derivedPowerTorsionCounit_app.{u, v} A I hI K)

end Main

/-- A coreflection inverts the components of its counit: the unit of an adjunction with fully
faithful left adjoint is invertible, and the right triangle identity exhibits `G(ε_Y)` as the
remaining factor of an identity. -/
private lemma isIso_rightAdjoint_map_counit {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Full] [F.Faithful] (adj : F ⊣ G) (Y : D) :
    IsIso (G.map (adj.counit.app Y)) := by
  have hunit : IsIso (adj.unit.app (G.obj Y)) :=
    ((asIso adj.unit).app (G.obj Y)).isIso_hom
  have := hunit
  have hcomp : IsIso (adj.unit.app (G.obj Y) ≫ G.map (adj.counit.app Y)) := by
    rw [adj.right_triangle_components]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_left (adj.unit.app (G.obj Y)) (G.map (adj.counit.app Y))

/-- Across a natural transformation whose two functors both invert a morphism, invertibility at
the source of that morphism transfers to its target. -/
private lemma isIso_app_of_naturality {C D : Type*} [Category C] [Category D] {G H : C ⥤ D}
    (τ : G ⟶ H) {X Y : C} (f : X ⟶ Y) (hG : IsIso (G.map f)) (hH : IsIso (H.map f))
    (hX : IsIso (τ.app X)) : IsIso (τ.app Y) := by
  have := hG
  have := hH
  have := hX
  have hcomp : IsIso (G.map f ≫ τ.app Y) := by
    rw [τ.naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left (G.map f) (τ.app Y)

/-- A right adjoint inverts a morphism which is universal from the image of the left adjoint:
if composing with `c` is bijective on morphisms out of every `F(Z)`, then `G(c)` is invertible,
by the Yoneda lemma transported along the adjunction. -/
theorem isIso_rightAdjoint_map_of_bijective {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {W K : D} (c : W ⟶ K)
    (h : ∀ Z : C, Function.Bijective (fun g : F.obj Z ⟶ W => g ≫ c)) : IsIso (G.map c) := by
  refine isIso_of_yoneda_map_bijective (G.map c) (fun Z => ?_)
  have key : ∀ g : Z ⟶ G.obj W, (adj.homEquiv Z K).symm (g ≫ G.map c) =
      (adj.homEquiv Z W).symm g ≫ c := by
    intro g
    rw [adj.homEquiv_counit Z K (g ≫ G.map c), adj.homEquiv_counit Z W g, F.map_comp,
      Category.assoc, ← Functor.comp_map, adj.counit.naturality c, Functor.id_map]
    exact (Category.assoc _ _ _).symm
  have hcomp : (fun g : Z ⟶ G.obj W => g ≫ G.map c) =
      (adj.homEquiv Z K) ∘ (fun g : F.obj Z ⟶ W => g ≫ c) ∘ (adj.homEquiv Z W).symm := by
    funext g
    simp only [Function.comp_apply]
    rw [← key g, Equiv.apply_symm_apply]
  rw [hcomp]
  exact (adj.homEquiv Z K).bijective.comp ((h Z).comp (adj.homEquiv Z W).symm.bijective)

section Comparison

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)

omit [IsNoetherianRing A] in
/-- Derived `I`-power torsion inverts the local cohomology counit: the counit `ι(RΓ_Z(K)) ⟶ K`
is universal among morphisms to `K` from an object with `I`-power-torsion cohomology, and every
object in the image of the derived inclusion of the `I`-power-torsion modules is such. -/
private lemma isIso_derivedPowerTorsion_map_localCohomologyCounit
    (K : DerivedCategory (ModuleCat.{max u v} A)) :
    IsIso ((derivedPowerTorsion.{u, v} A I hI).map
      ((localCohomologyAdjunction.{u, max u v} A I hI).counit.app K)) := by
  refine isIso_rightAdjoint_map_of_bijective (derivedPowerTorsionAdjunction.{u, v} A I hI)
    ((localCohomologyAdjunction.{u, max u v} A I hI).counit.app K) (fun Z => ?_)
  exact Stacks.LocalCohomology.counit_bijective (derivedPowerTorsionProperty A I hI)
    (localCohomologyAdjunction.{u, max u v} A I hI) K
    ⟨_, ((powerTorsionComparison.{u, max u v} A I hI).obj Z).property⟩

/-- **Stacks 0955, part (3).** Let `A` be a Noetherian ring and `I ⊆ A` a finitely generated
ideal. The comparison `RΓ_I ⟶ RΓ_Z` of [Stacks, Tag 0A6U] is an isomorphism at every object of
`D(A)`, with no torsion or boundedness hypothesis.

Evaluate the naturality square of the comparison at the local cohomology counit
`c : ι(RΓ_Z(K)) ⟶ K`. Its source has `I`-power-torsion cohomology, so the comparison is
invertible there by part (1); `RΓ_Z(c)` is invertible because `RΓ_Z` is a coreflection; and
`RΓ_I(c)` is invertible because the counit is universal among morphisms from torsion objects. -/
@[stacks 0955 "part (3)"]
theorem isIso_compareTorsionFunctors_app
    (K : DerivedCategory (ModuleCat.{max u v} A)) :
    IsIso ((compareTorsionFunctors.{u, v} A I hI).app K) := by
  have hW : IsIso ((compareTorsionFunctors.{u, v} A I hI).app
      ((derivedPowerTorsionProperty A I hI).ι.obj
        ((localCohomologyFunctor.{u, max u v} A I hI).obj K))) :=
    isIso_compareTorsionFunctors_app_obj.{u, v} A I hI
      ((localCohomologyFunctor.{u, max u v} A I hI).obj K)
  have hZ : IsIso ((localCohomologyFunctor.{u, max u v} A I hI).map
      ((localCohomologyAdjunction.{u, max u v} A I hI).counit.app K)) :=
    isIso_rightAdjoint_map_counit (localCohomologyAdjunction.{u, max u v} A I hI) K
  have hT := isIso_derivedPowerTorsion_map_localCohomologyCounit.{u, v} A I hI K
  have hF : IsIso ((derivedPowerTorsion.{u, v} A I hI ⋙
      powerTorsionComparison.{u, max u v} A I hI).map
      ((localCohomologyAdjunction.{u, max u v} A I hI).counit.app K)) :=
    ((powerTorsionComparison.{u, max u v} A I hI).mapIso (@asIso _ _ _ _ _ hT)).isIso_hom
  exact isIso_app_of_naturality (compareTorsionFunctors.{u, v} A I hI)
    ((localCohomologyAdjunction.{u, max u v} A I hI).counit.app K) hF hZ hW

end Comparison

end Dualizing.TorsionCounit

namespace Stacks.LocalCohomology

attribute [local instance] HasDerivedCategory.standard

open Dualizing

section

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)

/-- **The two models of local cohomology agree over a Noetherian ring.** The canonical map from
derived sections with support in `V(I)` to local cohomology `RΓ_Z` is an isomorphism at every
object of `D(A)`. This is [Stacks, Tag 0955] in the `RΓ_{V(I)}` spelling. -/
theorem isIso_compareSectionsWithSupportLocalCohomology_app
    (K : DerivedCategory (ModuleCat.{max u v} A)) :
    IsIso ((compareSectionsWithSupportLocalCohomology.{u, v} A I hI).app K) := by
  have h1 : IsIso ((compareTorsionFunctors.{u, v} A I hI).app K) :=
    TorsionCounit.isIso_compareTorsionFunctors_app.{u, v} A I hI K
  have := h1
  show IsIso
    ((derivedSectionsWithSupportInIsoDerivedPowerTorsion.{u, v} A I hI).hom.app K ≫
      (Functor.isoWhiskerLeft (derivedPowerTorsion.{u, v} A I hI)
        (powerTorsionComparisonCompInclusionIso.{u, max u v} A I hI)).inv.app K ≫
      (derivedPowerTorsionProperty A I hI).ι.map
        ((compareTorsionFunctors.{u, v} A I hI).app K))
  have ha : IsIso ((derivedSectionsWithSupportInIsoDerivedPowerTorsion.{u, v}
      A I hI).hom.app K) :=
    ((derivedSectionsWithSupportInIsoDerivedPowerTorsion.{u, v} A I hI).app K).isIso_hom
  have hb : IsIso ((Functor.isoWhiskerLeft (derivedPowerTorsion.{u, v} A I hI)
      (powerTorsionComparisonCompInclusionIso.{u, max u v} A I hI)).inv.app K) :=
    ((Functor.isoWhiskerLeft (derivedPowerTorsion.{u, v} A I hI)
      (powerTorsionComparisonCompInclusionIso.{u, max u v} A I hI)).app K).isIso_inv
  have hc : IsIso ((derivedPowerTorsionProperty A I hI).ι.map
      ((compareTorsionFunctors.{u, v} A I hI).app K)) :=
    ((derivedPowerTorsionProperty A I hI).ι.mapIso
      (@asIso _ _ _ _ ((compareTorsionFunctors.{u, v} A I hI).app K) h1)).isIso_hom
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ ha (@IsIso.comp_isIso _ _ _ _ _ _ _ hb hc)

/-- **The two models of local cohomology agree over a Noetherian ring**, as natural
transformations: `RΓ_{V(I)} ⟶ RΓ_Z` is a natural isomorphism. -/
theorem isIso_compareSectionsWithSupportLocalCohomology :
    IsIso (compareSectionsWithSupportLocalCohomology.{u, v} A I hI) := by
  have h : ∀ K, IsIso ((compareSectionsWithSupportLocalCohomology.{u, v} A I hI).app K) :=
    fun K ↦ isIso_compareSectionsWithSupportLocalCohomology_app.{u, v} A I hI K
  exact NatIso.isIso_of_isIso_app _

end

end Stacks.LocalCohomology

end
