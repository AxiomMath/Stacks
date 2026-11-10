module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.Double
public import Mathlib.RingTheory.Extension.Cotangent.BaseChange
public import Mathlib.RingTheory.Flat.Equalizer
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.Homology.TorAmplitude.Module
public import StacksFrontier.Homology.TorAmplitude.Triangle
public import StacksFrontier.RingTheory.NaiveCotangent.DerivedBaseChange

@[expose] public noncomputable section

/-!
# Flat base change of the naive cotangent complex along a cocartesian square

Let `A → B` be flat and let `A → A'` be arbitrary. Write `B' = A' ⊗[A] B` for the pushout, so
that the square with corners `A, A', B, B'` is cocartesian. This file proves that the canonical
map `NL_{B/A} ⊗_B B' → NL_{B'/A'}` is then a quasi-isomorphism, and that if moreover `NL_{B/A}`
has Tor amplitude in `[-1, 0]` the same is true of the derived base-change map
`NL_{B/A} ⊗_B^L B' → NL_{B'/A'}`.

## Main results

* `NaiveCotangent.naiveCotangentComplex_quasiIso_baseChange_of_flat` (Stacks 0FJU).

## Implementation notes

The cocartesian square is represented by its canonical pushout `A' ⊗[A] B`, with the
`B`-algebra structure `Algebra.TensorProduct.rightAlgebra` introduced locally in the statement,
as in `NaiveCotangent.finite_projective_ker_naiveCotangent_baseChange_homology_negOne`
(Stacks 0FV1).

Both conclusions are carried by one statement, in two layers.

The first layer is the two-term model. The naive cotangent complex of the canonical presentation
is the differential from the conormal module to the cotangent space, so a quasi-isomorphism of
two-term complexes is bijectivity on the kernels (degree `-1` homology) together with
bijectivity on the cokernels (degree `0` homology), and that is how the ordinary base-change
statement is recorded: elementwise, with no choice of homology model. Surjectivity on kernels
and bijectivity on cokernels hold for an arbitrary base change and are taken from
`NaiveCotangent.naiveCotangentComplex_baseChange_homology` (Stacks 0FUZ); flatness of `A → B` is
what adds injectivity on kernels, through the identification
`B' ⊗_B I/I² ≅ I'/(I')²` of Stacks 0FJU's own proof.

The second layer is cohomological. The two-term complex is realized as
`HomologicalComplex.double`, in degrees `-1` and `0`, over `ULift B`: the four rings live in
independent universes, so the module categories are carried to one universe, and lifting the
ring as well puts the ring and its modules in a single universe, which is where the Tor
amplitude theory of Stacks 0652 is stated. Derived extension of scalars along `B → B'` is
quantified over by its universal property as a total left derived functor, and the chain map
between the two doubles is produced from the module-level comparison, so that no model of
derived base change enters the statement. Tor amplitude in `[-1, 0]` forces the conormal module
to be flat — through the distinguished triangle of the two-term complex and Stacks 0655, then
Stacks 0654 and 066F — hence the double to be K-flat, hence the comparison from derived to
ordinary extension of scalars to be invertible there.

The derived tensor product of Stacks 0652 is supplied as a bifunctor certified by a comparison
with termwise tensoring and the universal property making each `- ⊗ᴸ M[0]` a total left derived
functor, as in `StacksDraft.TorAmplitude.HasTorAmplitude`; the two further hypotheses that each
`- ⊗ᴸ M[0]` commutes with the shift and is triangulated are the exactness input of Stacks 0655,
whose endpoints are stated with them.

## References

* [The Stacks Project, Lemma 15.87.3 (0FJU)](https://stacks.math.columbia.edu/tag/0FJU)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TensorProduct

namespace NaiveCotangent

universe uA uB uC

attribute [local instance] HasDerivedCategory.standard

/-! ### Flat base change of the conormal module -/

section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
private lemma tensorCotangentHom_injective_of_flat_quotient
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (I : Ideal S) [Module.Flat R (S ⧸ I)] :
    Function.Injective (I.tensorCotangentHom R T) := by
  let a : S →+* T ⊗[R] S := Algebra.TensorProduct.includeRight.toRingHom
  let f : (I.map a).Cotangent →ₗ[T] T ⊗[R] S ⧸ (I.map a) ^ 2 :=
    (Ideal.cotangentToQuotientSquare _).restrictScalars T
  suffices h : Function.Injective (f ∘ₗ I.tensorCotangentHom R T) from .of_comp h
  let g : T ⊗[R] I.Cotangent →ₗ[T] T ⊗[R] (S ⧸ I ^ 2) :=
    AlgebraTensorModule.lTensor T T I.cotangentToQuotientSquare
  let e : T ⊗[R] (S ⧸ I ^ 2) ≃ₐ[T] T ⊗[R] S ⧸ (I.map a) ^ 2 :=
    (Algebra.TensorProduct.tensorQuotientEquiv _ _ _ _).trans
      (Ideal.quotientEquivAlgOfEq T (Ideal.map_pow _ _ _))
  have hcomm : f ∘ₗ I.tensorCotangentHom R T = e.toLinearMap ∘ₗ g := by
    ext x
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    dsimp [f, g, e]
    rw [Ideal.tensorCotangentHom_tmul, one_smul, Ideal.toCotangent_to_quotient_square]
    simp
  rw [hcomm, LinearMap.coe_comp]
  apply e.injective.comp
  let q := (Ideal.Quotient.factorₐ R (Ideal.pow_le_self (I := I) two_ne_zero)).toLinearMap
  have hq : Function.Surjective q :=
    Ideal.Quotient.factor_surjective (Ideal.pow_le_self two_ne_zero)
  have he : Function.Exact (I.cotangentToQuotientSquare.restrictScalars R) q := by
    rw [LinearMap.exact_iff]
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    symm
    change (∃ y, I.cotangentToQuotientSquare y = Ideal.Quotient.mk (I ^ 2) x) ↔
      Ideal.Quotient.mk I x = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine ⟨fun ⟨y, hy⟩ => ?_, fun hx => ⟨I.toCotangent ⟨x, hx⟩, rfl⟩⟩
    obtain ⟨y, rfl⟩ := I.toCotangent_surjective y
    rw [Ideal.toCotangent_to_quotient_square] at hy
    change Ideal.Quotient.mk (I ^ 2) y.1 = Ideal.Quotient.mk (I ^ 2) x at hy
    rw [Ideal.Quotient.eq] at hy
    simpa using I.sub_mem y.2 (Ideal.pow_le_self two_ne_zero hy)
  exact LinearMap.lTensor_injective_of_exact_of_flat q hq
    (I.cotangentToQuotientSquare.restrictScalars R)
    I.cotangentToQuotientSquare_injective he T

private noncomputable def tensorCotangentOfFlatTarget
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (P : Algebra.Extension R S) (T : Type*) [CommRing T] [Algebra R T] :
    T ⊗[R] P.Cotangent ≃ₗ[T] (P.baseChange (T := T)).Cotangent := by
  let f : P.Ring →ₐ[R] S := IsScalarTower.toAlgHom R P.Ring S
  let e : (P.Ring ⧸ P.ker) ≃ₐ[R] S :=
    Ideal.quotientKerAlgEquivOfSurjective (f := f) P.algebraMap_surjective
  let : Module.Flat R (P.Ring ⧸ (P.ker : Ideal P.Ring)) :=
    Module.Flat.of_linearEquiv e.toLinearEquiv
  let eI := LinearEquiv.ofBijective (P.ker.tensorCotangentHom R T)
    ⟨tensorCotangentHom_injective_of_flat_quotient P.ker,
      P.ker.tensorCotangentHom_surjective R T⟩
  exact AlgebraTensorModule.congr (.refl T T)
    (P.cotangentEquivCotangentKer.restrictScalars R) ≪≫ₗ eI ≪≫ₗ
      (Ideal.Cotangent.equivOfEq _ _ (P.ker_baseChange T).symm).restrictScalars T ≪≫ₗ
      (P.baseChange (T := T)).cotangentEquivCotangentKer.symm.restrictScalars T

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
private lemma tensorCotangentOfFlatTarget_tmul
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (P : Algebra.Extension R S) (T : Type*) [CommRing T] [Algebra R T]
    (t : T) (x : P.Cotangent) :
    tensorCotangentOfFlatTarget P T (t ⊗ₜ x) =
      t • Algebra.Extension.Cotangent.map (P.toBaseChange T) x := by
  obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  simp only [tensorCotangentOfFlatTarget, LinearEquiv.trans_apply,
    AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
    LinearEquiv.restrictScalars_apply, Algebra.Extension.cotangentEquivCotangentKer_apply,
    Algebra.Extension.Cotangent.val_mk, LinearEquiv.ofBijective_apply,
    Ideal.tensorCotangentHom_tmul, map_smul, Algebra.Extension.Cotangent.map_mk,
    Algebra.Extension.Hom.toAlgHom_apply, Ideal.Cotangent.equivOfEq_toCotangent]
  rfl

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
private lemma cotangent_liftBaseChange_bijective_of_flat_target
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (P : Algebra.Extension R S) (T : Type*) [CommRing T] [Algebra R T] :
    Function.Bijective
      ((Algebra.Extension.Cotangent.map (P.toBaseChange T)).liftBaseChange (T ⊗[R] S)) := by
  let e := Algebra.IsPushout.cancelBaseChange R T S (T ⊗[R] S) P.Cotangent
  let f := (Algebra.Extension.Cotangent.map (P.toBaseChange T)).liftBaseChange (T ⊗[R] S)
  have heq : f.restrictScalars T ∘ₗ e.symm.toLinearMap =
      (tensorCotangentOfFlatTarget P T).toLinearMap := by
    refine TensorProduct.AlgebraTensorModule.ext fun t x => ?_
    simp only [LinearMap.coe_restrictScalars, LinearMap.comp_apply, LinearEquiv.coe_coe,
      e, Algebra.IsPushout.cancelBaseChange_symm_tmul, f, LinearMap.liftBaseChange_tmul,
      tensorCotangentOfFlatTarget_tmul]
    exact IsScalarTower.algebraMap_smul (T ⊗[R] S) t _
  refine (Function.Bijective.of_comp_iff _ e.symm.bijective).1 ?_
  rw [show ⇑f ∘ ⇑e.symm = ⇑(tensorCotangentOfFlatTarget P T) from congrArg DFunLike.coe heq]
  exact (tensorCotangentOfFlatTarget P T).bijective

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
private lemma cotangent_generators_liftBaseChange_injective_of_flat_target
    {R S T ι : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Module.Flat R S]
    (P : Algebra.Generators R S ι) :
    let h := (P.baseChangeFromBaseChange T).comp (P.toExtension.toBaseChange T)
    Function.Injective ((Algebra.Extension.Cotangent.map h).liftBaseChange (T ⊗[R] S)) := by
  intro h
  let f := P.baseChangeFromBaseChange T
  let g := P.baseChangeToBaseChange T
  have hgf : g.comp f = .id _ := by
    ext x
    change (MvPolynomial.algebraTensorAlgEquiv R T).symm
      (MvPolynomial.algebraTensorAlgEquiv R T x) = x
    exact (MvPolynomial.algebraTensorAlgEquiv R T).symm_apply_apply x
  have hf : Function.Injective (Algebra.Extension.Cotangent.map f) := by
    have hcomp : Algebra.Extension.Cotangent.map g ∘ₗ Algebra.Extension.Cotangent.map f =
        LinearMap.id := by
      calc
        _ = Algebra.Extension.Cotangent.map (g.comp f) := by
          simpa using (Algebra.Extension.Cotangent.map_comp _ f g).symm
        _ = _ := by rw [hgf, Algebra.Extension.Cotangent.map_id]
    refine Function.Injective.of_comp (f := ⇑(Algebra.Extension.Cotangent.map g)) ?_
    rw [← LinearMap.coe_comp, hcomp]
    exact Function.injective_id
  have hcomp : (Algebra.Extension.Cotangent.map h).liftBaseChange (T ⊗[R] S) =
      Algebra.Extension.Cotangent.map f ∘ₗ
        (Algebra.Extension.Cotangent.map (P.toExtension.toBaseChange T)).liftBaseChange
          (T ⊗[R] S) := by
    rw [LinearMap.liftBaseChange_comp, ← Algebra.Extension.Cotangent.map_comp]
  rw [hcomp]
  exact hf.comp (cotangent_liftBaseChange_bijective_of_flat_target P.toExtension T).1

/-- **Flat base change is injective on the cycles of the conormal term.**  Let `R → S` be flat,
let `R → T` be arbitrary and let `S' = T ⊗[R] S` be the pushout.  An element of
`S' ⊗_S I/I²` killed by the base change to `S'` of the differential of `NL_{S/R}` and by the
functorial map to `J/J²` for the canonical presentation of `S'` over `T` is zero.

This is the degree-`1` injectivity that flatness buys, and the step of Stacks 0FJU that
distinguishes it from the base change statement of Stacks 0FUZ, which gives only surjectivity
there.  It is stated for the canonical presentations and for the canonical morphism between
them; any other morphism of extensions is homotopic to it, so nothing is lost. -/
lemma cotangent_intrinsic_baseChange_cycle_injective_of_flat
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Module.Flat R S] :
    let S' := T ⊗[R] S
    letI : Algebra S S' := Algebra.TensorProduct.rightAlgebra
    let P := Algebra.Generators.self R S
    let P' := Algebra.Generators.self T S'
    let h := (P.defaultHom P').toExtensionHom
    ∀ x : S' ⊗[S] P.toExtension.Cotangent,
      AlgebraTensorModule.lTensor S' S' P.toExtension.cotangentComplex x = 0 →
      (Algebra.Extension.Cotangent.map h).liftBaseChange S' x = 0 → x = 0 := by
  intro S'
  let : Algebra S S' := Algebra.TensorProduct.rightAlgebra
  intro P P' h x hx hfx
  let G := P.baseChange T
  let b := (P.baseChangeFromBaseChange T).comp (P.toExtension.toBaseChange T)
  let q := (G.defaultHom P').toExtensionHom
  let f := (Algebra.Extension.Cotangent.map b).liftBaseChange S'
  have hy : G.toExtension.cotangentComplex (f x) = 0 := by
    have hsq := DFunLike.congr_fun (cotangent_generators_baseChange_square P (T := T)) x
    change G.toExtension.cotangentComplex (f x) =
      (Algebra.Extension.CotangentSpace.map b).liftBaseChange S'
        (AlgebraTensorModule.lTensor S' S' P.toExtension.cotangentComplex x) at hsq
    rwa [hx, map_zero] at hsq
  let y : G.toExtension.H1Cotangent := ⟨f x, hy⟩
  have hqy : Algebra.Extension.H1Cotangent.map q y = 0 := by
    apply Subtype.ext
    have hc : Algebra.Extension.Cotangent.map q ∘ₗ f =
        (Algebra.Extension.Cotangent.map (q.comp b)).liftBaseChange S' := by
      rw [LinearMap.liftBaseChange_comp, ← Algebra.Extension.Cotangent.map_comp]
    change (Algebra.Extension.Cotangent.map q ∘ₗ f) x = 0
    rw [hc, ← cotangent_maps_agree_on_tensored_cycles h (q.comp b) x hx]
    exact hfx
  exact cotangent_generators_liftBaseChange_injective_of_flat_target P
    ((congrArg Subtype.val ((Algebra.Generators.H1Cotangent.equiv G P').injective
      (hqy.trans (map_zero _).symm))).trans (map_zero f).symm)

end

/-! ### Two-term cochain complexes -/

open scoped ChangeOfRings

section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private lemma fromExtendScalars_one_tmul
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {X : ModuleCat R} {Y : ModuleCat S}
    (g : X ⟶ (ModuleCat.restrictScalars f).obj Y) (x : X) :
    (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars f g)
      ((1 : S) ⊗ₜ[R,f] x) = g x := by
  change (1 : S) • g x = g x
  exact one_smul S (g x)

/-- Two additive maps out of an extension of scalars agreeing on pure tensors are equal. -/
private lemma extendScalars_addMonoidHom_apply_eq
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {X : ModuleCat R}
    {N : Type*} [AddCommGroup N] (φ ψ : (ModuleCat.extendScalars f).obj X →+ N)
    (h : ∀ (s : S) (x : X), φ (s ⊗ₜ[R,f] x) = ψ (s ⊗ₜ[R,f] x))
    (x : (ModuleCat.extendScalars f).obj X) : φ x = ψ x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s x => exact h s x

private lemma exists_map_double
    {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroObject C] [HasZeroObject D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {ι : Type*} {c : ComplexShape ι} {i₀ i₁ : ι}
    (hd : c.Rel i₀ i₁) (hne : i₀ ≠ i₁)
    {X₁ X₀ : C} {Y₁ Y₀ : D} (d : X₁ ⟶ X₀) (e : Y₁ ⟶ Y₀)
    (f₁ : F.obj X₁ ⟶ Y₁) (f₀ : F.obj X₀ ⟶ Y₀)
    (h : F.map d ≫ f₀ = f₁ ≫ e) :
    ∃ g : (F.mapHomologicalComplex c).obj
        (HomologicalComplex.double d hd) ⟶ HomologicalComplex.double e hd,
      g.f i₀ = F.map (HomologicalComplex.doubleXIso₀ d hd).hom ≫ f₁ ≫
          (HomologicalComplex.doubleXIso₀ e hd).inv ∧
      g.f i₁ = F.map (HomologicalComplex.doubleXIso₁ d hd hne).hom ≫ f₀ ≫
          (HomologicalComplex.doubleXIso₁ e hd hne).inv := by
  classical
  let K := (F.mapHomologicalComplex c).obj
    (HomologicalComplex.double d hd)
  let L := HomologicalComplex.double e hd
  let φ : ∀ i : ι, K.X i ⟶ L.X i := fun i =>
    if hi : i = i₀ then
      eqToHom (by subst i; rfl) ≫ F.map (HomologicalComplex.doubleXIso₀ d hd).hom ≫ f₁ ≫
        (HomologicalComplex.doubleXIso₀ e hd).inv ≫ eqToHom (by subst i; rfl)
    else if hi : i = i₁ then
      eqToHom (by subst i; rfl) ≫ F.map (HomologicalComplex.doubleXIso₁ d hd hne).hom ≫ f₀ ≫
        (HomologicalComplex.doubleXIso₁ e hd hne).inv ≫ eqToHom (by subst i; rfl)
    else 0
  have hc (i j : ι) (hij : c.Rel i j) :
      K.d i j ≫ φ j = φ i ≫ L.d i j := by
    by_cases hi : i = i₀
    · subst i
      have hj : j = i₁ := c.next_eq hij hd
      clear hij
      subst j
      simp only [φ, dite_eq_left rfl, dite_eq_right hne.symm,
        eqToHom_refl, Category.id_comp, Category.comp_id, dite_true]
      dsimp only [K, L, Functor.mapHomologicalComplex_obj_d]
      rw [HomologicalComplex.double_d d hd hne,
        HomologicalComplex.double_d e hd hne]
      simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
      rw [← F.map_comp_assoc (HomologicalComplex.doubleXIso₁ d hd hne).inv
        (HomologicalComplex.doubleXIso₁ d hd hne).hom,
        Iso.inv_hom_id, F.map_id, Category.id_comp]
      simpa only [Category.assoc] using congrArg
        (fun k => F.map (HomologicalComplex.doubleXIso₀ d hd).hom ≫ k ≫
          (HomologicalComplex.doubleXIso₁ e hd hne).inv) h
    · have hdz : K.d i j = 0 := by
        dsimp only [K, Functor.mapHomologicalComplex_obj_d]
        rw [HomologicalComplex.double_d_eq_zero₀ d hd i j hi, F.map_zero]
      have hez : L.d i j = 0 := HomologicalComplex.double_d_eq_zero₀ e hd i j hi
      rw [hdz, hez, zero_comp, comp_zero]
  refine ⟨{ f := φ, comm' := fun i j hij => (hc i j hij).symm }, ?_, ?_⟩ <;>
    simp [φ, hne.symm]

set_option backward.isDefEq.respectTransparency false in
private lemma quasiIso_of_cycle_boundaries
    {R : Type*} [CommRing R] {S T : ShortComplex (ModuleCat R)} (f : S ⟶ T)
    (hinj : ∀ x : S.X₂, S.g x = 0 → f.τ₂ x ∈ LinearMap.range T.f.hom →
      x ∈ LinearMap.range S.f.hom)
    (hsurj : ∀ y : T.X₂, T.g y = 0 → ∃ x : S.X₂,
      S.g x = 0 ∧ y - f.τ₂ x ∈ LinearMap.range T.f.hom) : ShortComplex.QuasiIso f := by
  let c : LinearMap.ker S.g.hom →ₗ[R] LinearMap.ker T.g.hom :=
    (f.τ₂.hom.comp (LinearMap.ker S.g.hom).subtype).codRestrict _ (by
      intro x
      have h := ConcreteCategory.congr_hom f.comm₂₃ x.val
      change T.g (f.τ₂ x.val) = f.τ₃ (S.g x.val) at h
      change T.g (f.τ₂ x.val) = 0
      rw [h, show S.g x.val = 0 from x.property, map_zero])
  have hc : LinearMap.range S.moduleCatToCycles ≤
      (LinearMap.range T.moduleCatToCycles).comap c := by
    rintro _ ⟨x, rfl⟩
    exact ⟨f.τ₁ x, Subtype.ext (ConcreteCategory.congr_hom f.comm₁₂ x)⟩
  let q := (LinearMap.range S.moduleCatToCycles).mapQ
    (LinearMap.range T.moduleCatToCycles) c hc
  let data : ShortComplex.LeftHomologyMapData f
      S.moduleCatLeftHomologyData T.moduleCatLeftHomologyData := {
    φK := ModuleCat.ofHom c
    φH := ModuleCat.ofHom q
    commi := by ext x; rfl
    commf' := by
      ext x
      exact Subtype.ext (ConcreteCategory.congr_hom f.comm₁₂ x).symm
    commπ := by ext x; rfl }
  rw [data.quasiIso_iff, ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective q
  refine ⟨(injective_iff_map_eq_zero q).mpr fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨x, rfl⟩ := (LinearMap.range S.moduleCatToCycles).mkQ_surjective x
    change (LinearMap.range T.moduleCatToCycles).mkQ (c x) = 0 at hx
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx ⊢
    obtain ⟨y, hy⟩ := hx
    obtain ⟨z, hz⟩ := hinj x.val x.property ⟨y, congrArg Subtype.val hy⟩
    exact ⟨z, Subtype.ext hz⟩
  · obtain ⟨y, rfl⟩ := (LinearMap.range T.moduleCatToCycles).mkQ_surjective y
    obtain ⟨x, hx, z, hz⟩ := hsurj y.val y.property
    refine ⟨(LinearMap.range S.moduleCatToCycles).mkQ ⟨x, hx⟩, ?_⟩
    change (LinearMap.range T.moduleCatToCycles).mkQ (c ⟨x, hx⟩) =
      (LinearMap.range T.moduleCatToCycles).mkQ y
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    refine ⟨-z, ?_⟩
    apply Subtype.ext
    change T.f (-z) = f.τ₂ x - y.val
    rw [map_neg, hz]
    abel

private lemma quasiIso_of_twoTerm
    {R : Type*} [CommRing R] {K L : CochainComplex (ModuleCat R) ℤ} (f : K ⟶ L)
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (K.X i))
    (hL : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (L.X i))
    (hi₁ : ∀ x, K.d (-1) 0 x = 0 → f.f (-1) x = 0 → x = 0)
    (hs₁ : ∀ y, L.d (-1) 0 y = 0 → ∃ x, K.d (-1) 0 x = 0 ∧ f.f (-1) x = y)
    (hi₀ : ∀ x, f.f 0 x ∈ LinearMap.range (L.d (-1) 0).hom →
      x ∈ LinearMap.range (K.d (-1) 0).hom)
    (hs₀ : ∀ y, ∃ x, y - f.f 0 x ∈ LinearMap.range (L.d (-1) 0).hom) :
    QuasiIso f := by
  rw [quasiIso_iff]
  intro i
  by_cases hi : i = -1
  · subst i
    rw [quasiIsoAt_iff' f (-2) (-1) 0 (by simp) (by simp)]
    have hez : L.d (-2) (-1) = 0 := (hL (-2) (by decide) (by decide)).eq_of_src _ _
    apply quasiIso_of_cycle_boundaries
    · intro x hx hfx
      change f.f (-1) x ∈ LinearMap.range (L.d (-2) (-1)).hom at hfx
      rw [hez, ModuleCat.hom_zero, LinearMap.range_zero, Submodule.mem_bot] at hfx
      change x ∈ LinearMap.range (K.d (-2) (-1)).hom
      rw [hi₁ x hx hfx]
      exact Submodule.zero_mem _
    · intro y hy
      change L.X (-1) at y
      obtain ⟨x, hx, hfx⟩ := hs₁ y hy
      refine ⟨x, hx, ?_⟩
      change y - f.f (-1) x ∈ LinearMap.range (L.d (-2) (-1)).hom
      rw [hfx, sub_self]
      exact Submodule.zero_mem _
  · by_cases hi' : i = 0
    · subst i
      rw [quasiIsoAt_iff' f (-1) 0 1 (by simp) (by simp)]
      have hdz : K.d 0 1 = 0 := (hK 1 (by decide) (by decide)).eq_of_tgt _ _
      apply quasiIso_of_cycle_boundaries
      · exact fun x _ hx => hi₀ x hx
      · intro y _
        obtain ⟨x, hx⟩ := hs₀ y
        refine ⟨x, ?_, hx⟩
        change K.d 0 1 x = 0
        rw [hdz]
        rfl
    · exact (quasiIsoAt_iff_exactAt f i ((K.sc i).exact_of_isZero_X₂ (hK i hi hi'))).2
        ((L.sc i).exact_of_isZero_X₂ (hL i hi hi'))

private lemma quasiIso_of_twoTerm_equiv
    {R : Type*} [CommRing R] {K L : CochainComplex (ModuleCat R) ℤ} (f : K ⟶ L)
    {M₁ M₀ N₁ N₀ : Type*} [AddCommGroup M₁] [AddCommGroup M₀]
    [AddCommGroup N₁] [AddCommGroup N₀]
    (d : M₁ →+ M₀) (e : N₁ →+ N₀) (f₁ : M₁ →+ N₁) (f₀ : M₀ →+ N₀)
    (k₁ : K.X (-1) ≃+ M₁) (k₀ : K.X 0 ≃+ M₀)
    (l₁ : L.X (-1) ≃+ N₁) (l₀ : L.X 0 ≃+ N₀)
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (K.X i))
    (hL : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (L.X i))
    (hd : ∀ x, k₀ (K.d (-1) 0 x) = d (k₁ x))
    (he : ∀ x, l₀ (L.d (-1) 0 x) = e (l₁ x))
    (hf₁ : ∀ x, l₁ (f.f (-1) x) = f₁ (k₁ x))
    (hf₀ : ∀ x, l₀ (f.f 0 x) = f₀ (k₀ x))
    (hi₁ : ∀ x, d x = 0 → f₁ x = 0 → x = 0)
    (hs₁ : ∀ y, e y = 0 → ∃ x, d x = 0 ∧ f₁ x = y)
    (hi₀ : ∀ x, (∃ y, e y = f₀ x) → ∃ y, d y = x)
    (hs₀ : ∀ y, ∃ x z, e z = y - f₀ x) : QuasiIso f := by
  apply quasiIso_of_twoTerm f hK hL
  · intro x hx hfx
    apply k₁.injective
    rw [map_zero]
    apply hi₁
    · rw [← hd, hx, map_zero]
    · rw [← hf₁, hfx, map_zero]
  · intro y hy
    obtain ⟨x, hx, hfx⟩ := hs₁ (l₁ y) (by rw [← he, hy, map_zero])
    refine ⟨k₁.symm x, ?_, ?_⟩
    · apply k₀.injective
      rw [map_zero, hd, k₁.apply_symm_apply, hx]
    · apply l₁.injective
      rw [hf₁, k₁.apply_symm_apply, hfx]
  · rintro x ⟨y, hy⟩
    obtain ⟨z, hz⟩ := hi₀ (k₀ x) ⟨l₁ y, by rw [← he, hy, hf₀]⟩
    refine ⟨k₁.symm z, ?_⟩
    apply k₀.injective
    rw [hd, k₁.apply_symm_apply, hz]
  · intro y
    obtain ⟨x, z, hz⟩ := hs₀ (l₀ y)
    refine ⟨k₀.symm x, l₁.symm z, ?_⟩
    apply l₀.injective
    rw [he, l₁.apply_symm_apply, hz, map_sub, hf₀, k₀.apply_symm_apply]

private lemma quasiIso_map_double_of_equiv
    {R R' : Type*} [CommRing R] [CommRing R'] (F : ModuleCat R ⥤ ModuleCat R')
    [F.PreservesZeroMorphisms] (hd : (ComplexShape.up ℤ).Rel (-1) 0) (hne : (-1 : ℤ) ≠ 0)
    {X₁ X₀ : ModuleCat R} {Y₁ Y₀ : ModuleCat R'} (d : X₁ ⟶ X₀) (d' : Y₁ ⟶ Y₀)
    (f₁ : F.obj X₁ ⟶ Y₁) (f₀ : F.obj X₀ ⟶ Y₀)
    (g : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (HomologicalComplex.double d hd) ⟶
      HomologicalComplex.double d' hd)
    (hg₁ : g.f (-1) = F.map (HomologicalComplex.doubleXIso₀ d hd).hom ≫ f₁ ≫
      (HomologicalComplex.doubleXIso₀ d' hd).inv)
    (hg₀ : g.f 0 = F.map (HomologicalComplex.doubleXIso₁ d hd hne).hom ≫ f₀ ≫
      (HomologicalComplex.doubleXIso₁ d' hd hne).inv)
    {M₁ M₀ N₁ N₀ : Type*} [AddCommGroup M₁] [AddCommGroup M₀]
    [AddCommGroup N₁] [AddCommGroup N₀]
    (δ : M₁ →+ M₀) (δ' : N₁ →+ N₀) (φ₁ : M₁ →+ N₁) (φ₀ : M₀ →+ N₀)
    (e₁ : F.obj X₁ ≃+ M₁) (e₀ : F.obj X₀ ≃+ M₀) (e₁' : Y₁ ≃+ N₁) (e₀' : Y₀ ≃+ N₀)
    (hδ : ∀ x, e₀ (F.map d x) = δ (e₁ x)) (hδ' : ∀ x, e₀' (d' x) = δ' (e₁' x))
    (hφ₁ : ∀ x, e₁' (f₁ x) = φ₁ (e₁ x)) (hφ₀ : ∀ x, e₀' (f₀ x) = φ₀ (e₀ x))
    (hi₁ : ∀ x, δ x = 0 → φ₁ x = 0 → x = 0)
    (hs₁ : ∀ y, δ' y = 0 → ∃ x, δ x = 0 ∧ φ₁ x = y)
    (hi₀ : ∀ x, (∃ y, δ' y = φ₀ x) → ∃ y, δ y = x)
    (hs₀ : ∀ y, ∃ x z, δ' z = y - φ₀ x) : QuasiIso g := by
  refine quasiIso_of_twoTerm_equiv g δ δ' φ₁ φ₀
    ((F.mapIso (HomologicalComplex.doubleXIso₀ d hd)).toLinearEquiv.toAddEquiv.trans e₁)
    ((F.mapIso (HomologicalComplex.doubleXIso₁ d hd hne)).toLinearEquiv.toAddEquiv.trans e₀)
    ((HomologicalComplex.doubleXIso₀ d' hd).toLinearEquiv.toAddEquiv.trans e₁')
    ((HomologicalComplex.doubleXIso₁ d' hd hne).toLinearEquiv.toAddEquiv.trans e₀')
    (fun i hi hi' => F.map_isZero (HomologicalComplex.isZero_double_X d hd i hi hi'))
    (fun i hi hi' => HomologicalComplex.isZero_double_X d' hd i hi hi') ?_ ?_ ?_ ?_
    hi₁ hs₁ hi₀ hs₀
  · intro x
    change e₀ ((F.map (HomologicalComplex.doubleXIso₁ d hd hne).hom)
      ((F.map ((HomologicalComplex.double d hd).d (-1) 0)) x)) =
        δ (e₁ ((F.map (HomologicalComplex.doubleXIso₀ d hd).hom) x))
    have hc : F.map ((HomologicalComplex.double d hd).d (-1) 0) ≫
        F.map (HomologicalComplex.doubleXIso₁ d hd hne).hom =
        F.map (HomologicalComplex.doubleXIso₀ d hd).hom ≫ F.map d := by
      rw [← Functor.map_comp, HomologicalComplex.double_d d hd hne]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Functor.map_comp]
    rw [← ModuleCat.comp_apply, hc, ModuleCat.comp_apply]
    exact hδ _
  · intro x
    change e₀' ((HomologicalComplex.doubleXIso₁ d' hd hne).hom
      ((HomologicalComplex.double d' hd).d (-1) 0 x)) =
        δ' (e₁' ((HomologicalComplex.doubleXIso₀ d' hd).hom x))
    rw [HomologicalComplex.double_d d' hd hne]
    simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply]
    exact hδ' _
  · intro x
    change e₁' ((HomologicalComplex.doubleXIso₀ d' hd).hom (g.f (-1) x)) =
      φ₁ (e₁ ((F.map (HomologicalComplex.doubleXIso₀ d hd).hom) x))
    rw [hg₁]
    simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply]
    exact hφ₁ _
  · intro x
    change e₀' ((HomologicalComplex.doubleXIso₁ d' hd hne).hom (g.f 0 x)) =
      φ₀ (e₀ ((F.map (HomologicalComplex.doubleXIso₁ d hd hne).hom) x))
    rw [hg₀]
    simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply]
    exact hφ₀ _

private lemma exists_double_shortExact
    {R : Type*} [CommRing R] {X₁ X₀ : ModuleCat R} (d : X₁ ⟶ X₀) :
    let K := HomologicalComplex.double d (show (ComplexShape.up ℤ).Rel (-1) 0 by decide)
    ∃ (i : (CochainComplex.singleFunctor (ModuleCat R) 0).obj X₀ ⟶ K)
      (p : K ⟶ (CochainComplex.singleFunctor (ModuleCat R) (-1)).obj X₁)
      (h : i ≫ p = 0), (ShortComplex.mk i p h).ShortExact := by
  classical
  intro K
  let hd : (ComplexShape.up ℤ).Rel (-1) 0 := by decide
  let i : (CochainComplex.singleFunctor (ModuleCat R) 0).obj X₀ ⟶ K :=
    HomologicalComplex.mkHomFromSingle (HomologicalComplex.doubleXIso₁ d hd (by omega)).inv
      (by intro k hk; rw [HomologicalComplex.double_d_eq_zero₀ d hd 0 k (by omega), comp_zero])
  let p : K ⟶ (CochainComplex.singleFunctor (ModuleCat R) (-1)).obj X₁ :=
    HomologicalComplex.mkHomToSingle (HomologicalComplex.doubleXIso₀ d hd).hom
      (by intro j hj; rw [HomologicalComplex.double_d_eq_zero₁ d hd j (-1) (by omega), zero_comp])
  have hi : IsIso (i.f 0) := by
    dsimp only [i]
    rw [HomologicalComplex.mkHomFromSingle_f]
    infer_instance
  have hp : IsIso (p.f (-1)) := by
    dsimp only [p]
    rw [HomologicalComplex.mkHomToSingle_f]
    infer_instance
  have hip : i ≫ p = 0 := by
    apply HomologicalComplex.from_single_hom_ext
    exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (-1) X₁ 0
      (by omega)).eq_of_tgt _ _
  refine ⟨i, p, hip, HomologicalComplex.shortExact_of_degreewise_shortExact _ ?_⟩
  intro n
  let S := (ShortComplex.mk i p hip).map (HomologicalComplex.eval (ModuleCat R) _ n)
  change S.ShortExact
  have hm : Mono S.f := by
    by_cases hn : n = 0
    · subst n; exact inferInstanceAs (Mono (i.f 0))
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 X₀ n hn).mono _
  have he : Epi S.g := by
    by_cases hn : n = -1
    · subst n; exact inferInstanceAs (Epi (p.f (-1)))
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (-1) X₁ n hn).epi _
  refine { exact := ?_, mono_f := hm, epi_g := he }
  by_cases hn : n = 0
  · subst n
    rw [ShortComplex.moduleCat_exact_iff]
    exact fun x _ => (ModuleCat.epi_iff_surjective (i.f 0)).1 inferInstance x
  · by_cases hn' : n = -1
    · subst n
      rw [ShortComplex.moduleCat_exact_iff]
      intro x hx
      have hx0 : x = 0 := (ModuleCat.mono_iff_injective (p.f (-1))).1 inferInstance
        (hx.trans (map_zero _).symm)
      exact ⟨0, (map_zero _).trans hx0.symm⟩
    · exact S.exact_of_isZero_X₂ (HomologicalComplex.isZero_double_X d hd n hn' hn)

end

/-! ### From Tor amplitude to flatness of the conormal term -/

section TorAmplitude

open StacksDraft.TorAmplitude

variable {R : Type uA} [CommRing R]
  {derivedTensor : DerivedCategory (ModuleCat.{uA} R) ⥤
    DerivedCategory (ModuleCat.{uA} R) ⥤ DerivedCategory (ModuleCat.{uA} R)}
  (tensorComparison : ∀ M : ModuleCat.{uA} R,
    DerivedCategory.Q ⋙ derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{uA} R) 0).obj M) ⟶
      (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (tensorIsLeftDerived : ∀ M : ModuleCat.{uA} R,
    (derivedTensor.flip.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{uA} R) 0).obj M)).IsLeftDerivedFunctor
        (tensorComparison M)
        (HomologicalComplex.quasiIso (ModuleCat.{uA} R) (ComplexShape.up ℤ)))
  (tensorCommShift : ∀ M : ModuleCat.{uA} R,
    (derivedTensor.flip.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{uA} R) 0).obj M)).CommShift ℤ)
  (tensorTriangulated : ∀ M : ModuleCat.{uA} R, letI := tensorCommShift M;
    (derivedTensor.flip.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{uA} R) 0).obj M)).IsTriangulated)

/-- Tor amplitude of Stacks 0652 with the endofunctor `- ⊗ᴸ N[0]` written in flipped form and
the excluded degrees spelled `i < a ∨ b < i`. -/
private lemma hasTorAmplitude_iff_flip (K : DerivedCategory (ModuleCat.{uA} R)) (a b : ℤ) :
    HasTorAmplitude derivedTensor tensorComparison tensorIsLeftDerived K a b ↔
      ∀ (N : ModuleCat.{uA} R) (i : ℤ), (i < a ∨ b < i) →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{uA} R) i).obj
          ((derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{uA} R) 0).obj N)).obj K)) := by
  simp only [HasTorAmplitude, Set.mem_Icc, not_and_or, not_le, Functor.flip_obj_obj]

include tensorCommShift in
/-- Shifting an object of `D(R)` shifts an interval of Tor amplitude. -/
private lemma hasTorAmplitude_shift (X : DerivedCategory (ModuleCat.{uA} R)) (a b n : ℤ)
    (h : HasTorAmplitude derivedTensor tensorComparison tensorIsLeftDerived X a b) :
    HasTorAmplitude derivedTensor tensorComparison tensorIsLeftDerived (X⟦n⟧) (a - n) (b - n) := by
  rw [hasTorAmplitude_iff_flip] at h ⊢
  intro N j hj
  let := tensorCommShift N
  exact (h N (n + j) (by omega)).of_iso
    (((DerivedCategory.homologyFunctor (ModuleCat.{uA} R) j).mapIso
      (((derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{uA} R) 0).obj N)).commShiftIso n).app X)) ≪≫
    ((DerivedCategory.homologyFunctor (ModuleCat.{uA} R) 0).shiftIso n j (n + j) rfl).app _)

/-- A module placed in cohomological degree `0` whose Tor amplitude is bounded below by `0` is
flat, whatever the upper bound: a bounded above projective representative of `M[0]` vanishes in
positive degrees, so the termwise tensor complex has no cohomology there. -/
private lemma flat_of_hasTorAmplitude_single (X : ModuleCat.{uA} R) (b : ℤ)
    (h : HasTorAmplitude derivedTensor tensorComparison tensorIsLeftDerived
      ((DerivedCategory.singleFunctor (ModuleCat.{uA} R) 0).obj X) 0 b) :
    Module.Flat R X := by
  have hsingle (i : ℤ) (hi : i ≠ 0) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{uA} R) i).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{uA} R) 0).obj X)) :=
    (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 X i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat.{uA} R) i).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{uA} R) 0).app X) ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{uA} R) i).app _)
  obtain ⟨P, hproj, hPLE, ⟨eP⟩⟩ := exists_projective_representative_of_isLE
    ((DerivedCategory.singleFunctor (ModuleCat.{uA} R) 0).obj X) 0
    (fun i hi => hsingle i (by omega))
  have hflat (i : ℤ) : Module.Flat R (P.X i) := by
    have := hproj i
    infer_instance
  have hbdd : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i) :=
    ⟨0, (CochainComplex.isStrictlyLE_iff P 0).1 hPLE⟩
  have hP := (hasTorAmplitude_iff_termwise_of_flat tensorComparison tensorIsLeftDerived P hbdd
    hflat 0 b).mp ((hasTorAmplitude_of_iso eP 0 b).mp h)
  refine (hasTorDimensionLE_iff_hasFlatRepresentative tensorComparison tensorIsLeftDerived
    X 0).2.mp ((hasTorAmplitude_of_iso eP 0 0).mpr
      ((hasTorAmplitude_iff_termwise_of_flat tensorComparison tensorIsLeftDerived P hbdd
        hflat 0 0).mpr ?_))
  rintro M i (hi | hi)
  · exact hP M i (Or.inl hi)
  · rcases lt_or_ge b i with hib | hib
    · exact hP M i (Or.inr hib)
    · exact (HomologicalComplex.ExactAt.of_isZero
        ((MonoidalCategory.tensorRight M).map_isZero
          ((CochainComplex.isStrictlyLE_iff P 0).1 hPLE i hi))).isZero_homology

include tensorCommShift tensorTriangulated in
/-- **Flatness from Tor amplitude for a two-term complex.** If the two-term complex
`X₁ → X₀` in degrees `-1` and `0` has Tor amplitude in `[-1, 0]` and `X₀` is flat, then `X₁` is
flat. This is the direction of Stacks 0653 used in the proof of Stacks 0FJU. -/
private lemma flat_of_double_torAmplitude {X₁ X₀ : ModuleCat.{uA} R} (d : X₁ ⟶ X₀)
    [Module.Flat R X₀]
    (h : HasTorAmplitude derivedTensor tensorComparison tensorIsLeftDerived
      (DerivedCategory.Q.obj (HomologicalComplex.double d
        (show (ComplexShape.up ℤ).Rel (-1) 0 by decide))) (-1) 0) :
    Module.Flat R X₁ := by
  obtain ⟨i, p, hip, hS⟩ := exists_double_shortExact d
  let T := DerivedCategory.triangleOfSES hS
  have h₀ : HasTorAmplitude derivedTensor tensorComparison tensorIsLeftDerived
      ((DerivedCategory.singleFunctor (ModuleCat.{uA} R) 0).obj X₀) 0 0 :=
    (hasTorDimensionLE_iff_hasFlatRepresentative tensorComparison tensorIsLeftDerived
      X₀ 0).2.mpr inferInstance
  have h₀' : HasTorAmplitude derivedTensor tensorComparison tensorIsLeftDerived T.obj₁ 0 1 := by
    have h₀q := (hasTorAmplitude_of_iso
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{uA} R) 0).app X₀) 0 0).mp h₀
    intro M j hj
    exact h₀q M j (by simp only [Set.mem_Icc, not_and_or, not_le] at hj ⊢; omega)
  have h₁ : HasTorAmplitude derivedTensor tensorComparison tensorIsLeftDerived T.obj₃ (-1) 0 :=
    hasTorAmplitude_obj₃_of_obj₁_obj₂ derivedTensor tensorComparison tensorIsLeftDerived
      tensorCommShift tensorTriangulated T (DerivedCategory.triangleOfSES_distinguished hS)
      (-1) 0 h₀' h
  have h₁' := (hasTorAmplitude_of_iso
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{uA} R) (-1)).app X₁) (-1) 0).mpr h₁
  have hs := hasTorAmplitude_shift tensorComparison tensorIsLeftDerived tensorCommShift
    _ (-1) 0 (-1) h₁'
  exact flat_of_hasTorAmplitude_single tensorComparison tensorIsLeftDerived X₁ 1
    ((hasTorAmplitude_of_iso
      (((DerivedCategory.singleFunctors (ModuleCat.{uA} R)).shiftIso (-1) 0 (-1)
        (by omega)).app X₁) 0 1).mp (by simpa using hs))

end TorAmplitude

/-! ### Derived extension of scalars at a K-flat complex -/

/-- A two-term complex of flat modules in degrees `-1` and `0` is K-flat. -/
private lemma kFlat_double_of_flat {R : Type uA} [CommRing R] {X₁ X₀ : ModuleCat.{uA} R}
    (d : X₁ ⟶ X₀) (hd : (ComplexShape.up ℤ).Rel (-1) 0) [Module.Flat R X₁] [Module.Flat R X₀] :
    CochainComplex.KFlat (HomologicalComplex.double d hd) := by
  have (n : ℤ) : Module.Flat R ((HomologicalComplex.double d hd).X n) := by
    by_cases hn : n = -1
    · subst n
      exact Module.Flat.of_linearEquiv (HomologicalComplex.doubleXIso₀ d hd).toLinearEquiv
    · by_cases hn' : n = 0
      · subst n
        exact Module.Flat.of_linearEquiv
          (HomologicalComplex.doubleXIso₁ d hd (by omega)).toLinearEquiv
      · exact Module.Flat.of_linearEquiv
          (HomologicalComplex.isZero_double_X d hd n hn hn').isoZero.toLinearEquiv
  have : CochainComplex.IsStrictlyLE (HomologicalComplex.double d hd) 0 :=
    (CochainComplex.isStrictlyLE_iff _ 0).mpr fun n hn =>
      HomologicalComplex.isZero_double_X d hd n (by omega) (by omega)
  exact CochainComplex.KFlat.kFlat_of_flat.{uA, uA} _ 0

/-- The comparison from derived to termwise extension of scalars is invertible at a K-flat
complex, for any functor exhibited as the total left derived functor of termwise extension of
scalars: it agrees, by uniqueness of total left derived functors, with the constructed one of
Stacks 064H, whose comparison is invertible there. -/
private lemma isIso_extensionComparison_of_kFlat
    {R S : Type uA} [CommRing R] [CommRing S] (f : R →+* S)
    (L : DerivedCategory (ModuleCat.{uA} R) ⥤ DerivedCategory (ModuleCat.{uA} S))
    (α : DerivedCategory.Q ⋙ L ⟶ (ModuleCat.extendScalars.{uA, uA, uA} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (hα : L.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{uA} R) (ComplexShape.up ℤ)))
    (K : CochainComplex (ModuleCat.{uA} R) ℤ) (hK : K.KFlat) : IsIso (α.app K) := by
  let W := HomologicalComplex.quasiIso (ModuleCat.{uA} R) (ComplexShape.up ℤ)
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uA, uA, uA} f
  let α' : DerivedCategory.Q ⋙ L ⟶
      CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral.{uA, uA, uA} f := α
  have hα' : L.IsLeftDerivedFunctor α' W := hα
  have : D.functor.IsLeftDerivedFunctor D.comparison W := D.isLeftDerived
  let e : D.functor ≅ L := Functor.leftDerivedUnique _ _ D.comparison α' W
  have he : e.hom.app (DerivedCategory.Q.obj K) ≫ α'.app K = D.comparison.app K := by
    simp [e, Functor.leftDerivedNatIso]
  have : IsIso (e.hom.app (DerivedCategory.Q.obj K) ≫ α'.app K) := by
    rw [he]
    exact D.comparison_isIso_of_kFlat K hK
  exact IsIso.of_isIso_comp_left (e.hom.app (DerivedCategory.Q.obj K)) (α'.app K)

/-- The cotangent space of a family of generators, lifted together with its ring to any
universes, is flat. -/
private lemma flat_ulift_cotangentSpace {R : Type*} {S : Type uB} [CommRing R] [CommRing S]
    [Algebra R S] {ι : Type*} (P : Algebra.Generators R S ι) :
    Module.Flat (ULift.{uA} S) (ULift.{uC} P.toExtension.CotangentSpace) := by
  rw [Module.Flat.ulift_left_iff, Module.Flat.ulift_right_iff]
  have : Module.Free S P.toExtension.CotangentSpace := Module.Free.of_basis P.cotangentSpaceBasis
  infer_instance

/-! ### Stacks 0FJU -/

section Statement

attribute [local instance] Algebra.TensorProduct.rightAlgebra ULift.algebra'

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Extension of scalars along `B → B'` of a lifted `B`-module `M`, as an additive equivalence
with the base change `B' ⊗[B] M`. -/
private def extendScalarsULiftAddEquiv.{u₁, u₂, u₃} (B : Type u₁) (B' : Type u₂) [CommRing B]
    [CommRing B'] [Algebra B B'] (M : Type u₃) [AddCommGroup M] [Module B M] :
    (ModuleCat.extendScalars ((algebraMap B B').ulift)).obj
        (ModuleCat.of (ULift.{max u₁ u₂ u₃} B) (ULift.{max u₁ u₂ u₃} M)) ≃+ B' ⊗[B] M :=
  let eR : ((ModuleCat.restrictScalars ((algebraMap B B').ulift)).obj
      (ModuleCat.of (ULift.{max u₁ u₂ u₃} B') (ULift.{max u₁ u₂ u₃} B'))) ≃ₗ[
        ULift.{max u₁ u₂ u₃} B] ULift.{max u₁ u₂ u₃} B' := {
    __ := AddEquiv.refl _
    map_smul' := by
      intro r x
      change ULift.up (algebraMap B B' r.down * x.down) = ULift.up (r.down • x.down)
      rw [Algebra.smul_def] }
  (TensorProduct.congr eR (LinearEquiv.refl _ _)).toAddEquiv.trans
    ((AlgebraTensorModule.uliftEquiv.{u₁, u₂, u₂, u₃, max u₁ u₂ u₃, max u₁ u₂ u₃,
        max u₁ u₂ u₃, max u₁ u₂ u₃} B B' B' M).symm.toAddEquiv.trans
      (ULift.moduleEquiv : ULift.{max u₁ u₂ u₃} (B' ⊗[B] M) ≃ₗ[B'] _).toAddEquiv)

/-- `extendScalarsULiftAddEquiv` sends `a ⊗ₜ x` to `a.down ⊗ₜ x.down`. -/
private lemma extendScalarsULiftAddEquiv_tmul.{u₁, u₂, u₃} (B : Type u₁) (B' : Type u₂) [CommRing B]
    [CommRing B'] [Algebra B B'] (M : Type u₃) [AddCommGroup M] [Module B M]
    (a : ULift.{max u₁ u₂ u₃} B')
    (x : ModuleCat.of (ULift.{max u₁ u₂ u₃} B) (ULift.{max u₁ u₂ u₃} M)) :
    extendScalarsULiftAddEquiv B B' M
        (a ⊗ₜ[ULift.{max u₁ u₂ u₃} B,(algebraMap B B').ulift] x) = a.down ⊗ₜ[B] x.down := by
  change ((AlgebraTensorModule.uliftEquiv.{u₁, u₂, u₂, u₃, max u₁ u₂ u₃, max u₁ u₂ u₃,
        max u₁ u₂ u₃, max u₁ u₂ u₃} B B' B' M).symm (a ⊗ₜ x)).down = _
  rfl

-- The lifted module categories over four rings in independent universes put every scalar tower
-- and every `ULift` module structure through instance search.
-- The chain map between the two doubles is produced from the module-level comparison, whose
-- elaboration unfolds extension of scalars termwise.
/-- **Stacks 0FJU.** Let `A → B` be flat, let `A → A'` be arbitrary and let `B' = A' ⊗[A] B` be
the pushout, so that the square with corners `A, A', B, B'` is cocartesian. Then the canonical
map `NL_{B/A} ⊗_B B' → NL_{B'/A'}` is a quasi-isomorphism, and if in addition `NL_{B/A}` has Tor
amplitude in `[-1, 0]` then the derived base-change map `NL_{B/A} ⊗_B^L B' → NL_{B'/A'}` is a
quasi-isomorphism too.

The naive cotangent complexes are the two-term complexes `HomologicalComplex.double` of the
canonical presentations, in cohomological degrees `-1` and `0`, with their modules and rings
lifted to one universe. The map of the first assertion is the displayed chain map `g`; the map of
the second is that chain map composed with the comparison from derived to ordinary extension of
scalars, which is what makes the composite the derived base-change map. -/
@[stacks 0FJU]
public theorem naiveCotangentComplex_quasiIso_baseChange_of_flat
    {A : Type uA} {B : Type uB} {A' : Type uC}
    [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A'] [Module.Flat A B] :
    let B' := A' ⊗[A] B
    letI : Algebra B B' := Algebra.TensorProduct.rightAlgebra
    let P := Algebra.Generators.self A B
    let P' := Algebra.Generators.self A' B'
    let h := (P.defaultHom P').toExtensionHom
    let X₁ : ModuleCat.{max uA uB uC} (ULift.{max uA uB uC} B) :=
      ModuleCat.of (ULift.{max uA uB uC} B)
        (ULift.{max uA uB uC} P.toExtension.Cotangent)
    let X₀ : ModuleCat.{max uA uB uC} (ULift.{max uA uB uC} B) :=
      ModuleCat.of (ULift.{max uA uB uC} B)
        (ULift.{max uA uB uC} P.toExtension.CotangentSpace)
    let X₁' : ModuleCat.{max uA uB uC} (ULift.{max uA uB uC} B') :=
      ModuleCat.of (ULift.{max uA uB uC} B')
        (ULift.{max uA uB uC} P'.toExtension.Cotangent)
    let X₀' : ModuleCat.{max uA uB uC} (ULift.{max uA uB uC} B') :=
      ModuleCat.of (ULift.{max uA uB uC} B')
        (ULift.{max uA uB uC} P'.toExtension.CotangentSpace)
    let d : X₁ ⟶ X₀ := ModuleCat.ofHom {
      toFun := fun x => ULift.up (P.toExtension.cotangentComplex x.down)
      map_add' := by
        intro x y
        exact congrArg ULift.up (P.toExtension.cotangentComplex.map_add x.down y.down)
      map_smul' := by
        intro r x
        exact congrArg ULift.up (P.toExtension.cotangentComplex.map_smul r.down x.down) }
    let d' : X₁' ⟶ X₀' := ModuleCat.ofHom {
      toFun := fun x => ULift.up (P'.toExtension.cotangentComplex x.down)
      map_add' := by
        intro x y
        exact congrArg ULift.up (P'.toExtension.cotangentComplex.map_add x.down y.down)
      map_smul' := by
        intro r x
        exact congrArg ULift.up (P'.toExtension.cotangentComplex.map_smul r.down x.down) }
    let hd : (ComplexShape.up ℤ).Rel (-1) 0 := by decide
    let hne : (-1 : ℤ) ≠ 0 := by decide
    let K : CochainComplex (ModuleCat.{max uA uB uC} (ULift.{max uA uB uC} B)) ℤ :=
      HomologicalComplex.double d hd
    let K' : CochainComplex (ModuleCat.{max uA uB uC} (ULift.{max uA uB uC} B')) ℤ :=
      HomologicalComplex.double d' hd
    let E : ModuleCat.{max uA uB uC} (ULift.{max uA uB uC} B) ⥤
        ModuleCat.{max uA uB uC} (ULift.{max uA uB uC} B') :=
      ModuleCat.extendScalars.{max uA uB uC, max uA uB uC, max uA uB uC}
        ((algebraMap B B').ulift)
    let f₁ : E.obj X₁ ⟶ X₁' :=
      ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars ((algebraMap B B').ulift)
        (ModuleCat.ofHom (Y := (ModuleCat.restrictScalars ((algebraMap B B').ulift)).obj X₁')
          { toFun := fun x => ULift.up (Algebra.Extension.Cotangent.map h x.down)
            map_add' := by
              intro x y
              exact congrArg ULift.up ((Algebra.Extension.Cotangent.map h).map_add x.down y.down)
            map_smul' := by
              intro r x
              change ULift.up _ = ULift.up _
              congr 1
              change (Algebra.Extension.Cotangent.map h) (r.down • x.down) =
                (algebraMap B B' r.down) • (Algebra.Extension.Cotangent.map h x.down)
              exact (Algebra.Extension.Cotangent.map h).map_smul r.down x.down })
    let f₀ : E.obj X₀ ⟶ X₀' :=
      ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars ((algebraMap B B').ulift)
        (ModuleCat.ofHom (Y := (ModuleCat.restrictScalars ((algebraMap B B').ulift)).obj X₀')
          { toFun := fun x => ULift.up (Algebra.Extension.CotangentSpace.map h x.down)
            map_add' := by
              intro x y
              exact congrArg ULift.up
                ((Algebra.Extension.CotangentSpace.map h).map_add x.down y.down)
            map_smul' := by
              intro r x
              change ULift.up _ = ULift.up _
              congr 1
              change (Algebra.Extension.CotangentSpace.map h) (r.down • x.down) =
                (algebraMap B B' r.down) • (Algebra.Extension.CotangentSpace.map h x.down)
              rw [IsScalarTower.algebraMap_smul]
              exact (Algebra.Extension.CotangentSpace.map h).map_smul r.down x.down })
    ∀ (derivedTensor :
        DerivedCategory (ModuleCat.{max uA uB uC} (ULift.{max uA uB uC} B)) ⥤
          DerivedCategory (ModuleCat.{max uA uB uC} (ULift.{max uA uB uC} B)) ⥤
            DerivedCategory (ModuleCat.{max uA uB uC} (ULift.{max uA uB uC} B)))
      (tensorComparison : ∀ M : ModuleCat.{max uA uB uC} (ULift.{max uA uB uC} B),
        DerivedCategory.Q ⋙ derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor
              (ModuleCat.{max uA uB uC} (ULift.{max uA uB uC} B)) 0).obj M) ⟶
          (StacksDraft.TorAmplitude.tensorModuleRight M).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (tensorIsLeftDerived : ∀ M : ModuleCat.{max uA uB uC} (ULift.{max uA uB uC} B),
        (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor
            (ModuleCat.{max uA uB uC} (ULift.{max uA uB uC} B))
            0).obj M)).IsLeftDerivedFunctor
          (tensorComparison M)
          (HomologicalComplex.quasiIso
            (ModuleCat.{max uA uB uC} (ULift.{max uA uB uC} B)) (ComplexShape.up ℤ)))
      (tensorCommShift : ∀ M : ModuleCat.{max uA uB uC} (ULift.{max uA uB uC} B),
        (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor
            (ModuleCat.{max uA uB uC} (ULift.{max uA uB uC} B)) 0).obj M)).CommShift ℤ)
      (tensorTriangulated : ∀ M : ModuleCat.{max uA uB uC} (ULift.{max uA uB uC} B),
        letI := tensorCommShift M
        (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor
            (ModuleCat.{max uA uB uC} (ULift.{max uA uB uC} B)) 0).obj M)).IsTriangulated)
      (derivedExtension :
        DerivedCategory (ModuleCat.{max uA uB uC} (ULift.{max uA uB uC} B)) ⥤
          DerivedCategory (ModuleCat.{max uA uB uC} (ULift.{max uA uB uC} B')))
      (extensionComparison :
        DerivedCategory.Q ⋙ derivedExtension ⟶
          E.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (_extensionIsLeftDerived : derivedExtension.IsLeftDerivedFunctor extensionComparison
        (HomologicalComplex.quasiIso
          (ModuleCat.{max uA uB uC} (ULift.{max uA uB uC} B)) (ComplexShape.up ℤ))),
    ∃ g : (E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ K',
      g.f (-1) =
          E.map (HomologicalComplex.doubleXIso₀ d hd).hom ≫ f₁ ≫
            (HomologicalComplex.doubleXIso₀ d' hd).inv ∧
        g.f 0 =
          E.map (HomologicalComplex.doubleXIso₁ d hd hne).hom ≫ f₀ ≫
            (HomologicalComplex.doubleXIso₁ d' hd hne).inv ∧
        QuasiIso g ∧
        (StacksDraft.TorAmplitude.HasTorAmplitude derivedTensor tensorComparison
            tensorIsLeftDerived (DerivedCategory.Q.obj K) (-1) 0 →
          IsIso (extensionComparison.app K ≫ DerivedCategory.Q.map g)) := by
  classical
  intro B' P P' h X₁ X₀ X₁' X₀' d d' hd hne K K' E f₁ f₀ derivedTensor tensorComparison
    tensorIsLeftDerived tensorCommShift tensorTriangulated derivedExtension extensionComparison
    extensionIsLeftDerived
  obtain ⟨-, -, -, -, -, hs₀', hi₀', hs₁'⟩ :=
    naiveCotangentComplex_baseChange_homology (T := A') (Algebra.Generators.self A B)
  have hsquare : E.map d ≫ f₀ = f₁ ≫ d' := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change f₀ ((E.map d) _) = d' (f₁ _)
    simp only [E, ModuleCat.ExtendScalars.map_tmul, f₀, f₁,
      fromExtendScalars_one_tmul]
    change (1 : ULift.{max uA uB uC} B') • ULift.up (Algebra.Extension.CotangentSpace.map h
      (P.toExtension.cotangentComplex x.down)) =
      ULift.up (P'.toExtension.cotangentComplex (Algebra.Extension.Cotangent.map h x.down))
    rw [one_smul]
    exact congrArg ULift.up
      (Algebra.Extension.CotangentSpace.map_cotangentComplex h x.down)
  have flatX₀ : Module.Flat (ULift.{max uA uB uC} B) X₀ := flat_ulift_cotangentSpace P
  obtain ⟨g, hg₁, hg₀⟩ := exists_map_double E hd hne d d' f₁ f₀ hsquare
  let dn := AlgebraTensorModule.lTensor B' B' P.toExtension.cotangentComplex
  let fn₁ := (Algebra.Extension.Cotangent.map h).liftBaseChange B'
  let fn₀ := (Algebra.Extension.CotangentSpace.map h).liftBaseChange B'
  let e₁ : E.obj X₁ ≃+ B' ⊗[B] P.toExtension.Cotangent :=
    extendScalarsULiftAddEquiv B B' P.toExtension.Cotangent
  let e₀ : E.obj X₀ ≃+ B' ⊗[B] P.toExtension.CotangentSpace :=
    extendScalarsULiftAddEquiv B B' P.toExtension.CotangentSpace
  let e₁' : X₁' ≃+ P'.toExtension.Cotangent :=
    (ULift.moduleEquiv : X₁' ≃ₗ[B'] P'.toExtension.Cotangent).toAddEquiv
  let e₀' : X₀' ≃+ P'.toExtension.CotangentSpace :=
    (ULift.moduleEquiv : X₀' ≃ₗ[B'] P'.toExtension.CotangentSpace).toAddEquiv
  have he₁ (a : ULift.{max uA uB uC} B') (x : X₁) :
      e₁ (a ⊗ₜ[ULift.{max uA uB uC} B,(algebraMap B B').ulift] x) = a.down ⊗ₜ[B] x.down :=
    extendScalarsULiftAddEquiv_tmul B B' _ a x
  have he₀ (a : ULift.{max uA uB uC} B') (x : X₀) :
      e₀ (a ⊗ₜ[ULift.{max uA uB uC} B,(algebraMap B B').ulift] x) = a.down ⊗ₜ[B] x.down :=
    extendScalarsULiftAddEquiv_tmul B B' _ a x
  have hdn (x : E.obj X₁) : e₀ (E.map d x) = dn (e₁ x) :=
    extendScalars_addMonoidHom_apply_eq _
      (e₀.toAddMonoidHom.comp (AddMonoidHom.mk' (E.map d) (map_add _)))
      (dn.toAddMonoidHom.comp e₁.toAddMonoidHom)
      (fun a x => by
        simp only [AddMonoidHom.comp_apply, AddMonoidHom.mk'_apply,
          AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
        erw [ModuleCat.ExtendScalars.map_tmul, extendScalarsULiftAddEquiv_tmul]) x
  have hfn₁ (x : E.obj X₁) : e₁' (f₁ x) = fn₁ (e₁ x) :=
    extendScalars_addMonoidHom_apply_eq _
      (e₁'.toAddMonoidHom.comp (AddMonoidHom.mk' f₁ (map_add _)))
      (fn₁.toAddMonoidHom.comp e₁.toAddMonoidHom)
      (fun a x => by
        change e₁' (f₁ _) = fn₁ (e₁ _)
        rw [he₁, LinearMap.liftBaseChange_tmul]; rfl) x
  have hfn₀ (x : E.obj X₀) : e₀' (f₀ x) = fn₀ (e₀ x) :=
    extendScalars_addMonoidHom_apply_eq _
      (e₀'.toAddMonoidHom.comp (AddMonoidHom.mk' f₀ (map_add _)))
      (fn₀.toAddMonoidHom.comp e₀.toAddMonoidHom)
      (fun a x => by
        change e₀' (f₀ _) = fn₀ (e₀ _)
        rw [he₀, LinearMap.liftBaseChange_tmul]; rfl) x
  have hgq : QuasiIso g :=
    quasiIso_map_double_of_equiv E hd hne d d' f₁ f₀ g hg₁ hg₀ dn.toAddMonoidHom
      P'.toExtension.cotangentComplex.toAddMonoidHom fn₁.toAddMonoidHom fn₀.toAddMonoidHom
      e₁ e₀ e₁' e₀' hdn (fun _ => rfl) hfn₁ hfn₀
      cotangent_intrinsic_baseChange_cycle_injective_of_flat hs₁' (fun x => (hi₀' x).1) hs₀'
  refine ⟨g, hg₁, hg₀, hgq, ?_⟩
  intro hamp
  have : Module.Flat (ULift.{max uA uB uC} B) X₁ :=
    flat_of_double_torAmplitude tensorComparison tensorIsLeftDerived tensorCommShift
      tensorTriangulated d hamp
  have : IsIso (extensionComparison.app K) :=
    isIso_extensionComparison_of_kFlat ((algebraMap B B').ulift) derivedExtension
      extensionComparison extensionIsLeftDerived K (kFlat_double_of_flat d hd)
  infer_instance

end Statement

end NaiveCotangent
