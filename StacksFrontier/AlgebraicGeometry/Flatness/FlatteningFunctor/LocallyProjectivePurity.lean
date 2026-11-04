module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineLocalization
public import StacksFrontier.AlgebraicGeometry.TateMap.Glue
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeLocality.GlobalSectionsAffineCase
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.ImpurityAscent
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.ClosedFibreAssociatedPrimes
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Purity
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.BaseChange
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.ConstructibleAssociatedPoints05KR
public import StacksFrontier.AlgebraicGeometry.Properties.LocallyProjectivePullback
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.Points
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent
import StacksFrontier.AlgebraicGeometry.Scheme.AffineOpenResidueField

/-!
# Relative purity of a module with locally projective direct image

A finite type quasi-coherent module on a scheme, affine and of finite type over a base, is
universally pure relative to the base as soon as its direct image is locally projective.

## Main results

* `AlgebraicGeometry.isUniversallyPureRelative_of_pushforward_isLocallyProjective`: the
  statement above, Stacks Tag 05K6.

## Implementation notes

An impurity of the module stays an impurity after the flat base change to the spectrum of the
stalk of the base at the chosen point, by `exists_impurity_after_flatPointedBaseChange`, so it
may be assumed that the base is the spectrum of a local ring and that both the base and the
source are affine.  The associated point witnessing the impurity then gives an associated
prime of the fibre module over the residue field, whose closure meets the closed fibre by
`Stacks.PureModules.associatedPrime_add_map_maximalIdeal_ne_top`; that contradicts the
impurity.

Local projectivity of the direct image is carried along the base changes by Tag 060M and the
third assertion of Tag 02KG, the latter supplied by
`Stacks.AlgebraicGeometry.AffineBaseChangeLocality.baseChangeIso` and passed to the private
lemmas as the hypothesis `bc` they take.

## References

* [Stacks Project, Tag 05K6](https://stacks.math.columbia.edu/tag/05K6)
-/

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

@[expose] public section

universe u

namespace AlgebraicGeometry

open scoped TensorProduct

private lemma relativeAssassin_mem_of_iso {Y T : Scheme.{u}} (f : Y ⟶ T)
    {M N : Y.Modules} (e : M ≅ N) {x : Y}
    (hx : x ∈ Stacks.Divisors.relativeAssassin f M) :
    x ∈ Stacks.Divisors.relativeAssassin f N := by
  rw [Stacks.Divisors.mem_relativeAssassin] at hx ⊢
  obtain ⟨s, y, hy, hyx⟩ := hx
  refine ⟨s, y, ?_, hyx⟩
  rwa [Stacks.Divisors.associatedPoints_congr
    ((Scheme.Modules.pullback (f.fiberι s)).mapIso e)] at hy

private lemma exists_closed_fiber_specialization
    (R : Type u) (S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [Algebra.FiniteType R S] (N : Type u) [AddCommGroup N] [Module S N]
    [Module R N] [IsScalarTower R S N] [Module.Projective R N] [Module.Finite S N]
    (q : PrimeSpectrum S)
    (hq : IsAssociatedPrimeStacks S
      (N ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField) q.asIdeal) :
    ∃ z : PrimeSpectrum S,
      q ≤ z ∧ (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤ z.asIdeal := by
  let I : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  let k := R ⧸ IsLocalRing.maximalIdeal R
  have : (IsLocalRing.maximalIdeal R).IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
  let : Field k := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
  let : Algebra k (S ⧸ I) :=
    (Ideal.quotientMap I (algebraMap R S) Ideal.le_comap_map).toAlgebra
  have hcomp : (algebraMap k (S ⧸ I)).comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)) =
      algebraMap R (S ⧸ I) := by
    ext r
    show Ideal.quotientMap I (algebraMap R S) Ideal.le_comap_map
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) r) =
      Ideal.Quotient.mk I ((algebraMap R S) r)
    rw [Ideal.quotientMap_mk]
  have hfiniteComp : (algebraMap R (S ⧸ I)).FiniteType := by
    rw [RingHom.finiteType_algebraMap]
    infer_instance
  have hfiniteFiber : (algebraMap k (S ⧸ I)).FiniteType := by
    have hcompFT : ((algebraMap k (S ⧸ I)).comp
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))).FiniteType := by
      rw [hcomp]
      exact hfiniteComp
    exact RingHom.FiniteType.of_comp_finiteType hcompFT
  have : Algebra.FiniteType k (S ⧸ I) := RingHom.finiteType_algebraMap.mp hfiniteFiber
  have : IsNoetherianRing k := inferInstance
  have : IsNoetherianRing (S ⧸ I) := Algebra.FiniteType.isNoetherianRing k (S ⧸ I)
  have : Module.Finite (S ⧸ I) (N ⧸ (I • (⊤ : Submodule S N))) := inferInstance
  have hproper : q.asIdeal + I ≠ ⊤ := by
    simpa [I] using Stacks.PureModules.associatedPrime_add_map_maximalIdeal_ne_top
      R S N q hq
  obtain ⟨M, hM, hqI⟩ := Ideal.exists_le_maximal (q.asIdeal + I) hproper
  refine ⟨⟨M, hM.isPrime⟩, ?_, ?_⟩
  · show q.asIdeal ≤ M
    exact le_trans le_sup_left hqI
  · show I ≤ M
    exact le_trans le_sup_right hqI

private lemma prime_spectrum_point_over_closed_point
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
    (z : PrimeSpectrum S)
    (hm : (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤ z.asIdeal) :
    PrimeSpectrum.comap (algebraMap R S) z = ⊤ := by
  apply PrimeSpectrum.ext
  show Ideal.comap (algebraMap R S) z.asIdeal = IsLocalRing.maximalIdeal R
  exact ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le
    (Ideal.comap_ne_top _ z.2.ne_top) (Ideal.map_le_iff_le_comap.mp hm)).symm

private lemma associatedPoint_affine_sections_prime
    {Y : Scheme.{u}} [IsLocallyNoetherian Y] (M : Y.Modules) [M.IsQuasicoherent]
    (V : Y.Opens) (hV : IsAffineOpen V) {x : Y} (hx : x ∈ V)
    (hassoc : Stacks.Divisors.IsAssociatedPoint M x) :
    IsAssociatedPrimeStacks Γ(Y, V) Γ(M, V)
      (hV.primeIdealOf ⟨x, hx⟩).asIdeal :=
  (isAssociatedPrime_sections_iff_isAssociatedPoint_of_isLocallyNoetherian
    M V hV hx).2 hassoc

private lemma associatedPrime_comap_of_scalarTower
    {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    {q : Ideal S} (hq : IsAssociatedPrimeStacks S M q) :
    IsAssociatedPrimeStacks R M (Ideal.comap (algebraMap R S) q) := by
  rcases hq with ⟨hqprime, x, hx⟩
  refine ⟨hqprime.comap (algebraMap R S), x, ?_⟩
  apply Submodule.ext
  intro r
  simp only [Submodule.mem_colon_span_singleton]
  rw [← hx]
  simp only [Submodule.mem_colon_span_singleton, Ideal.mem_comap]
  show r • x = 0 ↔ (algebraMap R S r) • x = 0
  rw [IsScalarTower.algebraMap_smul]

private lemma associatedPrime_of_linearEquiv
    {R M N : Type u} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (e : M ≃ₗ[R] N) {p : Ideal R}
    (h : IsAssociatedPrimeStacks R M p) : IsAssociatedPrimeStacks R N p := by
  rcases h with ⟨hp, m, hm⟩
  refine ⟨hp, e m, ?_⟩
  apply Submodule.ext
  intro r
  rw [← hm]
  simp only [Submodule.mem_colon_span_singleton, Submodule.mem_bot]
  rw [← e.map_smul, e.map_eq_zero_iff]

private lemma projective_of_extension_scalars
    {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.Projective R M] :
    Module.Projective S (S ⊗[R] M) := by
  let : Module.Projective S S := inferInstance
  exact Module.Projective.tensorProduct

private lemma residueFieldEquivOfAffineOpen_evaluation
    {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U) (y : Y) (hy : y ∈ U)
    (r : Γ(Y, U)) :
    residueFieldEquivOfAffineOpen U hU y hy (Y.evaluation U y hy r) =
      algebraMap (Γ(Y, U)) (hU.primeIdealOf ⟨y, hy⟩).asIdeal.ResidueField r := by
  let p := (hU.primeIdealOf ⟨y, hy⟩).asIdeal
  let : Algebra Γ(Y, U) (Y.presheaf.stalk y) :=
    (Y.presheaf.germ U y hy).hom.toAlgebra
  let : IsLocalization p.primeCompl (Y.presheaf.stalk y) :=
    hU.isLocalization_stalk ⟨y, hy⟩
  let e := IsLocalization.algEquiv p.primeCompl (Y.presheaf.stalk y)
      (Localization.AtPrime p)
  show IsLocalRing.ResidueField.mapEquiv e.toRingEquiv
      (IsLocalRing.residue _ ((Y.presheaf.germ U y hy).hom r)) = _
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  rw [IsScalarTower.algebraMap_apply Γ(Y, U) (Localization.AtPrime p)
    (IsLocalRing.ResidueField (Localization.AtPrime p))]
  rw [IsLocalRing.ResidueField.algebraMap_eq]
  rw [show (Y.presheaf.germ U y hy).hom r =
    algebraMap (Γ(Y, U)) (Y.presheaf.stalk y) r from rfl]
  show IsLocalRing.residue (Localization.AtPrime p)
      (e (algebraMap (Γ(Y, U)) (Y.presheaf.stalk y) r) : Localization.AtPrime p) = _
  rw [e.commutes r]

private lemma eqToHom_scheme_apply {X Y : Scheme.{u}} (e : X = Y) (x : X) :
    (eqToHom e) x = e ▸ x := by
  cases e
  rfl

private lemma fromSpecResidueField_appTop_eval
    {Y : Scheme.{u}} (y : Y) :
    (Y.fromSpecResidueField y).appTop ≫
      (Scheme.ΓSpecIso (Y.residueField y)).hom = Y.Γevaluation y := by
  rw [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop]
  rw [Category.assoc, Scheme.ΓSpecIso_naturality (Y.residue y)]
  rw [← Category.assoc, Scheme.fromSpecStalk_appTop]
  simp [Scheme.Γevaluation, Scheme.evaluation, Category.assoc]

/-- In the pushout square of rings `R → A`, `R → S`, `A → B`, `S → B`, base change of an
`A`-module `M` along `A → B` is `A`-linearly the base change of `M` to `S` along `R → S`, with
the two tensor factors exchanged.  `Algebra.IsPushout.cancelBaseChange` gives the same
identification `S`-linearly; the `A`-linear reading is what an associated prime over `A` is
transported along. -/
private noncomputable def pushoutBaseChangeCommEquiv (R S A B : Type u) [CommRing R]
    [CommRing S] [CommRing A] [CommRing B] [Algebra R S] [Algebra R A] [Algebra R B]
    [Algebra A B] [Algebra S B] [IsScalarTower R A B] [IsScalarTower R S B]
    [Algebra.IsPushout R S A B] (M : Type u) [AddCommGroup M] [Module R M] [Module A M]
    [IsScalarTower R A M] :
    (B ⊗[A] M) ≃ₗ[A] M ⊗[R] S := by
  let hcancel : (B ⊗[A] M) ≃ₗ[S] S ⊗[R] M := Algebra.IsPushout.cancelBaseChange R S A B M
  let ecomm := TensorProduct.comm R S M
  let fwd : (B ⊗[A] M) → M ⊗[R] S := fun x => ecomm (hcancel x)
  let inv : M ⊗[R] S → (B ⊗[A] M) := fun z => hcancel.symm (ecomm.symm z)
  have hinv_smul (a : A) (z : M ⊗[R] S) : inv (a • z) = a • inv z := by
    induction z using TensorProduct.induction_on with
    | zero => simp [inv]
    | add z w hz hw => simp [inv, hz, hw]
    | tmul m k =>
        simp only [inv, ecomm, TensorProduct.smul_tmul', TensorProduct.comm_symm_tmul]
        simp only [hcancel]
        rw [Algebra.IsPushout.cancelBaseChange_symm_tmul R S A B M k (a • m),
          Algebra.IsPushout.cancelBaseChange_symm_tmul R S A B M k m]
        exact TensorProduct.tmul_smul a (algebraMap S B k) m
  have hinv_inj : Function.Injective inv := fun _ _ hab =>
    ecomm.symm.injective (hcancel.symm.injective hab)
  have hfwd_smul (a : A) (x : B ⊗[A] M) : fwd (a • x) = a • fwd x := by
    apply hinv_inj
    calc
      inv (fwd (a • x)) = a • x := by simp [inv, fwd]
      _ = a • inv (fwd x) := by simp [inv, fwd]
      _ = inv (a • fwd x) := (hinv_smul a _).symm
  exact LinearEquiv.ofBijective
    { toFun := fwd
      map_add' := fun x y => by simp [fwd, ecomm]
      map_smul' := hfwd_smul }
    (ecomm.bijective.comp hcancel.bijective)

/-- A point of an affine scheme that an isomorphism onto the spectrum of a local ring carries to
the closed point is the point cut out by the maximal ideal of the ring of functions. -/
private lemma eq_fromSpec_closedPoint {T : Scheme.{u}} [IsAffine T] [IsLocalRing Γ(T, ⊤)]
    {A : CommRingCat.{u}} [IsLocalRing A] (e : T ≅ Spec A) {t : T}
    (ht : e.hom t = IsLocalRing.closedPoint A) :
    t = (isAffineOpen_top T).fromSpec (IsLocalRing.closedPoint Γ(T, ⊤)) := by
  have htopImage : e.hom
      ((isAffineOpen_top T).fromSpec (IsLocalRing.closedPoint Γ(T, ⊤))) =
      IsLocalRing.closedPoint A := by
    apply (Spec A).isoSpec.hom.homeomorph.injective
    show (Spec A).isoSpec.hom (e.hom
        ((isAffineOpen_top T).fromSpec (IsLocalRing.closedPoint Γ(T, ⊤)))) =
      (Spec A).isoSpec.hom (IsLocalRing.closedPoint A)
    have : IsLocalRing Γ(Spec A, ⊤) :=
      (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv.symm.isLocalRing
    have : IsIso e.hom.appTop := (Scheme.Γ.mapIso e.op).isIso_hom
    have hcomm : T.isoSpec.hom ≫ Spec.map e.hom.appTop =
        e.hom ≫ (Spec A).isoSpec.hom := Scheme.isoSpec_hom_naturality e.hom
    have hlocal : IsLocalHom e.hom.appTop.hom :=
      IsLocalHom.of_surjective _ (ConcreteCategory.bijective_of_isIso e.hom.appTop).2
    have hpoint := congrArg
      (fun k : T ⟶ Spec Γ(Spec A, ⊤) =>
        k ((isAffineOpen_top T).fromSpec (IsLocalRing.closedPoint Γ(T, ⊤)))) hcomm
    have hpoint' : (Spec A).isoSpec.hom (e.hom
          ((isAffineOpen_top T).fromSpec (IsLocalRing.closedPoint Γ(T, ⊤)))) =
        Spec.map e.hom.appTop (T.isoSpec.hom
          ((isAffineOpen_top T).fromSpec (IsLocalRing.closedPoint Γ(T, ⊤)))) := by
      simpa only [Scheme.Hom.comp_apply] using hpoint.symm
    have hx : T.isoSpec.hom.base
        ((isAffineOpen_top T).fromSpec (IsLocalRing.closedPoint Γ(T, ⊤))) =
        IsLocalRing.closedPoint Γ(T, ⊤) := by
      rw [IsAffineOpen.fromSpec_top (X := T)]
      show (T.isoSpec.inv ≫ T.isoSpec.hom).base (IsLocalRing.closedPoint Γ(T, ⊤)) = _
      rw [T.isoSpec.inv_hom_id]
      rfl
    rw [hpoint', hx, Spec_closedPoint, Scheme.isoSpec_Spec_hom]
    have he : IsLocalHom ((Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv :
        Γ(Spec A, ⊤) →+* A) :=
      IsLocalHom.of_surjective _
        (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv.surjective
    show IsLocalRing.closedPoint Γ(Spec A, ⊤) =
      PrimeSpectrum.comap ((Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv :
        Γ(Spec A, ⊤) →+* A) (IsLocalRing.closedPoint A)
    exact (IsLocalRing.comap_closedPoint
      ((Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv : Γ(Spec A, ⊤) →+* A)).symm
  apply e.hom.homeomorph.injective
  show e.hom t = e.hom ((isAffineOpen_top T).fromSpec (IsLocalRing.closedPoint Γ(T, ⊤)))
  rw [ht, htopImage]

/-- The map on global sections of a morphism is its `appLE` on the top opens. -/
private lemma appTop_eq_appLE {W T : Scheme.{u}} (π : W ⟶ T)
    (hle : (⊤ : W.Opens) ≤ π ⁻¹ᵁ (⊤ : T.Opens)) : π.appTop = π.appLE ⊤ ⊤ hle := by
  have h : π.appTop = π.appLE ⊤ ⊤ le_top := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    congr 1
  simpa using h

/-- For a quasi-coherent module `G` and an affine open `U`, the `Γ(X, U)`-module attached to
the inverse image of `G` on `Spec Γ(X, U)` is the module of sections of `G` over `U`. -/
private noncomputable def moduleSpecΓPullbackFromSpecEquiv {X : Scheme.{u}} (G : X.Modules)
    [G.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) :
    (AlgebraicGeometry.moduleSpecΓFunctor.obj
        ((Scheme.Modules.pullback hU.fromSpec).obj G)).carrier ≃ₗ[Γ(X, U)] Γ(G, U) := by
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  exact ((AlgebraicGeometry.moduleSpecΓFunctor (R := CommRingCat.of Γ(X, U))).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).app G).symm).toLinearEquiv.trans
    (fromSpecSectionsLinearEquiv G hU)

/-- For a morphism between schemes with affine total space, the prime of the ring of global
functions cut out by a point of the source contracts, along the map on global sections, to the
prime cut out by the image point. -/
private lemma comap_appTop_primeIdealOf_top {W T : Scheme.{u}} (π : W ⟶ T) [IsAffine W]
    [IsAffine T] (x : W) :
    PrimeSpectrum.comap π.appTop.hom
        ((isAffineOpen_top W).primeIdealOf ⟨x, Set.mem_univ _⟩) =
      (isAffineOpen_top T).primeIdealOf ⟨π x, Set.mem_univ _⟩ := by
  have hle : (⊤ : W.Opens) ≤ π ⁻¹ᵁ (⊤ : T.Opens) := by simp
  rw [appTop_eq_appLE π hle]
  exact IsAffineOpen.comap_primeIdealOf_appLE (f := π) (⊤ : T.Opens) (isAffineOpen_top T)
    (⊤ : W.Opens) (isAffineOpen_top W) hle (Set.mem_univ x)

private lemma locallyProjective_of_iso {Y : Scheme.{u}} {M N : Y.Modules}
    (e : M ≅ N) (hM : Scheme.Modules.IsLocallyProjective M) :
    Scheme.Modules.IsLocallyProjective N := by
  intro U hU
  let : Module.Projective (Γ(Y, U)) (Γ(M, U)) := hM U hU
  let eiso : M.val.obj (Opposite.op U) ≅ N.val.obj (Opposite.op U) :=
    { hom := e.hom.val.app (Opposite.op U), inv := e.inv.val.app (Opposite.op U),
      hom_inv_id := congrArg (fun g : M ⟶ M => g.val.app (Opposite.op U)) e.hom_inv_id,
      inv_hom_id := congrArg (fun g : N ⟶ N => g.val.app (Opposite.op U)) e.inv_hom_id }
  let eU : Γ(M, U) ≃ₗ[Γ(Y, U)] Γ(N, U) := eiso.toLinearEquiv
  show Module.Projective Γ(Y, U) Γ(N, U)
  exact Module.Projective.of_equiv' eU

/-- Local projectivity of a direct image along an affine morphism is inherited by the direct
image after a base change, granted the third assertion of Stacks Tag 02KG for that square:
the base-changed direct image is the inverse image of the direct image, and Tag 060M says
inverse images of locally projective modules are locally projective. -/
private lemma locallyProjective_pushforward_after_affineBaseChange
    {X S X' S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (f : X ⟶ S) (g : S' ⟶ S) (h : IsPullback g' f' f g)
    (bc : ∀ {Y' Y T' T : Scheme.{u}} (q' : Y' ⟶ Y) (p' : Y' ⟶ T') (p : Y ⟶ T) (q : T' ⟶ T),
      IsPullback q' p' p q → IsAffineHom p → ∀ G : Y.Modules, G.IsQuasicoherent →
      ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pushforward p).obj G) ≅
        (Scheme.Modules.pushforward p').obj ((Scheme.Modules.pullback q').obj G)))
    (F : X.Modules) [F.IsQuasicoherent] [IsAffineHom f]
    (hF : Scheme.Modules.IsLocallyProjective ((Scheme.Modules.pushforward f).obj F)) :
    Scheme.Modules.IsLocallyProjective ((Scheme.Modules.pushforward f').obj
      ((Scheme.Modules.pullback g').obj F)) :=
  locallyProjective_of_iso (bc g' f' f g h ‹IsAffineHom f› F ‹F.IsQuasicoherent›)
    (pullback_isLocallyProjective g ((Scheme.Modules.pushforward f).obj F) hF)

private lemma locallyProjective_pushforward_of_baseChange_witness
    (H : FlatPointedBaseChangeSituation.{u})
    (P : PrePureSituation.{u})
    (eS : P.S = H.S') (eX : P.X = Limits.pullback H.f H.g)
    (hcomm : eqToHom eX.symm ≫ P.f ≫ eqToHom eS = Limits.pullback.snd H.f H.g)
    (hF : HEq P.F ((Scheme.Modules.pullback (Limits.pullback.fst H.f H.g)).obj H.F))
    (hcanon : Scheme.Modules.IsLocallyProjective
      ((Scheme.Modules.pushforward (Limits.pullback.snd H.f H.g)).obj
        ((Scheme.Modules.pullback (Limits.pullback.fst H.f H.g)).obj H.F))) :
    Scheme.Modules.IsLocallyProjective ((Scheme.Modules.pushforward P.f).obj P.F) := by
  cases P with
  | mk S X f F s =>
    cases eS
    cases eX
    let F₀ := F
    cases hF
    have hf : f = Limits.pullback.snd H.f H.g := by simpa using hcomm
    exact locallyProjective_of_iso
      ((Scheme.Modules.pushforwardCongr hf).app F₀).symm hcanon

private lemma isAffineHom_of_baseChange_witness
    (H : FlatPointedBaseChangeSituation.{u})
    (P : PrePureSituation.{u})
    (eS : P.S = H.S') (eX : P.X = Limits.pullback H.f H.g)
    (hcomm : eqToHom eX.symm ≫ P.f ≫ eqToHom eS = Limits.pullback.snd H.f H.g)
    [IsAffineHom H.f] : IsAffineHom P.f := by
  cases P with
  | mk S X f F s =>
    cases eS
    cases eX
    obtain rfl : f = Limits.pullback.snd H.f H.g := by simpa using hcomm
    exact isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback H.f H.g) inferInstance

/-- For a morphism of affine schemes, the image of the point of the source cut out by a prime
of its ring of functions is the point of the target cut out by the contracted prime. -/
private lemma fromSpec_top_naturality {W T : Scheme.{u}} (π : W ⟶ T) [IsAffine W] [IsAffine T]
    (z : PrimeSpectrum Γ(W, ⊤)) :
    π ((isAffineOpen_top W).fromSpec z) =
      (isAffineOpen_top T).fromSpec (PrimeSpectrum.comap π.appTop.hom z) := by
  have hqz : (isAffineOpen_top W).primeIdealOf
      ⟨(isAffineOpen_top W).fromSpec z, Set.mem_univ _⟩ = z := by
    show (isAffineOpen_top W).isoSpec.hom.base ((isAffineOpen_top W).isoSpec.inv.base z) = z
    exact congr($((isAffineOpen_top W).isoSpec.inv_hom_id).base z)
  have h := comap_appTop_primeIdealOf_top π ((isAffineOpen_top W).fromSpec z)
  rw [hqz] at h
  rw [h]
  exact ((isAffineOpen_top T).fromSpec_primeIdealOf ⟨_, Set.mem_univ _⟩).symm

/-- A point of the fibre of `π` over `t` maps to `t`. -/
private lemma apply_fiberι {Y T : Scheme.{u}} (π : Y ⟶ T) (t : T) (x : π.fiber t) :
    π ((π.fiberι t) x) = t := by
  have hrange : (π.fiberι t) x ∈ Set.range (π.fiberι t) := ⟨x, rfl⟩
  rw [π.range_fiberι] at hrange
  simpa using hrange

/-- A point of the relative assassin of a module along a morphism, lying over a given point of
the target, comes from an associated point of the inverse image of the module on the fibre over
that point. -/
private lemma exists_fiber_associatedPoint {Y T : Scheme.{u}} (π : Y ⟶ T) (M : Y.Modules)
    {ξ : Y} {t : T} (hlies : π.base ξ = t)
    (hmem : ξ ∈ Stacks.Divisors.relativeAssassin π M) :
    ∃ x : π.fiber t,
      x ∈ Stacks.Divisors.associatedPoints ((Scheme.Modules.pullback (π.fiberι t)).obj M) ∧
        (π.fiberι t) x = ξ := by
  rcases (Stacks.Divisors.mem_relativeAssassin π M ξ).mp hmem with ⟨t₀, x₀, hx₀, hxi⟩
  obtain rfl : t₀ = t := (apply_fiberι π t₀ x₀).symm.trans ((congrArg π hxi).trans hlies)
  exact ⟨x₀, hx₀, hxi⟩

/-- For a morphism between schemes with affine total space, the prime of the ring of global
functions cut out by a point of a fibre contracts, along the map on global sections, to the prime
cut out by the point of the target that the fibre lies over. -/
private lemma comap_appTop_primeIdealOf_fiber {Y T : Scheme.{u}} (π : Y ⟶ T) [IsAffine Y]
    [IsAffine T] (t : T) (x : π.fiber t) :
    PrimeSpectrum.comap π.appTop.hom
        ((isAffineOpen_top Y).primeIdealOf ⟨(π.fiberι t) x, Set.mem_univ _⟩) =
      (isAffineOpen_top T).primeIdealOf ⟨t, Set.mem_univ _⟩ := by
  have h := comap_appTop_primeIdealOf_top π ((π.fiberι t) x)
  rwa [apply_fiberι] at h

/-- For a point of a scheme with affine total space, the ring of global functions on the spectrum
of its residue field is the residue field of the prime of the ring of global functions that the
point cuts out. -/
private noncomputable def residueFieldSectionsRingEquiv {T : Scheme.{u}} [IsAffine T] (t : T) :
    Γ(Spec (T.residueField t), ⊤) ≃+*
      ((isAffineOpen_top T).primeIdealOf ⟨t, Set.mem_univ _⟩).asIdeal.ResidueField :=
  (Scheme.ΓSpecIso (CommRingCat.of (T.residueField t))).commRingCatIsoToRingEquiv.trans
    (residueFieldEquivOfAffineOpen ⊤ (isAffineOpen_top T) t (Set.mem_univ _))

/-- The identification of `residueFieldSectionsRingEquiv` is compatible with the two maps out of
the ring of global functions. -/
private lemma residueFieldSectionsRingEquiv_appTop {T : Scheme.{u}} [IsAffine T] (t : T)
    (r : Γ(T, ⊤)) :
    residueFieldSectionsRingEquiv t ((T.fromSpecResidueField t).appTop.hom r) =
      algebraMap Γ(T, ⊤)
        ((isAffineOpen_top T).primeIdealOf ⟨t, Set.mem_univ _⟩).asIdeal.ResidueField r := by
  have hgamma : (Scheme.ΓSpecIso (CommRingCat.of (T.residueField t))).commRingCatIsoToRingEquiv
      ((T.fromSpecResidueField t).appTop.hom r) = T.Γevaluation t r := by
    show (Scheme.ΓSpecIso (CommRingCat.of (T.residueField t))).hom
      ((T.fromSpecResidueField t).appTop.hom r) = _
    exact congrArg (fun k : CommRingCat.Hom _ _ => k.hom r)
      (fromSpecResidueField_appTop_eval t)
  show residueFieldEquivOfAffineOpen ⊤ (isAffineOpen_top T) t (Set.mem_univ _)
      ((Scheme.ΓSpecIso (CommRingCat.of (T.residueField t))).commRingCatIsoToRingEquiv
        ((T.fromSpecResidueField t).appTop.hom r)) = _
  rw [hgamma]
  exact residueFieldEquivOfAffineOpen_evaluation ⊤ (isAffineOpen_top T) t (Set.mem_univ _) r

/-- For a commutative square `c ≫ d = a ≫ b`, the two iterated inverse images of a module along
its sides are isomorphic. -/
private noncomputable def pullbackObjIsoOfComm {A B C D : Scheme.{u}} {a : A ⟶ B} {b : B ⟶ D}
    {c : A ⟶ C} {d : C ⟶ D} (h : c ≫ d = a ≫ b) (M : D.Modules) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj M) ≅
      (Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback d).obj M) :=
  (Scheme.Modules.pullbackComp a b).app M ≪≫
    eqToIso (congrArg (fun k => (Scheme.Modules.pullback k).obj M) h.symm) ≪≫
      ((Scheme.Modules.pullbackComp c d).app M).symm

/-- The global sections of the sheaf `tilde N` on `Spec R` form a scalar tower over `R` and the
global sections of `Spec R`. -/
private lemma isScalarTower_ΓSpec_tilde (R : CommRingCat.{u}) (N : ModuleCat.{u} R) :
    letI : Algebra R Γ(Spec R, ⊤) := (Scheme.ΓSpecIso R).inv.hom.toAlgebra
    IsScalarTower R Γ(Spec R, ⊤) Γ(AlgebraicGeometry.tilde N, ⊤) := by
  let : Algebra R Γ(Spec R, ⊤) := (Scheme.ΓSpecIso R).inv.hom.toAlgebra
  apply IsScalarTower.of_algebraMap_smul
  intro r y
  show ((Scheme.ΓSpecIso R).inv r) • y = r • y
  rw [Scheme.Modules.smul_Spec_def]
  have hmap : (Spec R).presheaf.map (TopologicalSpace.Opens.leTop ⊤).op = 𝟙 _ := by
    rw [show (TopologicalSpace.Opens.leTop ⊤).op = 𝟙 _ from Subsingleton.elim _ _]
    exact (Spec R).presheaf.map_id _
  rw [hmap]
  simp

/-- The inverse image of a quasi-coherent module is quasi-coherent. -/
private lemma isQuasicoherent_pullback_obj {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [M.IsQuasicoherent] : ((Scheme.Modules.pullback f).obj M).IsQuasicoherent :=
  @SheafOfModules.modulePullback_isQuasicoherent _ _ f.toLRSHom.toShHom M
    (show M.IsQuasicoherent from inferInstance)

/-- For a morphism between schemes with affine total space and a quasi-coherent module on the
target, the module of global sections of the inverse image is the base change, along the map on
global functions, of the module attached to the global sections of the module. -/
private noncomputable def pullbackSectionsExtendScalarsEquiv {Y Z : Scheme.{u}}
    [IsAffine Y] [IsAffine Z] (ι : Z ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent] :
    Γ((Scheme.Modules.pullback ι).obj M, ⊤) ≃ₗ[Γ(Z, ⊤)]
      (ModuleCat.extendScalars ι.appTop.hom).obj
        (AlgebraicGeometry.moduleSpecΓFunctor.obj
          ((Scheme.Modules.pullback (isAffineOpen_top Y).fromSpec).obj M)) := by
  let Ffib := (Scheme.Modules.pullback ι).obj M
  let fX := (isAffineOpen_top Y).fromSpec
  let fY := (isAffineOpen_top Z).fromSpec
  have hfX : fX = Y.isoSpec.inv := IsAffineOpen.fromSpec_top
  have hfY : fY = Z.isoSpec.inv := IsAffineOpen.fromSpec_top
  have hFiberMap : Scheme.Spec.map (ι.appTop).op ≫ fX = fY ≫ ι := by
    rw [hfX, hfY]
    exact Scheme.isoSpec_inv_naturality ι
  let Fₓ := (Scheme.Modules.pullback fX).obj M
  let Fᵧ := (Scheme.Modules.pullback fY).obj Ffib
  have : Fₓ.IsQuasicoherent := isQuasicoherent_pullback_obj fX M
  let Mₓ : ModuleCat Γ(Y, ⊤) := AlgebraicGeometry.moduleSpecΓFunctor.obj Fₓ
  let eTildeToF : AlgebraicGeometry.tilde Mₓ ≅ Fₓ :=
    @asIso _ _ _ _ Fₓ.fromTildeΓ (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent Fₓ)
  have : Ffib.IsQuasicoherent := isQuasicoherent_pullback_obj ι M
  have : Fᵧ.IsQuasicoherent := isQuasicoherent_pullback_obj fY Ffib
  let α := ι.appTop
  let hPullbacks : Fᵧ ≅ ((Scheme.Modules.pullback (Scheme.Spec.map α.op)).obj Fₓ) :=
    pullbackObjIsoOfComm hFiberMap M
  let ePullTilde := (Scheme.Modules.pullback (Scheme.Spec.map α.op)).mapIso eTildeToF.symm ≪≫
    (pullbackTildeIso Γ(Y, ⊤) Γ(Z, ⊤) α).app Mₓ
  let eFiberTilde : Fᵧ ≅ AlgebraicGeometry.tilde
      ((ModuleCat.extendScalars α.hom).obj Mₓ) := hPullbacks ≪≫ ePullTilde
  let : IsOpenImmersion fY := (isAffineOpen_top Z).isOpenImmersion_fromSpec
  let : Algebra Γ(Z, ⊤) Γ(Spec Γ(Z, ⊤), ⊤) :=
    (Scheme.ΓSpecIso (Γ(Z, ⊤))).inv.hom.toAlgebra
  let Mext := (ModuleCat.extendScalars α.hom).obj Mₓ
  let eRestrictPullback := (Scheme.Modules.restrictFunctorIsoPullback fY).app Ffib
  let : IsScalarTower Γ(Z, ⊤) Γ(Spec Γ(Z, ⊤), ⊤) Γ(Fᵧ, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower Γ(Z, ⊤) Γ(Spec Γ(Z, ⊤), ⊤)
      Γ((Scheme.Modules.restrictFunctor fY).obj Ffib, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower Γ(Z, ⊤) Γ(Spec Γ(Z, ⊤), ⊤) Γ(AlgebraicGeometry.tilde Mext, ⊤) :=
    isScalarTower_ΓSpec_tilde Γ(Z, ⊤) Mext
  let eSectPullback : Γ(Fᵧ, ⊤) ≃ₗ[Γ(Z, ⊤)] Γ(Ffib, ⊤) :=
    ((sectionsLinearEquiv_of_iso eRestrictPullback.symm ⊤).restrictScalars
      (Γ(Z, ⊤))).trans
      (by simpa using fromSpecSectionsLinearEquiv Ffib (isAffineOpen_top Z))
  let eSectExt : Γ(Fᵧ, ⊤) ≃ₗ[Γ(Z, ⊤)] Mext :=
    ((sectionsLinearEquiv_of_iso eFiberTilde ⊤).restrictScalars (Γ(Z, ⊤))).trans
    (((AlgebraicGeometry.tilde.toTildeΓNatIso (R := Γ(Z, ⊤))).app Mext).toLinearEquiv.symm)
  exact eSectPullback.symm.trans eSectExt

/-- An associated point of the inverse image of a quasi-coherent module on an affine fibre gives
an associated prime of its module of global sections. -/
private lemma isAssociatedPrime_fiber_sections {Y T : Scheme.{u}} (π : Y ⟶ T) [IsAffine Y]
    [IsAffine T] [IsAffineHom π] [LocallyOfFiniteType π] (M : Y.Modules) [M.IsQuasicoherent]
    (t : T) (x : π.fiber t)
    (hx : x ∈ Stacks.Divisors.associatedPoints ((Scheme.Modules.pullback (π.fiberι t)).obj M)) :
    IsAssociatedPrimeStacks Γ(π.fiber t, ⊤) Γ((Scheme.Modules.pullback (π.fiberι t)).obj M, ⊤)
      ((isAffineOpen_top (π.fiber t)).primeIdealOf ⟨x, Set.mem_univ _⟩).asIdeal := by
  let : LocallyOfFiniteType (π.fiberToSpecResidueField t) :=
    locallyOfFiniteType_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback π (T.fromSpecResidueField t)) inferInstance
  let : IsLocallyNoetherian (π.fiber t) :=
    LocallyOfFiniteType.isLocallyNoetherian (π.fiberToSpecResidueField t)
  have : ((Scheme.Modules.pullback (π.fiberι t)).obj M).IsQuasicoherent :=
    isQuasicoherent_pullback_obj _ M
  exact associatedPoint_affine_sections_prime _ ⊤ (isAffineOpen_top _) (Set.mem_univ _)
    ((Stacks.Divisors.mem_associatedPoints_iff _ x).mp hx)

/-- Let `B` be the fibre ring of a finite type algebra `S` over a local ring `R` at a point `p`,
and `N` a finite `S`-module projective over `R`. The contraction to `S` of an associated prime of
the base change of `N` to `B` specializes to a prime of `S` over the closed point of `R`. -/
private lemma exists_le_comap_eq_top_of_isPushout {R S K B : CommRingCat.{u}} [IsLocalRing R]
    [Algebra R S] [Algebra.FiniteType R S] {g : R ⟶ K} {i : S ⟶ B} {j : K ⟶ B}
    (h : IsPushout (CommRingCat.ofHom (algebraMap R S)) g i j)
    (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Projective R N] [Module.Finite S N] {M : ModuleCat.{u} S} (eM : M ≃ₗ[S] N)
    {q : PrimeSpectrum B}
    (hq : IsAssociatedPrimeStacks B ((ModuleCat.extendScalars i.hom).obj M) q.asIdeal)
    {p : PrimeSpectrum R}
    (hp : PrimeSpectrum.comap (algebraMap R S) (PrimeSpectrum.comap i.hom q) = p)
    (eK : K ≃+* p.asIdeal.ResidueField)
    (hK : ∀ r : R, eK (g.hom r) = algebraMap R p.asIdeal.ResidueField r) :
    ∃ z : PrimeSpectrum S,
      PrimeSpectrum.comap i.hom q ≤ z ∧ PrimeSpectrum.comap (algebraMap R S) z = ⊤ := by
  subst hp
  let : Algebra R K := g.hom.toAlgebra
  let : Algebra S B := i.hom.toAlgebra
  let : Algebra K B := j.hom.toAlgebra
  let : Algebra R B := Algebra.compHom _ (algebraMap R S)
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hcomm : (algebraMap K B).comp (algebraMap R K) =
      (algebraMap S B).comp (algebraMap R S) := by
    ext r
    exact congrArg (fun φ : R ⟶ B => φ.hom r) h.w.symm
  let : IsScalarTower R K B := IsScalarTower.of_algebraMap_eq' hcomm.symm
  have h' : IsPushout (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom (algebraMap R K))
      (CommRingCat.ofHom (algebraMap S B)) (CommRingCat.ofHom (algebraMap K B)) := h
  let : Algebra.IsPushout R K S B :=
    Algebra.IsPushout.symm ((CommRingCat.isPushout_iff_isPushout).mp h')
  let : Module R M := Module.compHom _ (algebraMap R S)
  let : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let Mext := (ModuleCat.extendScalars i.hom).obj M
  let : Module S Mext := Module.compHom _ (algebraMap S B)
  let : IsScalarTower S B Mext := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hqExt : IsAssociatedPrimeStacks B Mext q.asIdeal := hq
  have hqM : IsAssociatedPrimeStacks S (M ⊗[R] K) (PrimeSpectrum.comap i.hom q).asIdeal :=
    associatedPrime_of_linearEquiv (pushoutBaseChangeCommEquiv R K S B M)
      (associatedPrime_of_linearEquiv
        ((StacksDraft.TorAmplitude.FaithfullyFlat.extendScalarsCarrierEquiv
          S B M).restrictScalars S) (associatedPrime_comap_of_scalarTower hqExt))
  obtain ⟨z, hqz, hIz⟩ := exists_closed_fiber_specialization R S N (PrimeSpectrum.comap i.hom q)
    (associatedPrime_of_linearEquiv (TensorProduct.AlgebraTensorModule.congr eM
      (AlgEquiv.ofRingEquiv (f := eK) hK).toLinearEquiv) hqM)
  exact ⟨z, hqz, prime_spectrum_point_over_closed_point R S z hIz⟩

/-- The local step of Stacks Tag 05K6.  On a scheme with affine total space over the spectrum of
a local ring, an associated point of the restriction of a finite type quasi-coherent module to a
fibre cuts out a prime contained in a prime that lies over the closed point of the base, as soon
as the direct image of the module is locally projective.

The associated point gives an associated prime of the fibre module over the residue field of the
base, whose sum with the ideal generated by the maximal ideal is proper by
`Stacks.PureModules.associatedPrime_add_map_maximalIdeal_ne_top`; any maximal ideal containing
that sum is the prime looked for. -/
private lemma exists_prime_comap_eq_top_of_fiber_associatedPoint {Y T : Scheme.{u}} (π : Y ⟶ T)
    [IsAffine Y] [IsAffine T] [IsAffineHom π] [LocallyOfFiniteType π] [IsLocalRing Γ(T, ⊤)]
    (M : Y.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (hloc : Scheme.Modules.IsLocallyProjective ((Scheme.Modules.pushforward π).obj M))
    (t : T) (x : π.fiber t)
    (hx : x ∈ Stacks.Divisors.associatedPoints
      ((Scheme.Modules.pullback (π.fiberι t)).obj M)) :
    ∃ z : PrimeSpectrum Γ(Y, ⊤),
      (isAffineOpen_top Y).primeIdealOf ⟨(π.fiberι t) x, Set.mem_univ _⟩ ≤ z ∧
        PrimeSpectrum.comap π.appTop.hom z = ⊤ := by
  let hTtop : IsAffineOpen (⊤ : T.Opens) := isAffineOpen_top T
  let hXtop : IsAffineOpen (⊤ : Y.Opens) := isAffineOpen_top Y
  let R := Γ(T, ⊤)
  let S₀ := Γ(Y, ⊤)
  let N₀ := Γ(M, ⊤)
  let htopLE : (⊤ : Y.Opens) ≤ π ⁻¹ᵁ (⊤ : T.Opens) := by simp
  have hSapp := appTop_eq_appLE π htopLE
  let : Algebra R S₀ := (π.appLE ⊤ ⊤ htopLE).hom.toAlgebra
  have hmapRS : (algebraMap R S₀) = π.appTop.hom :=
    congrArg CommRingCat.Hom.hom hSapp.symm
  let : Algebra.FiniteType R S₀ :=
    (RingHom.finiteType_algebraMap).mp (π.finiteType_appLE hTtop hXtop htopLE)
  let : Module S₀ N₀ := by
    show Module Γ(Y, ⊤) Γ(M, ⊤)
    infer_instance
  let : Module R N₀ := by
    show Module Γ(T, ⊤) Γ((Scheme.Modules.pushforward π).obj M, ⊤)
    infer_instance
  let : IsScalarTower R S₀ N₀ :=
    IsScalarTower.of_algebraMap_smul fun r n => by
      show ((π.appLE ⊤ ⊤ htopLE).hom) r • n = r • n
      rw [← hSapp]
      rfl
  have hprojN : Module.Projective R N₀ := by
    show Module.Projective Γ(T, ⊤) Γ((Scheme.Modules.pushforward π).obj M, ⊤)
    exact hloc ⊤ hTtop
  have hfiniteN : Module.Finite S₀ N₀ := moduleFinite_sections_on_affine M ⊤ hXtop
  have hPush : IsPushout (CommRingCat.ofHom (algebraMap R S₀))
      (T.fromSpecResidueField t).appTop (π.fiberι t).appTop
      (π.fiberToSpecResidueField t).appTop := by
    have hmap' : CommRingCat.ofHom (algebraMap R S₀) = π.appTop := by
      ext y
      exact congrArg (fun φ : R →+* S₀ => φ y) hmapRS
    rw [hmap']
    exact isPushout_appTop_of_isPullback (IsPullback.of_hasPullback π
      (T.fromSpecResidueField t) : IsPullback (π.fiberι t) (π.fiberToSpecResidueField t) π
        (T.fromSpecResidueField t))
  have hqS := comap_appTop_primeIdealOf_top (π.fiberι t) x
  have hp : PrimeSpectrum.comap (algebraMap R S₀) (PrimeSpectrum.comap (π.fiberι t).appTop.hom
      ((isAffineOpen_top (π.fiber t)).primeIdealOf ⟨x, Set.mem_univ _⟩)) =
      hTtop.primeIdealOf ⟨t, Set.mem_univ _⟩ := by
    rw [hqS, hmapRS]
    exact comap_appTop_primeIdealOf_fiber π t x
  obtain ⟨z, hqz, hz⟩ := exists_le_comap_eq_top_of_isPushout hPush N₀
    (moduleSpecΓPullbackFromSpecEquiv M hXtop)
    (associatedPrime_of_linearEquiv (pullbackSectionsExtendScalarsEquiv (π.fiberι t) M)
      (isAssociatedPrime_fiber_sections π M t x hx)) hp (residueFieldSectionsRingEquiv t)
    (residueFieldSectionsRingEquiv_appTop t)
  exact ⟨z, hqS.symm.le.trans hqz, by rwa [← hmapRS]⟩

/-- **Stacks Project, Tag 05K6, in the affine local case.**  A pre-pure situation with affine
morphism over a base with affine total space whose ring of global functions is local, with the
distinguished point of the base the closed point, admits no impurity diagram once the direct
image of the module is locally projective.

The chosen point of an impurity lies in the fibre over `D.t'`, so it is the image of an
associated point of the module restricted to that fibre.  By
`exists_prime_comap_eq_top_of_fiber_associatedPoint` the prime it cuts out is contained in a
prime lying over the closed point, and the corresponding point of the source is then a point of
the closure of the chosen point inside the closed fibre -- which an impurity forbids. -/
private lemma not_isImpurity_of_isAffine_of_isLocalRing (P : PrePureSituation.{u})
    (D : ImpurityDiagram P) [IsAffineHom P.f] [IsAffine D.T] [IsLocalRing Γ(D.T, ⊤)]
    (hclosed : D.t = (isAffineOpen_top D.T).fromSpec (IsLocalRing.closedPoint Γ(D.T, ⊤)))
    (hloc : Scheme.Modules.IsLocallyProjective
      ((Scheme.Modules.pushforward D.toT).obj (D.pulledBack P))) :
    ¬ IsImpurity P D := by
  intro himp
  let : IsAffineHom D.toT :=
    isAffineHom_isStableUnderBaseChange.of_isPullback D.isPullback inferInstance
  let : IsAffine D.X_T := isAffine_of_isAffineHom D.toT
  let : LocallyOfFiniteType D.toT :=
    locallyOfFiniteType_isStableUnderBaseChange.of_isPullback D.isPullback inferInstance
  let : (D.pulledBack P).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType D.toX.toLRSHom.toShHom P.F
  let : (D.pulledBack P).IsQuasicoherent := isQuasicoherent_pullback_obj D.toX P.F
  obtain ⟨x, hx, hxi⟩ :=
    exists_fiber_associatedPoint D.toT (D.pulledBack P) D.xi_liesOver himp.1
  obtain ⟨z, hqz, hzbase⟩ :=
    exists_prime_comap_eq_top_of_fiber_associatedPoint D.toT (D.pulledBack P) hloc D.t' x hx
  let hXtop : IsAffineOpen (⊤ : D.X_T.Opens) := isAffineOpen_top D.X_T
  let xZ : D.X_T := hXtop.fromSpec z
  have hxZclosure : xZ ∈ closure {D.xi} := by
    have hfromX : hXtop.fromSpec
        (hXtop.primeIdealOf ⟨(D.toT.fiberι D.t') x, Set.mem_univ _⟩) =
        (D.toT.fiberι D.t') x :=
      hXtop.fromSpec_primeIdealOf ⟨(D.toT.fiberι D.t') x, Set.mem_univ _⟩
    have hspecX : (D.toT.fiberι D.t') x ⤳ xZ := by
      rw [← hfromX]
      exact ((PrimeSpectrum.le_iff_specializes _ z).mp hqz).map hXtop.fromSpec.continuous
    have hxZ' : xZ ∈ closure {(D.toT.fiberι D.t') x} := specializes_iff_mem_closure.mp hspecX
    rwa [hxi] at hxZ'
  have htoTpoint : D.toT xZ = D.t := by
    refine (fromSpec_top_naturality D.toT z).trans ?_
    rw [hzbase]
    exact hclosed.symm
  have hxrange : xZ ∈ Set.range (D.toT.fiberι D.t) := by
    rw [D.toT.range_fiberι]
    exact Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr htoTpoint)
  have hxempty : xZ ∈ (∅ : Set D.X_T) := himp.2 ▸ ⟨hxZclosure, hxrange⟩
  simp at hxempty

/-- An impurity diagram whose base is the pullback of a local spectrum `Spec A` along an
isomorphism, with its point over the closed point, is not an impurity when the pushforward of the
pulled-back module is locally projective. -/
private lemma not_isImpurity_of_eq_pullback {P : PrePureSituation.{u}} (D : ImpurityDiagram P)
    [IsAffineHom P.f] {T S : Scheme.{u}} {A : CommRingCat.{u}} [IsLocalRing A] (g : T ⟶ S)
    (g' : Spec A ⟶ S) [IsIso g] (eT : D.T = Limits.pullback g g')
    (ht : (Limits.pullback.snd g g') (eT ▸ D.t) = IsLocalRing.closedPoint A)
    (hloc : Scheme.Modules.IsLocallyProjective
      ((Scheme.Modules.pushforward D.toT).obj (D.pulledBack P))) :
    ¬ IsImpurity P D := by
  let e : D.T ≅ Spec A := eqToIso eT ≪≫ asIso (Limits.pullback.snd g g')
  have : IsAffine D.T := IsAffine.of_isIso e.hom
  have : IsLocalRing Γ(D.T, ⊤) :=
    (((Scheme.Γ.mapIso e.op).commRingCatIsoToRingEquiv.symm).trans
      (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv).symm.isLocalRing
  refine not_isImpurity_of_isAffine_of_isLocalRing P D (eq_fromSpec_closedPoint e ?_) hloc
  show (Limits.pullback.snd g g') ((eqToHom eT) D.t) = _
  rw [eqToHom_scheme_apply]
  exact ht

/-- In a flat pointed base change situation, local projectivity of the direct image survives the
base change and the further affine base change to an impurity diagram. -/
private lemma locallyProjective_after_flatPointedBaseChange
    (H : FlatPointedBaseChangeSituation.{u}) [IsAffineHom H.f]
    (bc : ∀ {Y' Y T' T : Scheme.{u}} (q' : Y' ⟶ Y) (p' : Y' ⟶ T') (p : Y ⟶ T) (q : T' ⟶ T),
      IsPullback q' p' p q → IsAffineHom p → ∀ G : Y.Modules, G.IsQuasicoherent →
      ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pushforward p).obj G) ≅
        (Scheme.Modules.pushforward p').obj ((Scheme.Modules.pullback q').obj G)))
    (hH : Scheme.Modules.IsLocallyProjective ((Scheme.Modules.pushforward H.f).obj H.F))
    {P : PrePureSituation.{u}} (D : ImpurityDiagram P)
    (eS : P.S = H.S') (eX : P.X = Limits.pullback H.f H.g)
    (hcomm : eqToHom eX.symm ≫ P.f ≫ eqToHom eS = Limits.pullback.snd H.f H.g)
    (hF : HEq P.F ((Scheme.Modules.pullback (Limits.pullback.fst H.f H.g)).obj H.F)) :
    Scheme.Modules.IsLocallyProjective
      ((Scheme.Modules.pushforward D.toT).obj (D.pulledBack P)) := by
  have : IsAffineHom P.f := isAffineHom_of_baseChange_witness H P eS eX hcomm
  exact locallyProjective_pushforward_after_affineBaseChange D.toX D.toT P.f D.g D.isPullback bc
    P.F (locallyProjective_pushforward_of_baseChange_witness H P eS eX hcomm hF
      (locallyProjective_pushforward_after_affineBaseChange (Limits.pullback.fst H.f H.g)
        (Limits.pullback.snd H.f H.g) H.f H.g (IsPullback.of_hasPullback H.f H.g) bc H.F hH))

/-- **Stacks Project, Tag 05K6.** For an affine morphism of finite type, a finite type
quasi-coherent module with locally projective direct image is universally pure over the base.

The affine base change used along the way is the third assertion of Stacks Tag 02KG,
`Stacks.AlgebraicGeometry.AffineBaseChangeLocality.baseChangeIso`, bound to `bc` below and
threaded through the private lemmas in the shape in which they take it. -/
@[stacks 05K6]
public theorem isUniversallyPureRelative_of_pushforward_isLocallyProjective
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsAffineHom f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (hF : Scheme.Modules.IsLocallyProjective ((Scheme.Modules.pushforward f).obj F)) :
    IsUniversallyPureRelative f F := by
  have bc := @Stacks.AlgebraicGeometry.AffineBaseChangeLocality.baseChangeIso
  intro s
  let P : PrePureSituation.{u} :=
    { S := S, X := X, f := f, F := F, s := s }
  show ∀ D : ImpurityDiagram P, ¬ IsImpurity P D
  intro D hD
  let : LocallyOfFiniteType D.toT :=
    locallyOfFiniteType_isStableUnderBaseChange.of_isPullback D.isPullback inferInstance
  let : IsAffineHom D.toT :=
    isAffineHom_isStableUnderBaseChange.of_isPullback D.isPullback inferInstance
  let : D.pulledBack P |>.IsFiniteType :=
    SheafOfModules.pullback_isFiniteType D.toX.toLRSHom.toShHom P.F
  let P₀ : PrePureSituation.{u} :=
    { S := D.T, X := D.X_T, f := D.toT, F := D.pulledBack P, s := D.t }
  let D₀ : ImpurityDiagram P₀ :=
    { T := D.T, g := 𝟙 D.T, t' := D.t', t := D.t, specializes := D.specializes,
      mapsToChosenPoint := rfl,
      X_T := D.X_T, toX := 𝟙 D.X_T, toT := D.toT,
      isPullback := IsPullback.of_id_fst,
      xi := D.xi, xi_liesOver := by simpa using D.xi_liesOver }
  have hD₀ : IsImpurity P₀ D₀ := ⟨relativeAssassin_mem_of_iso D.toT
    ((Scheme.Modules.pullbackId D.X_T).app (D.pulledBack P)).symm hD.1, hD.2⟩
  let H : FlatPointedBaseChangeSituation.{u} :=
    { X := D.X_T, S := D.T, f := D.toT, F := D.pulledBack P, s := D.t,
      S' := Spec (D.T.presheaf.stalk D.t),
      s' := IsLocalRing.closedPoint (D.T.presheaf.stalk D.t),
      g := D.T.fromSpecStalk D.t,
      mapsTo := Scheme.fromSpecStalk_closedPoint,
      flatAt := by
        let : Flat (D.T.fromSpecStalk D.t) := flat_fromSpecStalk D.T D.t
        show ((D.T.fromSpecStalk D.t).stalkMap _).hom.Flat
        exact Flat.stalkMap _ _ }
  obtain ⟨P₁, D₁, eS, eX, eT, hcomm, hF₁, hs₁, hg₁, himp₁,
      ht'₁, ht₁, hst₁, hxi₁⟩ :=
    exists_impurity_after_flatPointedBaseChange H D₀ hD₀
  have : IsIso D₀.g := by
    dsimp [D₀]
    infer_instance
  have : IsAffineHom P₁.f := isAffineHom_of_baseChange_witness H P₁ eS eX hcomm
  exact not_isImpurity_of_eq_pullback D₁ D₀.g H.g eT hst₁
    (locallyProjective_after_flatPointedBaseChange H bc
      (locallyProjective_pushforward_after_affineBaseChange D.toX D.toT f D.g D.isPullback bc F hF)
      D₁ eS eX hcomm hF₁) himp₁


end AlgebraicGeometry

end
