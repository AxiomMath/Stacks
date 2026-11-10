module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.FrobeniusSurjectivity
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Twist
public import StacksFrontier.RingTheory.Etale.FrobeniusEquations
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# Frobenius minus the identity on a finite locally free étale module

Let `p` be a prime, let `S` be a scheme in characteristic `p`, and let `E` be a finite locally
free module on the small étale site of `S`. Let `F` be an additive endomorphism of the
underlying sheaf of abelian groups of `E` which is Frobenius semilinear, in the sense that
`F (a • e) = a ^ p • F e` on local sections. Then `F - 1` is an epimorphism of abelian sheaves,
that is, its cokernel is zero.

## Main results

* `AlgebraicGeometry.epi_frobeniusSemilinear_sub_id`: a Frobenius-semilinear additive
  endomorphism of a finite locally free module on the small étale site, minus the identity, is
  an epimorphism.

## Implementation notes

The characteristic hypothesis is the vanishing of `p` in the ring of global sections of `S`,
which is what it means for `S` to be a scheme over the prime field with `p` elements. Every
object of the small étale site of `S` is a scheme over `S`, hence also in characteristic `p`,
and this is how the hypothesis is used. It holds in particular for the empty object of the
site, whose ring of sections is the zero ring; asking instead that `p` be the characteristic of
every ring of sections would exclude that object, since `CharP R p` for a prime `p` forces `R`
to be nontrivial.

The endomorphism is a morphism of sheaves of abelian groups, not of modules, so its
semilinearity is recorded sectionwise. The vanishing of the cokernel is expressed as the
equivalent statement that the morphism is an epimorphism.

## References

* [Stacks Project, Tag 0GKU](https://stacks.math.columbia.edu/tag/0GKU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Frobenius

universe u v₁ u₁

namespace SheafOfModules

/-- The additive map induced on the sections over an object by a morphism between the sheaves
of abelian groups underlying two sheaves of modules. -/
noncomputable def sectionsAddHom {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R}
    (φ : (SheafOfModules.toSheaf R).obj M ⟶ (SheafOfModules.toSheaf R).obj N) (U : Cᵒᵖ) :
    M.val.obj U →+ N.val.obj U :=
  (φ.hom.app U).hom

end SheafOfModules

namespace AlgebraicGeometry

/-- A ring in which a prime `p` vanishes and which is nontrivial has characteristic `p`. -/
private theorem charP_of_prime_natCast_eq_zero (R : Type*) [CommRing R] [Nontrivial R] (p : ℕ)
    [Fact p.Prime] (hp : (p : R) = 0) : CharP R p := by
  rw [← ringChar.eq_iff]
  exact ((Nat.dvd_prime Fact.out).mp (ringChar.dvd hp)).resolve_left CharP.ringChar_ne_one

/-- A section of a sheaf of modules with a finite family of generating sections whose
presenting morphism is an isomorphism is a combination of the images of the standard basis
sections. -/
theorem generatingSections_eq_sum
    {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} R} (σ : M.GeneratingSections)
    [Fintype σ.I] [IsIso σ.π] (U : Cᵒᵖ) (x : M.val.obj U) :
    ∃ a : σ.I → R.obj.obj U, x = ∑ i, (SheafOfModules.ιFree i ≫ σ.π).val.app U (a i) := by
  classical
  let G : σ.I → SheafOfModules.{u} R := fun _ => SheafOfModules.unit R
  let : HasBiproduct G := HasBiproduct.of_hasProduct G
  let e : SheafOfModules.free (R := R) σ.I ≅ biproduct G :=
    IsColimit.coconePointUniqueUpToIso
      (SheafOfModules.isColimitFreeCofan σ.I) (biproduct.isColimit G)
  have hi (i : σ.I) : SheafOfModules.ιFree i ≫ e.hom = biproduct.ι G i :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (SheafOfModules.isColimitFreeCofan σ.I) (biproduct.isColimit G) (Discrete.mk i)
  have ht : (∑ i, (e.hom ≫ biproduct.π G i) ≫ SheafOfModules.ιFree i) = 𝟙 _ := by
    apply (cancel_mono e.hom).mp
    simp only [Preadditive.sum_comp, Category.assoc, hi, Category.id_comp]
    rw [← Preadditive.comp_sum, IsBilimit.total (biproduct.isBilimit G), Category.comp_id]
  let ev := SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj U
  let y : ev.obj (SheafOfModules.free σ.I) := (inv σ.π).val.app U x
  refine ⟨fun i => (e.hom ≫ biproduct.π G i).val.app U y, ?_⟩
  have hy := congrArg (fun f => f.val.app U y) ht
  change (ev.map _).hom y = _ at hy
  rw [Functor.map_sum] at hy
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply] at hy
  change (∑ i, (SheafOfModules.ιFree i).val.app U
    ((e.hom ≫ biproduct.π G i).val.app U y)) = y at hy
  have hx := congrArg (fun z => σ.π.val.app U z) hy
  rw [map_sum] at hx
  rw [show σ.π.val.app U y = x by
    change ((inv σ.π ≫ σ.π).val.app U) x = x
    simp] at hx
  exact hx.symm

/-- A sheaf of modules with a finite family of generating sections whose presenting morphism is
an isomorphism has, over every object, a finite family of sections spanning the sections over
that object. -/
private theorem finite_generatingSections_span
    {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} R} (σ : M.GeneratingSections)
    [Finite σ.I] [IsIso σ.π] (U : Cᵒᵖ) :
    ∃ (n : ℕ) (s : Fin n → M.val.obj U), ∀ x : M.val.obj U,
      ∃ a : Fin n → R.obj.obj U, x = ∑ i, a i • s i := by
  classical
  let : Fintype σ.I := Fintype.ofFinite σ.I
  let e := (Fintype.equivFin σ.I).symm
  let s (i : Fin (Fintype.card σ.I)) : M.val.obj U :=
    (SheafOfModules.ιFree (e i) ≫ σ.π).val.app U (1 : R.obj.obj U)
  refine ⟨Fintype.card σ.I, s, fun x => ?_⟩
  obtain ⟨a, ha⟩ := generatingSections_eq_sum σ U x
  refine ⟨a ∘ e, ha.trans ?_⟩
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  have key : ((SheafOfModules.ιFree (e i) ≫ σ.π).val.app U).hom (a (e i)) =
      a (e i) • ((SheafOfModules.ιFree (e i) ≫ σ.π).val.app U).hom
        (1 : R.obj.obj U) := by
    have h := ((SheafOfModules.ιFree (e i) ≫ σ.π).val.app U).hom.map_smul
      (a (e i)) (1 : R.obj.obj U)
    rw [← h]
    congr 1
    change a (e i) = a (e i) * (1 : R.obj.obj U)
    rw [mul_one]
  exact key

/-- The object of the small étale site given by an étale morphism to the underlying object of
`U`. -/
private abbrev smallEtaleOfEtale
    {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (U : SmallEtale B S hS)
    {Y : _} (g : Y ⟶ U.obj.left) (hg : Etale (B.inclusion.map g)) : SmallEtale B S hS :=
  ⟨Over.mk (g ≫ U.obj.hom), by
    change Etale (B.inclusion.map (g ≫ U.obj.hom))
    rw [B.inclusion.map_comp]
    let := hg
    infer_instance⟩

/-- A family of objects of the small étale site of `S` whose image in schemes is an étale
covering generates a covering sieve for the small étale topology. -/
private theorem etale_family_mem
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : SmallEtale B S hS} (E : PreZeroHypercover.{u + 1} X)
    (hE : (E.map (SmallEtale.toScheme B S hS)).presieve₀ ∈
      Scheme.etalePrecoverage ((SmallEtale.toScheme B S hS).obj X)) :
    Sieve.generate E.presieve₀ ∈ SmallEtale.topology B S hS X := by
  let H := SmallEtale.inclusion B S hS ⋙ Over.forget (B.obj S hS)
  let D := E.map H
  have hD : IsEtaleCovering ⟨H.obj X, D⟩ := hE
  obtain ⟨⟨T, R⟩, hR, hcomb⟩ := B.exists_covering_rep ⟨H.obj X, D⟩ hD
  rcases hcomb with ⟨ht, hcomb⟩
  cases ht
  obtain ⟨β, hX, hf⟩ := hcomb.2
  have he (i : R.I₀) : Etale (B.inclusion.map (R.f i)) := by
    have h := hR.1
    let P : MorphismProperty Scheme := fun {X Y} f => Etale f
    change Presieve.ofArrows _ _ ∈ Scheme.precoverage P _ at h
    rw [Scheme.ofArrows_mem_precoverage_iff] at h
    exact h.2 i
  let G : PreZeroHypercover.{u + 1} X := {
    I₀ := R.I₀
    X i := smallEtaleOfEtale X (R.f i) (he i)
    f i := ObjectProperty.homMk (Over.homMk (R.f i))
  }
  have hG : SmallEtale.IsCovering B S hS ⟨X, G⟩ := hR
  apply (SmallEtale.topology B S hS).superset_covering _
    ((SmallEtale.precoverage B S hS).generate_mem_toGrothendieck
      ((SmallEtale.mem_precoverage_iff B S hS).2 ⟨G, rfl, hG⟩))
  apply (Sieve.generate_le_iff _ _).2
  intro Y f h
  obtain ⟨i⟩ := h
  let g : G.X i ⟶ E.X (β i) := ObjectProperty.homMk
    (Over.homMk (eqToHom (hX i)) (by
      change eqToHom (hX i) ≫ (E.X (β i)).obj.hom = R.f i ≫ X.obj.hom
      rw [hf i]
      simp only [Category.assoc]
      congr 1
      exact (E.f (β i)).hom.w.symm))
  have hh : g ≫ E.f (β i) = G.f i := by
    ext
    exact congrArg (fun k => B.inclusion.map k) (hf i).symm
  rw [← hh]
  exact (Sieve.generate E.presieve₀).downward_closed
    (Sieve.le_generate _ _ _ (Presieve.ofArrows.mk _)) g

/-- Over an algebraically closed field of characteristic `p`, the Frobenius equations
`∑ⱼ aⱼᵢ xⱼᵖ - xᵢ = bᵢ` have a solution. -/
private theorem matrix_frobenius_sub_id_surjective
    {p n : ℕ} (hp : 0 < p) (k : Type*) [Field k] [IsAlgClosed k] [CharP k p]
    (a : Fin n → Fin n → k) (b : Fin n → k) :
    ∃ x : Fin n → k, ∀ i, (∑ j, a j i * x j ^ p) - x i = b i := by
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  let : Fact p.Prime := CharP.char_is_prime_of_pos k p
  let F : (Fin n → k) →+ (Fin n → k) :=
    { toFun := fun x i => ∑ j, a j i * x j ^ p
      map_zero' := by ext i; simp [Nat.ne_of_gt hp]
      map_add' := by
        intro x y; ext i
        simp only [Pi.add_apply, add_pow_char, mul_add, Finset.sum_add_distrib] }
  have hF (c : k) (x : Fin n → k) : F (c • x) = c ^ p • F x := by
    ext i; simp [F, smul_eq_mul, mul_pow, Finset.mul_sum, mul_left_comm]
  obtain ⟨x, hx⟩ :=
    frobeniusSemilinear_sub_id_surjective k hp (Fin n → k) F hF b
  exact ⟨x, fun i => congrFun hx i⟩

/-- The algebra cut out by the Frobenius equations `bᵢ + xᵢ - ∑ⱼ aⱼᵢ xⱼᵖ`. -/
abbrev frobeniusEquationAlgebra
    (p n : ℕ) (A : Type*) [CommRing A]
    (a : Fin n → Fin n → A) (b : Fin n → A) :=
  MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range fun i : Fin n =>
    MvPolynomial.C (b i) + MvPolynomial.X i -
      ∑ j : Fin n, MvPolynomial.C (a j i) * MvPolynomial.X j ^ p)

/-- Every homomorphism from the coefficient ring to an algebraically closed field of
characteristic `p` extends to the algebra cut out by the Frobenius equations. -/
private theorem frobeniusEquationAlgebra_has_field_point
    {p n : ℕ} [Fact p.Prime] {A K : Type*} [CommRing A] [Field K]
    [IsAlgClosed K] [CharP K p] (f : A →+* K)
    (a : Fin n → Fin n → A) (b : Fin n → A) :
    ∃ x : Fin n → K, ∃ φ : frobeniusEquationAlgebra p n A a b →+* K,
      (∀ c, φ (Ideal.Quotient.mk _ (MvPolynomial.C c)) = f c) ∧
        (∀ i, φ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = x i) := by
  obtain ⟨x, hx⟩ := matrix_frobenius_sub_id_surjective (Nat.Prime.pos Fact.out) K
    (fun j i => f (a j i)) (fun i => f (b i))
  let eval : MvPolynomial (Fin n) A →+* K := MvPolynomial.eval₂Hom f x
  have heval : ∀ i : Fin n,
      eval (MvPolynomial.C (b i) + MvPolynomial.X i -
        ∑ j : Fin n, MvPolynomial.C (a j i) * MvPolynomial.X j ^ p) = 0 := by
    intro i
    rw [map_sub, map_add, map_sum]
    simp only [eval, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
      map_mul, map_pow]
    linear_combination -(hx i)
  have hker : Ideal.span (Set.range fun i : Fin n =>
      MvPolynomial.C (b i) + MvPolynomial.X i -
        ∑ j : Fin n, MvPolynomial.C (a j i) * MvPolynomial.X j ^ p) ≤ RingHom.ker eval := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact RingHom.mem_ker.mpr (heval i)
  let φ := Ideal.Quotient.lift _ eval (fun z hz => RingHom.mem_ker.mp (hker hz))
  exact ⟨x, φ, fun c => by simp [φ, eval], fun i => by simp [φ, eval]⟩

/-- The algebra cut out by the Frobenius equations is faithfully flat over its coefficient
ring: the induced map on prime spectra is surjective. -/
private theorem frobeniusEquationAlgebra_spec_surjective
    (p n : ℕ) [Fact p.Prime] (A : Type*) [CommRing A] (hp : (p : A) = 0)
    (a : Fin n → Fin n → A) (b : Fin n → A) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A
      (frobeniusEquationAlgebra p n A a b))) := by
  intro P
  let k := P.asIdeal.ResidueField
  let K := AlgebraicClosure k
  let f : A →+* K := (algebraMap k K).comp (algebraMap A k)
  have : CharP K p := charP_of_prime_natCast_eq_zero K p (by
    rw [← map_natCast f, hp, map_zero])
  let Q := frobeniusEquationAlgebra p n A a b
  obtain ⟨x, φ, hcoeff, hx⟩ :=
    frobeniusEquationAlgebra_has_field_point (p := p) (A := A) (K := K) f a b
  let q : PrimeSpectrum Q := ⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩
  refine ⟨q, ?_⟩
  apply PrimeSpectrum.ext
  change (RingHom.ker φ).comap (algebraMap A Q) = P.asIdeal
  ext z
  simp only [Ideal.mem_comap, RingHom.mem_ker]
  rw [show φ (algebraMap A Q z) = f z from ?_]
  · rw [show f z = algebraMap k K (algebraMap A k z) from rfl]
    rw [map_eq_zero_iff (algebraMap k K) (FaithfulSMul.algebraMap_injective k K)]
    exact Ideal.algebraMap_residueField_eq_zero
  · rw [show algebraMap A Q z = Ideal.Quotient.mk _ (MvPolynomial.C z) by
      rw [← Ideal.Quotient.mk_algebraMap]
      exact congrArg (Ideal.Quotient.mk _)
        (DFunLike.congr_fun (MvPolynomial.C_eq_algebraMap A (Fin n)) z).symm]
    exact hcoeff z

/-- On a scheme in characteristic `p`, a system of Frobenius equations with global
coefficients acquires a solution over a surjective quasi-compact étale cover. -/
private theorem exists_etale_roots
    (p n : ℕ) [Fact p.Prime] (X : Scheme.{u}) (hX : IsInCharacteristic X p)
    (a : Fin n → Fin n → Γ(X, ⊤)) (b : Fin n → Γ(X, ⊤)) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), Etale f ∧ Surjective f ∧ QuasiCompact f ∧
      ∃ x : Fin n → Γ(Y, ⊤), ∀ i,
        (∑ j, f.appTop (a j i) * x j ^ p) - x i = f.appTop (b i) := by
  let A := Γ(X, ⊤)
  let Q := frobeniusEquationAlgebra p n A a b
  let : Algebra.Etale A Q := Algebra.frobeniusEquationAlgebra_isEtale p n A hX a b
  let g : Spec (.of Q) ⟶ Spec A := Spec.map (CommRingCat.ofHom (algebraMap A Q))
  let : Etale g := (HasRingHomProperty.Spec_iff (P := @Etale)).2
    (RingHom.etale_algebraMap.mpr inferInstance)
  let : Surjective g := ⟨frobeniusEquationAlgebra_spec_surjective p n A hX a b⟩
  let Y := pullback g X.toSpecΓ
  let f : Y ⟶ X := pullback.snd g X.toSpecΓ
  let q : Q →+* Γ(Y, ⊤) :=
    ((Scheme.ΓSpecIso (.of Q)).inv ≫ (pullback.fst g X.toSpecΓ).appTop).hom
  have hc : (CommRingCat.ofHom (algebraMap A Q)) ≫ CommRingCat.ofHom q = f.appTop := by
    change CommRingCat.ofHom (algebraMap A Q) ≫ (Scheme.ΓSpecIso (.of Q)).inv ≫
      (pullback.fst g X.toSpecΓ).appTop = f.appTop
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      ← Scheme.Hom.comp_appTop, pullback.condition, Scheme.Hom.comp_appTop,
      Scheme.toSpecΓ_appTop]
    change (Scheme.ΓSpecIso A).inv ≫ (Scheme.ΓSpecIso A).hom ≫ f.appTop = _
    rw [Iso.inv_hom_id_assoc]
  have hq (c : A) : q (algebraMap A Q c) = f.appTop c := ConcreteCategory.congr_hom hc c
  let x (i : Fin n) : Γ(Y, ⊤) := q (Ideal.Quotient.mk _ (MvPolynomial.X i))
  refine ⟨Y, f, inferInstance, inferInstance, inferInstance, x, ?_⟩
  intro i
  have hz : (Ideal.Quotient.mk _ (MvPolynomial.C (b i) + MvPolynomial.X i -
      ∑ j, MvPolynomial.C (a j i) * MvPolynomial.X j ^ p) : Q) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  have hh := congrArg q hz
  have hcoeff (c : A) : q (Ideal.Quotient.mk _ (MvPolynomial.C c)) = f.appTop c := by
    rw [show Ideal.Quotient.mk _ (MvPolynomial.C c) = algebraMap A Q c from rfl]
    exact hq c
  simp only [map_sub, map_add, map_sum, map_mul, map_pow, map_zero, hcoeff] at hh
  change f.appTop (b i) + x i - ∑ j, f.appTop (a j i) * x j ^ p = 0 at hh
  linear_combination -hh

/-- The value of a Frobenius-semilinear endomorphism minus the identity on a combination of
basis sections, when the coefficients solve the associated Frobenius equations. -/
theorem frobenius_sub_id_sum
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (p n : ℕ) (G : M →+ M) (hG : ∀ (a : A) (x : M), G (a • x) = a ^ p • G x)
    (s : Fin n → M) (a : Fin n → Fin n → A) (b t : Fin n → A)
    (ha : ∀ j, G (s j) = ∑ i, a j i • s i)
    (ht : ∀ i, (∑ j, a j i * t j ^ p) - t i = b i) :
    G (∑ j, t j • s j) - ∑ j, t j • s j = ∑ i, b i • s i := by
  rw [map_sum]
  simp_rw [hG, ha, Finset.smul_sum, smul_smul, mul_comm (t _ ^ p)]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sub_smul, ht]

/-- Every section of a finite locally free module is locally in the image of a
Frobenius-semilinear endomorphism minus the identity, when a spanning family is given. -/
@[sga "1 XI 6.7" "more general"]
private theorem imageSieve_mem_of_span
    (p : ℕ) [Fact p.Prime]
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (E : SheafOfModules.{u} (SmallEtale.structureSheaf B S hS))
    (F : ((SheafOfModules.toSheaf (SmallEtale.structureSheaf B S hS)).obj E) ⟶
      ((SheafOfModules.toSheaf (SmallEtale.structureSheaf B S hS)).obj E))
    (hF : ∀ (U : SmallEtale B S hS)
      (a : (SmallEtale.structureSheaf B S hS).obj.obj (op U))
      (e : E.val.obj (op U)),
      SheafOfModules.sectionsAddHom F (op U) (a • e) =
        a ^ p • SheafOfModules.sectionsAddHom F (op U) e)
    (U : SmallEtale B S hS)
    (hc : IsInCharacteristic ((SmallEtale.toScheme B S hS).obj U) p)
    (n : ℕ) (s : Fin n → E.val.obj (op U))
    (hspan : ∀ x : E.val.obj (op U),
      ∃ a : Fin n → (SmallEtale.structureSheaf B S hS).obj.obj (op U),
        x = ∑ i, a i • s i) (z : E.val.obj (op U)) :
    Presheaf.imageSieve (F - 𝟙 _).hom z ∈ SmallEtale.topology B S hS U := by
  classical
  obtain ⟨b, hb⟩ := hspan z
  choose a ha using fun j => hspan (SheafOfModules.sectionsAddHom F (op U) (s j))
  let X := (SmallEtale.toScheme B S hS).obj U
  obtain ⟨Y, f, hf, hsurj, hqc, t, ht⟩ := exists_etale_roots p n X hc a b
  let := hf
  let := hsurj
  let := hqc
  have hY : B.Contains Y :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact f U.obj.left.property
  let fB : B.obj Y hY ⟶ U.obj.left := ObjectProperty.homMk f
  let V := smallEtaleOfEtale U fB hf
  let g : V ⟶ U := ObjectProperty.homMk (Over.homMk fB)
  let AY := Γ(Y, ⊤)
  let : Module AY (E.val.obj (op V)) := (E.val.obj (op V)).isModule
  let G : E.val.obj (op V) →+ E.val.obj (op V) := SheafOfModules.sectionsAddHom F (op V)
  let D : PreZeroHypercover.{u + 1} U := {
    I₀ := PUnit.{u + 2}
    X _ := V
    f _ := g
  }
  have hD : Sieve.generate D.presieve₀ ∈ SmallEtale.topology B S hS U := by
    apply etale_family_mem B S hS D
    let P : MorphismProperty Scheme := fun {X Y} f => Etale f
    change Presieve.ofArrows (fun _ : PUnit.{u + 2} => Y) (fun _ => f) ∈
      Scheme.precoverage P X
    rw [Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨fun x => ⟨PUnit.unit, f.surjective x⟩, fun _ => hf⟩
  apply (SmallEtale.topology B S hS).superset_covering _ hD
  apply (Sieve.generate_le_iff _ _).2
  intro W g' hg'
  obtain ⟨i⟩ := hg'
  change ∃ y : E.val.obj (op V), (F - 𝟙 _).hom.app (op V) y = E.val.map g.op z
  let s' (j : Fin n) : E.val.obj (op V) := E.val.map g.op (s j)
  have hn (x : E.val.obj (op U)) :
      SheafOfModules.sectionsAddHom F (op V) (E.val.map g.op x) =
        E.val.map g.op (SheafOfModules.sectionsAddHom F (op U) x) :=
    ConcreteCategory.congr_hom (F.hom.naturality g.op) x
  have ha' (j : Fin n) :
      SheafOfModules.sectionsAddHom F (op V) (s' j) =
        ∑ i, f.appTop (a j i) • s' i := by
    rw [hn, ha j, map_sum]
    simp only [E.val.map_smul]
    rfl
  refine ⟨∑ j, t j • s' j, ?_⟩
  change G (∑ j, t j • s' j) - (∑ j, t j • s' j) = E.val.map g.op z
  rw [frobenius_sub_id_sum (A := AY) p n G (hF V) s'
    (fun j i => f.appTop (a j i)) (fun i => f.appTop (b i)) t ha' ht, hb, map_sum]
  simp only [E.val.map_smul]
  rfl

/-- Let `S` be a scheme in characteristic `p` and let `E` be a finite locally free module on the
small étale site of `S`. A Frobenius-semilinear additive endomorphism of the underlying abelian
sheaf of `E`, minus the identity, is an epimorphism; equivalently its cokernel is zero. This is the
cokernel half of Stacks 0GKU, whose full statement, with the constructibility of the kernel, is
`AlgebraicGeometry.isZero_cokernel_and_isConstructible_kernel_frobeniusSemilinear_sub_id`. -/
@[sga "4½ Fonctions_L 3.1" "partial"]
theorem epi_frobeniusSemilinear_sub_id
    (p : ℕ) [Fact p.Prime]
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [∀ V : SmallEtale B S hS,
      HasWeakSheafify ((SmallEtale.topology B S hS).over V) AddCommGrpCat.{u}]
    [∀ V : SmallEtale B S hS,
      ((SmallEtale.topology B S hS).over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (E : SheafOfModules.{u} (SmallEtale.structureSheaf B S hS))
    [SheafOfModules.IsFiniteLocallyFree E]
    (hchar : IsInCharacteristic S p)
    (F : ((SheafOfModules.toSheaf (SmallEtale.structureSheaf B S hS)).obj E) ⟶
      ((SheafOfModules.toSheaf (SmallEtale.structureSheaf B S hS)).obj E))
    (hF : ∀ (U : SmallEtale B S hS)
      (a : (SmallEtale.structureSheaf B S hS).obj.obj (op U))
      (e : E.val.obj (op U)),
      SheafOfModules.sectionsAddHom F (op U) (a • e) =
        a ^ p • SheafOfModules.sectionsAddHom F (op U) e) :
    Epi (F - 𝟙 _) := by
  classical
  let J := SmallEtale.topology B S hS
  obtain ⟨q, hq, hfin⟩ :=
    SheafOfModules.IsFiniteLocallyFree.exists_isFiniteLocallyFreeData (M := E)
  let := hq
  let := hfin
  let : Presheaf.IsLocallySurjective J (F - 𝟙 _).hom := ⟨by
    intro U z
    apply J.transitive (q.coversTop U)
    intro V f hf
    obtain ⟨i, ⟨g⟩⟩ := hf
    rw [Presheaf.pullback_imageSieve]
    let := hfin.isFiniteType i
    obtain ⟨n, s, hs⟩ := finite_generatingSections_span (q.generators i) (op (Over.mk g))
    exact imageSieve_mem_of_span p B S hS E F hF V
      (isInCharacteristic_of_hom (B.inclusion.map V.obj.hom) p hchar) n s hs
      (E.val.map f.op z)⟩
  exact Sheaf.epi_of_isLocallySurjective (F - 𝟙 _)

end AlgebraicGeometry

end
