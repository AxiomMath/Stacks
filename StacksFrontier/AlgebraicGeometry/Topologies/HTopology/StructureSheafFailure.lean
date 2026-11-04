module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.TrivSqZeroExt.Ideal
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.AlgebraicGeometry.Topologies.H.BigSite
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.Coverings
public import StacksCore.Tactic.StacksAttribute

/-!
# The structure sheaf is not a sheaf for the h topology, and the h topology is not subcanonical

A surjective closed immersion of finite presentation `X ⟶ Y` is an h covering of `Y`, and it is a
monomorphism, so that `X ×_Y X = X`; the sheaf condition for the one-element family `{X ⟶ Y}` would
therefore force the restriction map `𝒪(Y) ⟶ 𝒪(X)` to be bijective. It is not, already for the
square-zero thickening `Spec k ⟶ Spec k[x]/(x²)` of a point, whose restriction map is the
surjection `k[x]/(x²) ⟶ k` with kernel `(x) ≠ 0`.

On a big h site over a base scheme `S` the same failure obstructs subcanonicity. The presheaf of
global functions on the big h category over `S` is represented by the affine line `𝔸¹_S = 𝔸(n; S)`
over `S` with `n` a one-element index type, since a morphism `X ⟶ 𝔸¹_S` over `S` is the same thing
as a global function on `X`; so a representable presheaf on `(Sch/S)_h` fails the sheaf condition,
and the h topology on `(Sch/S)_h` is not subcanonical. Over a base whose underlying space is empty
every representable presheaf on the site takes singleton values and is therefore a sheaf, so
nonemptiness of `S` is needed.

## Main definitions

* `AlgebraicGeometry.squareZeroThickening`: the ring `k[x]/(x²)`.
* `AlgebraicGeometry.squareZeroEval`: evaluation at the origin `k[x]/(x²) ⟶ k`.
* `AlgebraicGeometry.BigHOver.affineSpaceObj` and `AlgebraicGeometry.BigHOver.affineLine`: affine
  `n`-space and the affine line over `S`, as objects of the big h category over `S`.
* `AlgebraicGeometry.BigHOver.globalFunctions`: the presheaf of global functions on the big h
  category over `S`.

## Main results

* `AlgebraicGeometry.isHCovering_specMap`: for a surjection of rings whose kernel is finitely
  generated and consists of nilpotents, the induced morphism of spectra is an h covering.
* `AlgebraicGeometry.not_isSheafFor_squareZeroEval`: global sections of the structure sheaf fail
  the sheaf condition for the h covering `{Spec k ⟶ Spec k[x]/(x²)}`.
* `AlgebraicGeometry.not_isSheafFor_isHCovering_gamma`: the presheaf of global sections of the
  structure sheaf is not a sheaf for the h topology.
* `AlgebraicGeometry.BigHOver.homEquivGlobalFunctions` and
  `AlgebraicGeometry.BigHOver.globalFunctionsIsoYonedaAffineLine`: global functions on an object of
  the big h category over `S` are the `S`-morphisms to affine space, so that the presheaf of global
  functions is the presheaf represented by the affine line.
* `AlgebraicGeometry.BigHOver.not_isSheaf_yoneda_affineLine`: over a nonempty base the presheaf
  represented by the affine line is not a sheaf for the big h topology.
* `AlgebraicGeometry.BigHOver.not_subcanonical_topology`: over a nonempty base the big h topology
  is not subcanonical.

## References

* [Stacks Project, Tag 0ETW](https://stacks.math.columbia.edu/tag/0ETW)
* [Stacks Project, Tag 0EV0](https://stacks.math.columbia.edu/tag/0EV0)
* [Stacks Project, Tag 0EV1](https://stacks.math.columbia.edu/tag/0EV1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe t u v w

namespace CategoryTheory.Presieve

/-- If a presheaf of types satisfies the sheaf condition for the one-element family consisting of a
monomorphism `f`, then restriction along `f` is bijective. -/
public theorem bijective_map_op_of_isSheafFor_mono {C : Type u} [Category.{v} C] {X Y : C}
    (F : Cᵒᵖ ⥤ Type w) (f : X ⟶ Y) [Mono f] {J : Type t} [Unique J]
    (hF : (Presieve.ofArrows (fun _ : J ↦ X) (fun _ ↦ f)).IsSheafFor F) :
    Function.Bijective (F.map f.op) := by
  rw [Presieve.isSheafFor_arrows_iff] at hF
  have hcomp : ∀ y : F.obj (op X),
      Presieve.Arrows.Compatible F (fun _ : J ↦ f) (fun _ ↦ y) := by
    intro y _ _ _ gi gj h
    obtain rfl : gi = gj := (cancel_mono f).1 h
    rfl
  refine ⟨fun s t hst ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨_, _, huniq⟩ := hF (fun _ ↦ F.map f.op s) (hcomp (F.map f.op s))
    exact (huniq s fun _ ↦ rfl).trans (huniq t fun _ ↦ hst.symm).symm
  · obtain ⟨s, hs, -⟩ := hF (fun _ ↦ y) (hcomp y)
    exact ⟨s, hs default⟩

end CategoryTheory.Presieve

namespace AlgebraicGeometry

/-- Restricting the global function attached to a ring element along `Spec φ` is applying `φ` to
that element. -/
private theorem appTop_specMap_ΓSpecIso_inv {R S : CommRingCat.{u}} (φ : R ⟶ S) (x : R) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv x) = (Scheme.ΓSpecIso S).inv (φ x) := by
  simpa only [CommRingCat.comp_apply] using
    (congrArg (fun g : R ⟶ _ => g x) (Scheme.ΓSpecIso_inv_naturality φ)).symm

/-- If a morphism of rings has nonzero kernel, then restriction of global functions along the
induced morphism of spectra is not injective. -/
private theorem not_injective_appTop_specMap {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hker : RingHom.ker φ.hom ≠ ⊥) :
    ¬ Function.Injective (Spec.map φ).appTop := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  intro hinj
  refine hx0 ?_
  have h1 : (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv x) =
      (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv 0) := by
    rw [appTop_specMap_ΓSpecIso_inv, appTop_specMap_ΓSpecIso_inv, map_zero,
      RingHom.mem_ker.mp hx]
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).1 (hinj h1)

section Nilpotent

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- If a surjection of rings has kernel consisting of nilpotents, the induced morphism of spectra
is surjective. -/
public theorem surjective_specMap_of_ker_le_nilradical (hφ : Function.Surjective φ)
    (hnil : RingHom.ker φ.hom ≤ nilradical R) : Surjective (Spec.map φ) := by
  refine ⟨fun p => ?_⟩
  have hp := p.isPrime
  have hmem : p ∈ PrimeSpectrum.zeroLocus (RingHom.ker φ.hom : Set R) :=
    (hnil.trans (nilradical_le_prime p.asIdeal) : _)
  rwa [← range_comap_of_surjective _ φ.hom hφ] at hmem

/-- A surjection of rings with finitely generated kernel induces a morphism of spectra of finite
presentation. -/
public theorem finitePresentation_specMap_of_fg_ker (hφ : Function.Surjective φ)
    (hfg : (RingHom.ker φ.hom).FG) : FinitePresentation (Spec.map φ) := by
  have : IsClosedImmersion (Spec.map φ) := IsClosedImmersion.spec_of_surjective φ hφ
  refine ⟨?_, inferInstance, inferInstance⟩
  rw [LocallyOfFinitePresentation.SpecMap_iff]
  exact RingHom.FinitePresentation.of_surjective φ.hom hφ hfg

/-- If a surjection of rings has finitely generated kernel consisting of nilpotents, the induced
morphism of spectra forms a one-element h covering. -/
public theorem isHCovering_specMap {J : Type t} [Unique J] (hφ : Function.Surjective φ)
    (hnil : RingHom.ker φ.hom ≤ nilradical R) (hfg : (RingHom.ker φ.hom).FG) :
    IsHCovering (fun _ : J ↦ Spec S) (fun _ ↦ Spec.map φ) := by
  have : IsClosedImmersion (Spec.map φ) := IsClosedImmersion.spec_of_surjective φ hφ
  have : Surjective (Spec.map φ) := surjective_specMap_of_ker_le_nilradical φ hφ hnil
  exact (surjective_proper_isHCovering _
    (finitePresentation_specMap_of_fg_ker φ hφ hfg)).reindex (Equiv.ofUnique J Unit)

/-- For a surjection of rings `R ⟶ S` with nonzero kernel, global sections of the structure sheaf
fail the sheaf condition for the one-element family `{Spec S ⟶ Spec R}`. -/
public theorem not_isSheafFor_specMap {J : Type t} [Unique J] (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ.hom ≠ ⊥) :
    ¬ (Presieve.ofArrows (fun _ : J ↦ Spec S) (fun _ ↦ Spec.map φ)).IsSheafFor
      (Scheme.Γ.{u} ⋙ forget CommRingCat.{u}) := by
  intro hsheaf
  have : IsClosedImmersion (Spec.map φ) := IsClosedImmersion.spec_of_surjective φ hφ
  have hbij := Presieve.bijective_map_op_of_isSheafFor_mono _ (Spec.map φ) hsheaf
  simp only [Functor.comp_map, Scheme.Γ_map_op] at hbij
  exact not_injective_appTop_specMap φ hker hbij.1

end Nilpotent

section SquareZero

variable (k : Type u) [Field k]

/-- The square-zero thickening `k[x]/(x²)` of a point over `k`. -/
public noncomputable abbrev squareZeroThickening : CommRingCat.{u} :=
  .of (Polynomial k ⧸ Ideal.span {(Polynomial.X : Polynomial k) ^ 2})

/-- Evaluation at the origin `k[x]/(x²) ⟶ k`, exhibiting `Spec k` as the reduced closed subscheme
of `Spec k[x]/(x²)`. -/
public noncomputable def squareZeroEval : squareZeroThickening k ⟶ .of k :=
  CommRingCat.ofHom <| Ideal.Quotient.lift _ (Polynomial.evalRingHom (0 : k)) <| by
    intro p hp
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.1 hp
    simp

/-- Evaluation at the origin `k[x]/(x²) ⟶ k` is surjective. -/
public theorem surjective_squareZeroEval : Function.Surjective (squareZeroEval k) :=
  fun a ↦ ⟨Ideal.Quotient.mk _ (Polynomial.C a), by simp [squareZeroEval]⟩

/-- The kernel of `k[x]/(x²) ⟶ k` is the ideal generated by the class of `x`. -/
public theorem ker_squareZeroEval : RingHom.ker (squareZeroEval k).hom =
    Ideal.span {Ideal.Quotient.mk _ (Polynomial.X : Polynomial k)} := by
  apply le_antisymm
  · intro u hu
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective u
    rw [RingHom.mem_ker] at hu
    have hp : (Polynomial.X : Polynomial k) ∣ p := by
      rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
      simpa [squareZeroEval] using hu
    obtain ⟨q, rfl⟩ := hp
    exact Ideal.mem_span_singleton.2 ⟨Ideal.Quotient.mk _ q, by simp⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    simp [squareZeroEval]

/-- The kernel of `k[x]/(x²) ⟶ k` consists of nilpotents. -/
public theorem ker_squareZeroEval_le_nilradical :
    RingHom.ker (squareZeroEval k).hom ≤ nilradical (squareZeroThickening k) := by
  rw [ker_squareZeroEval, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
    mem_nilradical]
  refine ⟨2, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

/-- The kernel of `k[x]/(x²) ⟶ k` is finitely generated. -/
public theorem fg_ker_squareZeroEval : (RingHom.ker (squareZeroEval k).hom).FG := by
  rw [ker_squareZeroEval]
  exact ⟨{Ideal.Quotient.mk _ (Polynomial.X : Polynomial k)}, by simp⟩

/-- The kernel of `k[x]/(x²) ⟶ k` is nonzero. -/
public theorem ker_squareZeroEval_ne_bot : RingHom.ker (squareZeroEval k).hom ≠ ⊥ := by
  rw [ker_squareZeroEval, Ne, Ideal.span_singleton_eq_bot, Ideal.Quotient.eq_zero_iff_mem]
  intro hmem
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 hmem
  have hcoeff := congrArg (fun p : Polynomial k ↦ p.coeff 1) hq
  simp [Polynomial.coeff_X_pow_mul'] at hcoeff

/-- `Spec k ⟶ Spec k[x]/(x²)` is a closed immersion. -/
public instance isClosedImmersion_specMap_squareZeroEval :
    IsClosedImmersion (Spec.map (squareZeroEval k)) :=
  IsClosedImmersion.spec_of_surjective _ (surjective_squareZeroEval k)

/-- `Spec k ⟶ Spec k[x]/(x²)` is surjective. -/
public instance surjective_specMap_squareZeroEval :
    Surjective (Spec.map (squareZeroEval k)) :=
  surjective_specMap_of_ker_le_nilradical _ (surjective_squareZeroEval k)
    (ker_squareZeroEval_le_nilradical k)

/-- `Spec k ⟶ Spec k[x]/(x²)` is of finite presentation. -/
public theorem finitePresentation_specMap_squareZeroEval :
    FinitePresentation (Spec.map (squareZeroEval k)) :=
  finitePresentation_specMap_of_fg_ker _ (surjective_squareZeroEval k) (fg_ker_squareZeroEval k)

/-- The one-element family `{Spec k ⟶ Spec k[x]/(x²)}` is an h covering for which global sections
of the structure sheaf fail the sheaf condition. -/
public theorem not_isSheafFor_squareZeroEval :
    IsHCovering (fun _ : Unit ↦ Spec (.of k)) (fun _ ↦ Spec.map (squareZeroEval k)) ∧
      ¬ (Presieve.ofArrows (fun _ : Unit ↦ Spec (.of k))
          (fun _ ↦ Spec.map (squareZeroEval k))).IsSheafFor
        (Scheme.Γ.{u} ⋙ forget CommRingCat.{u}) :=
  ⟨isHCovering_specMap _ (surjective_squareZeroEval k) (ker_squareZeroEval_le_nilradical k)
      (fg_ker_squareZeroEval k),
    not_isSheafFor_specMap _ (surjective_squareZeroEval k) (ker_squareZeroEval_ne_bot k)⟩

end SquareZero

/-- The structure sheaf is not a sheaf for the h topology: the presheaf of global sections on
schemes fails the sheaf condition for some h covering family. -/
@[stacks 0EV0]
public theorem not_isSheafFor_isHCovering_gamma :
    ¬ ∀ (T : Scheme.{u}) (I : Type t) (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T),
        IsHCovering X f →
          (Presieve.ofArrows X f).IsSheafFor (Scheme.Γ.{u} ⋙ forget CommRingCat.{u}) := by
  intro hsheaf
  refine not_isSheafFor_specMap (J := PUnit.{t + 1}) (squareZeroEval (ULift.{u} ℚ))
    (surjective_squareZeroEval _) (ker_squareZeroEval_ne_bot _) (hsheaf _ _ _ _ ?_)
  exact isHCovering_specMap _ (surjective_squareZeroEval _)
    (ker_squareZeroEval_le_nilradical _) (fg_ker_squareZeroEval _)

section NotSubcanonical

open TrivSqZeroExt DualNumber

/-- For a finite index type `n`, affine `n`-space over a scheme of size below a cutoff is again of
size below that cutoff. -/
public theorem Scheme.size_affineSpace_lt {κ : Cardinal.{u}} (n : Type u) [Finite n]
    {S : Scheme.{u}} (hS : S.size < κ) : (AffineSpace n S).size < κ :=
  Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (AffineSpace n S ↘ S) hS

/-! ### The square-zero thickening of an arbitrary commutative ring -/

/-- The projection `A[ε] ⟶ A` of the dual numbers onto their constant part, as a morphism of
commutative rings. It presents `Spec A` as the reduced closed subscheme of `Spec A[ε]`. -/
private noncomputable def dualNumberFst (R : CommRingCat.{u}) :
    CommRingCat.of (DualNumber R) ⟶ R :=
  CommRingCat.ofHom (fstHom R R R).toRingHom

/-- The inclusion `A ⟶ A[ε]` of the constants into the dual numbers, as a morphism of commutative
rings. It is a section of `AlgebraicGeometry.dualNumberFst`. -/
private noncomputable def dualNumberInl (R : CommRingCat.{u}) :
    R ⟶ CommRingCat.of (DualNumber R) :=
  CommRingCat.ofHom (inlHom R R)

/-- The constants are a section of the projection `A[ε] ⟶ A`. -/
private theorem dualNumberInl_comp_fst (R : CommRingCat.{u}) :
    dualNumberInl R ≫ dualNumberFst R = 𝟙 R := by
  ext _
  rfl

/-- The projection `A[ε] ⟶ A` is surjective. -/
private theorem surjective_dualNumberFst (R : CommRingCat.{u}) :
    Function.Surjective (dualNumberFst R) :=
  fun a => ⟨inl a, rfl⟩

/-- The kernel of `A[ε] ⟶ A` is the principal ideal generated by `ε`. -/
private theorem ker_dualNumberFst (R : CommRingCat.{u}) :
    RingHom.ker (dualNumberFst R).hom = Ideal.span {(ε : DualNumber R)} := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    have hx' : x = inr x.snd := by
      rwa [← mem_kerIdeal_iff_inr]
    rw [hx', Ideal.mem_span_singleton]
    refine ⟨inl x.snd, ?_⟩
    rw [DualNumber.eps, inr_mul_inl]
    simp
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    change fst (ε : DualNumber R) = 0
    simp

/-- The kernel of `A[ε] ⟶ A` consists of nilpotents. -/
private theorem ker_dualNumberFst_le_nilradical (R : CommRingCat.{u}) :
    RingHom.ker (dualNumberFst R).hom ≤ nilradical (CommRingCat.of (DualNumber R)) := by
  rw [ker_dualNumberFst, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
    mem_nilradical]
  exact ⟨2, by rw [pow_two]; exact DualNumber.eps_mul_eps⟩

/-- The kernel of `A[ε] ⟶ A` is finitely generated. -/
private theorem fg_ker_dualNumberFst (R : CommRingCat.{u}) :
    (RingHom.ker (dualNumberFst R).hom).FG :=
  ⟨{(ε : DualNumber R)}, by rw [ker_dualNumberFst]; simp⟩

/-- Over a nonzero ring the kernel of `A[ε] ⟶ A` is nonzero. -/
private theorem ker_dualNumberFst_ne_bot (R : CommRingCat.{u}) [Nontrivial R] :
    RingHom.ker (dualNumberFst R).hom ≠ ⊥ := by
  rw [ker_dualNumberFst, Ne, Ideal.span_singleton_eq_bot]
  exact fun h => one_ne_zero (congrArg snd h)

/-- The dual numbers `A[ε]` are a finite type `A`-algebra, generated by `ε`. -/
private theorem algebra_finiteType_dualNumber (A : Type u) [CommRing A] :
    Algebra.FiniteType A (DualNumber A) := by
  refine ⟨⟨{(ε : DualNumber A)}, ?_⟩⟩
  rw [Finset.coe_singleton]
  have h := DualNumber.range_inlAlgHom_sup_adjoin_eps (R := A) (A := A)
  rw [show (AlgHom.range (inlAlgHom A A A)) = ⊥ from ?_] at h
  · simpa using h
  · ext x
    simp [Algebra.mem_bot, AlgHom.mem_range, algebraMap_eq_inlHom]

namespace BigHOver

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The affine line on a big h site -/

/-- A sheaf on the big h category over `S` satisfies the sheaf condition for every family of
morphisms of the site whose underlying family of morphisms of schemes is an h covering. -/
public theorem isSheafFor_presieve₀_of_isHCovering
    {F : (BigHOver B S hS)ᵒᵖ ⥤ Type v} (hF : Presheaf.IsSheaf (topology B S hS) F)
    {X : BigHOver B S hS} (E : PreZeroHypercover.{u + 1} X)
    (hE : IsHCovering (E.map (toScheme B S hS)).X (E.map (toScheme B S hS)).f) :
    Presieve.IsSheafFor F E.presieve₀ := by
  let K := forget B S hS
  let E' := E.map K
  have hE' : IsHCoveringInCutoff (κ := B.cutoff) ⟨X.left, E'⟩ := hE
  obtain ⟨⟨T', V⟩, hV, hT, hcomb⟩ := B.covering_representative ⟨X.left, E'⟩ hE'
  cases hT
  have hE'V : E'.presieve₀ = V.presieve₀ :=
    PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hcomb
  have hE'sieve : Sieve.generate E'.presieve₀ ∈ B.topology X.left := by
    rw [hE'V]
    exact B.precoverage.generate_mem_toGrothendieck ⟨V, rfl, hV⟩
  have hgen : Sieve.generate E.presieve₀ ∈ topology B S hS X := by
    rw [topology, GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate]
    apply B.topology.superset_covering _ hE'sieve
    rw [Sieve.generate_le_iff]
    rintro Y f ⟨i⟩
    exact ⟨E'.X i, 𝟙 _, E'.f i,
      ⟨E.X i, E.f i, 𝟙 _, ⟨i⟩, by simp [E', K, PreZeroHypercover.map]⟩, by simp⟩
  rw [Presieve.isSheafFor_iff_generate]
  exact hF.isSheafFor _ hgen

/-- Affine `n`-space over `S`, as an object of the big h category over `S`: the scheme `𝔸(n; S)`,
which lies below the site's cutoff, equipped with its canonical morphism to `S`. -/
public noncomputable def affineSpaceObj (n : Type u)
    (hn : (AffineSpace n S).size < B.cutoff) : BigHOver B S hS :=
  Over.mk (ObjectProperty.homMk (X := B.obj (AffineSpace n S) hn) (Y := B.obj S hS)
    (AffineSpace n S ↘ S))

/-- The scheme underlying affine `n`-space over `S` in the big h category over `S` is `𝔸(n; S)`. -/
public theorem toScheme_obj_affineSpaceObj (n : Type u)
    (hn : (AffineSpace n S).size < B.cutoff) :
    (toScheme B S hS).obj (affineSpaceObj B S hS n hn) = AffineSpace n S :=
  rfl

/-- Morphisms of the big h category over `S` from an object `U` to affine `n`-space are the
families of `n` global functions on the scheme underlying `U`. -/
public noncomputable def homEquivGlobalFunctions (n : Type u)
    (hn : (AffineSpace n S).size < B.cutoff) (U : BigHOver B S hS) :
    (U ⟶ affineSpaceObj B S hS n hn) ≃ (n → Γ((toScheme B S hS).obj U, ⊤)) :=
  letI : ((toScheme B S hS).obj U).Over S := OverClass.ofHom (B.inclusion.map U.hom)
  Equiv.trans
    { toFun := fun g => ⟨g.left.hom, (Scheme.Hom.isOver_iff (S := S)).mpr (by
        have h := congrArg B.inclusion.map g.w
        rw [Functor.map_comp] at h
        exact h)⟩
      invFun := fun f => Over.homMk (ObjectProperty.homMk f.1) (by
        apply ObjectProperty.hom_ext
        rw [ObjectProperty.FullSubcategory.comp_hom]
        exact (Scheme.Hom.isOver_iff (S := S)).mp f.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    (AffineSpace.homOverEquiv (n := n) S)

/-- The `i`-th global function attached to a morphism to affine `n`-space is the pullback of the
`i`-th standard coordinate. -/
public theorem homEquivGlobalFunctions_apply (n : Type u)
    (hn : (AffineSpace n S).size < B.cutoff) {U : BigHOver B S hS}
    (g : U ⟶ affineSpaceObj B S hS n hn) (i : n) :
    homEquivGlobalFunctions B S hS n hn U g i = g.left.hom.appTop (AffineSpace.coord S i) :=
  rfl

/-- The identification of morphisms to affine `n`-space with families of global functions is
compatible with restriction: precomposing a morphism with `f` restricts its global functions along
`f`. -/
public theorem homEquivGlobalFunctions_comp (n : Type u)
    (hn : (AffineSpace n S).size < B.cutoff) {U V : BigHOver B S hS} (f : V ⟶ U)
    (g : U ⟶ affineSpaceObj B S hS n hn) (i : n) :
    homEquivGlobalFunctions B S hS n hn V (f ≫ g) i =
      ((toScheme B S hS).map f).appTop (homEquivGlobalFunctions B S hS n hn U g i) := by
  rw [homEquivGlobalFunctions_apply, homEquivGlobalFunctions_apply]
  change (f.left.hom ≫ g.left.hom).appTop (AffineSpace.coord S i) = _
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- The affine line over `S`, as an object of the big h category over `S`: affine `n`-space for a
one-element index type. -/
public noncomputable def affineLine : BigHOver B S hS :=
  affineSpaceObj B S hS (ULift.{u} (Fin 1)) (Scheme.size_affineSpace_lt _ hS)

/-- Morphisms of the big h category over `S` from an object `U` to the affine line are the global
functions on the scheme underlying `U`. -/
public noncomputable def affineLineHomEquiv (U : BigHOver B S hS) :
    (U ⟶ affineLine B S hS) ≃ Γ((toScheme B S hS).obj U, ⊤) :=
  (homEquivGlobalFunctions B S hS _ _ U).trans (Equiv.funUnique _ _)

/-- The identification of morphisms to the affine line with global functions is compatible with
restriction. -/
public theorem affineLineHomEquiv_comp {U V : BigHOver B S hS} (f : V ⟶ U)
    (g : U ⟶ affineLine B S hS) :
    affineLineHomEquiv B S hS V (f ≫ g) =
      ((toScheme B S hS).map f).appTop (affineLineHomEquiv B S hS U g) :=
  homEquivGlobalFunctions_comp B S hS _ _ f g default

/-- The presheaf of global functions on the big h category over `S`: the presheaf of types obtained
by taking global sections of the structure sheaf of the underlying scheme. -/
public noncomputable abbrev globalFunctions : (BigHOver B S hS)ᵒᵖ ⥤ Type u :=
  (toScheme B S hS).op ⋙ Scheme.Γ.{u} ⋙ CategoryTheory.forget CommRingCat.{u}

/-- The presheaf of global functions on the big h category over `S` is the presheaf represented by
the affine line over `S`: `𝒪(X) = Mor_S(X, 𝔸¹_S)` naturally in `X`. -/
@[ega "II 1.7.13" "identification Hom_S(X"]
public noncomputable def globalFunctionsIsoYonedaAffineLine :
    globalFunctions B S hS ≅ yoneda.obj (affineLine B S hS) :=
  (NatIso.ofComponents (fun U => (affineLineHomEquiv B S hS U.unop).toIso) (by
    intro U V f
    ext g
    exact affineLineHomEquiv_comp B S hS f.unop g)).symm

/-! ### Failure of subcanonicity -/

/-- Over a nonempty base there is a one-element h covering in the big h category over `S` which is
a monomorphism and along which global functions do not restrict injectively. -/
public theorem exists_mono_isHCovering_not_injective_appTop [Nonempty S] :
    ∃ (Y X : BigHOver B S hS) (p : X ⟶ Y), Mono p ∧
      IsHCovering (fun _ : PUnit.{u + 2} ↦ (toScheme B S hS).obj X)
        (fun _ ↦ (toScheme B S hS).map p) ∧
      ¬ Function.Injective ((toScheme B S hS).map p).appTop := by
  obtain ⟨s⟩ := ‹Nonempty S›
  set j := S.affineOpenCover.idx s
  set R : CommRingCat.{u} := S.affineOpenCover.X j
  have hne : Nonempty (Spec R) := by
    obtain ⟨y, -⟩ := S.affineOpenCover.covers s
    exact ⟨y⟩
  have : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp hne
  have := algebra_finiteType_dualNumber (R : Type u)
  have hsR : (Spec R).size < B.cutoff :=
    Scheme.size_lt_of_isOpenImmersion (S.affineOpenCover.f j) hS
  have hsD : (Spec (CommRingCat.of (DualNumber R))).size < B.cutoff :=
    Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      (R : Type u) (DualNumber R) hsR
  set φ : CommRingCat.of (DualNumber R) ⟶ R := dualNumberFst R
  have : IsClosedImmersion (Spec.map φ) :=
    IsClosedImmersion.spec_of_surjective φ (surjective_dualNumberFst R)
  set ιS : Spec R ⟶ S := S.affineOpenCover.f j
  have hpσ : Spec.map φ ≫ Spec.map (dualNumberInl R) = 𝟙 (Spec R) := by
    rw [← Spec.map_comp, dualNumberInl_comp_fst, Spec.map_id]
  refine ⟨Over.mk (ObjectProperty.homMk
      (X := B.obj (Spec (CommRingCat.of (DualNumber R))) hsD) (Y := B.obj S hS)
      (Spec.map (dualNumberInl R) ≫ ιS)),
    Over.mk (ObjectProperty.homMk (X := B.obj (Spec R) hsR) (Y := B.obj S hS) ιS),
    Over.homMk (ObjectProperty.homMk (Spec.map φ)) ?_, ?_, ?_, ?_⟩
  · apply ObjectProperty.hom_ext
    change Spec.map φ ≫ (Spec.map (dualNumberInl R) ≫ ιS) = ιS
    rw [← Category.assoc, hpσ, Category.id_comp]
  · exact (toScheme B S hS).mono_of_mono_map (inferInstanceAs (Mono (Spec.map φ)))
  · exact isHCovering_specMap φ (surjective_dualNumberFst R)
      (ker_dualNumberFst_le_nilradical R) (fg_ker_dualNumberFst R)
  · exact not_injective_appTop_specMap φ (ker_dualNumberFst_ne_bot R)

/-- Over a nonempty base the presheaf represented by the affine line is not a sheaf for the big h
topology. -/
public theorem not_isSheaf_yoneda_affineLine [Nonempty S] :
    ¬ Presheaf.IsSheaf (topology B S hS) (yoneda.obj (affineLine B S hS)) := by
  intro hsheaf
  obtain ⟨Y, X, p, hmono, hcov, hinj⟩ :=
    exists_mono_isHCovering_not_injective_appTop B S hS
  refine hinj ?_
  have hsf : Presieve.IsSheafFor (yoneda.obj (affineLine B S hS))
      (PreZeroHypercover.presieve₀
        ({ I₀ := PUnit.{u + 2}, X := fun _ => X, f := fun _ => p } :
          PreZeroHypercover.{u + 1} Y)) :=
    isSheafFor_presieve₀_of_isHCovering B S hS hsheaf _ hcov
  have hbij := Presieve.bijective_map_op_of_isSheafFor_mono (J := PUnit.{u + 2})
    (yoneda.obj (affineLine B S hS)) p hsf
  intro a b hab
  have key : p ≫ (affineLineHomEquiv B S hS Y).symm a
      = p ≫ (affineLineHomEquiv B S hS Y).symm b := by
    apply (affineLineHomEquiv B S hS X).injective
    rw [affineLineHomEquiv_comp, affineLineHomEquiv_comp, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply, hab]
  simpa using congrArg (affineLineHomEquiv B S hS Y) (hbij.1 key)

/-- On a big h site over a nonempty base scheme `S` the h topology is not subcanonical: not every
representable presheaf on `(Sch/S)_h` is a sheaf. -/
@[stacks 0EV1]
public theorem not_subcanonical_topology [Nonempty S] :
    ¬ (topology B S hS).Subcanonical := by
  intro hsub
  refine not_isSheaf_yoneda_affineLine B S hS ?_
  exact (isSheaf_iff_isSheaf_of_type _ _).mpr
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

end BigHOver

end NotSubcanonical

end AlgebraicGeometry
