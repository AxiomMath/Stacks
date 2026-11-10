module

public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Derivation.Basic
public import StacksFrontier.Deformation.FormalObject.DerivationOrbits
public import StacksFrontier.Deformation.FormalObject.RepresentableMorphism
public import StacksFrontier.Deformation.Groupoid.Smooth
public import StacksFrontier.Deformation.PredeformationTangent.TangentVectorSpace
public import StacksFrontier.Deformation.RimSchlessingerCategory.Prorepresentable
public import StacksFrontier.Deformation.Schlessinger.MinimalVersalOrbits
public import StacksFrontier.Deformation.Schlessinger.MiniversalSeparable
public import StacksFrontier.Deformation.Schlessinger.VersalBijectiveDifferential
public import StacksFrontier.Deformation.SchlessingerConditions.SmoothMorphisms
public import StacksFrontier.Deformation.TangentSpace.BijectiveDifferential
public import StacksFrontier.Deformation.TangentSpace.Derivations
public import StacksFrontier.Deformation.Terminal
public import StacksFrontier.Deformation.VersalObject.MinimalVersalDerivationOrbits
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver

/-!
# A versal formal object, bijective on derivation orbits, with no condition (S2)

The quotient of the functor represented by the dual numbers by the involution attached to a
nonzero derivation of a purely inseparable quadratic extension is a predeformation category
carrying a versal formal object whose differential is bijective on `Der_Λ(k, k)`-orbits and
which does not satisfy Schlessinger's condition (S2).

## Main definitions

* `Deformation.OrbitQuotient.der`: a nonzero `Λ`-derivation of the residue field.
* `Deformation.OrbitQuotient.quotFun`: the quotient of the functor represented by the dual
  numbers by the involution attached to that derivation.
* `Deformation.OrbitQuotient.xi`: the formal object of its category of elements over the
  dual numbers.

## Main results

* `Deformation.exists_versal_orbitBijective_not_schlessingerConditionS2` (**Stacks 06T7**): there
  is a predeformation category with a versal formal object whose differential is bijective on
  `Der_Λ(k, k)`-orbits and which does not satisfy (S2).
* `Deformation.OrbitQuotient.isVersal`,
  `Deformation.OrbitQuotient.hasBijectiveDifferentialOnDerivationOrbits` and
  `Deformation.OrbitQuotient.not_schlessingerConditionS2`: the three assertions about this
  example.

## Implementation notes

The base ring is `Λ = 𝔽₂(t)` and the residue field is the purely inseparable quadratic
extension `k = Λ[u]/(u² - t)`, so `Λ` is Noetherian and `k` is finite over it, as the chapter
assumes. The involution of `k[ε]` is the twisting automorphism of a nonzero `δ ∈ Der_Λ(k, k)`;
since `k` has characteristic two it has order two, so it generates a finite nontrivial subgroup
of the automorphism group of `k[ε]` over `𝒞_Λ`, which is the group the source quotients by. A
subgroup acting on `ε` by a scalar other than one would move the differential outside the
`Der_Λ(k, k)`-orbit of its source, so the inseparability is what makes the orbit condition hold
while (S2) fails.

Smoothness of the quotient morphism, which is versality of the formal object, comes from the
orbit of a representative: a lift along a surjection can be corrected by the involution.
Failure of (S2) is read off the fibre product `k[ε] ×_k k[ε]`: the two points with coordinates
`(1, ε)` and `(σ, ε)` have the same pair of projections up to the involution but lie in
different orbits.

## References

* [Stacks Project, Tag 06T7](https://stacks.math.columbia.edu/tag/06T7)
-/

@[expose] public section

open CategoryTheory Polynomial

namespace Deformation.OrbitQuotient

/-! ### An inseparable quadratic extension in characteristic two -/

/-- The base field. -/
noncomputable abbrev Lam : Type := RatFunc (ZMod 2)

/-- The variable `X` is not a square in `𝔽₂(X)`. -/
theorem not_isSquare_X : ∀ b : Lam, b ^ 2 ≠ RatFunc.X := by
  intro b hb
  have h0 : b ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hb
    exact RatFunc.X_ne_zero hb.symm
  have h := RatFunc.intDegree_mul (x := b) (y := b) h0 h0
  rw [← pow_two, hb, RatFunc.intDegree_X] at h
  omega

/-- The inseparable quadratic polynomial. -/
noncomputable abbrev polyF : Lam[X] := X ^ 2 - C RatFunc.X

/-- The polynomial `X² - t` is irreducible over `Lam`. -/
theorem irreducible_polyF : Irreducible polyF :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two not_isSquare_X

/-- The polynomial `polyF` is irreducible. -/
instance : Fact (Irreducible polyF) := ⟨irreducible_polyF⟩

/-- The residue field: a purely inseparable quadratic extension of `Lam`. -/
noncomputable abbrev Kay : Type := AdjoinRoot polyF

/-- The field `Kay` has characteristic two. -/
instance : CharP Kay 2 :=
  charP_of_injective_algebraMap (algebraMap Lam Kay).injective 2

/-- The field `Kay` is finite over `Lam`. -/
instance : Module.Finite Lam Kay :=
  (AdjoinRoot.powerBasis (f := polyF) irreducible_polyF.ne_zero).finite

/-- In `Lam`, `2 = 0`. -/
theorem two_eq_zero_lam : (2 : Lam) = 0 := CharTwo.two_eq_zero

/-- The quotient map onto the residue field, as an algebra homomorphism. -/
noncomputable def mkAlg : Lam[X] →ₐ[Lam] Kay where
  toFun := AdjoinRoot.mk polyF
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' r := by simp [AdjoinRoot.algebraMap_eq, AdjoinRoot.mk_C]

/-- The map `mkAlg` sends a polynomial to its class modulo `polyF`. -/
theorem mkAlg_apply (p : Lam[X]) : mkAlg p = AdjoinRoot.mk polyF p := rfl

/-- The quotient map `mkAlg` is surjective. -/
theorem mkAlg_surjective : Function.Surjective (mkAlg : Lam[X] → Kay) :=
  fun y => AdjoinRoot.mk_surjective y

/-- Differentiation of polynomials, as a derivation. -/
noncomputable abbrev derivPoly : Derivation Lam Lam[X] Lam[X] :=
  Polynomial.mkDerivation Lam (1 : Lam[X])

/-- The derivation `derivPoly` is the formal derivative. -/
theorem derivPoly_apply (p : Lam[X]) : derivPoly p = derivative p := by
  rw [Polynomial.mkDerivation_apply, smul_eq_mul, mul_one]

/-- The formal derivative of `X² - t` vanishes in characteristic two. -/
theorem derivative_polyF : derivative polyF = 0 := by
  simp only [polyF, derivative_sub, derivative_X_pow, derivative_C, Nat.cast_ofNat]
  rw [two_eq_zero_lam]
  simp

/-- Differentiation preserves the ideal generated by `polyF`. -/
theorem derivPoly_mem (p : Lam[X]) (hp : mkAlg p = 0) : mkAlg (derivPoly p) = 0 := by
  rw [derivPoly_apply, mkAlg_apply, AdjoinRoot.mk_eq_zero]
  rw [mkAlg_apply, AdjoinRoot.mk_eq_zero] at hp
  obtain ⟨q, rfl⟩ := hp
  rw [derivative_mul, derivative_polyF]
  exact ⟨derivative q, by ring⟩

/-- A nonzero `Lam`-derivation of the inseparable extension `Kay`. -/
noncomputable def der : Derivation Lam Kay Kay :=
  Derivation.liftOfSurjective (f := mkAlg) mkAlg_surjective derivPoly_mem

/-- The derivation `der` sends the adjoined root to `1`. -/
theorem der_root : der (AdjoinRoot.root polyF) = 1 := by
  have hx : (AdjoinRoot.root polyF : Kay) = mkAlg X := rfl
  rw [hx, der, Derivation.liftOfSurjective_apply mkAlg_surjective derivPoly_mem X,
    derivPoly_apply, derivative_X, mkAlg_apply]
  exact map_one _

/-- The derivation `der` is nonzero. -/
theorem der_ne_zero : der ≠ 0 := by
  intro h
  have h1 := der_root
  rw [h] at h1
  simp at h1

/-- The derivation `der` has additive order dividing two. -/
theorem der_add_der : der + der = 0 := by
  ext x
  simp only [Derivation.add_apply, Derivation.zero_apply]
  exact CharTwo.add_self_eq_zero _

/-! ### The dual numbers and the twisting involution -/

/-- The residue field `Kay`, as a complete local `Lam`-algebra. -/
noncomputable abbrev auxBase : CompleteLocalAlgCat.{0, 0, 0} Lam Kay :=
  artinianToComplete.obj (residueFieldObject.{0, 0, 0} Lam Kay)

/-- The category of elements of the functor represented by the residue field: an auxiliary
predeformation category, used only to name the twisting automorphisms. -/
noncomputable abbrev auxCat := Functor.Elements.π (restrictedCoyoneda auxBase)

/-- The category `auxCat` is a predeformation category. -/
theorem auxCat_isPredeformationCategory : IsPredeformationCategory.{0, 0, 0} auxCat :=
  (isPredeformationCategory_iff _).mpr
    (restrictedCoyoneda_isPredeformationFunctor.{0, 0, 0} auxBase)

/-- The dual numbers over `Kay`, as a complete local algebra. -/
noncomputable abbrev dualBase : CompleteLocalAlgCat.{0, 0, 0} Lam Kay :=
  artinianToComplete.obj (artinianDualNumbers.{0, 0, 0} Lam Kay)

/-- The twisting automorphism of the dual numbers attached to the derivation `der`. -/
noncomputable def twist : artinianDualNumbers.{0, 0, 0} Lam Kay ⟶
    artinianDualNumbers.{0, 0, 0} Lam Kay :=
  dualNumbersTwistHom auxCat auxCat_isPredeformationCategory der

/-- The twisting automorphism `twist` is an involution. -/
theorem twist_twist : twist ≫ twist = 𝟙 _ := by
  have h := dualNumbersTwistHom_add auxCat auxCat_isPredeformationCategory der der
  rw [der_add_der, dualNumbersTwistHom_zero] at h
  exact h.symm

/-- The twisting automorphism, as an endomorphism of the complete local algebra. -/
noncomputable def sigma : dualBase ⟶ dualBase := artinianToComplete.map twist

/-- The endomorphism `sigma` is the image of `twist` under `artinianToComplete`. -/
theorem sigma_def : sigma = artinianToComplete.map twist := rfl

/-- The endomorphism `sigma` is an involution. -/
theorem sigma_sigma : sigma ≫ sigma = 𝟙 _ := by
  rw [sigma, ← Functor.map_comp, twist_twist]
  exact artinianToComplete.map_id _

/-! ### The quotient of the represented functor by the involution -/

/-- Two points of the dual numbers are in the same orbit of the involution. -/
def orbitRel (A : ArtinianLocalAlgCat.{0, 0, 0} Lam Kay)
    (alpha beta : (restrictedCoyoneda dualBase).obj A) : Prop :=
  beta = alpha ∨ beta = sigma ≫ alpha

/-- Precomposing a point twice with `sigma` gives the point back. -/
theorem sigma_comp_sigma_comp {A : ArtinianLocalAlgCat.{0, 0, 0} Lam Kay}
    (alpha : (restrictedCoyoneda dualBase).obj A) : sigma ≫ sigma ≫ alpha = alpha := by
  rw [← Category.assoc, sigma_sigma, Category.id_comp]

/-- The orbit relation is an equivalence relation. -/
def orbitSetoid (A : ArtinianLocalAlgCat.{0, 0, 0} Lam Kay) :
    Setoid ((restrictedCoyoneda dualBase).obj A) where
  r := orbitRel A
  iseqv := by
    refine ⟨fun a => Or.inl rfl, ?_, ?_⟩
    · rintro a b (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (sigma_comp_sigma_comp a).symm
    · rintro a b c (rfl | rfl) (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inr rfl
      · exact Or.inl (sigma_comp_sigma_comp a)

/-- The orbit relation is preserved by postcomposition with a morphism of Artinian algebras. -/
theorem orbitRel_comp {A B : ArtinianLocalAlgCat.{0, 0, 0} Lam Kay} (f : A ⟶ B)
    {alpha beta : (restrictedCoyoneda dualBase).obj A} (h : orbitRel A alpha beta) :
    orbitRel B (alpha ≫ artinianToComplete.map f) (beta ≫ artinianToComplete.map f) := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Category.assoc _ _ _)

/-- The quotient of the functor represented by the dual numbers by the involution. -/
noncomputable def quotFun : ArtinianLocalAlgCat.{0, 0, 0} Lam Kay ⥤ Type 0 where
  obj A := Quotient (orbitSetoid A)
  map {A B} f := TypeCat.ofHom
    (Quotient.map (fun alpha => alpha ≫ artinianToComplete.map f)
      (fun _ _ h => orbitRel_comp f h))
  map_id A := by
    ext x
    induction x using Quotient.ind with
    | _ a =>
      exact congrArg (Quotient.mk (orbitSetoid A))
        (by rw [artinianToComplete.map_id]; exact Category.comp_id a)
  map_comp {A B C} f g := by
    ext x
    induction x using Quotient.ind with
    | _ a =>
      exact congrArg (Quotient.mk (orbitSetoid C))
        (by rw [artinianToComplete.map_comp]; exact (Category.assoc a _ _).symm)

/-- The predeformation category of the quotient functor. -/
noncomputable abbrev quotCat := Functor.Elements.π quotFun

/-- The quotient functor `quotFun` is a predeformation functor. -/
theorem quotFun_isPredeformationFunctor : IsPredeformationFunctor.{0, 0, 0} quotFun := by
  obtain ⟨hu⟩ := restrictedCoyoneda_isPredeformationFunctor.{0, 0, 0} dualBase
  refine ⟨⟨⟨Quotient.mk (orbitSetoid _) hu.default⟩, ?_⟩⟩
  intro q
  induction q using Quotient.ind with
  | _ a => exact congrArg (Quotient.mk (orbitSetoid _)) (hu.uniq a)

/-- The category `quotCat` is a predeformation category. -/
theorem quotCat_isPredeformationCategory : IsPredeformationCategory.{0, 0, 0} quotCat :=
  (isPredeformationCategory_iff quotFun).mpr quotFun_isPredeformationFunctor

/-- The quotient map, as a natural transformation of functors on Artinian local algebras. -/
noncomputable def toQuot : restrictedCoyoneda dualBase ⟶ quotFun where
  app A := TypeCat.ofHom (fun alpha => Quotient.mk (orbitSetoid A) alpha)
  naturality {A B} f := by ext alpha; rfl

/-- The quotient map sends a point to its orbit class. -/
theorem toQuot_app (A : ArtinianLocalAlgCat.{0, 0, 0} Lam Kay)
    (alpha : (restrictedCoyoneda dualBase).obj A) :
    (ConcreteCategory.hom (toQuot.app A)) alpha = Quotient.mk (orbitSetoid A) alpha := rfl

/-- The functor `quotFun` acts on orbit classes by postcomposition of representatives. -/
theorem quotFun_map_mk {A B : ArtinianLocalAlgCat.{0, 0, 0} Lam Kay} (f : A ⟶ B)
    (alpha : (restrictedCoyoneda dualBase).obj A) :
    (ConcreteCategory.hom (quotFun.map f)) (Quotient.mk (orbitSetoid A) alpha) =
      Quotient.mk (orbitSetoid B) (alpha ≫ artinianToComplete.map f) := rfl

/-- The formal object of the quotient category over the dual numbers. -/
noncomputable def xi : FormalObject quotCat where
  base := dualBase
  level n := Functor.elementsMk quotFun (AdicTruncation.obj dualBase n)
    (Quotient.mk (orbitSetoid _) (canonicalQuotientPoint dualBase n))
  level_eq _ := rfl
  transition n := Functor.Elements.homMk (AdicTruncation.transition dualBase n)
    (congrArg (Quotient.mk (orbitSetoid _)) (canonicalQuotientPoint_transition dualBase n))
  transition_lift _ := CategoryTheory.IsHomLift.of_fac quotCat _ _ rfl rfl rfl

/-- The base of the formal object `xi` is the dual numbers. -/
theorem xi_base : xi.base = dualBase := rfl

/-! ### Failure of Schlessinger's condition (S2) -/

open CategoryTheory.Limits

/-- The functor `artinianToComplete` is faithful. -/
theorem artinianToComplete_map_injective {A B : ArtinianLocalAlgCat.{0, 0, 0} Lam Kay}
    {f g : A ⟶ B} (h : artinianToComplete.map f = artinianToComplete.map g) : f = g :=
  ArtinianLocalAlgCat.hom_ext (congrArg CompleteLocalAlgCat.Hom.hom h)

/-- The automorphism `twist` is the twisting automorphism of `der` computed in `quotCat`. -/
theorem twist_eq_dualNumbersTwistHom :
    twist = dualNumbersTwistHom quotCat quotCat_isPredeformationCategory der :=
  dualNumbersTwistHom_eq_of_formula auxCat auxCat_isPredeformationCategory quotCat
    quotCat_isPredeformationCategory der

/-- The residue map of the dual numbers sends `inl a` to `a`. -/
theorem residueHom_dualBase_inl (a : Kay) :
    residueHom dualBase (TrivSqZeroExt.inl a : (artinianDualNumbers.{0, 0, 0} Lam Kay)) = a := by
  change (artinianDualNumbers.{0, 0, 0} Lam Kay).residueEquiv
      (IsLocalRing.residue _ (TrivSqZeroExt.inl a)) = a
  rw [squareZeroExtensionArtinian_residue]
  rfl

/-- The twisting automorphism is not the identity. -/
theorem twist_ne_id : twist ≠ 𝟙 (artinianDualNumbers.{0, 0, 0} Lam Kay) := by
  intro h
  have key := twist_squareZeroPoint_snd quotCat_isPredeformationCategory xi der
    (𝟙 dualBase) (TrivSqZeroExt.inl (AdjoinRoot.root polyF))
  rw [← twist_eq_dualNumbersTwistHom] at key
  have hpt : (restrictedCoyoneda xi.base).map twist (𝟙 dualBase) = 𝟙 dualBase := by
    change 𝟙 dualBase ≫ artinianToComplete.map twist = 𝟙 dualBase
    rw [Category.id_comp, h]
    exact artinianToComplete.map_id _
  rw [hpt] at key
  have h0 : der (residueHom xi.base
      (TrivSqZeroExt.inl (AdjoinRoot.root polyF) : xi.base)) = 0 := by
    linear_combination -key
  have h1 : der (AdjoinRoot.root polyF) = 0 := by
    rwa [← residueHom_dualBase_inl (AdjoinRoot.root polyF)]
  rw [der_root] at h1
  exact one_ne_zero h1

/-- The one-dimensional `Kay`-module whose square-zero extension is the dual numbers. -/
noncomputable abbrev dualMod : FGModuleCat.{0} Kay := dualNumbersModule.{0, 0, 0} Lam Kay

/-- The fibre product `k[ε] ×_k k[ε]`, as the square-zero extension by `dualMod × dualMod`. -/
noncomputable abbrev prodP : ArtinianLocalAlgCat.{0, 0, 0} Lam Kay :=
  (squareZeroExtensionArtinian Lam Kay).obj (prodModule dualMod dualMod)

/-- The first projection of the fibre product `prodP`. -/
noncomputable abbrev projFst : prodP ⟶ artinianDualNumbers.{0, 0, 0} Lam Kay :=
  squareZeroProductFst.{0, 0, 0}
/-- The second projection of the fibre product `prodP`. -/
noncomputable abbrev projSnd : prodP ⟶ artinianDualNumbers.{0, 0, 0} Lam Kay :=
  squareZeroProductSnd.{0, 0, 0}

/-- The residue-field object is terminal. -/
noncomputable def isTerminalResidueFieldObject :
    IsTerminal (residueFieldObject.{0, 0, 0} Lam Kay) :=
  ArtinianLocalAlgCat.isTerminal_of_algEquiv _ (ULift.algEquiv (R := Lam) (A := Kay))

/-- The algebra `prodP` with its two projections is the fibre product `k[ε] ×_k k[ε]`. -/
theorem prodP_isPullback :
    IsPullback projFst projSnd (squareZeroProjection.{0, 0, 0} dualMod)
      (squareZeroProjection.{0, 0, 0} dualMod) :=
  squareZeroProduct_isPullback.{0, 0, 0}

/-- The diagonal point of the fibre product. -/
noncomputable def ptDiag : artinianDualNumbers.{0, 0, 0} Lam Kay ⟶ prodP :=
  prodP_isPullback.lift (𝟙 _) (𝟙 _) (isTerminalResidueFieldObject.hom_ext _ _)

/-- The point of the fibre product twisted in the first coordinate only. -/
noncomputable def ptTwist : artinianDualNumbers.{0, 0, 0} Lam Kay ⟶ prodP :=
  prodP_isPullback.lift twist (𝟙 _) (isTerminalResidueFieldObject.hom_ext _ _)

/-- The first coordinate of `ptDiag` is the identity. -/
theorem ptDiag_fst : ptDiag ≫ projFst = 𝟙 _ := prodP_isPullback.lift_fst _ _ _
/-- The second coordinate of `ptDiag` is the identity. -/
theorem ptDiag_snd : ptDiag ≫ projSnd = 𝟙 _ := prodP_isPullback.lift_snd _ _ _
/-- The first coordinate of `ptTwist` is `twist`. -/
theorem ptTwist_fst : ptTwist ≫ projFst = twist := prodP_isPullback.lift_fst _ _ _
/-- The second coordinate of `ptTwist` is the identity. -/
theorem ptTwist_snd : ptTwist ≫ projSnd = 𝟙 _ := prodP_isPullback.lift_snd _ _ _

/-- The predeformation category `quotCat` does not satisfy Schlessinger's condition (S2). -/
theorem not_schlessingerConditionS2 : ¬ SchlessingerConditionS2 quotCat := by
  intro hS2
  have hbij := elements_bijective_of_schlessingerConditionS2 quotFun
    (squareZeroProjection.{0, 0, 0} dualMod) (squareZeroProjection.{0, 0, 0} dualMod)
    projFst projSnd prodP_isPullback.flip
    (squareZeroProjection_isSquareZeroProjection.{0, 0, 0} dualMod)
    (categoryOfElements_projection_isCofibered quotFun) hS2
    (fun x y => by
      obtain ⟨hu⟩ := quotFun_isPredeformationFunctor
      exact (hu.uniq _).trans (hu.uniq _).symm)
  have key := hbij.1 (a₁ := Quotient.mk (orbitSetoid prodP) (artinianToComplete.map ptDiag))
    (a₂ := Quotient.mk (orbitSetoid prodP) (artinianToComplete.map ptTwist)) ?_
  · rcases Quotient.exact key with heq | heq
    · refine twist_ne_id (artinianToComplete_map_injective ?_)
      simpa only [← Functor.map_comp, ptDiag_fst, ptTwist_fst] using
        congrArg (fun z => z ≫ artinianToComplete.map projFst) heq
    · refine twist_ne_id (artinianToComplete_map_injective ?_)
      have h := congrArg (fun z => z ≫ artinianToComplete.map projSnd) heq
      simp only [← Functor.map_comp, ptDiag_snd, ptTwist_snd, Category.assoc] at h
      rw [artinianToComplete.map_id, Category.comp_id] at h
      rw [artinianToComplete.map_id, ← sigma_def]
      exact h.symm
  · refine Prod.ext ?_ ?_
    · change (ConcreteCategory.hom (quotFun.map projFst)) _ =
        (ConcreteCategory.hom (quotFun.map projFst)) _
      rw [quotFun_map_mk, quotFun_map_mk]
      refine Quotient.sound (Or.inr ?_)
      rw [← Functor.map_comp, ← Functor.map_comp, ptDiag_fst, ptTwist_fst,
        artinianToComplete.map_id, sigma, Category.comp_id]
    · change (ConcreteCategory.hom (quotFun.map projSnd)) _ =
        (ConcreteCategory.hom (quotFun.map projSnd)) _
      rw [quotFun_map_mk, quotFun_map_mk, ← Functor.map_comp, ← Functor.map_comp,
        ptDiag_snd, ptTwist_snd]

/-! ### The morphism associated to the formal object is the quotient map -/

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

/-- The fibre value of the element `⟨A, x⟩` over `A` is `x`. -/
theorem elementsFiberValue_mk (A : ArtinianLocalAlgCat.{0, 0, 0} Lam Kay)
    (x : quotFun.obj A) :
    elementsFiberValue quotFun A ⟨quotFun.elementsMk A x, rfl⟩ = x := by
  change (ConcreteCategory.hom (quotFun.map (eqToHom rfl))) x = x
  rw [eqToHom_refl]
  exact Functor.map_id_apply quotFun A x

/-- The `n`-th level of `xi` is the orbit class of the canonical quotient point. -/
theorem elementsFiberValue_xi_level (n : ℕ) :
    elementsFiberValue quotFun (AdicTruncation.obj dualBase n) ⟨xi.level n, xi.level_eq n⟩ =
      Quotient.mk (orbitSetoid _) (canonicalQuotientPoint dualBase n) :=
  elementsFiberValue_mk _ _

/-- The value of the associated morphism of `xi` at an Artinian point is the orbit class of
that point. -/
theorem associatedMorphism_value (P : ChosenPushforwards quotCat)
    (A : ArtinianLocalAlgCat.{0, 0, 0} Lam Kay)
    (alpha : (restrictedCoyoneda dualBase).obj A) :
    elementsFiberValue quotFun A
        ⟨(associatedMorphism quotCat_isPredeformationCategory.cofibered xi P).toBasedFunctor.obj
            ((restrictedCoyoneda dualBase).elementsMk A alpha),
          (associatedMorphism quotCat_isPredeformationCategory.cofibered
            xi P).toBasedFunctor.w_obj ((restrictedCoyoneda dualBase).elementsMk A alpha)⟩ =
      Quotient.mk (orbitSetoid A) alpha := by
  set M := associatedMorphism quotCat_isPredeformationCategory.cofibered xi P
  let n := M.level ⟨alpha⟩
  let m := M.factor ⟨alpha⟩
  let src : Functor.Fiber quotCat (AdicTruncation.obj dualBase n) := ⟨xi.level n, xi.level_eq n⟩
  let tgt : Functor.Fiber quotCat A := (P m).obj src
  have hval : (ConcreteCategory.hom (quotFun.map m))
      (elementsFiberValue quotFun (AdicTruncation.obj dualBase n) src) =
      elementsFiberValue quotFun A tgt :=
    elementsFiberValue_map quotFun m src tgt ((P m).inclusion src)
      ((P m).cocartesian src).toIsHomLift
  rw [show elementsFiberValue quotFun (AdicTruncation.obj dualBase n) src = _ from
    elementsFiberValue_xi_level n] at hval
  have hval2 : Quotient.mk (orbitSetoid A)
      (canonicalQuotientPoint dualBase n ≫ artinianToComplete.map m) =
      elementsFiberValue quotFun A tgt := hval
  have hcomp : canonicalQuotientPoint dualBase n ≫ artinianToComplete.map m = alpha := by
    apply CompleteLocalAlgCat.Hom.ext
    rw [CompleteLocalAlgCat.comp_hom, canonicalQuotientPoint_hom]
    exact (M.factor_spec ⟨alpha⟩).2.2
  have hobj : (⟨M.toBasedFunctor.obj ⟨alpha⟩, M.toBasedFunctor.w_obj ⟨alpha⟩⟩ :
      Functor.Fiber quotCat A) = tgt := Subtype.ext (M.obj_eq ⟨alpha⟩)
  refine (congrArg (elementsFiberValue quotFun A) hobj).trans ?_
  rw [← hval2, hcomp]

/-- An element over `A` with fibre value `v` is the element `⟨A, v⟩`. -/
theorem elements_eq_of_value {A : ArtinianLocalAlgCat.{0, 0, 0} Lam Kay}
    (z : quotFun.Elements) (h : quotCat.obj z = A) (v : quotFun.obj A)
    (hv : elementsFiberValue quotFun A ⟨z, h⟩ = v) : z = quotFun.elementsMk A v := by
  obtain @⟨z1, z2⟩ := z
  obtain rfl : z1 = A := h
  rw [elementsFiberValue_mk] at hv
  exact congrArg (fun w => (⟨w⟩ : quotFun.Elements)) hv

/-- The associated morphism of `xi` sends a point to its orbit class. -/
theorem associatedMorphism_obj (P : ChosenPushforwards quotCat)
    (X : (restrictedCoyoneda dualBase).Elements) :
    (associatedMorphism quotCat_isPredeformationCategory.cofibered xi P).toBasedFunctor.obj X =
      quotFun.elementsMk X.obj (Quotient.mk (orbitSetoid X.obj) X.val) :=
  elements_eq_of_value _
    ((associatedMorphism quotCat_isPredeformationCategory.cofibered xi P).toBasedFunctor.w_obj X)
    _ (associatedMorphism_value P X.obj X.val)

/-- The associated morphism of `xi` is the functor of elements induced by `toQuot`. -/
theorem associatedMorphism_eq (P : ChosenPushforwards quotCat) :
    (associatedMorphism quotCat_isPredeformationCategory.cofibered xi P).toBasedFunctor =
      elementsBasedFunctor toQuot := by
  have hobj : ∀ X : (restrictedCoyoneda dualBase).Elements,
      (associatedMorphism quotCat_isPredeformationCategory.cofibered xi P).toBasedFunctor.obj X =
        (elementsBasedFunctor toQuot).obj X := fun X => associatedMorphism_obj P X
  refine BasedCategory.BasedFunctor.ext' (CategoryTheory.Functor.ext hobj ?_)
  intro X Y h
  apply Functor.Elements.hom_ext
  have hlift : (BasedCategory.ofFunctor
      (Functor.Elements.π (restrictedCoyoneda xi.base))).p.IsHomLift h.hom h :=
    IsHomLift.of_fac _ h.hom h rfl rfl rfl
  have hfac := IsHomLift.fac' (BasedCategory.ofFunctor quotCat).p h.hom
    ((associatedMorphism quotCat_isPredeformationCategory.cofibered xi P).toBasedFunctor.map h)
  change (BasedCategory.ofFunctor quotCat).p.map
      ((associatedMorphism quotCat_isPredeformationCategory.cofibered xi P).toBasedFunctor.map h) =
    (BasedCategory.ofFunctor quotCat).p.map
      (eqToHom (hobj X) ≫ (elementsBasedFunctor toQuot).map h ≫ eqToHom (hobj Y).symm)
  rw [hfac]
  simp only [CategoryTheory.Functor.map_comp, eqToHom_map]
  rfl

/-- The functor of elements induced by the quotient map `toQuot` is smooth. -/
theorem isSmooth_toQuot : IsSmooth (elementsBasedFunctor toQuot) := by
  refine (isSmooth_elementsBasedFunctor_iff toQuot).mpr ?_
  intro B A f hf xA yB hxy
  obtain ⟨beta, hbeta⟩ := Quotient.exists_rep yB
  subst hbeta
  rcases Quotient.exact hxy with h1 | h1
  · exact ⟨beta, h1, rfl⟩
  · refine ⟨sigma ≫ beta, ?_, Quotient.sound (Or.inr (sigma_comp_sigma_comp beta).symm)⟩
    change (sigma ≫ beta) ≫ artinianToComplete.map f = xA
    rw [Category.assoc, show beta ≫ artinianToComplete.map f = sigma ≫ xA from h1,
      sigma_comp_sigma_comp]

/-- The formal object `xi` is versal. -/
theorem isVersal : IsVersal quotCat_isPredeformationCategory.cofibered xi := by
  intro P
  rw [associatedMorphism_eq P]
  exact isSmooth_toQuot

/-! ### Bijectivity of the differential on derivation orbits -/

/-- The dual numbers over `Kay`, as an Artinian local algebra. -/
noncomputable abbrev dualPt : ArtinianLocalAlgCat.{0, 0, 0} Lam Kay :=
  artinianDualNumbers.{0, 0, 0} Lam Kay

/-- The proof that `quotCat` is a predeformation category. -/
noncomputable abbrev hpre := quotCat_isPredeformationCategory

/-- Objects of a fibre of `quotCat` with the same isomorphism class are equal. -/
theorem classOf_injective {A : ArtinianLocalAlgCat.{0, 0, 0} Lam Kay}
    (x y : Functor.Fiber quotCat A)
    (h : classOf (BasedCategory.ofFunctor quotCat) hpre.cofibered x =
      classOf (BasedCategory.ofFunctor quotCat) hpre.cofibered y) : x = y := by
  have h1 := classOf_eq (BasedCategory.ofFunctor quotCat) hpre.cofibered x
  have h2 := classOf_eq (BasedCategory.ofFunctor quotCat) hpre.cofibered y
  rw [h] at h1
  exact elementsFiber_skeletal quotFun A (Quotient.exact (h1.symm.trans h2))

/-- On tangent vectors, the associated morphism of `xi` sends the class of a point to the class
of its orbit. -/
theorem map_classOf_point (P : ChosenPushforwards quotCat)
    (alpha : (restrictedCoyoneda xi.base).obj dualPt) :
    mapIsomorphismClasses
        (categoryOfElements_projection_isCofibered (restrictedCoyoneda xi.base))
        hpre.cofibered
        (associatedMorphism hpre.cofibered xi P).toBasedFunctor dualPt
        (classOf (BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda xi.base)))
          (categoryOfElements_projection_isCofibered (restrictedCoyoneda xi.base))
          ⟨(restrictedCoyoneda xi.base).elementsMk dualPt alpha, rfl⟩) =
      classOf (BasedCategory.ofFunctor quotCat) hpre.cofibered
        ⟨quotFun.elementsMk dualPt (Quotient.mk (orbitSetoid dualPt) alpha), rfl⟩ := by
  refine (mapIsomorphismClasses_classOf
    (𝓕 := BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda xi.base)))
    (categoryOfElements_projection_isCofibered (restrictedCoyoneda xi.base))
    (𝓖 := BasedCategory.ofFunctor quotCat) hpre.cofibered
    (associatedMorphism hpre.cofibered xi P).toBasedFunctor
    (A := dualPt) ⟨(restrictedCoyoneda xi.base).elementsMk dualPt alpha, rfl⟩).trans ?_
  exact congrArg (classOf (BasedCategory.ofFunctor quotCat) hpre.cofibered)
    (Subtype.ext (associatedMorphism_obj P ⟨alpha⟩))

/-- If a point `alpha` of the dual numbers has derivation `D`, then the class of its orbit lies
on the graph of the differential at `D`. -/
theorem graph_of_point (P : ChosenPushforwards quotCat)
    (D : Derivations xi.base Kay) (alpha : (restrictedCoyoneda xi.base).obj dualPt)
    (hD : ∀ r : xi.base, (alpha.hom r).snd.down = D r) :
    derivationDifferentialGraph.{0, 0, 0} quotCat hpre xi D
      (classOf (BasedCategory.ofFunctor quotCat) hpre.cofibered
        ⟨quotFun.elementsMk dualPt (Quotient.mk (orbitSetoid dualPt) alpha), rfl⟩) :=
  ⟨P, alpha, hD, map_classOf_point P alpha⟩

/-- A tangent vector on the graph of the differential at `D` is the class of the orbit of a
point with derivation `D`. -/
theorem point_of_graph (D : Derivations xi.base Kay)
    (y : predeformationTangentSpace.{0, 0, 0} quotCat hpre)
    (hy : derivationDifferentialGraph.{0, 0, 0} quotCat hpre xi D y) :
    ∃ alpha : (restrictedCoyoneda xi.base).obj dualPt,
      (∀ r : xi.base, (alpha.hom r).snd.down = D r) ∧
        classOf (BasedCategory.ofFunctor quotCat) hpre.cofibered
          ⟨quotFun.elementsMk dualPt (Quotient.mk (orbitSetoid dualPt) alpha), rfl⟩ = y := by
  obtain ⟨P, alpha, hD, hcl⟩ := hy
  exact ⟨alpha, hD, (map_classOf_point P alpha).symm.trans hcl⟩

/-- Every tangent vector of `quotCat` lies on the graph of the differential at some
derivation. -/
theorem exists_graph (y : predeformationTangentSpace.{0, 0, 0} quotCat hpre) :
    ∃ D : Derivations xi.base Kay,
      derivationDifferentialGraph.{0, 0, 0} quotCat hpre xi D y := by
  obtain ⟨x, hx⟩ := classOf_surjective (BasedCategory.ofFunctor quotCat) hpre.cofibered dualPt y
  obtain ⟨@⟨A, v⟩, hA⟩ := x
  have hA' : A = dualPt := hA
  subst hA'
  obtain ⟨alpha, halpha⟩ := Quotient.exists_rep v
  let : Algebra xi.base Kay := (residueHom xi.base).toRingHom.toAlgebra
  refine ⟨standardToDerivation xi (tangentSpaceDerivationsLinearEquiv xi.base alpha), ?_⟩
  have hcl : classOf (BasedCategory.ofFunctor quotCat) hpre.cofibered
      ⟨quotFun.elementsMk dualPt (Quotient.mk (orbitSetoid dualPt) alpha), rfl⟩ = y := by
    rw [halpha]
    exact hx
  rw [← hcl]
  refine graph_of_point (chosenPushforwardsOfCofibered quotCat hpre.cofibered) _ alpha ?_
  intro r
  refine Eq.symm ((standardToDerivation_apply xi _ r).trans ?_)
  exact tangentSpaceDerivationsLinearEquiv_apply xi.base alpha r

/-! ### The effect of the involution on square-zero components -/

/-- The underlying ring of the dual numbers. -/
noncomputable abbrev DNB : Type := dualBase

/-- The scalar part of a dual number. -/
noncomputable def inlD (c : Kay) : DNB := TrivSqZeroExt.inl c

/-- The nilpotent part of a dual number. -/
noncomputable def inrD (m : ULift Kay) : DNB := TrivSqZeroExt.inr m

/-- The canonical nilpotent of the dual numbers. -/
noncomputable abbrev eps : DNB := inrD (ULift.up (1 : Kay))

/-- The residue map of the dual numbers is the scalar part. -/
theorem residueHom_fst (r : DNB) : residueHom dualBase r = TrivSqZeroExt.fst r := rfl

/-- The residue map sends the scalar `inlD c` to `c`. -/
theorem residueHom_inlD (c : Kay) : residueHom dualBase (inlD c) = c := rfl

/-- The residue map kills the nilpotent part. -/
theorem residueHom_inrD (m : ULift Kay) : residueHom dualBase (inrD m) = 0 := rfl

/-- A dual number is the sum of its scalar and nilpotent parts. -/
theorem decompose_dualBase (r : DNB) :
    inlD (TrivSqZeroExt.fst r) + inrD (TrivSqZeroExt.snd r) = r :=
  TrivSqZeroExt.inl_fst_add_inr_snd_eq r

/-- The involution `sigma` sends `a + bε` to `a + (b + der a)ε`. -/
theorem sigma_hom_apply (a : Kay) (b : ULift Kay) :
    sigma.hom (inlD a + inrD b) = inlD a + inrD (b + ULift.up (der a)) :=
  dualNumbersTwistHom_apply_ulift auxCat auxCat_isPredeformationCategory der a b

private theorem raw_inr_mul (c : Kay) :
    (TrivSqZeroExt.inr (ULift.up c) : TrivSqZeroExt Kay (ULift Kay)) =
      TrivSqZeroExt.inl c * TrivSqZeroExt.inr (ULift.up (1 : Kay)) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · simp
  · simp [ULift.ext_iff]

private theorem raw_key (a : Kay) (b : ULift Kay) (c : Kay) :
    ((TrivSqZeroExt.inl a : TrivSqZeroExt Kay (ULift Kay)) +
        TrivSqZeroExt.inr (b + ULift.up c)) =
      ((TrivSqZeroExt.inl a : TrivSqZeroExt Kay (ULift Kay)) + TrivSqZeroExt.inr b) +
        (TrivSqZeroExt.inl c : TrivSqZeroExt Kay (ULift Kay)) *
          TrivSqZeroExt.inr (ULift.up (1 : Kay)) := by
  rw [TrivSqZeroExt.inr_add, ← raw_inr_mul c]
  ring

/-- In the dual numbers, `a + (b + c)ε = (a + bε) + cε`. -/
theorem split_dualBase (a : Kay) (b : ULift Kay) (c : Kay) :
    inlD a + inrD (b + ULift.up c) = (inlD a + inrD b) + inlD c * eps := raw_key a b c

/-- The involution `sigma` sends `r` to `r + der (r̄) ε`, where `r̄` is the scalar part of `r`. -/
theorem sigma_hom_eq (r : DNB) :
    sigma.hom r = r + inlD (der (TrivSqZeroExt.fst r)) * eps := by
  calc sigma.hom r
      = sigma.hom (inlD (TrivSqZeroExt.fst r) + inrD (TrivSqZeroExt.snd r)) := by
        rw [decompose_dualBase]
    _ = inlD (TrivSqZeroExt.fst r) +
          inrD (TrivSqZeroExt.snd r + ULift.up (der (TrivSqZeroExt.fst r))) :=
        sigma_hom_apply _ _
    _ = (inlD (TrivSqZeroExt.fst r) + inrD (TrivSqZeroExt.snd r)) +
          inlD (der (TrivSqZeroExt.fst r)) * eps := split_dualBase _ _ _
    _ = r + inlD (der (TrivSqZeroExt.fst r)) * eps := by rw [decompose_dualBase]

/-- The derivation of the point `sigma ≫ alpha` is that of `alpha` plus `der` scaled by the
`ε`-component of `alpha ε`. -/
theorem point_snd_sigma (alpha : (restrictedCoyoneda dualBase).obj dualPt) (r : DNB) :
    (alpha.hom (sigma.hom r)).snd.down =
      (alpha.hom r).snd.down + der (residueHom dualBase r) * (alpha.hom eps).snd.down := by
  let : Algebra dualBase Kay := (residueHom dualBase).toRingHom.toAlgebra
  have h1 : ∀ s : DNB,
      (alpha.hom s).snd.down = tangentSpaceDerivationsLinearEquiv dualBase alpha s :=
    fun s => (tangentSpaceDerivationsLinearEquiv_apply dualBase alpha s).symm
  have halg : ∀ s : DNB, algebraMap dualBase Kay s = residueHom dualBase s := fun _ => rfl
  simp only [h1]
  rw [sigma_hom_eq r, map_add, Derivation.leibniz, Algebra.smul_def, Algebra.smul_def,
    halg, halg, residueHom_inlD, residueHom_inrD, residueHom_fst]
  ring

/-! ### The orbit condition -/

/-- If `z` lies in the `Der_Λ(k, k)`-orbit of `y`, then the derivations `E` and `D` attached to
them differ by an element of `Der_Λ(k, k)` composed with the residue map. -/
theorem exists_eq_add (D E : Derivations xi.base Kay)
    (y z : predeformationTangentSpace.{0, 0, 0} quotCat hpre)
    (hy : derivationDifferentialGraph.{0, 0, 0} quotCat hpre xi D y)
    (hz : derivationDifferentialGraph.{0, 0, 0} quotCat hpre xi E z)
    (hact : ∃ delta : Derivation Lam Kay Kay,
      z = (derivationAction.{0, 0, 0} quotCat hpre).action (delta, y)) :
    ∃ delta : Derivation Lam Kay Kay,
      ∀ r : xi.base, E r = D r + delta (residueHom xi.base r) := by
  obtain ⟨delta, hdelta⟩ := hact
  obtain ⟨E0, hE0, hg0⟩ :=
    exists_derivationDifferentialGraph_action.{0, 0, 0} hpre xi D delta y hy
  rw [← hdelta] at hg0
  obtain ⟨aE, haE, hclE⟩ := point_of_graph E z hz
  obtain ⟨a0, ha0, hcl0⟩ := point_of_graph E0 z hg0
  have hcl : Quotient.mk (orbitSetoid dualPt) aE = Quotient.mk (orbitSetoid dualPt) a0 := by
    have h := classOf_injective _ _ (hclE.trans hcl0.symm)
    have h2 := congrArg (elementsFiberValue quotFun dualPt) h
    rw [← elementsFiberValue_mk dualPt (Quotient.mk (orbitSetoid dualPt) aE),
      ← elementsFiberValue_mk dualPt (Quotient.mk (orbitSetoid dualPt) a0)]
    exact h2
  rcases Quotient.exact hcl with h1 | h1
  · refine ⟨delta, fun r => ?_⟩
    rw [← haE r, ← h1, ha0 r, hE0 r]
  · refine ⟨delta - (aE.hom eps).snd.down • der, fun r => ?_⟩
    have hsnd : E0 r = E r + der (residueHom xi.base r) * (aE.hom eps).snd.down := by
      rw [← ha0 r, h1, ← haE r]
      exact point_snd_sigma aE r
    rw [hE0 r] at hsnd
    have hfin := hsnd.symm
    rw [Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul]
    linear_combination hfin

/-- The differential of `xi` is bijective on `Der_Λ(k, k)`-orbits. -/
theorem hasBijectiveDifferentialOnDerivationOrbits :
    HasBijectiveDifferentialOnDerivationOrbits.{0, 0, 0} quotCat hpre xi := by
  refine ⟨fun D => existsUnique_derivationDifferentialGraph hpre xi D,
    fun y => exists_graph y,
    fun D delta y hy => exists_derivationDifferentialGraph_action.{0, 0, 0} hpre xi D delta y hy,
    fun D E y z hy hz => ⟨?_, ?_⟩⟩
  · exact fun hact => exists_eq_add D E y z hy hz hact
  · exact fun hadd => eq_action_of_eq_add.{0, 0, 0} hpre xi D E y z hy hz hadd

end Deformation.OrbitQuotient

namespace Deformation

open OrbitQuotient

/-! ### The example -/

/-- There is a predeformation category carrying a versal formal object whose differential is
bijective on `Der_Λ(k, k)`-orbits and which does not satisfy Schlessinger's condition (S2). -/
@[stacks 06T7]
theorem exists_versal_orbitBijective_not_schlessingerConditionS2 :
    ∃ (B : BasedCategory.{0, 1} (ArtinianLocalAlgCat.{0, 0, 0} Lam Kay))
      (hp : IsPredeformationCategory.{0, 0, 0} B.p) (ksi : FormalObject B.p),
      IsVersal hp.cofibered ksi ∧
        HasBijectiveDifferentialOnDerivationOrbits.{0, 0, 0} B.p hp ksi ∧
          ¬ SchlessingerConditionS2 B.p :=
  ⟨BasedCategory.ofFunctor quotCat, quotCat_isPredeformationCategory, xi, isVersal,
    hasBijectiveDifferentialOnDerivationOrbits, not_schlessingerConditionS2⟩

end Deformation
