module

public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import StacksFrontier.Algebra.Category.Ring.FinitePresentation
public import StacksFrontier.FieldTheory.Separable.Basic
public import StacksFrontier.RingTheory.FinitePresentation.FiniteTypeDescent
public import StacksFrontier.RingTheory.Smooth.Field
public import StacksFrontier.RingTheory.Smoothing.NeronBlowupSequence
public import StacksFrontier.RingTheory.Smoothing.ProductOfFilteredColimits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Néron desingularization: an unramified extension of discrete valuation rings is ind-smooth

Let `R ⊂ Λ` be an extension of discrete valuation rings of ramification index one which induces a
separable extension of residue fields and a separable extension of fraction fields. Then `Λ` is a
filtered colimit of smooth `R`-algebras.

The proof is the source's. By the criterion for being a filtered colimit of members of a family of
algebras (Lemma 07C3) it is enough to factor every `R`-algebra map `A → Λ` with `A` of finite
presentation over `R` through a smooth `R`-algebra. Replacing `A` by its image in `Λ` makes `A` a
domain whose fraction field sits inside the fraction field of `Λ`, hence separable over the
fraction field of `R`; so `R → A` is smooth at the generic prime `(0)` by Lemma 07ND. Finitely many
affine Néron blowups then make `R → A` smooth at the distinguished prime `𝔭` (Lemma 0BJ6), and
localizing at an element outside `𝔭` produces the required smooth algebra.

## Main results

* `Stacks.Smoothing.NeronStage.exists_algHom_of_reflTransGen`: a chain of affine Néron blowups
  from one stage to another induces an `R`-algebra map between them compatible with the maps
  to `Λ`.
* `Stacks.Smoothing.exists_smooth_factorization_of_ramificationIdx_one`: the key step, that every
  finite-type `R`-algebra mapping to `Λ` maps to it through a smooth `R`-algebra.
* `Stacks.Smoothing.ind_underSmooth_of_ramificationIdx_one`: Lemma 0BJ7 itself, that `Λ` is a
  filtered colimit of smooth `R`-algebras.

## Implementation notes

"`Λ` is a filtered colimit of smooth `R`-algebras" is Mathlib's
`CategoryTheory.ObjectProperty.ind.{u}` applied to the property `UnderSmooth (CommRingCat.of R)`
on the category `Under (CommRingCat.of R)` of `R`-algebras — a small filtered index category
together with a colimit presentation of `Λ` all of whose values are smooth `R`-algebras. This is
exactly the left-hand side of the library's form of Lemma 07C3,
`CommRingCat.ind_under_iff_exists_factorization`, which is the only way the conclusion is produced.

The residue fields are spelled `(IsLocalRing.maximalIdeal R).ResidueField`, that is
`Ideal.ResidueField` at the maximal ideal, with the extension `Ideal.residueFieldAlgebra` of a
prime lying over another, taken at the two maximal ideals: `(IsLocalRing.maximalIdeal Λ)` lies
over `(IsLocalRing.maximalIdeal R)` for a local homomorphism, by Mathlib's instance for
`IsLocalHom`. This is the spelling used throughout the
Néron chain (`NeronSituation.residueFieldExtension`, Lemmas 0BJ4, 0BJ5, 0BJ6); it is
canonically isomorphic to `IsLocalRing.ResidueField`, so the hypothesis is neither stronger nor
weaker than the source's.

The fraction fields are abstract, pinned by `IsFractionRing` together with compatible scalar
towers, as in Lemma 07ND; this is more general than instantiating them at
`FractionRing`. An extension of discrete valuation rings is an injective local homomorphism
([Stacks 09E4](https://stacks.math.columbia.edu/tag/09E4)), stated directly, and the ramification
index is `Stacks.DiscreteValuationRing.Ramification.ramificationIdx`.

## Scope: nothing of Lemma 0BJ7 is omitted

Lemma 0BJ7 is a single assertion with no functoriality, naturality or uniqueness clause, and
`Stacks.Smoothing.ind_underSmooth_of_ramificationIdx_one` states it in full: every hypothesis is
the source's and the conclusion is the source's. The two inputs the source's proof cites but does
not prove here, Lemmas 0BJ6 and 07C3, are
`Stacks.Smoothing.exists_finite_affineNeronBlowup_smoothAt` and
`CommRingCat.ind_under_iff_exists_factorization`; Lemma 07ND is
`Algebra.isSmoothAt_bot_iff_isSeparableExtension`. Nothing in this file is assumed.

## References

* [Stacks Project, Tag 0BJ7](https://stacks.math.columbia.edu/tag/0BJ7)
* [Stacks Project, Tag 0BJ6](https://stacks.math.columbia.edu/tag/0BJ6)
* [Stacks Project, Tag 07C3](https://stacks.math.columbia.edu/tag/07C3)
* [Stacks Project, Tag 07ND](https://stacks.math.columbia.edu/tag/07ND)
-/

@[expose] public section

namespace Stacks.Smoothing

universe u v w

open CategoryTheory CategoryTheory.Limits

/-- Separability of a field extension passes to a subextension: if `L/k` is separable and `K`
embeds into `L` over `k`, then `K/k` is separable. -/
private lemma isSeparableExtension_of_algHom {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] (f : K →ₐ[k] L) [Algebra.IsSeparableExtension k L] :
    Algebra.IsSeparableExtension k K := by
  have : Algebra.IsGeometricallyReduced k L :=
    ((Algebra.isSeparableExtension_tfae k L (ringExpChar k)).out 1 4).mp
      (show Algebra.IsSeparableExtension k L from inferInstance)
  exact ((Algebra.isSeparableExtension_tfae k K (ringExpChar k)).out 4 1).mp
    (Algebra.IsGeometricallyReduced.of_injective f f.injective)

/-- A chain of affine Néron blowups from the stage `X` to the stage `Y` induces an `R`-algebra map
`X.A → Y.A` compatible with the two maps to `Λ`. -/
theorem NeronStage.exists_algHom_of_reflTransGen
    (S : NeronSituation.{u, v, w}) (X Y : NeronStage S)
    (h : Relation.ReflTransGen (IsAffineNeronBlowup S) X Y) :
    ∃ f : X.A →ₐ[S.R] Y.A, (algebraMap Y.A S.Λ).comp f = algebraMap X.A S.Λ := by
  induction h with
  | refl => exact ⟨AlgHom.id S.R X.A, RingHom.ext fun _ => rfl⟩
  | @tail b c _ hyz ih =>
      obtain ⟨f, hf⟩ := ih
      obtain ⟨π, _, φ, e, he₁, he₂⟩ := hyz
      let B := affineBlowupAlgebra b.maximalIdealPreimage
        (algebraMap S.R b.A π) (Localization.Away (algebraMap S.R b.A π))
      let g : b.A →ₐ[S.R] c.A :=
        { toRingHom := e.toRingEquiv.toRingHom.comp (algebraMap b.A B)
          commutes' := fun r => e.commutes r }
      have hg : (algebraMap c.A S.Λ).comp g = algebraMap b.A S.Λ := by
        ext y
        show algebraMap c.A S.Λ (e (algebraMap b.A B y)) = _
        rw [he₂]
        exact DFunLike.congr_fun he₁ y
      refine ⟨g.comp f, ?_⟩
      ext x
      exact (DFunLike.congr_fun hg (f x)).trans (DFunLike.congr_fun hf x)

/-- A subalgebra of a domain over a Bézout domain `R`, with `R → Λ` injective, is flat over `R`. -/
private theorem flat_subalgebra_of_injective {R Λ : Type*} [CommRing R] [IsDomain R] [IsBezout R]
    [CommRing Λ] [IsDomain Λ] [Algebra R Λ] (hinj : Function.Injective (algebraMap R Λ))
    (C : Subalgebra R Λ) : Module.Flat R C := by
  have hRC : Function.Injective (algebraMap R C) :=
    Function.Injective.of_comp (f := Subtype.val) hinj
  have : Module.IsTorsionFree R C := Module.IsTorsionFree.of_smul_eq_zero fun r x hx => by
    have hmul : algebraMap R C r * x = 0 := by simpa only [Algebra.smul_def] using hx
    exact (mul_eq_zero.mp hmul).imp_left fun hr => hRC (by simpa using hr)
  exact (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout (R := R) (M := C)).2 <|
    Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance

/-- A finite-type subalgebra `C` of `Λ`, with `R → Λ` injective and the fraction field of `Λ`
separable over that of `R`, is smooth over `R` at the generic prime `(0)`. -/
private theorem isSmoothAt_bot_subalgebra_of_isSeparableExtension {R Λ K L : Type*} [CommRing R]
    [IsDomain R] [CommRing Λ] [IsDomain Λ] [Algebra R Λ] [Field K] [Field L] [Algebra R K]
    [IsFractionRing R K] [Algebra Λ L] [IsFractionRing Λ L] [Algebra R L] [Algebra K L]
    [IsScalarTower R Λ L] [IsScalarTower R K L] [Algebra.IsSeparableExtension K L]
    (hinj : Function.Injective (algebraMap R Λ)) (C : Subalgebra R Λ) [Algebra.FiniteType R C] :
    Algebra.IsSmoothAt R (⊥ : Ideal C) := by
  have hRC : Function.Injective (algebraMap R C) :=
    Function.Injective.of_comp (f := Subtype.val) hinj
  let LC := FractionRing C
  let : Algebra C L := ((algebraMap Λ L).comp (algebraMap C Λ)).toAlgebra
  have hCL : Function.Injective (algebraMap C L) :=
    (IsFractionRing.injective Λ L).comp Subtype.val_injective
  let fCL : LC →+* L := IsFractionRing.lift (A := C) (K := LC) (L := L) hCL
  let : Algebra LC L := fCL.toAlgebra
  have hRLC : Function.Injective (algebraMap R LC) := (IsFractionRing.injective C LC).comp hRC
  let : Algebra K LC :=
    (IsFractionRing.lift (A := R) (K := K) (L := LC) hRLC).toAlgebra
  have hKLC (r : R) : algebraMap K LC (algebraMap R K r) = algebraMap R LC r :=
    IsFractionRing.lift_algebraMap (A := R) (K := K) (L := LC) hRLC r
  have : IsScalarTower R K LC := IsScalarTower.of_algebraMap_eq fun r => (hKLC r).symm
  have hcomp : (algebraMap LC L).comp (algebraMap K LC) = algebraMap K L := by
    refine IsFractionRing.ringHom_ext (A := R) fun r => ?_
    show fCL (algebraMap K LC (algebraMap R K r)) = _
    rw [hKLC r, IsScalarTower.algebraMap_apply R C LC r]
    show fCL (algebraMap C LC (algebraMap R C r)) = _
    rw [IsFractionRing.lift_algebraMap (A := C) (K := LC) (L := L) hCL (algebraMap R C r),
      ← IsScalarTower.algebraMap_apply R K L r]
    show (algebraMap Λ L) (algebraMap C Λ (algebraMap R C r)) = _
    rw [← IsScalarTower.algebraMap_apply R C Λ r, ← IsScalarTower.algebraMap_apply R Λ L r]
  let fFrac : LC →ₐ[K] L :=
    { toRingHom := fCL
      commutes' := fun x => RingHom.congr_fun hcomp x }
  have : Algebra.IsSeparableExtension K LC := isSeparableExtension_of_algHom fFrac
  exact (Algebra.isSmoothAt_bot_iff_isSeparableExtension R C K LC).2 inferInstance

section Factorization

variable {R : Type u} {Λ : Type v} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra R Λ]
  [IsLocalHom (algebraMap R Λ)]
  {K L : Type*} [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra Λ L]
  [IsFractionRing Λ L] [Algebra R L] [Algebra K L] [IsScalarTower R Λ L] [IsScalarTower R K L]

/-- **The key step of Stacks 0BJ7.** Let `R ⊂ Λ` be an extension of discrete valuation rings of
ramification index one inducing a separable extension of residue fields and a separable extension
of fraction fields. Then every `R`-algebra map `φ : A → Λ` with `A` of finite type over `R`
factors as `A → B → Λ` with `B` a smooth `R`-algebra. -/
theorem exists_smooth_factorization_of_ramificationIdx_one
    (hinj : Function.Injective (algebraMap R Λ))
    (hram : Stacks.DiscreteValuationRing.Ramification.ramificationIdx R Λ = 1)
    (hres : letI := Ideal.residueFieldAlgebra (IsLocalRing.maximalIdeal R)
                (IsLocalRing.maximalIdeal Λ)
      Algebra.IsSeparableExtension (IsLocalRing.maximalIdeal R).ResidueField
        (IsLocalRing.maximalIdeal Λ).ResidueField)
    [Algebra.IsSeparableExtension K L]
    (A : Type w) [CommRing A] [Algebra R A] [Algebra.FiniteType R A] (φ : A →ₐ[R] Λ) :
    ∃ (B : Type v) (_ : CommRing B) (_ : Algebra R B) (_ : Algebra.Smooth R B)
      (g : A →ₐ[R] B) (ψ : B →ₐ[R] Λ), ψ.comp g = φ := by
  -- Replace `A` by its image `C` in `Λ`, a flat finite-type `R`-algebra which is a domain.
  let C := φ.range
  let φC : A →ₐ[R] C := φ.rangeRestrict
  have : Algebra.FiniteType R C :=
    Algebra.FiniteType.of_surjective φC (AlgHom.rangeRestrict_surjective φ)
  have : IsPrincipalIdealRing R := IsDiscreteValuationRing.toIsPrincipalIdealRing
  have : Module.Flat R C := flat_subalgebra_of_injective hinj C
  let S : NeronSituation.{u, v, v} :=
    { R := R
      Λ := Λ
      A := C
      extension := ⟨hinj, inferInstance⟩
      ramificationIndex_one := hram }
  -- The fraction field of `C` sits between `K` and `L`, so it is separable over `K`.
  -- Hence `R → C` is smooth at the generic prime `(0)` (Lemma 07ND).
  have : Algebra.FinitePresentation R C := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.IsSmoothAt R (⊥ : Ideal C) :=
    isSmoothAt_bot_subalgebra_of_isSeparableExtension (K := K) (L := L) hinj C
  obtain ⟨a, ha, hasmooth⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R (⊥ : Ideal C)
  have hker : S.kernelIdeal = (⊥ : Ideal C) := eq_bot_iff.mpr fun x hx => Subtype.ext hx
  have : S.kernelIdeal.IsPrime := NeronSituation.isPrime_kernelIdeal S
  have hsm : Algebra.SmoothAt S.R S.A S.kernelIdeal := by
    have hsmBot : Algebra.SmoothAt R C (⊥ : Ideal C) := ⟨a, by simpa using ha, hasmooth⟩
    simpa only [hker] using hsmBot
  -- Finitely many affine Néron blowups make `R → C` smooth at `𝔭` (Lemma 0BJ6).
  obtain ⟨T, hchain, hTsm⟩ := exists_finite_affineNeronBlowup_smoothAt S hsm hres
  let : Algebra R T.A := T.algebraRA
  let : Algebra T.A Λ := T.algebraAΛ
  have : IsScalarTower R T.A Λ := T.tower
  obtain ⟨g₀, hg₀, hgsmooth⟩ := hTsm
  have hgunit : IsUnit (IsScalarTower.toAlgHom R T.A Λ g₀) := IsLocalRing.notMem_maximalIdeal.1 hg₀
  -- Localizing at an element outside `𝔭` gives the smooth algebra we want.
  let X := NeronStage.initial S
  let : Algebra R X.A := X.algebraRA
  let : Algebra X.A Λ := X.algebraAΛ
  have : IsScalarTower R X.A Λ := X.tower
  obtain ⟨v, hv⟩ := NeronStage.exists_algHom_of_reflTransGen S X T hchain
  let B := Localization.Away g₀
  let lift : B →ₐ[R] Λ := IsLocalization.Away.liftAlgHom g₀ hgunit
  refine ⟨B, inferInstance, inferInstance, hgsmooth,
    (IsScalarTower.toAlgHom R T.A B).comp (v.comp φC), lift, ?_⟩
  ext x
  exact (DFunLike.congr_fun (IsLocalization.Away.lift_comp g₀ hgunit) (v (φC x))).trans
    (DFunLike.congr_fun hv (φC x))

end Factorization

section IndSmooth

variable {R Λ : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra R Λ]
  [IsLocalHom (algebraMap R Λ)]
  {K L : Type*} [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra Λ L]
  [IsFractionRing Λ L] [Algebra R L] [Algebra K L] [IsScalarTower R Λ L] [IsScalarTower R K L]

/-- **Stacks 0BJ7 (Néron desingularization for discrete valuation rings).** Let `R ⊂ Λ` be an
extension of discrete valuation rings which has ramification index `1` and induces a separable
extension of residue fields and of fraction fields. Then `Λ` is a filtered colimit of smooth
`R`-algebras. -/
@[stacks 0BJ7 "\"`Λ` is a filtered colimit of smooth `R`-algebras\" is
`CategoryTheory.ObjectProperty.ind.{u}` of `UnderSmooth (CommRingCat.of R)` on the category
`Under (CommRingCat.of R)` of `R`-algebras, the same spelling as the left-hand side of the library's
Lemma 07C3. The residue fields are `Ideal.ResidueField` at the maximal ideals, as in the library's
Lemmas 0BJ4-0BJ6, and the fraction fields are abstract, pinned by `IsFractionRing`. See the module
docstring.", sga "7 I 0.5.1" "ind-smooth colimit", sga "7 I 0.5" "Lemma 0.5.1"]
theorem ind_underSmooth_of_ramificationIdx_one
    (hinj : Function.Injective (algebraMap R Λ))
    (hram : Stacks.DiscreteValuationRing.Ramification.ramificationIdx R Λ = 1)
    (hres : letI := Ideal.residueFieldAlgebra (IsLocalRing.maximalIdeal R)
                (IsLocalRing.maximalIdeal Λ)
      Algebra.IsSeparableExtension (IsLocalRing.maximalIdeal R).ResidueField
        (IsLocalRing.maximalIdeal Λ).ResidueField)
    [Algebra.IsSeparableExtension K L] :
    ObjectProperty.ind.{u} (UnderSmooth (CommRingCat.of R))
      (Under.mk (CommRingCat.ofHom (algebraMap R Λ))) := by
  have hE : (UnderSmooth (CommRingCat.of R) : ObjectProperty (Under (CommRingCat.of R))) ≤
      fun X : Under (CommRingCat.of R) => X.hom.hom.FinitePresentation := by
    intro X hX
    let : Algebra R X.right := X.hom.hom.toAlgebra
    change Algebra.Smooth R X.right at hX
    show Algebra.FinitePresentation R X.right
    exact hX.finitePresentation
  refine (CommRingCat.ind_under_iff_exists_factorization
    (Under.mk (CommRingCat.ofHom (algebraMap R Λ))) hE).2 ?_
  intro A hA f
  let : Algebra R A.right := A.hom.hom.toAlgebra
  let φ : A.right →ₐ[R] Λ :=
    { toRingHom := f.right.hom
      commutes' := fun r => congrArg (fun q => q.hom r) f.w }
  have : Algebra.FinitePresentation R A.right := hA
  obtain ⟨B, _, _, hBsm, g, ψ, hgψ⟩ :=
    exists_smooth_factorization_of_ramificationIdx_one (K := K) (L := L) hinj hram hres A.right φ
  let b : Under (CommRingCat.of R) := Under.mk (CommRingCat.ofHom (algebraMap R B))
  refine ⟨b, Under.homMk (CommRingCat.ofHom g.toRingHom) (by ext r; exact g.commutes r),
    Under.homMk (CommRingCat.ofHom ψ.toRingHom) (by ext r; exact ψ.commutes r), ?_, ?_⟩
  · ext x
    exact DFunLike.congr_fun hgψ x
  · dsimp [UnderSmooth, b]
    have halg : (inferInstance : Algebra R B) = (CommRingCat.Hom.hom b.hom).toAlgebra :=
      Algebra.algebra_ext _ _ fun _ => rfl
    rw [← halg]
    exact hBsm

end IndSmooth

end Stacks.Smoothing

end
