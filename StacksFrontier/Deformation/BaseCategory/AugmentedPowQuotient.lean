module

public import Mathlib.RingTheory.SimpleModule.Basic
public import StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting
public import StacksFrontier.Deformation.TangentSpace.Functor
public import StacksFrontier.RingTheory.Ideal.RadicalMaximalQuotient
import StacksCore.Tactic.StacksAttribute

/-!
# The objects `A ⧸ 𝔭 ^ n` of `𝒞_Λ` and the small extensions between them

Let `Λ → R` be a Noetherian `Λ`-algebra together with a surjective augmentation
`ε : R →ₐ[Λ] k` onto a field `k`. Its kernel `𝔭 = Ker ε` is a maximal ideal, so for `n ≠ 0`
the ring `R ⧸ 𝔭 ^ n` is Artinian and local with residue field `k`: it is an object of the
base category `𝒞_Λ` of [Stacks, Tag 06GC]. A surjection `φ : R' ↠ R` of such augmented
algebras induces a morphism `R' ⧸ (𝔭') ^ n ⟶ R ⧸ 𝔭 ^ n` of `𝒞_Λ`, whose kernel is the image
of `Ker φ`.

This is the construction [Stacks, Tag 07YM] performs at a closed point `u₀` of `U = Spec A`
in order to apply the criterion of [Stacks, Tag 06H0]. There `A' ⟶ A` is the square-zero
extension of [Stacks, Tag 07YL], `I = Ker(A' → A)` is a one-dimensional `k`-vector space, and
`𝔭' = Ker(A' → k)` annihilates `I`; the Artin–Rees step
`Deformation.Artin.exists_pow_inf_eq_bot_of_mul_eq_bot` produces `n > 1` with
`(𝔭') ^ n ⊓ I = 0`, and that is exactly what makes `A' ⧸ (𝔭') ^ n ⟶ A ⧸ 𝔭 ^ n` a *small*
extension: its kernel is the image of `I`, which `(𝔭') ^ n ⊓ I = 0` identifies with `I`
itself, a module of length one.

## Main definitions

* `Deformation.ArtinianLocalAlgCat.powQuotientAug`: the augmentation `R ⧸ 𝔭 ^ n →ₐ[Λ] k`
  induced by `ε`.
* `Deformation.ArtinianLocalAlgCat.powQuotientObj`: the object `R ⧸ 𝔭 ^ n` of `𝒞_Λ`.
* `Deformation.ArtinianLocalAlgCat.powQuotientMapAlgHom` and
  `Deformation.ArtinianLocalAlgCat.powQuotientMap`: the induced map of quotients, as an
  algebra homomorphism and as a morphism of `𝒞_Λ`.

## Main results

* `Ideal.isSimpleModule_map_mk_of_inf_eq_bot`: for ideals with `J ⊓ I = ⊥`, the image of `I`
  in `R ⧸ J` is a simple `R ⧸ J`-module as soon as `I` is a simple `R`-module.
* `Deformation.ArtinianLocalAlgCat.ker_powQuotientMapAlgHom`: the kernel of the induced map is
  the image of `Ker φ`.
* `Deformation.ArtinianLocalAlgCat.isSmallExtension_powQuotientMap`: the induced map is a
  small extension in the sense of `InfinitesimalLifting.IsSmallExtension`, given
  `(𝔭') ^ n ⊓ Ker φ = ⊥` and `Ker φ` of length one.

## Implementation notes

The augmentation, not a separately chosen prime, is the datum carried around: `𝔭` is defined
as `RingHom.ker ε.toRingHom` throughout, which makes its maximality automatic and makes the
residue-field identification of `Deformation.residueEquivOfAugmentation` available with no
further input. Compatibility of two augmentations with a map between the algebras is the
single hypothesis `ε.comp φ = ε'`; it supplies both the morphism of quotients and, through
`IsLocalRing.isLocalHom_of_comp_augmentation`, the locality that `𝒞_Λ` demands of it.

Noetherianity of *both* algebras is asked for, because each of the two objects of `𝒞_Λ` needs
it to be Artinian; when `φ` is surjective the second follows from the first, but the two
objects are formed before `φ` is in sight.

The three universes of `Deformation.ArtinianLocalAlgCat` stay independent throughout: the
algebras live in the carrier universe, which `InfinitesimalLifting.IsSmallExtension` fixes as
that of its `CommRingCat` but which is tied neither to `Λ` nor to `k`. The `example` closing
the file records that the small extension does land in the shape — all three universes equal
— that the consumers of [Stacks, Tag 06H0] are written at.

## References

* [Stacks Project, Tag 06GC](https://stacks.math.columbia.edu/tag/06GC)
* [Stacks Project, Tag 06H0](https://stacks.math.columbia.edu/tag/06H0)
* [Stacks Project, Tag 07YL](https://stacks.math.columbia.edu/tag/07YL)
* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
-/

@[expose] public section

/-! ### A simple ideal stays simple in a quotient meeting it trivially -/

/-- Let `J` and `I` be ideals of `R` meeting in `0`. Then the image of `I` in `R ⧸ J` is a
simple `R ⧸ J`-module as soon as `I` is a simple `R`-module: the quotient map restricts to a
bijection of `I` onto that image, semilinear over the surjection `R → R ⧸ J`, and simplicity
transports along such a bijection. -/
public theorem Ideal.isSimpleModule_map_mk_of_inf_eq_bot {R : Type*} [CommRing R]
    {J I : Ideal R} (hJI : J ⊓ I = ⊥) [IsSimpleModule R I] :
    IsSimpleModule (R ⧸ J) (I.map (Ideal.Quotient.mk J)) := by
  have : RingHomSurjective (Ideal.Quotient.mk J) := ⟨Ideal.Quotient.mk_surjective⟩
  let l : I →ₛₗ[Ideal.Quotient.mk J] (I.map (Ideal.Quotient.mk J)) :=
    { toFun := fun x => ⟨Ideal.Quotient.mk J x.1, Ideal.mem_map_of_mem _ x.2⟩
      map_add' := fun x y => Subtype.ext (map_add (Ideal.Quotient.mk J) x.1 y.1)
      map_smul' := fun r x => Subtype.ext (map_mul (Ideal.Quotient.mk J) r x.1) }
  refine (l.isSimpleModule_iff_of_bijective ⟨?_, ?_⟩).mp ‹_›
  · intro x y hxy
    have hmem : x.1 - y.1 ∈ J ⊓ I :=
      ⟨Ideal.Quotient.eq.mp (congrArg Subtype.val hxy), I.sub_mem x.2 y.2⟩
    rw [hJI, Submodule.mem_bot, sub_eq_zero] at hmem
    exact Subtype.ext hmem
  · intro y
    obtain ⟨a, ha, hay⟩ := Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective y.2
    exact ⟨⟨a, ha⟩, Subtype.ext hay⟩

namespace Deformation

namespace ArtinianLocalAlgCat

section

open CategoryTheory IsLocalRing

universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-! ### The object `R ⧸ 𝔭 ^ n` -/

section Object

variable {R : Type v} [CommRing R] [Algebra Λ R]

/-- The kernel of a surjective augmentation onto a field is a maximal ideal. -/
public theorem isMaximal_ker_augmentation (ε : R →ₐ[Λ] k) (hε : Function.Surjective ε) :
    (RingHom.ker ε.toRingHom).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective ε.toRingHom hε

/-- The augmentation `R ⧸ 𝔭 ^ n →ₐ[Λ] k` induced by `ε`, for `𝔭 = Ker ε` and `n ≠ 0`. -/
public def powQuotientAug (ε : R →ₐ[Λ] k) (n : ℕ) [NeZero n] :
    (R ⧸ RingHom.ker ε.toRingHom ^ n) →ₐ[Λ] k :=
  Ideal.Quotient.liftₐ _ ε fun _ ha =>
    RingHom.mem_ker.mp (Ideal.pow_le_self (NeZero.ne n) ha)

/-- The induced augmentation is `ε` on representatives. -/
@[simp] public theorem powQuotientAug_mk (ε : R →ₐ[Λ] k) (n : ℕ) [NeZero n] (a : R) :
    powQuotientAug ε n (Ideal.Quotient.mk (RingHom.ker ε.toRingHom ^ n) a) = ε a := rfl

/-- The induced augmentation is surjective. -/
public theorem powQuotientAug_surjective (ε : R →ₐ[Λ] k) (hε : Function.Surjective ε)
    (n : ℕ) [NeZero n] : Function.Surjective (powQuotientAug ε n) :=
  Function.Surjective.of_comp (g := Ideal.Quotient.mk _) hε

/-- The object `R ⧸ 𝔭 ^ n` of `𝒞_Λ`, for `𝔭 = Ker ε` the augmentation ideal of a surjective
augmentation of a Noetherian `Λ`-algebra and `n ≠ 0`. The algebra `R` itself is not asked to
be local or Artinian. -/
@[stacks 07YM "the object `A/𝔭 ^ n` of `𝒞_Λ` at a closed point", ega "0 19.5.6.2" "special case"]
public noncomputable def powQuotientObj [IsNoetherianRing R] (ε : R →ₐ[Λ] k)
    (hε : Function.Surjective ε) (n : ℕ) [NeZero n] : ArtinianLocalAlgCat.{u, v, w} Λ k :=
  haveI := isMaximal_ker_augmentation ε hε
  { carrier := R ⧸ RingHom.ker ε.toRingHom ^ n
    residueEquiv :=
      residueEquivOfAugmentation (powQuotientAug ε n) (powQuotientAug_surjective ε hε n) }

/-- The underlying ring of `powQuotientObj` is the quotient it is built from. -/
public theorem powQuotientObj_carrier [IsNoetherianRing R] (ε : R →ₐ[Λ] k)
    (hε : Function.Surjective ε) (n : ℕ) [NeZero n] :
    (powQuotientObj ε hε n).carrier = (R ⧸ RingHom.ker ε.toRingHom ^ n) := rfl

/-- The residue-field identification of `powQuotientObj` is the induced augmentation. -/
@[simp] public theorem powQuotientObj_residueEquiv_residue [IsNoetherianRing R]
    (ε : R →ₐ[Λ] k) (hε : Function.Surjective ε) (n : ℕ) [NeZero n]
    (x : R ⧸ RingHom.ker ε.toRingHom ^ n) :
    haveI := isMaximal_ker_augmentation ε hε
    (powQuotientObj ε hε n).residueEquiv (residue _ x) = powQuotientAug ε n x := rfl

/-- The `n`-th power of the maximal ideal of `R ⧸ 𝔭 ^ n` vanishes. This is the hypothesis
`𝔪_{B'} ^ n = 0` of
`Deformation.ArtinianLocalAlgCat.not_isEssentialSurjection_of_lift_powQuotient`, read at the
object `Deformation.ArtinianLocalAlgCat.powQuotientObj` of `𝒞_Λ` rather than at the bare
quotient ring; it is `IsLocalRing.maximalIdeal_quotient_pow_pow_eq_bot`, the augmentation
ideal being maximal. -/
@[stacks 07YM "the maximal ideal of the object `A'/(𝔭') ^ n` of `𝒞_Λ` has vanishing power"]
public theorem maximalIdeal_pow_powQuotientObj_eq_bot [IsNoetherianRing R] (ε : R →ₐ[Λ] k)
    (hε : Function.Surjective ε) (n : ℕ) [NeZero n] :
    maximalIdeal (powQuotientObj ε hε n : Type v) ^ n = ⊥ :=
  have := isMaximal_ker_augmentation ε hε
  IsLocalRing.maximalIdeal_quotient_pow_pow_eq_bot (RingHom.ker ε.toRingHom) n

end Object

/-! ### The morphism of quotients -/

section Map

variable {R' R : Type v} [CommRing R'] [CommRing R] [Algebra Λ R'] [Algebra Λ R]

/-- A compatible pair of augmentations identifies the augmentation ideal of `R'` with the
preimage of that of `R`. -/
public theorem ker_augmentation_comap {ε' : R' →ₐ[Λ] k} {ε : R →ₐ[Λ] k} {φ : R' →ₐ[Λ] R}
    (hφ : ε.comp φ = ε') :
    RingHom.ker ε'.toRingHom = (RingHom.ker ε.toRingHom).comap φ.toRingHom := by
  rw [RingHom.comap_ker]
  exact congrArg RingHom.ker (congrArg AlgHom.toRingHom hφ).symm

/-- A compatible pair of augmentations carries the augmentation ideal of `R'` into that of
`R`. -/
public theorem map_ker_augmentation_le {ε' : R' →ₐ[Λ] k} {ε : R →ₐ[Λ] k} {φ : R' →ₐ[Λ] R}
    (hφ : ε.comp φ = ε') :
    (RingHom.ker ε'.toRingHom).map φ.toRingHom ≤ RingHom.ker ε.toRingHom := by
  rw [ker_augmentation_comap hφ]
  exact Ideal.map_comap_le

/-- The algebra homomorphism `R' ⧸ (𝔭') ^ n →ₐ[Λ] R ⧸ 𝔭 ^ n` induced by a map of augmented
algebras. -/
public def powQuotientMapAlgHom {ε' : R' →ₐ[Λ] k} {ε : R →ₐ[Λ] k} {φ : R' →ₐ[Λ] R}
    (hφ : ε.comp φ = ε') (n : ℕ) :
    (R' ⧸ RingHom.ker ε'.toRingHom ^ n) →ₐ[Λ] (R ⧸ RingHom.ker ε.toRingHom ^ n) :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ Λ (RingHom.ker ε.toRingHom ^ n)).comp φ)
    fun _ ha => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_comap.mp
      (Ideal.pow_le_comap_pow_of_map_le φ.toRingHom (map_ker_augmentation_le hφ) n ha))

/-- The induced map sends the class of `a` to the class of `φ a`. -/
@[simp] public theorem powQuotientMapAlgHom_mk {ε' : R' →ₐ[Λ] k} {ε : R →ₐ[Λ] k}
    {φ : R' →ₐ[Λ] R} (hφ : ε.comp φ = ε') (n : ℕ) (a : R') :
    powQuotientMapAlgHom hφ n (Ideal.Quotient.mk (RingHom.ker ε'.toRingHom ^ n) a) =
      Ideal.Quotient.mk (RingHom.ker ε.toRingHom ^ n) (φ a) := rfl

/-- The induced map respects the induced augmentations. -/
@[simp] public theorem powQuotientAug_powQuotientMapAlgHom {ε' : R' →ₐ[Λ] k} {ε : R →ₐ[Λ] k}
    {φ : R' →ₐ[Λ] R} (hφ : ε.comp φ = ε') (n : ℕ) [NeZero n]
    (x : R' ⧸ RingHom.ker ε'.toRingHom ^ n) :
    powQuotientAug ε n (powQuotientMapAlgHom hφ n x) = powQuotientAug ε' n x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun hφ a

/-- The induced map is surjective when `φ` is. -/
public theorem powQuotientMapAlgHom_surjective {ε' : R' →ₐ[Λ] k} {ε : R →ₐ[Λ] k}
    {φ : R' →ₐ[Λ] R} (hφ : ε.comp φ = ε') (n : ℕ) (hsurj : Function.Surjective φ) :
    Function.Surjective (powQuotientMapAlgHom hφ n) :=
  Function.Surjective.of_comp (g := Ideal.Quotient.mk _)
    (Ideal.Quotient.mk_surjective.comp hsurj)

/-- **The kernel computation of [Stacks, Tag 07YM].** For `φ : R' ↠ R` surjective, the kernel
of `R' ⧸ (𝔭') ^ n ⟶ R ⧸ 𝔭 ^ n` is the image of `Ker φ`.

The preimage of `𝔭 ^ n` under `φ` is `(𝔭') ^ n + Ker φ`, because `𝔭 ^ n` is the image of
`(𝔭') ^ n`; passing to `R' ⧸ (𝔭') ^ n` kills the first summand. -/
@[stacks 07YM "the kernel of `A'/(𝔭') ^ n ⟶ A/𝔭 ^ n` is the image of `I = Ker(A' → A)`"]
public theorem ker_powQuotientMapAlgHom {ε' : R' →ₐ[Λ] k} {ε : R →ₐ[Λ] k} {φ : R' →ₐ[Λ] R}
    (hφ : ε.comp φ = ε') (n : ℕ) (hsurj : Function.Surjective φ) :
    RingHom.ker (powQuotientMapAlgHom hφ n).toRingHom =
      (RingHom.ker φ.toRingHom).map
        (Ideal.Quotient.mk (RingHom.ker ε'.toRingHom ^ n)) := by
  have hmap : (RingHom.ker ε'.toRingHom).map φ.toRingHom = RingHom.ker ε.toRingHom := by
    rw [ker_augmentation_comap hφ, Ideal.map_comap_of_surjective φ.toRingHom hsurj]
  have hker : RingHom.ker
      ((Ideal.Quotient.mk (RingHom.ker ε.toRingHom ^ n)).comp φ.toRingHom) =
      RingHom.ker ε'.toRingHom ^ n ⊔ RingHom.ker φ.toRingHom := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, ← hmap, ← Ideal.map_pow,
      Ideal.comap_map_of_surjective φ.toRingHom hsurj, ← RingHom.ker_eq_comap_bot]
  have hle : RingHom.ker ε'.toRingHom ^ n ≤
      RingHom.ker ((Ideal.Quotient.mk (RingHom.ker ε.toRingHom ^ n)).comp φ.toRingHom) :=
    le_sup_left.trans_eq hker.symm
  have h := Ideal.ker_quotient_lift
    ((Ideal.Quotient.mk (RingHom.ker ε.toRingHom ^ n)).comp φ.toRingHom) hle
  rwa [hker, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq] at h

/-- The morphism `R' ⧸ (𝔭') ^ n ⟶ R ⧸ 𝔭 ^ n` of `𝒞_Λ` induced by a map of augmented
Noetherian algebras. -/
@[stacks 07YM "the morphism `A'/(𝔭') ^ n ⟶ A/𝔭 ^ n` of `𝒞_Λ`"]
public noncomputable def powQuotientMap [IsNoetherianRing R'] [IsNoetherianRing R]
    {ε' : R' →ₐ[Λ] k} {ε : R →ₐ[Λ] k} {φ : R' →ₐ[Λ] R} (hφ : ε.comp φ = ε')
    (hε' : Function.Surjective ε') (hε : Function.Surjective ε) (n : ℕ) [NeZero n] :
    powQuotientObj ε' hε' n ⟶ powQuotientObj ε hε n :=
  haveI := isMaximal_ker_augmentation ε' hε'
  haveI := isMaximal_ker_augmentation ε hε
  { hom := powQuotientMapAlgHom hφ n
    isLocal := IsLocalRing.isLocalHom_of_comp_augmentation
      (powQuotientAug ε' n).toRingHom (powQuotientAug_surjective ε' hε' n)
      (powQuotientAug ε n).toRingHom (powQuotientAug_surjective ε hε n) _
      (RingHom.ext (powQuotientAug_powQuotientMapAlgHom hφ n))
    residue_comm := fun a => powQuotientAug_powQuotientMapAlgHom hφ n a }

/-- The algebra homomorphism underlying `powQuotientMap`. -/
@[simp] public theorem powQuotientMap_hom [IsNoetherianRing R'] [IsNoetherianRing R]
    {ε' : R' →ₐ[Λ] k} {ε : R →ₐ[Λ] k} {φ : R' →ₐ[Λ] R} (hφ : ε.comp φ = ε')
    (hε' : Function.Surjective ε') (hε : Function.Surjective ε) (n : ℕ) [NeZero n] :
    (powQuotientMap hφ hε' hε n).hom = powQuotientMapAlgHom hφ n := rfl

end Map

/-! ### Smallness -/

section Small

variable {R' R : Type v} [CommRing R'] [CommRing R] [Algebra Λ R'] [Algebra Λ R]

/-- **The small extension of [Stacks, Tag 07YM].** Let `φ : R' ↠ R` be a surjection of
augmented Noetherian `Λ`-algebras whose kernel `I` has length one over `R'`, and suppose
`(𝔭') ^ n ⊓ I = 0`. Then `R' ⧸ (𝔭') ^ n ⟶ R ⧸ 𝔭 ^ n` is a small extension of Artinian local
rings.

The kernel is the image of `I` by `ker_powQuotientMapAlgHom`, and `(𝔭') ^ n ⊓ I = 0` makes
that image a copy of `I`, hence again of length one. In the source `I` is a one-dimensional
`k`-vector space and the hypothesis `(𝔭') ^ n ⊓ I = 0` is the conclusion of the Artin–Rees
step `Deformation.Artin.exists_pow_inf_eq_bot_of_mul_eq_bot`. -/
@[stacks 07YM "`A'/(𝔭') ^ n ⟶ A/𝔭 ^ n` is a small extension"]
public theorem isSmallExtension_powQuotientMap [IsNoetherianRing R'] [IsNoetherianRing R]
    {ε' : R' →ₐ[Λ] k} {ε : R →ₐ[Λ] k} {φ : R' →ₐ[Λ] R} (hφ : ε.comp φ = ε')
    (hε' : Function.Surjective ε') (hε : Function.Surjective ε)
    (hsurj : Function.Surjective φ) (n : ℕ) [NeZero n]
    (hinf : RingHom.ker ε'.toRingHom ^ n ⊓ RingHom.ker φ.toRingHom = ⊥)
    (hlen : Module.length R' (RingHom.ker φ.toRingHom) = 1) :
    InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom (powQuotientMap hφ hε' hε n).hom.toRingHom) := by
  have := isMaximal_ker_augmentation ε' hε'
  have := isMaximal_ker_augmentation ε hε
  have : IsSimpleModule R' (RingHom.ker φ.toRingHom) := Module.length_eq_one_iff.mp hlen
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    powQuotientMapAlgHom_surjective hφ n hsurj, ?_⟩
  have hsimple : IsSimpleModule (R' ⧸ RingHom.ker ε'.toRingHom ^ n)
      ((RingHom.ker φ.toRingHom).map (Ideal.Quotient.mk (RingHom.ker ε'.toRingHom ^ n))) :=
    Ideal.isSimpleModule_map_mk_of_inf_eq_bot hinf
  rw [← ker_powQuotientMapAlgHom hφ n hsurj] at hsimple
  exact Module.length_eq_one_iff.mpr hsimple

/-- A sanity check that the small extension lands in the shape the consumers of
[Stacks, Tag 06H0] use: all three universes equal. -/
example {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {R' R : Type u} [CommRing R']
    [CommRing R] [Algebra Λ R'] [Algebra Λ R] [IsNoetherianRing R'] [IsNoetherianRing R]
    {ε' : R' →ₐ[Λ] k} {ε : R →ₐ[Λ] k} {φ : R' →ₐ[Λ] R} (hφ : ε.comp φ = ε')
    (hε' : Function.Surjective ε') (hε : Function.Surjective ε)
    (hsurj : Function.Surjective φ) (n : ℕ) [NeZero n]
    (hinf : RingHom.ker ε'.toRingHom ^ n ⊓ RingHom.ker φ.toRingHom = ⊥)
    (hlen : Module.length R' (RingHom.ker φ.toRingHom) = 1) :
    ∃ (A B : ArtinianLocalAlgCat.{u, u, u} Λ k) (f : B ⟶ A),
      InfinitesimalLifting.IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom) :=
  ⟨powQuotientObj ε hε n, powQuotientObj ε' hε' n, powQuotientMap hφ hε' hε n,
    isSmallExtension_powQuotientMap hφ hε' hε hsurj n hinf hlen⟩

end Small

end

end ArtinianLocalAlgCat

end Deformation

end
