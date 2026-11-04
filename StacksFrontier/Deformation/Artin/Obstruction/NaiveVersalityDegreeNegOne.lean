module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersality
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityPowQuotientEssential
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalitySquareLift
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityThickeningSite
public import StacksFrontier.Deformation.BaseCategory.AugmentedPowQuotientSection
public import StacksFrontier.RingTheory.NaiveCotangent.DerivedSquareZeroExtension

/-!
# Stacks 07YM, the direction `(1) ⇒ (2)` in degree `-1`

Let `x` be a family over `Spec A` whose deformation theory is controlled by
`ξ : E ⟶ NL_{A/Λ}` in the sense of hypothesis (i) of [Stacks, Tag 07YM] — lifts of `x` across a
deformation situation `A' → A` exist exactly when `ξ` composed with `NL_{A/Λ} ⟶ NL_{A/A'}`
vanishes — and let `u₀` be a *closed* point of `Spec A` with residue field `κ`. This file proves
that versality of `x` at `u₀` forces condition (2) in degree `-1`: the map
`H^{-1}(E ⊗ᴸ_A κ) ⟶ H^{-1}(NL_{A/Λ} ⊗ᴸ_A κ)` is surjective.

The argument is the source's, by contradiction, and every one of its steps is already proved:

* were the map not surjective, [Stacks, Tag 07YL] would produce a square-zero extension
  `A' → A` of `Λ`-algebras whose kernel `I` is a copy of `κ`, which does not change
  differentials modulo `κ`, and which kills `ξ`
  (`Deformation.Artin.exists_squareZeroExtension_killing_cotangent_morphism`);
* `Deformation.Artin.squareZeroThickeningOfMkLe` presents it as a deformation situation in the
  site, so hypothesis (i) supplies a lift `x'` of `x` to `Spec A'`;
* `Deformation.Artin.exists_pow_inf_eq_bot_of_mul_eq_bot` produces `n > 1` with
  `(𝔭') ^ n ⊓ I = 0`, which makes `A' ⧸ (𝔭') ^ n ⟶ A ⧸ 𝔭 ^ n` a *small* extension of `𝒞_Λ`
  (`Deformation.ArtinianLocalAlgCat.isSmallExtension_powQuotientMap`) and an *essential* one
  (`Deformation.ArtinianLocalAlgCat.isEssentialSurjection_powQuotientMap_of_bijective`);
* versality, read over the affine open at the residue field of the prime
  (`Deformation.Artin.liftsAtResiduePoint_prime_base_of_isVersalAt`) and applied to the arrow
  joining the two restrictions, lifts `A` through that small extension
  (`Deformation.Artin.exists_algHom_powQuotient_of_liftsAtResiduePoint`);
* a lift gives a section, so the extension is *not* essential
  (`Deformation.ArtinianLocalAlgCat.not_isEssentialSurjection_of_lift_powQuotient`).

## Main results

* `Deformation.Artin.surjective_derivedTensorFibre_neg_one_of_isVersalAt` — **the direction
  `(1) ⇒ (2)` of [Stacks, Tag 07YM] in degree `-1`**: versality at a closed point `u₀` implies
  that `H^{-1}(ξ ⊗ᴸ_A κ(u₀))` is surjective.

## Implementation notes

Closedness of `u₀` enters twice and only through
`StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint`: the prime is maximal, which is what
makes the kernel of `A' → A` a module of length one, and the residue field is of finite type
over `A`, which is the finiteness hypothesis [Stacks, Tag 07YL] is proved under. This is the
source's remark that the step "fails if `u₀` is not closed".

The `Λ`-algebra structure of `κ` and the compatibilities of the tower `Λ → A' → A → κ` are not
hypotheses and are not introduced by hand: they are the ones instance synthesis already produces
for the residue field at a prime, which is also what [Stacks, Tag 07YL] states its bijectivity
with, so no transport of algebra structures happens here — that is done once, inside
`Deformation.ArtinianLocalAlgCat.isEssentialSurjection_powQuotientMap_of_bijective`.

Hypothesis (i) is taken in the single direction the argument uses, "`ξ` is killed, hence a lift
exists"; the tag states it as an equivalence, and nothing here needs the converse.

`Mono baseMap` is used, exactly as in the degree `0` half
`Deformation.Artin.injective_derivedTensorFibre_zero_of_isVersalAt`, and in exactly one place:
the `Λ`-algebra homomorphism `σ` is read off a morphism of schemes over `S` by
`Deformation.Artin.algHom_of_schemeMap_over`, which needs "over `S`" to imply "over `Spec Λ`".
See the implementation notes of
`StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalitySquareLift` for why that step cannot be
avoided. Nothing stronger is used: `baseMap` is *not* assumed to be an open immersion, which is
how [Stacks, Tag 07YM] presents the affine open, and the change of deformation base
(`Deformation.Artin.liftsAtResiduePoint_changeBase`) asks nothing of it at all.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
* [Stacks Project, Tag 07YL](https://stacks.math.columbia.edu/tag/07YL)
* [Stacks Project, Tag 07YX](https://stacks.math.columbia.edu/tag/07YX)
* [Stacks Project, Tag 06H0](https://stacks.math.columbia.edu/tag/06H0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

open Deformation.ArtinianLocalAlgCat

attribute [local instance] HasDerivedCategory.standard

universe u v w

section VersalDegreeNegOne

variable (Λ A : Type u) [CommRing Λ] [CommRing A] [Algebra Λ A]
  [IsNoetherianRing Λ] [IsNoetherianRing A] [Algebra.FiniteType Λ A]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (CommRingCat.of A) ⟶ S) (hA : B.Contains (Spec (CommRingCat.of A)))
  (baseMap : Spec (CommRingCat.of Λ) ⟶ S) [Mono baseMap]
  (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)
variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)
  (hp : p.IsFiberedInGroupoids)
variable (E : DerivedCategory (ModuleCat.{u} A))
  (hE : (DerivedCategory.TStructure.t (C := ModuleCat.{u} A)).minus E)
  (ξ : E ⟶ derivedNaiveCotangentComplex Λ A)
variable (u₀ : Spec (CommRingCat.of A)) (T : DerivedTensorProduct A)

include hbase hp hE in
/-- **Stacks 07YM, `(1) ⇒ (2)` in degree `-1`.** Let `x` be a family over `Spec A` whose
deformation theory is controlled by `ξ : E ⟶ NL_{A/Λ}` as in hypothesis (i) of the tag: `x` lifts
across a deformation situation `A' → A` whenever `ξ` composed with `NL_{A/Λ} ⟶ NL_{A/A'}`
vanishes. If `x` is versal at a *closed* point `u₀` of `Spec A`, then the map
`H^{-1}(E ⊗ᴸ_A κ(u₀)) ⟶ H^{-1}(NL_{A/Λ} ⊗ᴸ_A κ(u₀))` on the derived fibre at `u₀` is surjective.

Were it not, [Stacks, Tag 07YL] would supply a square-zero extension `A' → A` killing `ξ` and
not changing differentials modulo `κ(u₀)`, hypothesis (i) would lift `x` to `Spec A'`, and the
Artin–Rees step would turn the extension into a *small* extension
`A' ⧸ (𝔭') ^ n ⟶ A ⧸ 𝔭 ^ n` of `𝒞_Λ` which [Stacks, Tag 06H0] makes an essential surjection.
Versality applied to the arrow joining the restrictions of `x` and of its lift to the two
Artinian quotients then lifts `A` through that extension, hence splits it — contradicting
essential surjectivity. -/
@[stacks 07YM "(1) implies (2), degree -1"]
public theorem surjective_derivedTensorFibre_neg_one_of_isVersalAt
    (hclosed : IsClosed ({u₀} : Set (Spec (CommRingCat.of A))))
    (hLifts : ∀ (A' : Type u) [CommRing A'] [Algebra Λ A'] [Algebra A' A]
      [IsScalarTower Λ A' A] (D : SquareZeroThickening A B S hS toS hA A'),
      D.q = algebraMap A' A →
      Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ baseMap = B.inclusion.map D.toS' →
      ξ ≫ naiveCotangentBaseMap Λ A' A = 0 →
      Nonempty ((Under.post p).Fiber (Under.mk (eqToHom hx ≫ D.arrow))))
    (hversal : IsVersalAt (Over.mk toS) (p ⋙ Over.post B.inclusion) u₀ x
      (by change (Over.post B.inclusion).obj (p.obj x) = _; rw [hx]; rfl)) :
    Function.Surjective
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-1)).map
        ((T.tensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A u₀.asIdeal.ResidueField))).map ξ)) := by
  have hxS : (p ⋙ Over.post B.inclusion).obj x = Over.mk toS :=
    (congrArg (Over.post B.inclusion).obj hx).trans rfl
  have : u₀.asIdeal.IsMaximal :=
    AlgebraicGeometry.isMaximal_asIdeal_of_isClosed_singleton hclosed
  have : Algebra.FiniteType A u₀.asIdeal.ResidueField := u₀.asIdeal.finiteType_residueField
  by_contra hξ
  -- Stacks 07YL: the square-zero extension that kills `ξ`
  obtain ⟨A', _, _, _, _, hsurj, hsq, _, hcomp, ⟨eI⟩, hbij, hkill⟩ :=
    exists_squareZeroExtension_killing_cotangent_morphism Λ A u₀.asIdeal T E hE ξ hξ
  have : Module.Finite A (RingHom.ker (algebraMap A' A)) :=
    module_finite_ker_of_linearEquiv_residueField u₀.asIdeal eI
  have : IsNoetherianRing A' :=
    isNoetherianRing_of_squareZero_module_finite_ker hsurj hsq hcomp
  have hmkker := mk_ker_le_max_of_linearEquiv_residueField u₀.asIdeal eI
  -- the deformation situation, and the lift hypothesis (i) supplies
  let D := squareZeroThickeningOfMkLe Λ A B S hS toS hA baseMap hbase A' hsurj hsq hmkker
  obtain ⟨wlift⟩ := hLifts A' D rfl rfl hkill
  have hA' : B.Contains (Spec (CommRingCat.of A')) := D.hA'
  have hx' : p.obj wlift.1.right = algebraOver A' B S hS
      (Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ baseMap) hA' :=
    lift_obj B S hS p hx D.arrow wlift
  have hx'S : (p ⋙ Over.post B.inclusion).obj wlift.1.right =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ baseMap) :=
    (congrArg (Over.post B.inclusion).obj hx').trans rfl
  have hlift : schemeMap (p ⋙ Over.post B.inclusion) hxS hx'S wlift.1.hom =
      Spec.map (CommRingCat.ofHom (algebraMap A' A)) := by
    rw [schemeMap_lift_hom B S hS p hx D.arrow wlift hxS hx'S rfl rfl]
    show 𝟙 ((BigFppfOver.toScheme B S hS).obj (algebraOver A B S hS toS hA)) ≫
        (BigFppfOver.toScheme B S hS).map D.arrow ≫
        𝟙 ((BigFppfOver.toScheme B S hS).obj (Over.mk D.toS' : BigFppfOver B S hS)) =
      Spec.map (CommRingCat.ofHom (algebraMap A' A))
    rw [Category.id_comp, Category.comp_id]
    exact D.arrow_spec
  -- the three augmentations of the tower `Λ → A' → A → κ`
  let ε := IsScalarTower.toAlgHom Λ A u₀.asIdeal.ResidueField
  let ε' := IsScalarTower.toAlgHom Λ A' u₀.asIdeal.ResidueField
  let φ := IsScalarTower.toAlgHom Λ A' A
  have hε : Function.Surjective ε := u₀.asIdeal.algebraMap_residueField_surjective
  have hsurjφ : Function.Surjective φ := hsurj
  have hφ : ε.comp φ = ε' :=
    AlgHom.ext fun t' => (IsScalarTower.algebraMap_apply A' A u₀.asIdeal.ResidueField t').symm
  have hε' : Function.Surjective ε' := by
    rw [← hφ]
    exact hε.comp hsurjφ
  -- the Artin–Rees step
  have hker : ∀ t' ∈ RingHom.ker ε'.toRingHom,
      algebraMap A' A t' ∈ RingHom.ker (algebraMap A u₀.asIdeal.ResidueField) := by
    intro t' ht'
    rw [RingHom.mem_ker] at ht' ⊢
    rwa [← IsScalarTower.algebraMap_apply A' A u₀.asIdeal.ResidueField t']
  obtain ⟨n, hn1, hinf⟩ := exists_pow_inf_eq_bot_of_mul_eq_bot (RingHom.ker ε'.toRingHom)
    (RingHom.ker (algebraMap A' A))
    (mul_ker_eq_bot_of_linearEquiv_residueField hcomp u₀.asIdeal eI _ hker)
  have : NeZero n := ⟨by omega⟩
  -- the two Artinian quotients lie in the site
  have hC : B.Contains (Spec (CommRingCat.of (A ⧸ RingHom.ker ε.toRingHom ^ n))) :=
    contains_spec_quotient_of_mk_le B hA _ (le_max_right _ _)
  have hC' : B.Contains (Spec (CommRingCat.of (A' ⧸ RingHom.ker ε'.toRingHom ^ n))) :=
    contains_spec_quotient_of_mk_le B hA _
      (Cardinal.mk_le_max_of_surjective_of_mk_ker_le_max (algebraMap A' A) hsurj hmkker)
  -- versality lifts `A` through the small extension
  obtain ⟨σ, hσ⟩ := exists_algHom_powQuotient_of_liftsAtResiduePoint ε hε ε' hε' φ hφ hsurjφ n
    B S hS toS hA hA' baseMap hbase hC hC' p hp x wlift.1.right hx hxS hx' hx'S wlift.1.hom hlift
    (liftsAtResiduePoint_prime_base_of_isVersalAt toS u₀ baseMap
      (p ⋙ Over.post B.inclusion) x hxS hversal)
  -- a lift gives a section, contradicting essential surjectivity
  exact not_isEssentialSurjection_of_lift_powQuotient ε hε n (powQuotientObj ε' hε' n)
    (powQuotientMap hφ hε' hε n) σ hσ (maximalIdeal_pow_powQuotientObj_eq_bot ε' hε' n)
    (isSmallExtension_powQuotientMap hφ hε' hε hsurjφ n hinf
      (length_ker_eq_one_of_linearEquiv_residueField hsurj hcomp u₀.asIdeal eI))
    (isEssentialSurjection_powQuotientMap_of_bijective ε (fun _ => rfl) hε ε' (fun _ => rfl) hε'
      φ (fun _ => rfl) hφ n (by omega) hbij)

end VersalDegreeNegOne

end Deformation.Artin
