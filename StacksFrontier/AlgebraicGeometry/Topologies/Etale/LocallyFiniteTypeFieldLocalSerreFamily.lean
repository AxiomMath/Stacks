module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LocallyFiniteTypeSliceCohomology
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LocallyFiniteTypeSiteFieldVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.LocalSerreFamily
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.ModuleCohomologyOverObjectVanishing
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0DC6 over a finite or separably closed field

Let `S` be the spectrum of a finite field or of a separably closed field, `Λ` a finite ring whose
order is invertible on `S`, and `(C, Λ)` the site of schemes locally of finite type over `S` with
the étale topology, ringed by the constant sheaf `Λ`
(`AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.ringedSite`). Take `A_U` to be all sheaves of
`Λ`-modules on `C/U`, `B` the quasi-compact objects, for `V ∈ B`

`d_V = 1 + 2 dim(S) + sup_{v ∈ V} (trdeg_{κ(s)} κ(v) + 2 dim 𝒪_{V, v})`,

and `Cov_V` the étale coverings `{V_i ⟶ V}` with every `V_i` quasi-compact. Stacks 0DC6 asserts
that these data satisfy the conditions (1), (2), (3) of Stacks 0DC1 (Tags 0DC2, 0DC3, 0DC4). This
file proves it for the first two types of base of the example.

Conditions (1) and (2) hold because `A_U` is everything. For condition (3), every object is
covered by its affine opens, `Cov_V` is cofinal
(`AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.quasiCompactEtaleCoverings`), and the vanishing
`H^p(V_i, F) = 0` for `p > d_V` is reduced in three steps to the cohomological dimension of
`V_i`: the module cohomology over `V_i` is the abelian cohomology of the slice `(C/V)/V_i`
(`Stacks.Cohomology.isZero_moduleCohomology_of_subsingleton_sheafH_over`); that is the étale
cohomology of the small étale site of `V_i`
(`AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.subsingleton_sheafH_of_sliceSmallEtale`); and
a sheaf of `Λ`-modules is killed by the order of `Λ`, so it is a torsion sheaf, whose étale
cohomology on `V_i` vanishes above `d_V`
(`AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.subsingleton_H_of_etale_of_field`, from
`cd(V_i) ≤ 2 dim V_i + cd(k)` and `cd(k) ≤ 1`).

## Main definitions

* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.allModules`: the family `A_U = Mod(Λ_U)`.
* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.EtaleVanishingAboveBound`: the cohomological
  input of condition (3), the vanishing of `H^p_ét(W, G)` above `d_V`.
* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.boundOfVanishing`: the data of condition (3).
* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.localSerreFamilyOfVanishing`: the family
  packaged as a `Stacks.Cohomology.CohomologicalDescent.LocalSerreFamily`.

## Main results

* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.localSerre_of_etaleVanishingAboveBound`: the
  conditions of Stacks 0DC1 for any base of the example on which `EtaleVanishingAboveBound` holds.
* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.etaleVanishingAboveBound_of_field`: it holds
  over a finite or separably closed field.
* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.localSerre_of_finite`: **Stacks 0DC6, type
  (1)**, `S` the spectrum of a finite field.
* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.localSerre_of_isSepClosed`: **Stacks 0DC6,
  type (2)**, `S` the spectrum of a separably closed field.

## Implementation notes

The hypothesis that the order of `Λ` is invertible on `S` is part of the statement of the
example, and is carried as such; over a field the bound holds for every torsion sheaf, so the
proof does not use it.

`Cov_V` is `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.IsQuasiCompactEtaleCovering`: families
of étale morphisms, jointly surjective, with quasi-compact members, which is what the source calls
an étale covering. It is not the base's `IsQuasiCompactCovering`, whose families only generate a
covering sieve and need not consist of étale morphisms.

For the types (3) and (4) of the example, `S` the spectrum of a strictly henselian Noetherian local
ring or of a henselian Noetherian local ring with finite residue field,
`localSerre_of_etaleVanishingAboveBound` reduces the example to `EtaleVanishingAboveBound S |Λ|`,
which the source takes from Gabber's theorem on cohomological dimension (Travaux de Gabber,
Exposé XVIII-A, Corollary 1.2 and Lemma 2.2); that theorem is not proved here, and no
registration is made for those two types.

## References

* [Stacks Project, Tag 0DC6](https://stacks.math.columbia.edu/tag/0DC6)
* [Stacks Project, Tag 0DC1](https://stacks.math.columbia.edu/tag/0DC1)
* [Stacks Project, Tag 0DC4](https://stacks.math.columbia.edu/tag/0DC4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.CohomologicalDescent

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

variable {S : Scheme.{u}} (Λ : Type u) [CommRing Λ]

/-- The structure sheaf of the slice `C/V` of the ringed site `(C, Λ)`. -/
abbrev ringOver (V : Lifted S) :
    Sheaf ((liftedTopology S).over V) RingCat.{u + 1} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite S Λ).O).over V

/-- **The order of a finite ring `Λ` kills every sheaf of `Λ`-modules** on a slice of `(C, Λ)`. -/
lemma nsmul_card_eq_zero [Finite Λ] {V : Lifted S} (F : SheafOfModules.{u + 1} (ringOver Λ V))
    (Z : Over V) (y : F.val.obj (op Z)) : Nat.card Λ • y = 0 := by
  rw [← Nat.cast_smul_eq_nsmul ((ringOver Λ V).obj.obj (op Z))]
  have : ((Nat.card Λ : ℕ) : (ringOver Λ V).obj.obj (op Z)) = 0 :=
    natCast_card_eq_zero Λ Z.left
  rw [this, zero_smul]

variable (S) in
/-- The family `A_U = Mod(Λ_U)` of all sheaves of `Λ`-modules on the slices of `(C, Λ)`. -/
abbrev allModules : SliceProperties (ringedSite S Λ) := fun _ ↦ ⊤

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

variable (S) in
/-- **The cohomological input of condition (3) of Stacks 0DC1 in Stacks 0DC6**, for a base `S`
and an integer `n`: for every quasi-compact `V` locally of finite type over `S`, every
quasi-compact `W` étale over `V` and every abelian sheaf `G` on `W_ét` killed by `n`,
`H^p_ét(W, G) = 0` for `p > d_V`. With `n` the order of `Λ` this is what the source deduces from
Gabber's theorem on cohomological dimension. -/
def EtaleVanishingAboveBound (n : ℕ) : Prop :=
  ∀ (V : LocallyFiniteTypeEtale S), IsQuasiCompact V →
    ∀ (W : LocallyFiniteTypeEtale S), IsQuasiCompact W →
      ∀ g : W ⟶ V, Etale ((forget S).map g) →
        ∀ G : Sheaf W.obj.left.smallEtaleTopology AddCommGrpCat.{u + 1},
          (∀ (T : W.obj.left.Etale) (x : G.obj.obj (op T)), n • x = 0) →
            ∀ p : ℕ, V.obj.hom.etaleCohomologyBound < p → Subsingleton (Sheaf.H.{u + 1} G p)

/-- The restriction of a sheaf of `Λ`-modules on `C/V` to the small étale site of a member of a
covering is killed by the order of `Λ`. -/
lemma nsmul_card_sliceSmallEtale [Finite Λ] {V : Lifted S}
    (F : SheafOfModules.{u + 1} (ringOver Λ V)) (U : Over V) (T : (memberObj U).obj.left.Etale)
    (x : (((sliceSmallEtaleFunctor U).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (memberObj U).obj.left.smallEtaleTopology (sliceTopology U)).obj
          (((SheafOfModules.toSheaf.{u + 1} (ringOver Λ V)).obj F).over U)).obj.obj (op T)) :
    Nat.card Λ • x = 0 :=
  nsmul_card_eq_zero Λ F _ x

/-- The base `S` is of one of the first two types of Stacks 0DC6. -/
lemma isUnboundedDescentEtaleBase_of_field (k : Type u) [Field k]
    (hk : Finite k ∨ IsSepClosed k) (e : S ≅ Spec (.of k)) : IsUnboundedDescentEtaleBase S := by
  rcases hk with hk | hk
  · exact Or.inl ⟨k, inferInstance, hk, ⟨e⟩⟩
  · exact Or.inr (Or.inl ⟨k, inferInstance, hk, ⟨e⟩⟩)

/-- The natural number `d_V` of a quasi-compact object `V`. -/
def degreeOf (hS : IsUnboundedDescentEtaleBase S) (V : Lifted S)
    (hV : IsQuasiCompact ((liftedEquiv S).inverse.obj V)) : ℕ :=
  Classical.choose (hS.exists_natCast_eq_etaleCohomologyBound ((liftedEquiv S).inverse.obj V) hV)

lemma etaleCohomologyBound_eq_degreeOf (hS : IsUnboundedDescentEtaleBase S) (V : Lifted S)
    (hV : IsQuasiCompact ((liftedEquiv S).inverse.obj V)) :
    ((liftedEquiv S).inverse.obj V).obj.hom.etaleCohomologyBound = degreeOf hS V hV :=
  Classical.choose_spec
    (hS.exists_natCast_eq_etaleCohomologyBound ((liftedEquiv S).inverse.obj V) hV)

/-- **The data of condition (3) of Stacks 0DC1 for the family of Stacks 0DC6**, from the
cohomological input `EtaleVanishingAboveBound`: `B` is the set of quasi-compact objects, `d_V` is
the bound of the example, and `Cov_V` is the system of étale coverings with quasi-compact
members. -/
def boundOfVanishing [Finite Λ] (hS : IsUnboundedDescentEtaleBase S)
    (hvan : EtaleVanishingAboveBound S (Nat.card Λ)) :
    LocalCohomologicalBound (ringedSite S Λ) (allModules S Λ) where
  B := {V | IsQuasiCompact ((liftedEquiv S).inverse.obj V)}
  basisCover U := ⟨affineHypercover U, (isQuasiCompactEtaleCovering_affineHypercover U).mem,
    fun i ↦ (isQuasiCompactEtaleCovering_affineHypercover U).2.2 i⟩
  degreeBound V hV := degreeOf hS V hV
  coverings V _ := quasiCompactEtaleCoverings S V
  vanishing V hV 𝒰 h𝒰 := by
    intro i p hp F _
    have : EnoughInjectives (SheafOfModules.{u + 1} (ringOver Λ V)) :=
      IsGrothendieckAbelian.enoughInjectives
    apply Stacks.Cohomology.isZero_moduleCohomology_of_subsingleton_sheafH_over.{u + 1}
    apply subsingleton_sheafH_of_sliceSmallEtale (Over.mk (𝒰.f i))
    refine hvan ((liftedEquiv S).inverse.obj V) hV (memberObj (Over.mk (𝒰.f i))) (h𝒰.2.2 i)
      ((liftedEquiv S).inverse.map (𝒰.f i)) (h𝒰.1 i) _
      (nsmul_card_sliceSmallEtale Λ F (Over.mk (𝒰.f i))) p ?_
    rw [etaleCohomologyBound_eq_degreeOf hS V hV]
    have : degreeOf hS V hV < p := by exact_mod_cast hp
    exact_mod_cast this

/-- The family `A_U = Mod(Λ_U)`, from the cohomological input `EtaleVanishingAboveBound`, as a
family of weak Serre subcategories subject to the three conditions of Stacks 0DC1. -/
def localSerreFamilyOfVanishing [Finite Λ] (hS : IsUnboundedDescentEtaleBase S)
    (hvan : EtaleVanishingAboveBound S (Nat.card Λ)) : LocalSerreFamily (ringedSite S Λ) where
  A := allModules S Λ
  weakSerre _ := inferInstance
  restriction _ _ _ _ _ := trivial
  locality _ _ _ _ := ⟨fun _ _ ↦ trivial, fun _ ↦ trivial⟩
  bound := boundOfVanishing Λ hS hvan

/-- **The conditions of Stacks 0DC1 for the family of Stacks 0DC6, from the cohomological
input.** For `S` of one of the types of Stacks 0DC6 and `Λ` a finite ring such that
`EtaleVanishingAboveBound S |Λ|` holds, the family `A_U` of all sheaves of `Λ`-modules on the
slices of `(C, Λ)` satisfies conditions (1), (2), (3) of Stacks 0DC1 with the data of the
example. -/
theorem localSerre_of_etaleVanishingAboveBound [Finite Λ] (hS : IsUnboundedDescentEtaleBase S)
    (hvan : EtaleVanishingAboveBound S (Nat.card Λ)) :
    (∀ U, (allModules S Λ U).IsWeakSerreClass) ∧
      IsStableUnderRestriction (ringedSite S Λ) (allModules S Λ) ∧
      IsLocalOnCoverings (ringedSite S Λ) (allModules S Λ) ∧
      ∃ b : LocalCohomologicalBound (ringedSite S Λ) (allModules S Λ),
        b.B = {V | IsQuasiCompact ((liftedEquiv S).inverse.obj V)} ∧
        (∀ V hV, ∃ d : ℕ, b.degreeBound V hV = d ∧
          ((liftedEquiv S).inverse.obj V).obj.hom.etaleCohomologyBound = d) ∧
        ∀ V hV (𝒰 : PreZeroHypercover.{u + 1} V),
          (b.coverings V hV).cov 𝒰 ↔ IsQuasiCompactEtaleCovering 𝒰 :=
  ⟨(localSerreFamilyOfVanishing Λ hS hvan).weakSerre,
    (localSerreFamilyOfVanishing Λ hS hvan).restriction,
    (localSerreFamilyOfVanishing Λ hS hvan).locality, boundOfVanishing Λ hS hvan, rfl,
    fun V hV ↦ ⟨degreeOf hS V hV, rfl, etaleCohomologyBound_eq_degreeOf hS V hV⟩,
    fun _ _ _ ↦ Iff.rfl⟩

/-- **The cohomological input of Stacks 0DC6 over a finite or separably closed field**, for
every positive `n`: a sheaf killed by `n` is a torsion sheaf, and
`subsingleton_H_of_etale_of_field` bounds its cohomology. -/
theorem etaleVanishingAboveBound_of_field (k : Type u) [Field k] (hk : Finite k ∨ IsSepClosed k)
    (e : S ≅ Spec (.of k)) {n : ℕ} (hn : 0 < n) : EtaleVanishingAboveBound S n :=
  fun V hV W hW g hg G hG p hp ↦
    subsingleton_H_of_etale_of_field k hk e V hV W hW g hg G
      (fun T _ ↦ ⟨⊤, W.obj.left.smallEtaleTopology.top_mem T, fun _ _ _ ↦ ⟨n, hn, hG _ _⟩⟩) p hp

variable (S) in
/-- **Stacks 0DC6 over a finite or separably closed field.** For `S ≅ Spec k` with `k` finite or
separably closed and `Λ` a finite ring, the family `A_U` of all sheaves of `Λ`-modules on the
slices of the ringed site `(C, Λ)` of schemes locally of finite type over `S` with the étale
topology satisfies the conditions of Stacks 0DC1: each `A_U` is a weak Serre subcategory,
condition (1) (Stacks 0DC2) and condition (2) (Stacks 0DC3) hold, and condition (3)
(Stacks 0DC4) holds with `B` the quasi-compact objects, `d_V` the bound of the example and
`Cov_V` the étale coverings of `V` by quasi-compact objects. -/
theorem localSerre_of_field (k : Type u) [Field k] (hk : Finite k ∨ IsSepClosed k)
    (e : S ≅ Spec (.of k)) [Finite Λ] :
    (∀ U, (allModules S Λ U).IsWeakSerreClass) ∧
      IsStableUnderRestriction (ringedSite S Λ) (allModules S Λ) ∧
      IsLocalOnCoverings (ringedSite S Λ) (allModules S Λ) ∧
      ∃ b : LocalCohomologicalBound (ringedSite S Λ) (allModules S Λ),
        b.B = {V | IsQuasiCompact ((liftedEquiv S).inverse.obj V)} ∧
        (∀ V hV, ∃ d : ℕ, b.degreeBound V hV = d ∧
          ((liftedEquiv S).inverse.obj V).obj.hom.etaleCohomologyBound = d) ∧
        ∀ V hV (𝒰 : PreZeroHypercover.{u + 1} V),
          (b.coverings V hV).cov 𝒰 ↔ IsQuasiCompactEtaleCovering 𝒰 :=
  localSerre_of_etaleVanishingAboveBound Λ (isUnboundedDescentEtaleBase_of_field k hk e)
    (etaleVanishingAboveBound_of_field k hk e Nat.card_pos)

end AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

namespace AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

variable (S : Scheme.{u})

/-- **Stacks 0DC6, type (1): `S` the spectrum of a finite field.** Let `S ≅ Spec k` with `k` a
finite field, let `Λ` be a finite ring whose order is invertible on `S`, let `C` be the category
of schemes locally of finite type over `S` with the étale topology, ringed by the constant sheaf
`Λ` (`ringedSite S Λ`), and let `A_U` be the category of all sheaves of `Λ`-modules on `C/U`.
Then the conditions (1), (2), (3) of Stacks 0DC1 hold: each `A_U` is a weak Serre subcategory,
restriction along `U ⟶ V` sends `A_V` into `A_U` (Stacks 0DC2), membership in `A_U` is local on
coverings (Stacks 0DC3), and (Stacks 0DC4) with `B` the set of quasi-compact objects, for
`V ∈ B` the integer `d_V = 1 + 2 dim(S) + sup_{v ∈ V} (trdeg_{κ(s)} κ(v) + 2 dim 𝒪_{V, v})`, and
`Cov_V` the étale coverings `{V_i ⟶ V}` with every `V_i` quasi-compact, `H^p(V_i, F) = 0` for
every `{V_i ⟶ V}` in `Cov_V`, every `p > d_V` and every `F` in `A_V`. -/
@[stacks 0DC6 "type (1): S the spectrum of a finite field"]
theorem localSerre_of_finite (k : Type u) [Field k] [Finite k] (e : S ≅ Spec (.of k)) :
    ∀ (Λ : Type u) [CommRing Λ] [Finite Λ], IsUnit (Nat.card Λ : Γ(S, ⊤)) →
      (∀ U, (allModules S Λ U).IsWeakSerreClass) ∧
        IsStableUnderRestriction (ringedSite S Λ) (allModules S Λ) ∧
        IsLocalOnCoverings (ringedSite S Λ) (allModules S Λ) ∧
        ∃ b : LocalCohomologicalBound (ringedSite S Λ) (allModules S Λ),
          b.B = {V | IsQuasiCompact ((liftedEquiv S).inverse.obj V)} ∧
          (∀ V hV, ∃ d : ℕ, b.degreeBound V hV = d ∧
            ((liftedEquiv S).inverse.obj V).obj.hom.etaleCohomologyBound = d) ∧
          ∀ V hV (𝒰 : PreZeroHypercover.{u + 1} V),
            (b.coverings V hV).cov 𝒰 ↔ IsQuasiCompactEtaleCovering 𝒰 :=
  fun Λ _ _ _ ↦ localSerre_of_field S Λ k (Or.inl inferInstance) e

/-- **Stacks 0DC6, type (2): `S` the spectrum of a separably closed field.** Let `S ≅ Spec k`
with `k` a separably closed field, let `Λ` be a finite ring whose order is invertible on `S`, let
`C` be the category of schemes locally of finite type over `S` with the étale topology, ringed by
the constant sheaf `Λ` (`ringedSite S Λ`), and let `A_U` be the category of all sheaves of
`Λ`-modules on `C/U`. Then the conditions (1), (2), (3) of Stacks 0DC1 hold: each `A_U` is a weak
Serre subcategory, restriction along `U ⟶ V` sends `A_V` into `A_U` (Stacks 0DC2), membership in
`A_U` is local on coverings (Stacks 0DC3), and (Stacks 0DC4) with `B` the set of quasi-compact
objects, for `V ∈ B` the integer
`d_V = 1 + 2 dim(S) + sup_{v ∈ V} (trdeg_{κ(s)} κ(v) + 2 dim 𝒪_{V, v})`, and `Cov_V` the étale
coverings `{V_i ⟶ V}` with every `V_i` quasi-compact, `H^p(V_i, F) = 0` for every
`{V_i ⟶ V}` in `Cov_V`, every `p > d_V` and every `F` in `A_V`. -/
@[stacks 0DC6 "type (2): S the spectrum of a separably closed field"]
theorem localSerre_of_isSepClosed (k : Type u) [Field k] [IsSepClosed k]
    (e : S ≅ Spec (.of k)) :
    ∀ (Λ : Type u) [CommRing Λ] [Finite Λ], IsUnit (Nat.card Λ : Γ(S, ⊤)) →
      (∀ U, (allModules S Λ U).IsWeakSerreClass) ∧
        IsStableUnderRestriction (ringedSite S Λ) (allModules S Λ) ∧
        IsLocalOnCoverings (ringedSite S Λ) (allModules S Λ) ∧
        ∃ b : LocalCohomologicalBound (ringedSite S Λ) (allModules S Λ),
          b.B = {V | IsQuasiCompact ((liftedEquiv S).inverse.obj V)} ∧
          (∀ V hV, ∃ d : ℕ, b.degreeBound V hV = d ∧
            ((liftedEquiv S).inverse.obj V).obj.hom.etaleCohomologyBound = d) ∧
          ∀ V hV (𝒰 : PreZeroHypercover.{u + 1} V),
            (b.coverings V hV).cov 𝒰 ↔ IsQuasiCompactEtaleCovering 𝒰 :=
  fun Λ _ _ _ ↦ localSerre_of_field S Λ k (Or.inr inferInstance) e

end AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

end
