module

public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplanePushforwardCohomology
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.KernelRegularityBound
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.RegularitySectionMultiplicationArbitraryField
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The hyperplane-section chain on the cohomology of the twists of a coherent sheaf

Let `k` be a field, let `𝒦` be a coherent sheaf on `ℙ^{n+1}_k`, let `j : ℙⁿ_k ⟶ ℙ^{n+1}_k` be a
hyperplane cut out by a global section `s` of `𝒪(1)` and let `𝒢` be the restriction of `𝒦` to
it. [Stacks, Tag 08AG] uses the chain of multiplications by `s`,

`Hⁱ(ℙ^{n+1}_k, 𝒦(d)) ⟶ Hⁱ(ℙ^{n+1}_k, 𝒦(d+1))`,

and three of its properties: injectivity in the degrees `2 ≤ i ≤ n+1`, surjectivity in degree
one, and the propagation of injectivity in degree one from one step to the next. This file
proves all three from the regularity of `𝒢`, and nothing else.

## Main results

* `AlgebraicGeometry.isMRegular_of_le`: an `m`-regular coherent sheaf is `d`-regular for every
  `d ≥ m`, by iterating [Stacks, Tag 08A6].
* `AlgebraicGeometry.isZero_projectiveH_of_isMRegular`: an `m`-regular sheaf has
  `Hᵠ(ℙⁿ_k, ℱ(d)) = 0` whenever `q > 0` and `m ≤ d + q`, in every degree — above the dimension
  of the space by [Stacks, Tag 01YS] clause (2), below it by regularity.
* `AlgebraicGeometry.surjective_resH_succ_of_surjective`: **the propagation step.** For a
  hyperplane restriction package, if `H⁰(ℙ^{n+1}_k, ℱ(m)) ⟶ H⁰(ℙⁿ_k, 𝒢(m))` is surjective and
  `𝒢` is `m`-regular, then the same map one twist up is surjective.
* `AlgebraicGeometry.kernelChainDataOfPackage`: **the chain.** A hyperplane restriction
  package whose hyperplane is a closed immersion over `Spec k` and whose restriction `𝒢` is
  `b`-regular produces `AlgebraicGeometry.KernelChainData` at `b`.

## The mathematics

The chain map is the map induced on cohomology by
`…ProjectiveSpaceSectionMultiplication.twistSectionMul`, the first arrow of the twisted
hyperplane restriction sequence

`0 ⟶ 𝒦(d) ⟶ 𝒦(d+1) ⟶ j_*(𝒢(d+1)) ⟶ 0`

of [Stacks, Tag 08A0] and [Stacks, Tag 0EGK]. Its long exact sequence
(`AlgebraicGeometry.exists_cohomologyOverField_longExactSequence`) reads

`Hⁱ⁻¹(j_*𝒢(d+1)) ⟶ Hⁱ(𝒦(d)) ⟶ Hⁱ(𝒦(d+1)) ⟶ Hⁱ(j_*𝒢(d+1))`,

and `Hᵠ(ℙ^{n+1}_k, j_*𝒢(e)) = Hᵠ(ℙⁿ_k, 𝒢(e))` because `j` is a closed immersion over `Spec k`
([Stacks, Tag 089W], `AlgebraicGeometry.projectiveHPushforwardIso`). So injectivity in degree
`i` is the vanishing of `Hⁱ⁻¹(𝒢(d+1))` and surjectivity the vanishing of `Hⁱ(𝒢(d+1))`, both of
which `isZero_projectiveH_of_isMRegular` supplies from the regularity of `𝒢`.

Propagation in degree one is the source's own argument, and it is the only place where
[Stacks, Tag 08A7] is used. Injectivity of the chain map in degree one is, by exactness, the
vanishing of the connecting map out of `H⁰(j_*𝒢(d+1))`, which is the surjectivity of
`H⁰(𝒦(d+1)) ⟶ H⁰(𝒢(d+1))`. That surjectivity propagates: a class `g ∈ H⁰(𝒢(d+2))` is a
combination `∑ σ · gᵢ` of products with `gᵢ ∈ H⁰(𝒢(d+1))` by [Stacks, Tag 08A7] on `ℙⁿ_k`, each
`gᵢ` lifts to `H⁰(𝒦(d+1))` by hypothesis, each `σ` lifts to a degree-one form upstairs by the
`liftSection` clause of the package ([Stacks, Tag 089Z]), and the lifted combination restricts
to `g` because restriction intertwines the two multiplications. This is the argument of
`AlgebraicGeometry.span_mulSections_eq_top_of_isMRegular`'s inductive step, isolated.

## References

* [Stacks Project, Tag 08AG](https://stacks.math.columbia.edu/tag/08AG)
* [Stacks Project, Tag 08A6](https://stacks.math.columbia.edu/tag/08A6)
* [Stacks Project, Tag 08A7](https://stacks.math.columbia.edu/tag/08A7)
* [Stacks Project, Tag 08A0](https://stacks.math.columbia.edu/tag/08A0)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 089Z](https://stacks.math.columbia.edu/tag/089Z)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication (twistSectionMul)

universe u

namespace AlgebraicGeometry

attribute [local instance] isCoherent_projectiveTwist

/-! ### Regularity improves with the degree -/

/-- **An `m`-regular coherent sheaf on `ℙⁿ_k` is `d`-regular for every `d ≥ m`**, by iterating
[Stacks, Tag 08A6]. -/
theorem isMRegular_of_le (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsCoherent] {m d : ℤ}
    (hF : IsMRegular k n F m) (hmd : m ≤ d) : IsMRegular k n F d := by
  obtain ⟨a, rfl⟩ := Int.le.dest hmd
  clear hmd
  induction a with
  | zero => simpa using hF
  | succ a ih =>
    rw [show m + ((a + 1 : ℕ) : ℤ) = m + (a : ℤ) + 1 by push_cast; ring]
    exact isMRegular_add_one k n F _ ih

/-- **The vanishing that regularity gives, in every positive degree and at every twist far
enough up.** If `ℱ` is `m`-regular on `ℙⁿ_k`, `q > 0` and `m ≤ d + q`, then
`Hᵠ(ℙⁿ_k, ℱ(d)) = 0`.

For `q ≤ n` this is `(d+q)`-regularity of `ℱ`, which `AlgebraicGeometry.isMRegular_of_le`
supplies; for `q > n` it is the vanishing of cohomology above the dimension,
[Stacks, Tag 01YS] clause (2), and needs no hypothesis at all. -/
theorem isZero_projectiveH_of_isMRegular (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsCoherent] {m d : ℤ} (q : ℕ)
    (hF : IsMRegular k n F m) (hq : 0 < q) (hd : m ≤ d + q) :
    IsZero (projectiveH k n (projectiveTwist n F d) q) := by
  refine (isZero_cohomologyOverField_iff_isZero_hgroup k (projectiveSpaceToBase k n)
    (projectiveTwist n F d) q).mpr ?_
  by_cases hqn : q ≤ n
  · have h := isMRegular_of_le k n F hF hd q hq hqn
    rwa [add_sub_cancel_right] at h
  · have : (projectiveTwist n F d).IsQuasicoherent :=
      isQuasicoherent_projectiveTwist_of_isCoherent n F d
    exact Stacks.ProjectiveCohomology.isZero_Hgroup_of_lt n (.of k) _ q (by omega)

/-! ### Propagation of the surjectivity of restriction to the hyperplane -/

/-- **The propagation step of [Stacks, Tag 08AG], isolated from the inductive step of
[Stacks, Tag 08A7].** Let `P` be a hyperplane restriction package for `ℱ` on `ℙ^{n+1}_k`, with
restriction `𝒢` on `ℙⁿ_k`. If `𝒢` is `m`-regular and the restriction map
`H⁰(ℙ^{n+1}_k, ℱ(m)) ⟶ H⁰(ℙⁿ_k, 𝒢(m))` is surjective, then so is the restriction map one twist
up.

[Stacks, Tag 08A7] on `ℙⁿ_k` writes a class of `H⁰(𝒢(m+1))` as a combination of products
`σ · g` with `σ` a degree-one form on `ℙⁿ_k` and `g ∈ H⁰(𝒢(m))`. Each `g` lifts to
`H⁰(ℱ(m))` by hypothesis and each `σ` lifts to a degree-one form upstairs by the `liftSection`
clause of the package, which also says that restriction intertwines the two multiplications; so
the corresponding combination upstairs restricts to the given class. -/
@[sga "6 XIII 1.4" "(iii)"]
theorem surjective_resH_succ_of_surjective (k : Type u) [Field k] (n : ℕ)
    {F : (projectiveSpaceOverRing (n + 1) (.of k)).Modules}
    (P : HyperplaneRestrictionPackage k n F) (m : ℤ)
    (hG : @IsMRegular k _ n P.G P.isCoherent m)
    (hsurj : Function.Surjective (ConcreteCategory.hom (P.resH m))) :
    Function.Surjective (ConcreteCategory.hom (P.resH (m + 1))) := by
  let := P.isCoherent
  have hspanG : mulSectionsSpan k n P.G m = ⊤ :=
    span_mulSections_eq_top_of_isMRegular_field k n P.G m hG
  set T := mulSectionsSpan k (n + 1) F m
  set ψ := ConcreteCategory.hom (P.resH (m + 1)) with hψ
  have hA : mulSectionsSpan k n P.G m ≤ T.map ψ := by
    rw [mulSectionsSpan, Submodule.span_le]
    rintro x ⟨σ, g, rfl⟩
    obtain ⟨σ', hσ'⟩ := P.liftSection σ
    obtain ⟨f, hf⟩ := hsurj g
    refine ⟨ConcreteCategory.hom (mulSection k (n + 1) F σ' m) f,
      mem_mulSectionsSpan k (n + 1) F m σ' f, ?_⟩
    show ψ _ = _
    have hmor : mulSection k (n + 1) F σ' m ≫ P.resH (m + 1)
        = P.resH m ≫ mulSection k n P.G σ m := by
      change mulSection k (n + 1) F σ' m ≫
          projectiveHZeroMap k (n + 1) (P.res (m + 1)) ≫ (P.compare (m + 1)).inv
        = (projectiveHZeroMap k (n + 1) (P.res m) ≫ (P.compare m).inv) ≫
            mulSection k n P.G σ m
      rw [← Category.assoc, hσ' m]
      simp
    have happ : ConcreteCategory.hom (P.resH (m + 1))
          (ConcreteCategory.hom (mulSection k (n + 1) F σ' m) f)
        = ConcreteCategory.hom (mulSection k n P.G σ m)
          (ConcreteCategory.hom (P.resH m) f) :=
      congrFun (congrArg (fun h => (ConcreteCategory.hom h : _ → _)) hmor) f
    rw [hψ, happ, hf]
  have hB : T.map ψ = ⊤ := top_le_iff.1 (hspanG.symm.trans_le hA)
  intro t
  obtain ⟨t', -, h⟩ : t ∈ T.map ψ := hB ▸ Submodule.mem_top
  exact ⟨t', h⟩

/-! ### Transporting injectivity and surjectivity along a reindexing -/

/-- Composing with the transport along an equality of objects of `ModuleCat` changes neither
injectivity nor surjectivity. The chain of `AlgebraicGeometry.KernelChainData` indexes its steps
by a natural number, so its `j`-th map lands at the twist `b + (j+1 : ℕ)` while the map induced
by multiplication by the section lands at `(b + j) + 1`; the two degrees are equal and this is
the transport between them. -/
theorem injective_comp_eqToHom {k : Type u} [Field k] {A B C : ModuleCat.{u} k}
    (φ : A ⟶ B) (h : B = C) :
    Function.Injective (ConcreteCategory.hom (φ ≫ eqToHom h)) ↔
      Function.Injective (ConcreteCategory.hom φ) := by
  subst h
  simp

/-- Composing with the transport along an equality of objects of `ModuleCat` preserves
surjectivity; see `AlgebraicGeometry.injective_comp_eqToHom`. -/
theorem surjective_comp_eqToHom {k : Type u} [Field k] {A B C : ModuleCat.{u} k}
    (φ : A ⟶ B) (h : B = C) :
    Function.Surjective (ConcreteCategory.hom (φ ≫ eqToHom h)) ↔
      Function.Surjective (ConcreteCategory.hom φ) := by
  subst h
  simp

/-! ### The chain and its three properties -/

/-- **The chain of [Stacks, Tag 08AG], built from a hyperplane restriction package whose
restriction is regular.** Let `𝒦` be a coherent sheaf on `ℙ^{n+1}_k`, let `P` be a hyperplane
restriction package for it whose hyperplane `j` is a closed immersion over `Spec k`, and suppose
the restriction `𝒢 = P.G` is `b`-regular. Then the multiplications by the section of `𝒪(1)`
assemble into `AlgebraicGeometry.KernelChainData` at `b`.

Each of the three properties is read off the long exact sequence of the twisted restriction
sequence, whose third term's cohomology is cohomology on `ℙⁿ_k` by
`AlgebraicGeometry.projectiveHPushforwardIso`. Injectivity in degree `i ≥ 2` is the vanishing of
`Hⁱ⁻¹(𝒢(d+1))`, surjectivity in degree one is the vanishing of `H¹(𝒢(d+1))`, and both are
`AlgebraicGeometry.isZero_projectiveH_of_isMRegular`. Propagation of injectivity in degree one
passes through the surjectivity of restriction on `H⁰` and
`AlgebraicGeometry.surjective_resH_succ_of_surjective`. -/
@[sga "6 XIII 1.4" "partial"]
def kernelChainDataOfPackage (k : Type u) [Field k] (n : ℕ)
    (K : (projectiveSpaceOverRing (n + 1) (.of k)).Modules) [K.IsCoherent]
    (P : HyperplaneRestrictionPackage k n K) [IsClosedImmersion P.j]
    (hj : P.j ≫ projectiveSpaceToBase k (n + 1) = projectiveSpaceToBase k n)
    (b : ℤ) (hG : @IsMRegular k _ n P.G P.isCoherent b) :
    KernelChainData k (n + 1) K b := by
  letI := P.isCoherent
  -- the third term of the restriction sequence is acyclic in the relevant degrees
  have hvan : ∀ (q : ℕ), 0 < q → ∀ e : ℤ, b ≤ e + q →
      IsZero (projectiveH k (n + 1)
        ((Scheme.Modules.pushforward P.j).obj (projectiveTwist n P.G e)) q) :=
    fun q hq e he => (isZero_projectiveH_of_isMRegular k n P.G q hG hq he).of_iso
      (projectiveHPushforwardIso k P.j hj (projectiveTwist n P.G e) q).symm
  -- injectivity in the degrees at least two
  have hinjΦ : ∀ (d : ℤ), b ≤ d → ∀ i : ℕ, 2 ≤ i →
      Function.Injective (ConcreteCategory.hom (cohomologyOverFieldMap k
        (projectiveSpaceToBase k (n + 1))
        (twistSectionMul (n + 1) (Spec (.of k)) K P.s d) i)) := by
    intro d hd i hi
    obtain ⟨δ, -, -, -, hca⟩ :=
      exists_cohomologyOverField_longExactSequence k (projectiveSpaceToBase k (n + 1))
        (P.shortExact d)
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hz : δ i' = 0 := (hvan i' (by omega) (d + 1) (by omega)).eq_zero_of_src _
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨y, rfl⟩ := (hca i' x).mp hx
    rw [hz]
    rfl
  -- surjectivity in degree one
  have hsurjΦ : ∀ (d : ℤ), b ≤ d →
      Function.Surjective (ConcreteCategory.hom (cohomologyOverFieldMap k
        (projectiveSpaceToBase k (n + 1))
        (twistSectionMul (n + 1) (Spec (.of k)) K P.s d) 1)) := by
    intro d hd
    obtain ⟨-, -, hab, -, -⟩ :=
      exists_cohomologyOverField_longExactSequence k (projectiveSpaceToBase k (n + 1))
        (P.shortExact d)
    intro y
    refine (hab 1 y).mp ?_
    rw [(hvan 1 one_pos (d + 1) (by omega)).eq_zero_of_tgt
      (cohomologyOverFieldMap k (projectiveSpaceToBase k (n + 1)) (P.res (d + 1)) 1)]
    rfl
  -- injectivity in degree one is equivalent to surjectivity of restriction on `H⁰`
  have hiff : ∀ d : ℤ,
      Function.Injective (ConcreteCategory.hom (cohomologyOverFieldMap k
          (projectiveSpaceToBase k (n + 1))
          (twistSectionMul (n + 1) (Spec (.of k)) K P.s d) 1)) ↔
        Function.Surjective (ConcreteCategory.hom (P.resH (d + 1))) := by
    intro d
    obtain ⟨δ, -, -, hbc, hca⟩ :=
      exists_cohomologyOverField_longExactSequence k (projectiveSpaceToBase k (n + 1))
        (P.shortExact d)
    have hres : ∀ x, ConcreteCategory.hom (P.resH (d + 1)) x =
        ConcreteCategory.hom (P.compare (d + 1)).inv
          (ConcreteCategory.hom (projectiveHZeroMap k (n + 1) (P.res (d + 1))) x) := fun _ => rfl
    constructor
    · intro hinj g
      have hδ : ∀ y, ConcreteCategory.hom (δ 0) y = 0 := by
        intro y
        refine hinj ?_
        rw [(hca 0 (ConcreteCategory.hom (δ 0) y)).mpr ⟨y, rfl⟩]
        exact (map_zero _).symm
      obtain ⟨x, hx⟩ := (hbc 0 (ConcreteCategory.hom (P.compare (d + 1)).hom g)).mp
        (hδ (ConcreteCategory.hom (P.compare (d + 1)).hom g))
      refine ⟨x, ?_⟩
      rw [hres, hx]
      exact (P.compare (d + 1)).hom_inv_id_apply g
    · intro hsurj
      have hδ : ∀ y, ConcreteCategory.hom (δ 0) y = 0 := by
        intro y
        obtain ⟨x, hx⟩ := hsurj (ConcreteCategory.hom (P.compare (d + 1)).inv y)
        refine (hbc 0 y).mpr ⟨x, ?_⟩
        have h := congrArg (ConcreteCategory.hom (P.compare (d + 1)).hom) ((hres x).symm.trans hx)
        rwa [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply] at h
      refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
      obtain ⟨y, rfl⟩ := (hca 0 x).mp hx
      exact hδ y
  -- the propagation step
  have hpropΦ : ∀ (d : ℤ), b ≤ d →
      Function.Injective (ConcreteCategory.hom (cohomologyOverFieldMap k
          (projectiveSpaceToBase k (n + 1))
          (twistSectionMul (n + 1) (Spec (.of k)) K P.s d) 1)) →
        Function.Injective (ConcreteCategory.hom (cohomologyOverFieldMap k
          (projectiveSpaceToBase k (n + 1))
          (twistSectionMul (n + 1) (Spec (.of k)) K P.s (d + 1)) 1)) := by
    intro d hd h
    refine (hiff (d + 1)).mpr ?_
    have hGd : @IsMRegular k _ n P.G P.isCoherent (d + 1) :=
      isMRegular_of_le k n P.G hG (by omega)
    exact surjective_resH_succ_of_surjective k n P (d + 1) hGd ((hiff d).mp h)
  have hdeg : ∀ j : ℕ, b + (j : ℤ) + 1 = b + ((j + 1 : ℕ) : ℤ) := fun j => by push_cast; ring
  refine
    { step := fun i j => cohomologyOverFieldMap k (projectiveSpaceToBase k (n + 1))
        (twistSectionMul (n + 1) (Spec (.of k)) K P.s (b + (j : ℤ))) i ≫
          eqToHom (congrArg
            (fun e => projectiveH k (n + 1) (projectiveTwist (n + 1) K e) i) (hdeg j))
      injective_step := fun i hi _ j => ?_
      surjective_step := fun j => ?_
      injective_step_succ := fun j h => ?_ }
  · exact (injective_comp_eqToHom _ _).mpr (hinjΦ (b + (j : ℤ)) (by omega) i hi)
  · exact (surjective_comp_eqToHom _ _).mpr (hsurjΦ (b + (j : ℤ)) (by omega))
  · refine (injective_comp_eqToHom _ _).mpr ?_
    have hstep := hpropΦ (b + (j : ℤ)) (by omega) ((injective_comp_eqToHom _ _).mp h)
    rwa [hdeg j] at hstep

end AlgebraicGeometry

end
