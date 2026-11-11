module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FormalBranches
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalSituationFiniteDimensional
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRingMorphismHomotopy
public import StacksFrontier.Deformation.Formal.VersalObject.MapsToFormalObject
public import StacksFrontier.Deformation.Formal.VersalObject.PowerSeriesComparisonHom
public import StacksFrontier.Deformation.VersalRing.Uniqueness
public import StacksFrontier.RingTheory.MvPowerSeries.MinimalPrimes

/-!
# The formal branches of two versal rings are canonically identified (Stacks 0DRA)

In the versal situation of **Stacks 0DQU** let `x₀ : Spec k ⟶ 𝒳` be a point with `k` a field of
finite type over `S`, presented over an affine open `Spec Λ ⊆ S` with `Λ → k` finite, so that the
predeformation category `𝓕_{𝒳,k,x₀}` lives over `𝒞_Λ` (Stacks 07T2, 0DQW). Let `A`, `A'` be
versal rings to `𝒳` at `x₀`, the bases of versal formal objects `ξ`, `ξ'`. Definition
**Stacks 0DRA** takes the formal branches of `𝒳` through `x₀` to be the irreducible components
of `Spec A` (`AlgebraicGeometry.Stack.formalBranches`, recorded by their generic points, the
minimal primes of `A`), identified for different choices of `A` by the procedure of
**Stacks 0DR9**: after possibly swapping `A` and `A'` there is a formally smooth map
`φ : A → A'` compatible with the versal formal objects (Stacks 0DQX, 0DR1), well defined up to
formal homotopy (Stacks 0DQD), so `φ(𝔭)A'` is well defined (Stacks 0DQE), and `𝔭 ↦ φ(𝔭)A'` is a
bijection from the minimal primes of `A` onto those of `A'`.

This file proves that this procedure is well defined and makes the definition independent of
the choice of `A`.

## Main results

* `AlgebraicGeometry.Stack.exists_formallySmooth_comparison`: after possibly swapping `A` and
  `A'`, a map `φ : A → A'` compatible with the versal formal objects with `A' ≅ A[[t₁,…,t_r]]`
  carrying `φ` to the constants.
* `AlgebraicGeometry.Stack.map_eq_map_of_hom`: two maps `A → A'` compatible with the versal formal
  objects extend each formal branch of `A` to the same ideal of `A'`.
* `AlgebraicGeometry.Stack.bijOn_map_formalBranches`: `𝔭 ↦ φ(𝔭)A'` is a bijection of formal
  branches, for every map `φ` compatible with the versal formal objects.
* `AlgebraicGeometry.Stack.formalBranchesEquiv`: **Stacks 0DRA**, the identification, with
  `formalBranchesEquiv_eq` (independence of `φ`), `formalBranchesEquiv_refl` and
  `formalBranchesEquiv_trans` (compatibility with identities and composition).

## Implementation notes

The bijection holds for every map compatible with the versal formal objects, not only the
formally smooth one of the source: such a map is formally homotopic to the formally smooth map
when that one goes from `A` to `A'`, and is inverse on minimal primes to it, through Stacks 0DQD
applied to the two composites, when it goes from `A'` to `A`. So the identification exists
along every morphism `ξ ⟶ ξ'` of versal formal objects, and morphisms exist in both directions
(Stacks 06HT).

## References

* [Stacks Project, Tag 0DQD](https://stacks.math.columbia.edu/tag/0DQD)
* [Stacks Project, Tag 0DQE](https://stacks.math.columbia.edu/tag/0DQE)
* [Stacks Project, Tag 0DQX](https://stacks.math.columbia.edu/tag/0DQX)
* [Stacks Project, Tag 0DR1](https://stacks.math.columbia.edu/tag/0DR1)
* [Stacks Project, Tag 0DR9](https://stacks.math.columbia.edu/tag/0DR9)
* [Stacks Project, Tag 0DRA](https://stacks.math.columbia.edu/tag/0DRA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (D : VersalSituation.{u, w})
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
  (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
  (x₀ : D.𝒳.val.val.obj)
  (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hfinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
    QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  {ξ ξ' ξ'' : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
    (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection}
  (hξ : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
    D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ)
  (hξ' : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
    D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ')
  (hξ'' : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
    D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ'')

include hiΛ in
/-- The base of the chart is Noetherian, since `S` is locally Noetherian. -/
private theorem isNoetherianRing_chart : IsNoetherianRing Λ :=
  (isLocallyNoetherian_Spec (R := CommRingCat.of Λ)).mp
    (isLocallyNoetherian_of_isOpenImmersion iΛ)

include hiΛ hfinite hξ in
/-- **Two maps compatible with the versal formal objects extend a formal branch to the same
ideal.** Both are formally homotopic by Stacks 0DQD, and formally homotopic maps extend a minimal
prime to the same ideal (Stacks 0DQE). -/
theorem map_eq_map_of_hom (a b : ξ ⟶ ξ') {p : Ideal ξ.base} (hp : p ∈ minimalPrimes ξ.base) :
    p.map a.base.hom.toRingHom = p.map b.base.hom.toRingHom := by
  have : IsNoetherianRing Λ := isNoetherianRing_chart D iΛ hiΛ
  obtain ⟨hpd, hT, hInf⟩ :=
    isFiniteDimensionalDeformationCategory_of_versalSituation D iΛ hiΛ x₀ hx₀ hfinite
  exact Deformation.Ideal.map_eq_of_formallyHomotopic_of_mem_minimalPrimes _ _
    (Deformation.formallyHomotopic_of_isVersal _ hpd
      (Deformation.finiteDimensional_tangentModuleAt_of_tangentSpaceArtinian hpd hT)
      (fun x PF hx => hInf x hx PF) ξ ξ' hξ a.base b.base ⟨a, rfl⟩ ⟨b, rfl⟩) p hp

include hiΛ hfinite hξ in
/-- An endomorphism of a versal formal object fixes every formal branch. -/
theorem map_eq_self_of_endo (a : ξ ⟶ ξ) {p : Ideal ξ.base} (hp : p ∈ minimalPrimes ξ.base) :
    p.map a.base.hom.toRingHom = p := by
  rw [map_eq_map_of_hom D iΛ hiΛ x₀ hx₀ hfinite hξ a (𝟙 ξ) hp]
  exact Ideal.map_id p

omit [Module.Finite Λ k] in
/-- Extending along a composite of morphisms of formal objects is extending twice. -/
theorem map_comp_base (a : ξ ⟶ ξ') (b : ξ' ⟶ ξ'') (p : Ideal ξ.base) :
    p.map (a ≫ b).base.hom.toRingHom =
      (p.map a.base.hom.toRingHom).map b.base.hom.toRingHom := by
  rw [Ideal.map_map]
  rfl

include hiΛ hξ hξ' in
/-- **The formally smooth comparison of two versal rings (Stacks 0DQX, Stacks 0DR1).** After
possibly swapping `A = ξ.base` and `A' = ξ'.base`, there is a map `φ : A → A'` compatible with the
versal formal objects, the base of a morphism `ξ ⟶ ξ'`, together with an isomorphism
`A' ≅ A[[t₁, …, t_r]]` carrying `φ` to the inclusion of constants. -/
theorem exists_formallySmooth_comparison :
    (∃ r : ℕ, ∃ E : ξ'.base ≃ₐ[Λ] MvPowerSeries (Fin r) ξ.base, ∃ φ : ξ ⟶ ξ',
      ∀ b, E (φ.base.hom b) = MvPowerSeries.C b) ∨
    (∃ r : ℕ, ∃ E : ξ.base ≃ₐ[Λ] MvPowerSeries (Fin r) ξ'.base, ∃ φ : ξ' ⟶ ξ,
      ∀ b, E (φ.base.hom b) = MvPowerSeries.C b) := by
  have : IsNoetherianRing Λ := isNoetherianRing_chart D iΛ hiΛ
  exact (Deformation.exists_powerSeries_comparison_hom
    (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property) ξ ξ' hξ hξ').symm

omit [Module.Finite Λ k] in
/-- A formally smooth map extends the minimal primes of its source bijectively onto those of its
target. -/
private theorem bijOn_of_powerSeries {η η' : Deformation.FormalObject
    (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection}
    {r : ℕ} (E : η'.base ≃ₐ[Λ] MvPowerSeries (Fin r) η.base) (φ : η ⟶ η')
    (hE : ∀ b, E (φ.base.hom b) = MvPowerSeries.C b) :
    Set.BijOn (fun p : Ideal η.base => p.map φ.base.hom.toRingHom) (minimalPrimes η.base)
      (minimalPrimes η'.base) :=
  Ideal.bijOn_map_minimalPrimes_of_ringEquiv_mvPowerSeries φ.base.hom.toRingHom
    E.toRingEquiv hE

include hiΛ hξ hξ' in
/-- **Extension along any map compatible with the versal formal objects is a bijection of formal
branches.** For the formally smooth comparison of the source this is the computation in a power
series ring; any other map from `A` to `A'` is formally homotopic to it, and a map against the
direction of the comparison is inverse to it on minimal primes, since both composites are
endomorphisms of versal formal objects. -/
theorem bijOn_map_formalBranches (a : ξ ⟶ ξ') :
    Set.BijOn (fun p : Ideal ξ.base => p.map a.base.hom.toRingHom)
      (formalBranches D iΛ hiΛ x₀ hx₀ hfinite ξ.base ⟨ξ, rfl, hξ⟩)
      (formalBranches D iΛ hiΛ x₀ hx₀ hfinite ξ'.base ⟨ξ', rfl, hξ'⟩) := by
  rcases exists_formallySmooth_comparison D iΛ hiΛ x₀ hx₀ hξ hξ' with
    ⟨r, E, φ, hE⟩ | ⟨r, E, ψ, hE⟩
  · refine (bijOn_of_powerSeries D iΛ x₀ hx₀ E φ hE).congr fun p hp => ?_
    exact (map_eq_map_of_hom D iΛ hiΛ x₀ hx₀ hfinite hξ a φ hp).symm
  · have hψ := bijOn_of_powerSeries D iΛ x₀ hx₀ E ψ hE
    have hleft : ∀ p ∈ minimalPrimes ξ.base,
        (p.map a.base.hom.toRingHom).map ψ.base.hom.toRingHom = p := fun p hp => by
      rw [← map_comp_base]
      exact map_eq_self_of_endo D iΛ hiΛ x₀ hx₀ hfinite hξ (a ≫ ψ) hp
    have hright : ∀ q ∈ minimalPrimes ξ'.base,
        (q.map ψ.base.hom.toRingHom).map a.base.hom.toRingHom = q := fun q hq => by
      rw [← map_comp_base]
      exact map_eq_self_of_endo D iΛ hiΛ x₀ hx₀ hfinite hξ' (ψ ≫ a) hq
    refine Set.InvOn.bijOn ⟨hleft, hright⟩ (fun p hp => ?_) hψ.mapsTo
    obtain ⟨q, hq, rfl⟩ := hψ.surjOn hp
    change _ ∈ minimalPrimes ξ'.base
    rw [hright q hq]
    exact hq

/-- **Stacks 0DRA.** The formal branches of `𝒳` through `x₀` read off two versal rings
`A = ξ.base` and `A' = ξ'.base` are identified along any map `A → A'` compatible with the versal
formal objects (the base of a morphism `a : ξ ⟶ ξ'`), by `𝔭 ↦ a(𝔭)A'`. This is the procedure of
the source, which uses the formally smooth comparison of Stacks 0DQX and 0DR1
(`AlgebraicGeometry.Stack.exists_formallySmooth_comparison`); the identification does not depend
on the map (`AlgebraicGeometry.Stack.formalBranchesEquiv_eq`) and is compatible with identities and
composition (`AlgebraicGeometry.Stack.formalBranchesEquiv_refl`,
`AlgebraicGeometry.Stack.formalBranchesEquiv_trans`), so the set of formal branches is
independent of the choice of versal ring. -/
@[stacks 0DRA "the identification of the formal branches read off two versal rings A, A' along \
a map A → A' compatible with the versal formal objects, independent of the map"]
def formalBranchesEquiv (a : ξ ⟶ ξ') :
    formalBranches D iΛ hiΛ x₀ hx₀ hfinite ξ.base ⟨ξ, rfl, hξ⟩ ≃
      formalBranches D iΛ hiΛ x₀ hx₀ hfinite ξ'.base ⟨ξ', rfl, hξ'⟩ :=
  (bijOn_map_formalBranches D iΛ hiΛ x₀ hx₀ hfinite hξ hξ' a).equiv _

/-- The identification extends a branch along the map. -/
@[simp]
theorem coe_formalBranchesEquiv_apply (a : ξ ⟶ ξ')
    (p : formalBranches D iΛ hiΛ x₀ hx₀ hfinite ξ.base ⟨ξ, rfl, hξ⟩) :
    (formalBranchesEquiv D iΛ hiΛ x₀ hx₀ hfinite hξ hξ' a p : Ideal ξ'.base) =
      (p : Ideal ξ.base).map a.base.hom.toRingHom :=
  rfl

/-- **The identification of formal branches does not depend on the map.** -/
theorem formalBranchesEquiv_eq (a b : ξ ⟶ ξ') :
    formalBranchesEquiv D iΛ hiΛ x₀ hx₀ hfinite hξ hξ' a =
      formalBranchesEquiv D iΛ hiΛ x₀ hx₀ hfinite hξ hξ' b :=
  Equiv.ext fun p => Subtype.ext (map_eq_map_of_hom D iΛ hiΛ x₀ hx₀ hfinite hξ a b p.2)

/-- **The identification of the formal branches of a versal ring with themselves is the
identity.** -/
theorem formalBranchesEquiv_refl (a : ξ ⟶ ξ) :
    formalBranchesEquiv D iΛ hiΛ x₀ hx₀ hfinite hξ hξ a = Equiv.refl _ :=
  Equiv.ext fun p => Subtype.ext (map_eq_self_of_endo D iΛ hiΛ x₀ hx₀ hfinite hξ a p.2)

/-- **The identifications of formal branches compose.** -/
theorem formalBranchesEquiv_trans (a : ξ ⟶ ξ') (b : ξ' ⟶ ξ'') :
    (formalBranchesEquiv D iΛ hiΛ x₀ hx₀ hfinite hξ hξ' a).trans
        (formalBranchesEquiv D iΛ hiΛ x₀ hx₀ hfinite hξ' hξ'' b) =
      formalBranchesEquiv D iΛ hiΛ x₀ hx₀ hfinite hξ hξ'' (a ≫ b) :=
  Equiv.ext fun p => Subtype.ext (map_comp_base D iΛ x₀ hx₀ a b p.1).symm

omit [Module.Finite Λ k] in
include hξ in
/-- **Two versal formal objects have morphisms between them in both directions** (Stacks 06HT),
so any two versal rings at `x₀` have their formal branches identified. -/
theorem nonempty_hom_of_isVersal : Nonempty (ξ ⟶ ξ') :=
  Deformation.nonempty_hom_of_isVersal
    (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property) ξ ξ' hξ

end AlgebraicGeometry.Stack

end
