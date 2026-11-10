module

public import StacksFrontier.Deformation.Formal.VersalObject.MinimalPowerSeries
public import StacksFrontier.Deformation.Formal.VersalObject.MinimalUniqueness
public import StacksFrontier.RingTheory.AdicCompletion.AnalyticallyUnramified

/-!
# Comparing two versal formal objects along a morphism

Let `𝓕` be a predeformation category over `𝒞_Λ` and let `ξ`, `η` be two versal formal objects of
`𝓕` with bases `A` and `A'`. The uniqueness of versal rings (**Stacks 06T5**, used in the proof of
**Stacks 0DQX**) says that one base is a power series ring over the other, `A ≅ A'[[t₁, …, t_r]]`
or `A' ≅ A[[t₁, …, t_r]]`. This file proves the sharper statement that **Stacks 0DR1** records:
the isomorphism can be chosen compatible with the two formal objects, i.e. so that there is a
morphism of formal objects `η ⟶ ξ` lying over the composite `A' ⟶ A'[[t₁, …, t_r]] ≅ A` (or
symmetrically).

The proof is the source's. Both `ξ` and `η` are pushed forward from a minimal versal formal object
`ξ₀` over `R`, along `R ⟶ R[[x₁, …, x_m]] ≅ A` and `R ⟶ R[[x₁, …, x_n]] ≅ A'` (**Stacks 06T3**,
**Stacks 06T5**). If `n ≤ m` then `A ≅ R[[x₁, …, x_n]][[x_{n+1}, …, x_m]] ≅ A'[[t₁, …, t_{m-n}]]`,
and the morphism `ξ₀ ⟶ ξ`, being over `R ⟶ A' ⟶ A`, factors through the strongly cocartesian
morphism `ξ₀ ⟶ η` over `R ⟶ A'` by a morphism `η ⟶ ξ` over `A' ⟶ A`.

## Main results

* `Deformation.exists_powerSeries_comparison_hom`: two versal formal objects of a predeformation
  category are related by a morphism over `A' ⟶ A'[[t₁, …, t_r]] ≅ A` or over
  `A ⟶ A[[t₁, …, t_r]] ≅ A'`.

## Implementation notes

The residue-field compatibility of the map `A' ⟶ A` is not computed on power series: any local
`Λ`-algebra map `h : A' ⟶ A` with `h ∘ g = f` for morphisms `g : R ⟶ A'` and `f : R ⟶ A` of
`\widehat{𝒞}_Λ` is compatible with the identifications of residue fields with `k`, because every
residue class of `A'` comes from `R` (`Deformation.CompleteLocalAlgCat.residue_comm_of_comp_eq`).

## References

* [Stacks Project, Tag 06T3](https://stacks.math.columbia.edu/tag/06T3)
* [Stacks Project, Tag 06T5](https://stacks.math.columbia.edu/tag/06T5)
* [Stacks Project, Tag 0DQX](https://stacks.math.columbia.edu/tag/0DQX)
* [Stacks Project, Tag 0DR1](https://stacks.math.columbia.edu/tag/0DR1)
-/

@[expose] public noncomputable section

namespace Deformation

open CategoryTheory IsLocalRing

universe u v w uF vF

/-! ### Power series ring isomorphisms -/

section PowerSeries

/-- A ring isomorphism of coefficient rings induces a ring isomorphism of power series rings. -/
def mvPowerSeriesRingEquivOfRingEquiv (σ : Type*) {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) : MvPowerSeries σ A ≃+* MvPowerSeries σ B :=
  RingEquiv.ofRingHom (MvPowerSeries.map e.toRingHom) (MvPowerSeries.map e.symm.toRingHom)
    (by rw [← MvPowerSeries.map_comp]; simp)
    (by rw [← MvPowerSeries.map_comp]; simp)

/-- The isomorphism `mvPowerSeriesRingEquivOfRingEquiv σ e` sends the constant `C a` to the
constant `C (e a)`. -/
@[simp]
theorem mvPowerSeriesRingEquivOfRingEquiv_C (σ : Type*) {A B : Type*} [CommRing A]
    [CommRing B] (e : A ≃+* B) (a : A) :
    mvPowerSeriesRingEquivOfRingEquiv σ e (MvPowerSeries.C a) = MvPowerSeries.C (e a) :=
  MvPowerSeries.map_C (σ := σ) e.toRingHom a

/-- The sum/curry isomorphism of power series rings sends a constant to the constant constant. -/
theorem mvps_sumCurry_C (σ τ A : Type*) [CommRing A] (a : A) :
    Stacks.NoetherianCompletion.mvps_sumCurry σ τ A (MvPowerSeries.C a) =
      MvPowerSeries.C (MvPowerSeries.C a) := by
  classical
  ext s t
  change (MvPowerSeries.C a : MvPowerSeries (σ ⊕ τ) A)
      (Finsupp.sumFinsuppAddEquivProdFinsupp.symm (s, t)) =
    MvPowerSeries.coeff t (MvPowerSeries.coeff s (MvPowerSeries.C (MvPowerSeries.C a)))
  rw [MvPowerSeries.coeff_C]
  change MvPowerSeries.coeff (Finsupp.sumFinsuppAddEquivProdFinsupp.symm (s, t))
      (MvPowerSeries.C a) = _
  rw [MvPowerSeries.coeff_C]
  have hz : Finsupp.sumFinsuppAddEquivProdFinsupp.symm (s, t) = 0 ↔ s = 0 ∧ t = 0 := by
    rw [← map_zero Finsupp.sumFinsuppAddEquivProdFinsupp.symm,
      Finsupp.sumFinsuppAddEquivProdFinsupp.symm.injective.eq_iff, Prod.mk_eq_zero]
  simp only [hz]
  split_ifs <;> simp_all [MvPowerSeries.coeff_C]

end PowerSeries

/-! ### Residue compatibility through a common source -/

namespace CompleteLocalAlgCat

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **A local map compatible with two morphisms out of a common source respects the residue
fields.** If `g : R ⟶ B` and `f : R ⟶ C` are morphisms of `\widehat{𝒞}_Λ` and `h : B → C` is a
local ring map with `h ∘ g = f`, then `h` is compatible with the identifications of the residue
fields of `B` and `C` with `k`: every residue class of `B` is the residue class of an element of
`R`, since all three residue fields are identified with `k`. -/
theorem residue_comm_of_comp_eq {R B C : CompleteLocalAlgCat.{u, v, w} Λ k}
    (g : R ⟶ B) (f : R ⟶ C) (h : B →+* C) [IsLocalHom h]
    (hgf : ∀ a : R, h (g.hom a) = f.hom a) (b : B) :
    C.residueEquiv (residue C (h b)) = B.residueEquiv (residue B b) := by
  obtain ⟨x, ha⟩ := R.residueEquiv.surjective (B.residueEquiv (residue B b))
  obtain ⟨a, rfl⟩ := residue_surjective x
  have hb : residue B (g.hom a) = residue B b :=
    B.residueEquiv.injective ((g.residue_comm a).trans ha)
  have hmem : b - g.hom a ∈ maximalIdeal B := by
    rw [← residue_eq_zero_iff, map_sub, hb, sub_self]
  have hres : residue C (h b) = residue C (f.hom a) := by
    rw [← hgf a, ← sub_eq_zero, ← map_sub, ← map_sub]
    exact (residue_eq_zero_iff _).mpr (map_nonunit h _ hmem)
  rw [hres, f.residue_comm a, ha]

end CompleteLocalAlgCat

/-! ### The comparison -/

section Comparison

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}

/-- A morphism of formal objects lies over its base map for the projection to complete local
algebras. -/
theorem FormalObject.isHomLift_projection_base {X Y : FormalObject p} (f : X ⟶ Y) :
    (FormalObject.projection (p := p)).IsHomLift f.base f :=
  IsHomLift.of_fac _ f.base f rfl rfl (FormalObject.projection_map f).symm

/-- If `A ≅ R[[x₁, …, x_m]]` and `B ≅ R[[x₁, …, x_n]]` compatibly with `f : R ⟶ A` and
`g : R ⟶ B`, and `n ≤ m`, then `A ≅ B[[t₁, …, t_{m-n}]]` compatibly with `f` and `g`. -/
private theorem exists_algEquiv_mvPowerSeries_of_le {R A B : CompleteLocalAlgCat.{u, v, w} Λ k}
    (f : R ⟶ A) (g : R ⟶ B) (m n : ℕ) (e : MvPowerSeries (Fin m) R ≃+* A)
    (he : ∀ a, e (MvPowerSeries.C a) = f.hom a) (e' : MvPowerSeries (Fin n) R ≃+* B)
    (he' : ∀ a, e' (MvPowerSeries.C a) = g.hom a) (hnm : n ≤ m) :
    ∃ E : A ≃ₐ[Λ] MvPowerSeries (Fin (m - n)) B, ∀ a, E (f.hom a) = MvPowerSeries.C (g.hom a) := by
  let σ : Fin m ≃ Fin (m - n) ⊕ Fin n :=
    (finCongr (by omega : m = (m - n) + n)).trans finSumFinEquiv.symm
  let E₀ : A ≃+* MvPowerSeries (Fin (m - n)) B :=
    e.symm.trans ((MvPowerSeries.renameEquiv R σ).toRingEquiv.trans
      ((Stacks.NoetherianCompletion.mvps_sumCurry (Fin (m - n)) (Fin n) R).trans
        (mvPowerSeriesRingEquivOfRingEquiv (Fin (m - n)) e')))
  have key : ∀ a : R, E₀ (f.hom a) = MvPowerSeries.C (g.hom a) := by
    intro a
    have hren : (MvPowerSeries.renameEquiv R σ) (MvPowerSeries.C a) = MvPowerSeries.C a :=
      (MvPowerSeries.renameEquiv R σ).commutes a
    change mvPowerSeriesRingEquivOfRingEquiv (Fin (m - n)) e'
        (Stacks.NoetherianCompletion.mvps_sumCurry (Fin (m - n)) (Fin n) R
          ((MvPowerSeries.renameEquiv R σ) (e.symm (f.hom a)))) = _
    rw [← he a, e.symm_apply_apply, hren, mvps_sumCurry_C, mvPowerSeriesRingEquivOfRingEquiv_C,
      he' a]
  have hcomm : ∀ c : Λ, E₀ (algebraMap Λ A c) =
      algebraMap Λ (MvPowerSeries (Fin (m - n)) B) c := by
    intro c
    rw [← f.hom.commutes c, key, g.hom.commutes c, MvPowerSeries.algebraMap_apply]
  exact ⟨AlgEquiv.ofRingEquiv hcomm, fun a => by rw [AlgEquiv.ofRingEquiv_apply, key]⟩

/-- The one-sided comparison: two formal objects pushed forward from a common formal object
`ξ₀` along `R ⟶ R[[x₁, …, x_m]] ≅ A` and along `R ⟶ R[[x₁, …, x_n]] ≅ A'`, the second strongly
cocartesian, with `n ≤ m`, are related by a morphism over `A' ⟶ A'[[t₁, …, t_{m-n}]] ≅ A`. -/
theorem exists_powerSeries_comparison_hom_of_le (ξ η ξ₀ : FormalObject p)
    (f : ξ₀ ⟶ ξ) (g : ξ₀ ⟶ η)
    (hg : (FormalObject.projection (p := p)).IsStronglyCocartesian g.base g)
    (m n : ℕ) (e : MvPowerSeries (Fin m) ξ₀.base ≃+* ξ.base)
    (he : ∀ a, e (MvPowerSeries.C a) = f.base.hom a)
    (e' : MvPowerSeries (Fin n) ξ₀.base ≃+* η.base)
    (he' : ∀ a, e' (MvPowerSeries.C a) = g.base.hom a) (hnm : n ≤ m) :
    ∃ E : ξ.base ≃ₐ[Λ] MvPowerSeries (Fin (m - n)) η.base, ∃ φ : η ⟶ ξ,
      ∀ b, E (φ.base.hom b) = MvPowerSeries.C b := by
  obtain ⟨E, key⟩ := exists_algEquiv_mvPowerSeries_of_le f.base g.base m n e he e' he' hnm
  let hRing : η.base →+* ξ.base := E.symm.toRingEquiv.toRingHom.comp MvPowerSeries.C
  have hE : ∀ b, E (hRing b) = MvPowerSeries.C b := fun b => E.apply_symm_apply _
  have hloc : IsLocalHom hRing := by
    refine ⟨fun b hb => ?_⟩
    have h1 : IsUnit (MvPowerSeries.C (σ := Fin (m - n)) b) := by
      rw [← hE b]
      exact hb.map E
    simpa using MvPowerSeries.isUnit_iff_constantCoeff.mp h1
  have hgf : ∀ a : ξ₀.base, hRing (g.base.hom a) = f.base.hom a := fun a =>
    E.injective (by rw [hE, key])
  let hAlg : η.base →ₐ[Λ] ξ.base :=
    { hRing with
      commutes' := fun c => by
        apply E.injective
        change E (hRing (algebraMap Λ η.base c)) = _
        rw [hE, E.commutes, MvPowerSeries.algebraMap_apply] }
  let hHom : η.base ⟶ ξ.base :=
    { hom := hAlg
      isLocal := hloc
      residue_comm := CompleteLocalAlgCat.residue_comm_of_comp_eq g.base f.base hRing hgf }
  have hfac : f.base = g.base ≫ hHom :=
    CompleteLocalAlgCat.Hom.ext (AlgHom.ext fun a => (hgf a).symm)
  have := FormalObject.isHomLift_projection_base f
  let φ : η ⟶ ξ := Functor.IsStronglyCocartesian.map (FormalObject.projection (p := p))
    g.base g hfac f
  have hφ : hHom = φ.base := IsHomLift.eq_of_isHomLift (FormalObject.projection (p := p)) hHom φ
  exact ⟨E, φ, fun b => by rw [← hφ]; exact hE b⟩

/-- **Two versal formal objects are related by a morphism over a power series extension of one
base by the other** (the formal-object form of **Stacks 0DQX**, as upgraded by **Stacks 0DR1**,
part (1)). If `ξ` and `η` are versal formal objects of a predeformation category, then either there
are an isomorphism `E : ξ.base ≅ η.base[[t₁, …, t_r]]` of `Λ`-algebras and a morphism `η ⟶ ξ`
whose base map is `η.base ⟶ η.base[[t₁, …, t_r]] ≅ ξ.base`, or the same with `ξ` and `η`
exchanged. -/
theorem exists_powerSeries_comparison_hom [IsNoetherianRing Λ] [Module.Finite Λ k]
    (hp : IsPredeformationCategory p) (ξ η : FormalObject p)
    (hξ : IsVersal hp.cofibered ξ) (hη : IsVersal hp.cofibered η) :
    (∃ r : ℕ, ∃ E : ξ.base ≃ₐ[Λ] MvPowerSeries (Fin r) η.base, ∃ φ : η ⟶ ξ,
      ∀ b, E (φ.base.hom b) = MvPowerSeries.C b) ∨
    (∃ r : ℕ, ∃ E : η.base ≃ₐ[Λ] MvPowerSeries (Fin r) ξ.base, ∃ φ : ξ ⟶ η,
      ∀ b, E (φ.base.hom b) = MvPowerSeries.C b) := by
  obtain ⟨ξ₀, f, hξ₀, hf, m, e, he⟩ := exists_minimalVersal_powerSeries hp ξ hξ
  obtain ⟨η₀, g, hη₀, hg, n, e', he'⟩ := exists_minimalVersal_powerSeries hp η hη
  obtain ⟨j⟩ := isomorphic_of_isMinimalVersal hp ξ₀ η₀ hξ₀ hη₀
  have := hg
  have := FormalObject.isHomLift_projection_base j.hom
  have hg₁ : (FormalObject.projection (p := p)).IsStronglyCocartesian (j.hom ≫ g).base
      (j.hom ≫ g) := by
    change (FormalObject.projection (p := p)).IsStronglyCocartesian (j.hom.base ≫ g.base)
      (j.hom ≫ g)
    infer_instance
  let j₀ : ξ₀.base ≃+* η₀.base :=
    RingEquiv.ofRingHom j.hom.base.hom.toRingHom j.inv.base.hom.toRingHom
      (by
        ext a
        exact DFunLike.congr_fun (congrArg (fun φ => φ.base.hom) j.inv_hom_id) a)
      (by
        ext a
        exact DFunLike.congr_fun (congrArg (fun φ => φ.base.hom) j.hom_inv_id) a)
  let e₁ : MvPowerSeries (Fin n) ξ₀.base ≃+* η.base :=
    (mvPowerSeriesRingEquivOfRingEquiv (Fin n) j₀).trans e'.toRingEquiv
  have he₁ : ∀ a, e₁ (MvPowerSeries.C a) = (j.hom ≫ g).base.hom a := by
    intro a
    change e' (mvPowerSeriesRingEquivOfRingEquiv (Fin n) j₀ (MvPowerSeries.C a)) = _
    rw [mvPowerSeriesRingEquivOfRingEquiv_C, he']
    rfl
  rcases le_total n m with hnm | hmn
  · obtain ⟨E, φ, hE⟩ := exists_powerSeries_comparison_hom_of_le ξ η ξ₀ f (j.hom ≫ g) hg₁ m n
      e.toRingEquiv he e₁ he₁ hnm
    exact Or.inl ⟨m - n, E, φ, hE⟩
  · obtain ⟨E, φ, hE⟩ := exists_powerSeries_comparison_hom_of_le η ξ ξ₀ (j.hom ≫ g) f hf n m
      e₁ he₁ e.toRingEquiv he hmn
    exact Or.inr ⟨n - m, E, φ, hE⟩

end Comparison

end Deformation

end
