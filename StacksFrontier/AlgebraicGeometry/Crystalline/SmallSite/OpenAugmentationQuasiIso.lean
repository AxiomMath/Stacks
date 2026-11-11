module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialTotalRowZero
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechColumnQuasiIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechResolutionOpen07Q9

/-!
# The restriction of the sections over an open to the degree-zero member of a Čech system

Fix a global crystalline situation `(p, (S, I, γ), X)`, an open `W` of `X` and a cosimplicial
system `T(n)_e` of objects of `Cris(X/S)` which is a pro-covering of `W`
(`...SmallSite.IsOpenProCovering`).  For a complex `J^•` of injective abelian sheaves on
`Cris(X/S)` the **restriction**

`ρ : Γ(W, u_{X/S, *}J^•) ⟶ lim_e J^•(T(0)_e)`

(`...SmallSite.openAugmentationNat`, whose projection to the level `e` is the restriction
`...SmallSite.zariskiDirectImageEval` of a section over `W` to the object `T(0)_e` lying over
`W`) is the composite of the quasi-isomorphism `...SmallSite.cechAugmentationOpen` into the total
complex of the Čech double complex `(n, a) ↦ lim_e J^a(T(n)_e)` with the projection of that total
complex onto its Čech degree zero (`Crystalline.cosimplicialFlipTotalToRowZero`)
(`cechAugmentationOpen_comp_cosimplicialFlipTotalToRowZero`).  So `ρ` is a quasi-isomorphism as
soon as every codiagonal `lim_e J^•(T(b)_e) ⟶ lim_e J^•(T(0)_e)` is one
(`quasiIso_openAugmentationNat`).

This is the map-level form of the proof of [Stacks, Proposition 60.21.3, Tag 07LG] used in
[Stacks, Tag 07MW]: for `J` an injective resolution of the de Rham complex
`K = F ⊗ Ω^•_{X/S}` of a crystal, the Čech columns `lim_e K^•(T(b)_e)` are the completed de Rham
complexes `M(b) ⊗^∧_{D(b)} Ω^•_{D(b)}`, whose coprojections are quasi-isomorphisms by
[Stacks, Lemma 60.21.2, Tag 07LD]; restriction to `T(0)` is then a quasi-isomorphism onto the row
zero `M ⊗^∧_D Ω^•_D`.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `cechAugmentationOpen_comp_cosimplicialFlipTotalToRowZero` — **`ρ` is the Čech comparison
  followed by the projection onto the Čech degree zero.**
* `quasiIso_openAugmentationNat` — **`ρ` is a quasi-isomorphism** when every codiagonal of the
  Čech columns of `J` is one.
* `quasiIso_openAugmentationNat_of_rows` — the same, the hypothesis being read on a complex `K`
  mapping to `J` by a morphism which is a quasi-isomorphism on every Čech column: every
  coprojection `lim_e K^•(T(0)_e) ⟶ lim_e K^•(T(b)_e)` is a quasi-isomorphism.
* **`quasiIso_openAugmentationNat_of_quasiIso`** — for `φ : K^• ⟶ J^•` a quasi-isomorphism onto
  a complex of injectives, `K^•` having vanishing higher cohomology and surjective transitions at
  the levels of `T`: if every coprojection of the Čech columns of `K^•` is a quasi-isomorphism,
  then both maps of the roof
  `Γ(W, u_{X/S, *}J^•) ⟶ lim_e J^•(T(0)_e) ⟵ lim_e K^•(T(0)_e)`
  are quasi-isomorphisms; the roof commutes with `Γ(W, u_{X/S, *}φ)` by
  `...SmallSite.openAugmentationNat_naturality`.

## What is and is not proved

Nothing here is specific to the de Rham complex: the hypotheses are the quasi-isomorphy of the
codiagonals (or coprojections) of the Čech columns.  For the de Rham complex of a crystal that
hypothesis is the sheaf-side form of [Stacks, Lemma 60.21.2, Tag 07LD], which needs the
identification of `lim_e (F ⊗ Ω^•_{X/S})(T(b)_e)` with the completed de Rham complex of the
cosimplicial pair of the crystal, differentials included; that identification is **not** in the
library and is not proved here.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} {W : S.X.Opens}
  {T : SimplicialObject (ℕ ⥤ CrystallineThickening S)}

/-- **The restriction to `T(0)` is the Čech comparison followed by the projection onto the Čech
degree zero**: `ρ = pr₀ ∘ cechAugmentationOpen`, after extending `ρ` from `ℕ` to `ℤ`. -/
theorem cechAugmentationOpen_comp_cosimplicialFlipTotalToRowZero (hT : IsOpenProCovering S W T)
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ)
    [∀ a, Injective (K.X a)] :
    cechAugmentationOpen hT K ≫
        cosimplicialFlipTotalToRowZero ((cechCosimplicialComplex T).obj K) =
      HomologicalComplex.extendMap (openAugmentationNat hT K) ComplexShape.embeddingUpNat := by
  let Kc := (cechCosimplicialComplex T).obj K
  ext n : 1
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn
    have h1 : ((cechDoubleComplex T).obj K).ιTotal (ComplexShape.up ℤ) 0 n n (by simp) ≫
        (cosimplicialFlipTotalToRowZero Kc).f n =
        (cosimplicialDoubleComplexRowIso Kc 0).hom.f n :=
      ιTotal_cosimplicialFlipTotalToRowZero_f Kc n
    have h2 : (cosimplicialDoubleComplexRowIso Kc 0).inv.f n ≫
        (cosimplicialDoubleComplexRowIso Kc 0).hom.f n = 𝟙 _ :=
      congrArg (fun φ => HomologicalComplex.Hom.f φ (n : ℤ))
        (Iso.inv_hom_id (cosimplicialDoubleComplexRowIso Kc 0))
    refine (HomologicalComplex.comp_f _ _ _).trans ?_
    refine ((congrArg (· ≫ (cosimplicialFlipTotalToRowZero Kc).f n)
      (cechAugmentationOpen_f hT K n)).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h1))).trans ?_
    exact (congrArg (· ≫ (cosimplicialDoubleComplexRowIso Kc 0).hom.f n)
      (HomologicalComplex.comp_f (HomologicalComplex.extendMap (openAugmentationNat hT K)
        ComplexShape.embeddingUpNat) (cosimplicialDoubleComplexRowIso Kc 0).inv n)).trans
          ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h2).trans (Category.comp_id _)))
  · exact (HomologicalComplex.isZero_extend_X _ _ _
      (fun i hi => by simp only [ComplexShape.embeddingUpNat_f] at hi; omega)).eq_of_src _ _

/-- **The restriction `Γ(W, u_{X/S, *}J^•) ⟶ lim_e J^•(T(0)_e)` is a quasi-isomorphism** for a
complex `J^•` of injective abelian sheaves, as soon as every codiagonal
`lim_e J^•(T(b)_e) ⟶ lim_e J^•(T(0)_e)` of its Čech columns is one. -/
theorem quasiIso_openAugmentationNat (hT : IsOpenProCovering S W T)
    (J : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ)
    [∀ a, Injective (J.X a)]
    (h : ∀ b : ℕ, QuasiIso (cosimplicialRowMap
      (cosimplicialCodiagonal ((cechCosimplicialComplex T).obj J)) b)) :
    QuasiIso (openAugmentationNat hT J) := by
  have := quasiIso_cosimplicialFlipTotalToRowZero _ h
  have : QuasiIso (HomologicalComplex.extendMap (openAugmentationNat hT J)
      ComplexShape.embeddingUpNat) := by
    rw [← cechAugmentationOpen_comp_cosimplicialFlipTotalToRowZero]
    exact quasiIso_comp _ _ (hφ := quasiIso_cechAugmentationOpen hT J) (hφ' := this)
  exact (HomologicalComplex.quasiIso_extendMap_iff _ _).1 this

/-- **The restriction `Γ(W, u_{X/S, *}J^•) ⟶ lim_e J^•(T(0)_e)` is a quasi-isomorphism**, read on a
complex `K^•` mapping to `J^•`: if `φ : K^• ⟶ J^•` induces a quasi-isomorphism
`lim_e K^•(T(b)_e) ⟶ lim_e J^•(T(b)_e)` on every Čech column and every coprojection
`lim_e K^•(T(0)_e) ⟶ lim_e K^•(T(b)_e)` (induced by `⦋0⦌ ⟶ ⦋b⦌, 0 ↦ 0`) is a quasi-isomorphism,
then the restriction is one. -/
theorem quasiIso_openAugmentationNat_of_rows (hT : IsOpenProCovering S W T)
    {K J : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ} (φ : K ⟶ J)
    [∀ a, Injective (J.X a)]
    (hφ : ∀ b : ℕ, QuasiIso (cosimplicialRowMap ((cechCosimplicialComplex T).map φ) b))
    (hK : ∀ b : ℕ, QuasiIso
      (cosimplicialRowCoprojection ((cechCosimplicialComplex T).obj K) b)) :
    QuasiIso (openAugmentationNat hT J) :=
  quasiIso_openAugmentationNat hT J fun b =>
    quasiIso_cosimplicialRowMap_cosimplicialCodiagonal_of_rows _ hφ b
      ((quasiIso_cosimplicialRowMap_cosimplicialCodiagonal_iff _ b).2 (hK b))

/-- **The restriction to `T(0)` is a quasi-isomorphism onto the sections of `K^•` over `T(0)`.**

Let `φ : K^• ⟶ J^•` be a quasi-isomorphism of complexes of abelian sheaves on `Cris(X/S)`, with
`J^•` termwise injective and `K^•` termwise with vanishing higher cohomology and surjective
transition maps at the levels of `T`.  If every coprojection
`lim_e K^•(T(0)_e) ⟶ lim_e K^•(T(b)_e)` is a quasi-isomorphism, then

* the restriction `Γ(W, u_{X/S, *}J^•) ⟶ lim_e J^•(T(0)_e)` is a quasi-isomorphism, and
* the map `lim_e K^•(T(0)_e) ⟶ lim_e J^•(T(0)_e)` induced by `φ` is a quasi-isomorphism,

so that `Γ(W, u_{X/S, *}J^•) ≅ lim_e K^•(T(0)_e)` in the derived category through restriction. -/
theorem quasiIso_openAugmentationNat_of_quasiIso (hT : IsOpenProCovering S W T)
    (hTm : HasAffineMonoLevels T)
    {K J : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ} (φ : K ⟶ J)
    [QuasiIso φ] [∀ a, Injective (J.X a)]
    (hK : ∀ a, VanishingOnLevels07Q9 T (K.X a))
    (hKs : ∀ a, HasSurjectiveLevelTransitions T (K.X a))
    (hcop : ∀ b : ℕ, QuasiIso
      (cosimplicialRowCoprojection ((cechCosimplicialComplex T).obj K) b)) :
    QuasiIso (openAugmentationNat hT J) ∧
      QuasiIso (cosimplicialRowMap ((cechCosimplicialComplex T).map φ) 0) :=
  ⟨quasiIso_openAugmentationNat_of_rows hT φ
      (quasiIso_cosimplicialRowMap_cechCosimplicialComplex_map hTm φ hK hKs) hcop,
    quasiIso_cosimplicialRowMap_cechCosimplicialComplex_map hTm φ hK hKs 0⟩

end Crystalline.GlobalCrystallineSituation.SmallSite

end
