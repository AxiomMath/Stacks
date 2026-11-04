module

public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineOver
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ProperKernelPairColimit

/-!
# Descent of morphisms to affine targets from an equalizer of global functions

Condition (2) of Stacks 0GHL, for the Čech cocone of `p : Y ⟶ X'`, asks that morphisms from the
terms of a compatible étale diagram `E` to an affine `Z` over an affine `B'` descend uniquely to
the total space `U` of an affine realization of `E`. The source reduces it to a statement about
global functions through Properties of Spaces, Lemma 66.33.1 (the relative form of Stacks 05Z1,
`AlgebraicGeometry.Space.morphismToAffineOverEquiv`): morphisms to `Z` over `B'` are
`Γ(B')`-algebra homomorphisms `Γ(Z) ⟶ Γ(-)`. This file carries out that reduction: if
`Γ(U) ⟶ Γ(E₀) ⇉ Γ(E₁)` is an equalizer of rings, morphisms to affine targets descend.

## Main definitions

* `AlgebraicGeometry.Space.GlobalFunctionsEqualizer`: the statement that pullback of global
  functions along `q : E₀ ⟶ U` is injective with image the functions on which the two pullbacks
  along `d₀, d₁ : E₁ ⟶ E₀` agree.

## Main results

* `AlgebraicGeometry.Space.existsUnique_descend_of_globalFunctionsEqualizer`: morphisms to an
  affine space over an affine space descend along `q`.
* `AlgebraicGeometry.Space.cechAffineDescent_of_globalFunctionsEqualizer`: condition (2) of
  Stacks 0GHL for the Čech cocone of `p`, from the equalizer of global functions over every
  affine realization.

## References

* [Stacks Project, Tag 0GHL](https://stacks.math.columbia.edu/tag/0GHL)
* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
* [Stacks Project, Tag 0AGG](https://stacks.math.columbia.edu/tag/0AGG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **`Γ(U) ⟶ Γ(E₀) ⇉ Γ(E₁)` is an equalizer of rings**: pullback of global functions along
`q : E₀ ⟶ U` is injective, and a global function on `E₀` whose pullbacks along `d₀` and `d₁`
agree comes from `U`. -/
def GlobalFunctionsEqualizer {U E₀ E₁ : AlgebraicSpaces B S hS} (q : E₀ ⟶ U)
    (d₀ d₁ : E₁ ⟶ E₀) : Prop :=
  Function.Injective (globalFunctionsMap B S hS q) ∧
    ∀ s, globalFunctionsMap B S hS d₀ s = globalFunctionsMap B S hS d₁ s →
      ∃ t, globalFunctionsMap B S hS q t = s

section Descend

variable {U E₀ E₁ : AlgebraicSpaces B S hS} {q : E₀ ⟶ U} {d₀ d₁ : E₁ ⟶ E₀}
  (hG : GlobalFunctionsEqualizer q d₀ d₁)

include hG in
/-- **Morphisms to an affine object over an affine object descend along `q`**, when
`Γ(U) ⟶ Γ(E₀) ⇉ Γ(E₁)` is an equalizer: a morphism `f₀ : E₀ ⟶ W` over `V` equalizing `d₀` and
`d₁` is `q ≫ f` for a unique `f : U ⟶ W` over `V`. -/
theorem existsUnique_descend_of_globalFunctionsEqualizer {V W : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] (w : W ⟶ V) (u : U ⟶ schemeSpace V)
    (f₀ : E₀ ⟶ schemeSpace W) (hf₀ : f₀ ≫ schemeSpaceMap w = q ≫ u)
    (hd : d₀ ≫ f₀ = d₁ ≫ f₀) :
    ∃! f : U ⟶ schemeSpace W, f ≫ schemeSpaceMap w = u ∧ q ≫ f = f₀ := by
  let qs := globalFunctionsMap B S hS q
  let φ₀ := pullbackToGlobalFunctions B S hS E₀ W f₀
  have hφ₀ : ∀ s, φ₀ s ∈ qs.range := fun s => RingHom.mem_range.2 <| hG.2 (φ₀ s)
    (congrArg (fun k => k s) ((pullbackToGlobalFunctions_comp_left B S hS d₀ W f₀).symm.trans
      ((congrArg (pullbackToGlobalFunctions B S hS E₁ W) hd).trans
        (pullbackToGlobalFunctions_comp_left B S hS d₁ W f₀))))
  let e := RingEquiv.ofBijective qs.rangeRestrict
    ⟨fun a b h => hG.1 (congrArg Subtype.val h), qs.rangeRestrict_surjective⟩
  have he : ∀ x, qs (e.symm x) = x.val := fun x => congrArg Subtype.val (e.apply_symm_apply x)
  let φ : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) →+* globalFunctions B S hS U.1 :=
    e.symm.toRingHom.comp (φ₀.codRestrict qs.range hφ₀)
  have hqφ : qs.comp φ = φ₀ := RingHom.ext fun s => he ⟨φ₀ s, hφ₀ s⟩
  have hφw : φ.comp (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map w).op).hom =
      pullbackToGlobalFunctions B S hS U V u := by
    refine RingHom.ext fun s => hG.1 ?_
    have h1 := congrArg (fun k => k s) (pullbackToGlobalFunctions_comp_left B S hS q V u)
    have h2 := congrArg (fun k => k s)
      (pullbackToGlobalFunctions_comp_schemeSpaceMap_eq_comp B S hS E₀ w f₀)
    have h3 := congrArg (fun k => k s)
      (congrArg (pullbackToGlobalFunctions B S hS E₀ V) hf₀)
    have h4 := congrArg (fun k => k ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map w).op).hom
      s)) hqφ
    exact h4.trans (h2.symm.trans (h3.trans h1))
  obtain ⟨⟨f, hfw⟩, hf⟩ := ((morphismToAffineOverEquiv B S hS U w u).1).surjective ⟨φ, hφw⟩
  have hfφ : pullbackToGlobalFunctions B S hS U W f = φ :=
    ((morphismToAffineOverEquiv B S hS U w u).2 ⟨f, hfw⟩).symm.trans
      (congrArg Subtype.val hf)
  have hqf : q ≫ f = f₀ := by
    refine pullbackToGlobalFunctions_injective B S hS E₀ W ?_
    rw [pullbackToGlobalFunctions_comp_left, hfφ, hqφ]
  refine ⟨f, ⟨hfw, hqf⟩, fun f' ⟨_, hf'q⟩ => ?_⟩
  refine pullbackToGlobalFunctions_injective B S hS U W ?_
  refine RingHom.ext fun s => hG.1 ?_
  have h1 := congrArg (fun k => k s) (pullbackToGlobalFunctions_comp_left B S hS q W f')
  have h2 := congrArg (fun k => k s) (pullbackToGlobalFunctions_comp_left B S hS q W f)
  have h3 := congrArg (fun k => pullbackToGlobalFunctions B S hS E₀ W k s) (hf'q.trans hqf.symm)
  exact h1.symm.trans (h3.trans h2)

end Descend

/-! ### Condition (2) of Stacks 0GHL for the Čech cocone -/

section Cech

variable {X Y B₀ : AlgebraicSpaces B S hS} {p : Y ⟶ X} {ν : X ⟶ B₀}

/-- The isomorphism of algebraic spaces attached to an isomorphism of a presheaf with a
representable one. -/
def isoSchemeSpace {F : AlgebraicSpaces B S hS} {V : BigFppfOver B S hS}
    (e : F.obj ≅ yoneda.obj V) : F ≅ schemeSpace V where
  hom := ObjectProperty.homMk e.hom
  inv := ObjectProperty.homMk e.inv
  hom_inv_id := ObjectProperty.hom_ext _ e.hom_inv_id
  inv_hom_id := ObjectProperty.hom_ext _ e.inv_hom_id

/-- **Condition (2) of Stacks 0GHL for the Čech cocone of `p`, from an equalizer of global
functions**: if for every affine realization `r` of a compatible étale diagram `E` over the Čech
nerve lying over an affine `B'` étale over `B₀`, `Γ(r.U) ⟶ Γ(E₀) ⇉ Γ(E₁)` is an equalizer, then
morphisms to affine targets descend. -/
theorem cechAffineDescent_of_globalFunctionsEqualizer
    (hG : ∀ (B' : AlgebraicSpaces B S hS) (b : B' ⟶ B₀), IsAffineSpace B S hS B'.1 →
      IsEtale B S hS b.hom → ∀ (E : CompatibleEtaleDiagram B S hS (cechDiagram p ν))
      (r : EtaleRealization B S hS (cechCocone p ν) E), IsAffineSpace B S hS r.U.1 →
      ∀ (u : r.U ⟶ B'), r.toX ≫ ν = u ≫ b →
        GlobalFunctionsEqualizer (r.baseChange.app (op ⦋0⦌))
          (E.U.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op)
          (E.U.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).op)) :
    CechAffineDescent p ν := by
  intro B' b hB' hb Z z hZ E r hr u hu fᵢ hfᵢ
  have hGr := hG B' b hB' hb E r hr u hu
  obtain ⟨V, hV, ⟨eB⟩⟩ := hB'
  obtain ⟨W, hW, ⟨eZ⟩⟩ := hZ
  let iB := isoSchemeSpace eB
  let iZ := isoSchemeSpace eZ
  let w : W ⟶ V := yoneda.preimage (eZ.inv ≫ z.hom ≫ eB.hom)
  have hw : schemeSpaceMap w = iZ.inv ≫ z ≫ iB.hom :=
    ObjectProperty.hom_ext _ (yoneda.map_preimage _)
  have hzw : iZ.inv ≫ z = schemeSpaceMap w ≫ iB.inv := by
    rw [hw, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  -- the vertex maps of the Čech nerve
  have hbc (n : SimplexCategoryᵒᵖ) : r.baseChange.app n =
      E.U.map (SimplexCategory.const ⦋0⦌ n.unop 0).op ≫ r.baseChange.app (op ⦋0⦌) :=
    ((r.baseChange.naturality (SimplexCategory.const ⦋0⦌ n.unop 0).op).trans
      (Category.comp_id _)).symm
  have hfn (n : SimplexCategoryᵒᵖ) : fᵢ.app n =
      E.U.map (SimplexCategory.const ⦋0⦌ n.unop 0).op ≫ fᵢ.app (op ⦋0⦌) :=
    ((fᵢ.naturality (SimplexCategory.const ⦋0⦌ n.unop 0).op).trans (Category.comp_id _)).symm
  have hd : E.U.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op ≫ fᵢ.app (op ⦋0⦌) ≫ iZ.hom =
      E.U.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).op ≫ fᵢ.app (op ⦋0⦌) ≫ iZ.hom := by
    rw [← Category.assoc, ← Category.assoc,
      (fᵢ.naturality (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op).trans (Category.comp_id _),
      (fᵢ.naturality (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).op).trans (Category.comp_id _)]
  have hf₀ : (fᵢ.app (op ⦋0⦌) ≫ iZ.hom) ≫ schemeSpaceMap w =
      r.baseChange.app (op ⦋0⦌) ≫ u ≫ iB.hom := by
    rw [hw, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, hfᵢ, Category.assoc]
  obtain ⟨f', ⟨hf'w, hf'q⟩, huniq⟩ := existsUnique_descend_of_globalFunctionsEqualizer
    hGr w (u ≫ iB.hom) (fᵢ.app (op ⦋0⦌) ≫ iZ.hom) hf₀ hd
  refine ⟨f' ≫ iZ.inv, ⟨?_, fun n => ?_⟩, fun g ⟨hgz, hgn⟩ => ?_⟩
  · rw [Category.assoc, hzw, ← Category.assoc, hf'w, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  · rw [hbc n, hfn n, Category.assoc, ← Category.assoc _ f', hf'q, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  · have hg := huniq (g ≫ iZ.hom) ⟨by rw [hw, Category.assoc, Iso.hom_inv_id_assoc,
      ← Category.assoc, hgz], by rw [← Category.assoc, hgn]⟩
    rw [← hg, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Cech

/-! ### Stacks 0AGG from étale descent and the equalizer of global functions -/

variable (B S hS) in
/-- **The equalizer of global functions over the affine realizations of the Čech nerve of
`π : Y ⟶ X'`** (the content of the last paragraph of the proof of Stacks 0AGG): for `g : Y ⟶ X`
proper onto a locally Noetherian `X`, every affine `B'` étale over `X`, every compatible étale
diagram `E` over the Čech nerve of `π` and every affine realization `r` of `E` over `B'`,
`Γ(r.U) ⟶ Γ(E₀) ⇉ Γ(E₁)` is an equalizer. -/
def KernelPairSpecGlobalFunctionsEqualizer : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X),
    HasEtaleLocalProperty B S hS X.obj (fun W : Scheme.{u} => IsLocallyNoetherian W) →
    ∀ hg : IsProper B S hS g.hom,
    ∀ (B' : AlgebraicSpaces B S hS) (b : B' ⟶ X), IsAffineSpace B S hS B'.1 →
      IsEtale B S hS b.hom →
      ∀ (E : CompatibleEtaleDiagram B S hS
          (cechDiagram (kernelPairSpecπ hg) (kernelPairSpecToTarget hg)))
        (r : EtaleRealization B S hS
          (cechCocone (kernelPairSpecπ hg) (kernelPairSpecToTarget hg)) E),
        IsAffineSpace B S hS r.U.1 →
        ∀ (u : r.U ⟶ B'), r.toX ≫ kernelPairSpecToTarget hg = u ≫ b →
          GlobalFunctionsEqualizer (r.baseChange.app (op ⦋0⦌))
            (E.U.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op)
            (E.U.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).op)

/-- **Stacks 0AGG**, from étale descent of algebraic spaces along proper surjective morphisms
(`h`, condition (1) of Stacks 0GHL) and the equalizer of global functions over the affine
realizations of the Čech nerve (`hG`, which gives condition (2) of Stacks 0GHL through the
relative form of Stacks 05Z1). -/
theorem properKernelPairCoequalizers_of_etaleSpaceDescent_of_globalFunctionsEqualizer
    (h : EtaleSpaceDescentAlongProperSurjective B S hS)
    (hG : KernelPairSpecGlobalFunctionsEqualizer B S hS) :
    ProperKernelPairCoequalizers B S hS :=
  properKernelPairCoequalizers_of_isColimit_kernelPairSpecCofork B S hS fun g hX hg =>
    isColimit_kernelPairSpecCofork_of_cechAffineDescent h hg hX
      (cechAffineDescent_of_globalFunctionsEqualizer (hG g hX hg))

end AlgebraicGeometry.Space

end
