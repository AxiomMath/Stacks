module

public import StacksFrontier.AlgebraicGeometry.AmplePullbackPart1.TensorPowerTensor
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjDegreeOpenRepresents
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleVeroneseRestrict

/-!
# The morphism to `Proj` classified by a triple

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring and `X = Proj(A)`. A *triple* over a scheme `Y` is an
integer `d ≥ 1`, an invertible `𝒪_Y`-module `L` and a graded ring map
`ψ : A^{(d)} ⟶ Γ_*(Y, L)` whose degree-`d` values generate `L`. [Stacks, Tag 01N8] attaches to a
triple a unique pair `(φ, α)` with `φ : Y ⟶ U_d` and `α : φ⁎𝒪_X(d) ≅ L` compatible with `ψ`, and
the *classified morphism* of the triple is `φ` read into `X`.

This file defines the classified morphism, the condition that two triples classify the same
morphism `Y ⟶ X` (clause (4) of [Stacks, Tag 01NB]), and proves that strictly equivalent triples
classify the same morphism.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTripleClassifying.Triple`: a triple `(d, L, ψ)` over `Y`, bundled
  with `d ≥ 1` and the generation condition.
* `Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom`: the morphism `Y ⟶ U_d` of the
  unique pair of [Stacks, Tag 01N8].
* `Stacks.AlgebraicGeometry.ProjTripleClassifying.Triple.classifyingMorphism`: the morphism
  `Y ⟶ X` classified by a triple, that morphism composed with the open immersion `U_d ⟶ X`.
* `Stacks.AlgebraicGeometry.ProjTripleClassifying.Triple.veroneseRestrict`: the Veronese
  restriction `(kd, L^{⊗ k}, ψ|_{A^{(kd)}})` of a triple at a weight `k ≥ 1`.
* `Stacks.AlgebraicGeometry.ProjTripleClassifying.SameMorphism`: the condition that two triples
  classify one and the same morphism `Y ⟶ X`.
* `Stacks.AlgebraicGeometry.ProjTripleClassifying.SectionsEquiv`: strict equivalence of two graded
  maps of the same weight `d`, an isomorphism `β : L ≅ L'` carrying `ψ` to `ψ'` degreewise.

## Main results

* `Stacks.AlgebraicGeometry.ProjTripleClassifying.isCompatible_classifyingPair` and
  `Stacks.AlgebraicGeometry.ProjTripleClassifying.eq_classifyingPair_of_isCompatible`: the chosen
  pair is compatible with `ψ`, and it is the only compatible pair.
* `Stacks.AlgebraicGeometry.ProjTripleClassifying.isCompatible_of_sectionsEquiv`: a pair
  compatible with `ψ'` is, after composing `α` with `β⁻¹`, compatible with `ψ`.
* `Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom_eq_of_sectionsEquiv`: strictly
  equivalent triples classify the same morphism.
* `Stacks.AlgebraicGeometry.ProjTripleClassifying.natTensorPowCongr_pow`: an isomorphism matching
  two graded maps in degrees `0` and `1` matches their powers `ψ(f)^n` in every degree.

## Implementation notes

Triples are stated with `Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections`, the
spelling of `ψ : A^{(d)} ⟶ Γ_*(Y, L)` that
`Stacks.AlgebraicGeometry.MorphismToProjUniversal.existsUnique_pair` consumes; the other spellings
of a triple in the library have no multiplicative comparison with it.

## References

* [Stacks Project, Tag 01NB](https://stacks.math.columbia.edu/tag/01NB)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01N9](https://stacks.math.columbia.edu/tag/01N9)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.Proj (degreeOpen)
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.MorphismToProjUniversal
open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.AlgebraicGeometry.ProjSectionsUnique (Pair)
open Stacks.AmplePullbackPart1 (natTensorPowCongr)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowers (natTensorPow)
open Stacks.TensorPowerTrivialize (resTop)

universe u w

namespace Stacks.AlgebraicGeometry.ProjTripleClassifying

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-! ### The classified morphism -/

section Classifying

variable {Y : Scheme.{u}} {d : ℕ} {L : Y.Modules} [Stacks.Ample.IsInvertibleModule Y L]

/-- The pair `(φ, α)` of [Stacks, Tag 01N8] attached to a triple, the witness of
`Stacks.AlgebraicGeometry.MorphismToProjUniversal.existsUnique_pair`. -/
def classifyingPair (hd : 0 < d) (ψ : VeroneseSections 𝒜 d L)
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤) :
    Pair 𝒜 L d :=
  (existsUnique_pair 𝒜 hd ψ hgen).choose

/-- The pair attached to a triple is compatible with `ψ`. -/
theorem isCompatible_classifyingPair (hd : 0 < d) (ψ : VeroneseSections 𝒜 d L)
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤) :
    IsCompatible 𝒜 ψ (classifyingPair 𝒜 hd ψ hgen) :=
  (existsUnique_pair 𝒜 hd ψ hgen).choose_spec.1

/-- The pair attached to a triple is the only pair compatible with `ψ`. -/
theorem eq_classifyingPair_of_isCompatible (hd : 0 < d) (ψ : VeroneseSections 𝒜 d L)
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤) (p : Pair 𝒜 L d)
    (hp : IsCompatible 𝒜 ψ p) :
    p = classifyingPair 𝒜 hd ψ hgen :=
  (existsUnique_pair 𝒜 hd ψ hgen).choose_spec.2 p hp

/-- The morphism `Y ⟶ U_d` classified by a triple, the first component of the pair of
[Stacks, Tag 01N8]. -/
def classifyingHom (hd : 0 < d) (ψ : VeroneseSections 𝒜 d L)
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤) :
    Y ⟶ (degreeOpen 𝒜 d).toScheme :=
  (classifyingPair 𝒜 hd ψ hgen).1

/-- The classified morphism is the first component of any pair compatible with `ψ`. -/
theorem eq_classifyingHom_of_isCompatible (hd : 0 < d) (ψ : VeroneseSections 𝒜 d L)
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤) (p : Pair 𝒜 L d)
    (hp : IsCompatible 𝒜 ψ p) :
    p.1 = classifyingHom 𝒜 hd ψ hgen :=
  congrArg Sigma.fst (eq_classifyingPair_of_isCompatible 𝒜 hd ψ hgen p hp)

end Classifying

/-! ### Triples, bundled -/

/-- A triple `(d, L, ψ)` over `Y` for the graded ring `A`: an integer `d ≥ 1`, an invertible
`𝒪_Y`-module `L` and a graded ring map `ψ : A^{(d)} ⟶ Γ_*(Y, L)`, given as a degreewise
multiplicative family of additive maps, such that the nonvanishing opens of the degree-`d` values
`ψ(f)` cover `Y`. -/
structure Triple (Y : Scheme.{u}) where
  /-- The integer `d`. -/
  deg : ℕ
  /-- `d ≥ 1`. -/
  deg_pos : 0 < deg
  /-- The invertible `𝒪_Y`-module `L`. -/
  module : Y.Modules
  /-- `L` is invertible. -/
  isInvertible : Stacks.Ample.IsInvertibleModule Y module
  /-- The graded ring map `ψ : A^{(d)} ⟶ Γ_*(Y, L)`. -/
  psi : VeroneseSections 𝒜 deg module
  /-- `L` is generated by the degree-`d` values of `ψ`. -/
  generated : haveI := isInvertible;
    ⨆ f : 𝒜 deg, nonvanishingOpen Y module (psiSection 𝒜 psi f) = ⊤

namespace Triple

variable {𝒜} {Y : Scheme.{u}}

/-- The morphism `Y ⟶ Proj(A)` classified by a triple: the morphism `Y ⟶ U_d` of [Stacks,
Tag 01N8], read into `Proj(A)` along the open immersion `U_d ⟶ Proj(A)`. -/
def classifyingMorphism (t : Triple 𝒜 Y) : Y ⟶ AlgebraicGeometry.Proj 𝒜 :=
  haveI := t.isInvertible
  toProj 𝒜 (classifyingHom 𝒜 t.deg_pos t.psi t.generated)

/-- The Veronese restriction of a triple at a weight `k ≥ 1`: the triple
`(kd, L^{⊗ k}, ψ|_{A^{(kd)}})` obtained by restricting `ψ` to the smaller Veronese subring
`A^{(kd)}` and reading it into `Γ_*(Y, L^{⊗ k})`. -/
def veroneseRestrict (t : Triple 𝒜 Y) (k : ℕ) (hk : 0 < k) : Triple 𝒜 Y where
  deg := k * t.deg
  deg_pos := Nat.mul_pos hk t.deg_pos
  module := natTensorPow t.module k
  isInvertible := haveI := t.isInvertible; inferInstance
  psi := ProjVeroneseRestrict.veroneseRestrict 𝒜 t.psi k
  generated := haveI := t.isInvertible
    ProjVeroneseRestrict.iSup_nonvanishingOpen_veroneseRestrict 𝒜 t.psi k t.generated

end Triple

/-- The morphisms `Y ⟶ Proj(A)` that [Stacks, Tag 01N8] associates to the two triples are
equal. -/
def SameMorphism {Y : Scheme.{u}} (t t' : Triple 𝒜 Y) : Prop :=
  t.classifyingMorphism = t'.classifyingMorphism

/-! ### Strict equivalence does not change the classified morphism -/

section SectionsEquiv

variable {Y : Scheme.{u}} {d : ℕ} {L L' : Y.Modules}

/-- Strict equivalence of two graded maps of the same weight `d`: an isomorphism `β : L ≅ L'`
whose induced isomorphisms on the tensor powers carry `ψ` to `ψ'` degreewise. -/
def SectionsEquiv (ψ : VeroneseSections 𝒜 d L) (ψ' : VeroneseSections 𝒜 d L') : Prop :=
  ∃ β : L ≅ L', ∀ (n : ℕ) (x : 𝒜 (n * d)),
    (natTensorPowCongr β n).hom.app ⊤ (ψ.toFun n x) = ψ'.toFun n x

variable [Stacks.Ample.IsInvertibleModule Y L] [Stacks.Ample.IsInvertibleModule Y L']

omit [Stacks.Ample.IsInvertibleModule Y L] [Stacks.Ample.IsInvertibleModule Y L'] in
/-- The degree-one tensor power of an isomorphism is the isomorphism itself, up to the two left
unitors: `β ∘ (λ_ L) = (λ_ L') ∘ β^{⊗ 1}`. -/
theorem unitorPow_hom_app_natTensorPowCongr (β : L ≅ L') (x : Γ(natTensorPow L 1, ⊤)) :
    (unitorPow L').hom.app ⊤ ((natTensorPowCongr β 1).hom.app ⊤ x)
      = β.hom.app ⊤ ((unitorPow L).hom.app ⊤ x) := by
  have h : (natTensorPowCongr β 1).hom ≫ (unitorPow L').hom
      = (unitorPow L).hom ≫ β.hom := by
    show (Iso.refl (𝟙_ Y.Modules) ⊗ᵢ β).hom ≫ (λ_ L').hom = (λ_ L).hom ≫ β.hom
    simp
  simpa [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply] using
    congrArg (fun φ : natTensorPow L 1 ⟶ L' => φ.app ⊤ x) h

/-- The inverse of an isomorphism of modules undoes it on sections over any open. -/
private theorem inv_app_hom_app {M N : Y.Modules} (e : M ≅ N) (U : Y.Opens) (z : Γ(M, U)) :
    e.inv.app U (e.hom.app U z) = z := by
  have h := congrArg (fun φ : M ⟶ M => φ.app U z) e.hom_inv_id
  simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
    Scheme.Modules.Hom.id_app] at h
  simpa using h

omit [Stacks.Ample.IsInvertibleModule Y L] [Stacks.Ample.IsInvertibleModule Y L'] in
/-- Let `c` be a family of isomorphisms `L ^⊗ n ≅ L' ^⊗ n` carrying the degree-`n` component of
`ψ` to that of `ψ'`, with `c 1` compatible with `β : L ≅ L'` through the identifications
`L ^⊗ 1 ≅ L`. Then a pair compatible with `ψ'` becomes, after composing `α` with `β⁻¹`, a pair
compatible with `ψ`. -/
theorem isCompatible_of_isoFamily {ψ : VeroneseSections 𝒜 d L}
    {ψ' : VeroneseSections 𝒜 d L'} (β : L ≅ L')
    (c : ∀ n : ℕ, natTensorPow L n ≅ natTensorPow L' n)
    (hc₁ : ∀ y : Γ(natTensorPow L 1, ⊤),
      (unitorPow L').hom.app ⊤ ((c 1).hom.app ⊤ y) = β.hom.app ⊤ ((unitorPow L).hom.app ⊤ y))
    (hc : ∀ (n : ℕ) (x : 𝒜 (n * d)), (c n).hom.app ⊤ (ψ.toFun n x) = ψ'.toFun n x)
    (p : Pair 𝒜 L' d) (hp : IsCompatible 𝒜 ψ' p) :
    IsCompatible 𝒜 ψ ⟨p.1, p.2 ≪≫ β.symm⟩ := by
  have hpow : ∀ (n : ℕ) (f : A) (hf : f ∈ 𝒜 d),
      (c n).hom.app ⊤ (ψ.pow hf n) = ψ'.pow hf n := fun n f hf =>
    hc n ⟨f ^ n, Stacks.MorphismToProj.HomogeneousRatios.pow_mem hf n⟩
  refine ⟨fun x => ?_, fun f V hV n y hy a hay => ?_⟩
  · have h1 := hp.1 x
    have h2 : ((p.2 ≪≫ β.symm).hom.app ⊤)
        ((twistCast 𝒜 p.1 (one_mul d)).hom.app ⊤ (psiPullbackHom 𝒜 p.1 1 x))
        = β.inv.app ⊤ ((unitorPow L').hom.app ⊤ (ψ'.toFun 1 x)) := by
      rw [Iso.trans_hom, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, h1]
      rfl
    rw [h2, ← hc 1 x, hc₁]
    exact inv_app_hom_app β ⊤ _
  · have h := hp.2 f V hV n y hy a hay
    have e : ∀ x : Γ(natTensorPow L n, ⊤),
        resTop (natTensorPow L' n) ((c n).hom.app ⊤ x) V
          = (c n).hom.app V (resTop (natTensorPow L n) x V) := fun x =>
      Stacks.TensorPowerTrivialize.resTop_app _ x V
    rw [← hc n a, ← hpow n (f : A) f.2, e, e, ← Scheme.Modules.Hom.app_smul] at h
    simpa only [inv_app_hom_app] using congrArg ((c n).inv.app V) h

/-- Let `c` be a family of isomorphisms `L ^⊗ n ≅ L' ^⊗ n` carrying the degree-`n` component of
`ψ` to that of `ψ'`, with `c 1` compatible with `β : L ≅ L'`. Then `ψ` and `ψ'` classify the same
morphism. -/
theorem classifyingHom_eq_of_isoFamily (hd : 0 < d) {ψ : VeroneseSections 𝒜 d L}
    {ψ' : VeroneseSections 𝒜 d L'}
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤)
    (hgen' : ⨆ f : 𝒜 d, nonvanishingOpen Y L' (psiSection 𝒜 ψ' f) = ⊤)
    (β : L ≅ L') (c : ∀ n : ℕ, natTensorPow L n ≅ natTensorPow L' n)
    (hc₁ : ∀ y : Γ(natTensorPow L 1, ⊤),
      (unitorPow L').hom.app ⊤ ((c 1).hom.app ⊤ y) = β.hom.app ⊤ ((unitorPow L).hom.app ⊤ y))
    (hc : ∀ (n : ℕ) (x : 𝒜 (n * d)), (c n).hom.app ⊤ (ψ.toFun n x) = ψ'.toFun n x) :
    classifyingHom 𝒜 hd ψ hgen = classifyingHom 𝒜 hd ψ' hgen' := by
  have hp := isCompatible_classifyingPair 𝒜 hd ψ' hgen'
  rw [← eq_classifyingHom_of_isCompatible 𝒜 hd ψ hgen _
    (isCompatible_of_isoFamily 𝒜 β c hc₁ hc _ hp)]
  rfl

omit [Stacks.Ample.IsInvertibleModule Y L] [Stacks.Ample.IsInvertibleModule Y L'] in
/-- If `β : L ≅ L'` carries `ψ` to `ψ'` degreewise, a pair compatible with `ψ'` becomes, after
composing `α` with `β⁻¹`, a pair compatible with `ψ`. -/
theorem isCompatible_of_sectionsEquiv {ψ : VeroneseSections 𝒜 d L}
    {ψ' : VeroneseSections 𝒜 d L'} (β : L ≅ L')
    (hβ : ∀ (n : ℕ) (x : 𝒜 (n * d)),
      (natTensorPowCongr β n).hom.app ⊤ (ψ.toFun n x) = ψ'.toFun n x)
    (p : Pair 𝒜 L' d) (hp : IsCompatible 𝒜 ψ' p) :
    IsCompatible 𝒜 ψ ⟨p.1, p.2 ≪≫ β.symm⟩ :=
  isCompatible_of_isoFamily 𝒜 β (natTensorPowCongr β)
    (unitorPow_hom_app_natTensorPowCongr β) hβ p hp

/-- Strictly equivalent triples classify the same morphism. -/
theorem classifyingHom_eq_of_sectionsEquiv (hd : 0 < d) {ψ : VeroneseSections 𝒜 d L}
    {ψ' : VeroneseSections 𝒜 d L'}
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤)
    (hgen' : ⨆ f : 𝒜 d, nonvanishingOpen Y L' (psiSection 𝒜 ψ' f) = ⊤)
    (h : SectionsEquiv 𝒜 ψ ψ') :
    classifyingHom 𝒜 hd ψ hgen = classifyingHom 𝒜 hd ψ' hgen' := by
  obtain ⟨β, hβ⟩ := h
  exact classifyingHom_eq_of_isoFamily 𝒜 hd hgen hgen' β (natTensorPowCongr β)
    (unitorPow_hom_app_natTensorPowCongr β) hβ

/-- Two triples of the same weight `d` which are strictly equivalent classify the same morphism
`Y ⟶ Proj(A)`. -/
theorem sameMorphism_of_sectionsEquiv (hd : 0 < d) {ψ : VeroneseSections 𝒜 d L}
    {ψ' : VeroneseSections 𝒜 d L'}
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤)
    (hgen' : ⨆ f : 𝒜 d, nonvanishingOpen Y L' (psiSection 𝒜 ψ' f) = ⊤)
    (h : SectionsEquiv 𝒜 ψ ψ') :
    SameMorphism 𝒜 ⟨d, hd, L, inferInstance, ψ, hgen⟩ ⟨d, hd, L', inferInstance, ψ', hgen'⟩ :=
  congrArg (fun φ : Y ⟶ (degreeOpen 𝒜 d).toScheme => toProj 𝒜 φ)
    (classifyingHom_eq_of_sectionsEquiv 𝒜 hd hgen hgen' h)

end SectionsEquiv

/-! ### The tensor powers of an isomorphism are multiplicative on sections -/

section Multiplicativity

open Stacks.GradedSections (natPowerSystem powSections)
open Stacks.Monoidal (PowerSystem)

variable {Y : Scheme.{u}} {L L' : Y.Modules}

/-- The `n`-th tensor power of an isomorphism is the comparison of the two systems of iterated
tensor powers along it. -/
theorem natTensorPowCongr_eq_compare (β : L ≅ L') : ∀ n : ℕ,
    natTensorPowCongr β n = PowerSystem.compare (natPowerSystem L) (natPowerSystem L') β n
  | 0 => by
      rw [PowerSystem.compare_zero]
      refine Iso.ext ?_
      simp only [Iso.trans_hom, Iso.symm_hom]
      rfl
  | n + 1 => by
      rw [PowerSystem.compare_succ, ← natTensorPowCongr_eq_compare β n]
      refine Iso.ext ?_
      simp only [Iso.trans_hom, Iso.symm_hom]
      rfl

/-- The tensor powers of an isomorphism are multiplicative on sections of the tensor powers read
as morphisms out of the monoidal unit: `β^{⊗ (p + q)}` carries the product of a section of
`L ^⊗ p` with one of `L ^⊗ q` to the product of their images. -/
theorem mul_comp_natTensorPowCongr (β : L ≅ L') {p q : ℕ} (s : powSections L p)
    (t : powSections L q) :
    Stacks.GradedSections.mul s t ≫ (natTensorPowCongr β (p + q)).hom
      = Stacks.GradedSections.mul (s ≫ (natTensorPowCongr β p).hom)
          (t ≫ (natTensorPowCongr β q).hom) := by
  rw [natTensorPowCongr_eq_compare β (p + q), natTensorPowCongr_eq_compare β p,
    natTensorPowCongr_eq_compare β q, Stacks.GradedSections.mul_eq_sectionMul,
    Stacks.GradedSections.mul_eq_sectionMul]
  exact (PowerSystem.compare_sectionMul (natPowerSystem L) (natPowerSystem L') β s t).symm

/-- The tensor powers of an isomorphism are multiplicative for the product
`Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections` of global sections of the tensor
powers. -/
theorem mulSections_natTensorPowCongr (β : L ≅ L') (p q : ℕ) (s : Γ(natTensorPow L p, ⊤))
    (t : Γ(natTensorPow L q, ⊤)) :
    (natTensorPowCongr β (p + q)).hom.app ⊤ (mulSections L s t)
      = mulSections L' ((natTensorPowCongr β p).hom.app ⊤ s)
          ((natTensorPowCongr β q).hom.app ⊤ t) := by
  rw [ProjVeroneseRestrict.mulSections_eq_globalSection L s t,
    ProjVeroneseRestrict.mulSections_eq_globalSection L'
      ((natTensorPowCongr β p).hom.app ⊤ s) ((natTensorPowCongr β q).hom.app ⊤ t),
    ProjVeroneseRestrict.secOf_app, ProjVeroneseRestrict.secOf_app,
    ← Stacks.SectionProduct.globalSection_comp]
  exact congrArg (Stacks.SectionProduct.globalSection Y (natTensorPow L' (p + q)))
    (mul_comp_natTensorPowCongr β (secOf L s) (secOf L t))

/-- A family of isomorphisms `L ^⊗ n ≅ L' ^⊗ n`, multiplicative for
`Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections`, that matches `ψ(f)^n` and `ψ'(f)^n`
for `n = 0` and `n = 1` matches them for every `n`. -/
theorem pow_of_isoFamily {d : ℕ} {ψ : VeroneseSections 𝒜 d L}
    {ψ' : VeroneseSections 𝒜 d L'} (c : ∀ n : ℕ, natTensorPow L n ≅ natTensorPow L' n)
    (hmul : ∀ (p q : ℕ) (s : Γ(natTensorPow L p, ⊤)) (t : Γ(natTensorPow L q, ⊤)),
      (c (p + q)).hom.app ⊤ (mulSections L s t)
        = mulSections L' ((c p).hom.app ⊤ s) ((c q).hom.app ⊤ t))
    {f : A} (hf : f ∈ 𝒜 d)
    (h0 : (c 0).hom.app ⊤ (ψ.pow hf 0) = ψ'.pow hf 0)
    (h1 : (c 1).hom.app ⊤ (ψ.pow hf 1) = ψ'.pow hf 1) : ∀ n : ℕ,
    (c n).hom.app ⊤ (ψ.pow hf n) = ψ'.pow hf n
  | 0 => h0
  | n + 1 => by
      rw [← ψ.mulSections_pow hf n 1, ← ψ'.mulSections_pow hf n 1, hmul,
        pow_of_isoFamily c hmul hf h0 h1 n, h1]

/-- If the tensor powers of `β : L ≅ L'` match `ψ(f)^n` and `ψ'(f)^n` for `n = 0` and `n = 1`,
they match them for every `n`. -/
theorem natTensorPowCongr_pow {d : ℕ} {ψ : VeroneseSections 𝒜 d L}
    {ψ' : VeroneseSections 𝒜 d L'} (β : L ≅ L') {f : A} (hf : f ∈ 𝒜 d)
    (h0 : (natTensorPowCongr β 0).hom.app ⊤ (ψ.pow hf 0) = ψ'.pow hf 0)
    (h1 : (natTensorPowCongr β 1).hom.app ⊤ (ψ.pow hf 1) = ψ'.pow hf 1) (n : ℕ) :
    (natTensorPowCongr β n).hom.app ⊤ (ψ.pow hf n) = ψ'.pow hf n :=
  pow_of_isoFamily 𝒜 (natTensorPowCongr β) (mulSections_natTensorPowCongr β) hf h0 h1 n

end Multiplicativity

end Stacks.AlgebraicGeometry.ProjTripleClassifying

end
