module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreProductComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeRelativeDiagonalDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.JointlyLocallyEssSurjDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactDiagonalGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStackFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyFppfCover
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyFppfCoverGeneral

/-!
# Gerbes are flat and locally of finite presentation, and so are their relative diagonals

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` which makes `𝒳` a gerbe over `𝒴`
(**Stacks 06QC**). This file proves, unconditionally, that `f` and its relative diagonal
`Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` are flat and locally of finite presentation, together with the two
fppf-local statements the library's proofs of **Stacks 06QI**, **Stacks 0CPR** and
**Stacks 0CPS** were written against.

## The route

The source proves these facts by presenting a gerbe fppf-locally as a classifying stack `[U/G]`
(**Stacks 06QH** and **Stacks 06QG**), which rests on the flatness of `G` over `U`
(**Stacks 06PL**) and on the flatness of `U ⟶ [U/G]` (**Stacks 06FH**). None of this is needed
here. Everything comes from **Stacks 06NR** for 1-morphisms of algebraic stacks along a jointly
locally essentially surjective family
(`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_of_isJointlyLocallyEssSurj_of_isFlat_comp`),
which descends flatness from the composites `a j ≫ c` to `c` with no flatness hypothesis on the
`a j`:

* a *section* `s` of a gerbe `π : 𝒲 ⟶ 𝒵` is flat and locally of finite presentation: over the
  members `W i` of an fppf covering of a smooth presentation `W ⟶ 𝒲`, the presentation and
  `s ∘ π` agree by Stacks 06P1 (2)(b), so the composites `W i ⟶ 𝒵 ⟶ 𝒲` are flat, and the `W i`
  are jointly locally essentially surjective onto `𝒵`;
* hence `Δ_f`, a section of the gerbe `𝒳 ×_𝒴 𝒳 ⟶ 𝒳` (**Stacks 06QE**), is flat and locally of
  finite presentation;
* `f` is flat and locally of finite presentation: for a surjective flat locally finitely
  presented `p : 𝒲 ⟶ 𝒳` from an algebraic space, the comparison `𝒲 ×_𝒳 𝒲 ⟶ 𝒲 ×_𝒴 𝒲` is a base
  change of `Δ_f` (**Stacks 04Z1**), hence locally essentially surjective, so the first
  projection of `𝒲 ×_𝒴 𝒲` is flat; that projection is the base change of `p ≫ f` along itself,
  so **Stacks 045D** makes `p ≫ f` flat, and **Stacks 06Q0** cancels `p`.

## Main results

All of these live in the namespace `AlgebraicGeometry.Stack.AlgebraicStacks`.

* `isFlat_and_isLocallyOfFinitePresentation_of_section_of_isGerbeOver`: a section of a gerbe is
  flat and locally of finite presentation (the flatness clauses of **Stacks 06QG** (3), for an
  arbitrary algebraic stack as base).
* `localEssSurj_relativeDiagonal_of_isGerbeOver`: the relative diagonal of a gerbe is locally
  essentially surjective (Stacks 06P1 (2)(b)).
* `isFlat_and_isLocallyOfFinitePresentation_of_isGerbeOver`: a gerbe is flat and locally of
  finite presentation (**Stacks 06QI**, the two clauses besides surjectivity).
* `isFlat_and_isLocallyOfFinitePresentation_relativeDiagonal`: so is its relative diagonal
  (**Stacks 0CPR**, part (2), the two clauses besides surjectivity).
* `hasFlatLfpLocalSection_of_isGerbeOver` and `hasFlatLfpLocalRelativeDiagonal_of_isGerbeOver`:
  the fppf-local inputs `AlgebraicGeometry.Stack.AlgebraicStacks.HasFlatLfpLocalSection` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.HasFlatLfpLocalRelativeDiagonal`, which the source
  produces from Stacks 06QH (1) `⟹` (2), hold for every gerbe.

## References

* [Stacks Project, Tag 045D](https://stacks.math.columbia.edu/tag/045D)
* [Stacks Project, Tag 04Z1](https://stacks.math.columbia.edu/tag/04Z1)
* [Stacks Project, Tag 06NR](https://stacks.math.columbia.edu/tag/06NR)
* [Stacks Project, Tag 06P1](https://stacks.math.columbia.edu/tag/06P1)
* [Stacks Project, Tag 06Q0](https://stacks.math.columbia.edu/tag/06Q0)
* [Stacks Project, Tag 06QC](https://stacks.math.columbia.edu/tag/06QC)
* [Stacks Project, Tag 06QE](https://stacks.math.columbia.edu/tag/06QE)
* [Stacks Project, Tag 06QG](https://stacks.math.columbia.edu/tag/06QG)
* [Stacks Project, Tag 06QH](https://stacks.math.columbia.edu/tag/06QH)
* [Stacks Project, Tag 06QI](https://stacks.math.columbia.edu/tag/06QI)
* [Stacks Project, Tag 0CPR](https://stacks.math.columbia.edu/tag/0CPR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Sections of gerbes -/

/-- A morphism of `𝒲` whose image under a 1-morphism `π : 𝒲 ⟶ 𝒵` lies over `k` lies over `k`. -/
theorem isHomLift_of_isHomLift_homFunctor_comp_p {𝒲 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (π : 𝒲 ⟶ 𝒵) {m n : 𝒲.val.val.obj} {R T : BigFppfOver B S hS} (k : R ⟶ T) (φ : m ⟶ n)
    (h : (CatFiberedInGroupoids.homFunctor π.hom ⋙ 𝒵.val.val.p).IsHomLift k φ) :
    𝒲.val.val.p.IsHomLift k φ :=
  (BasedFunctor.isHomLift_iff π.hom.hom k φ).1 ((Functor.isHomLift_comp_iff _ _ k φ).1 h)

/-- A 1-morphism making `𝒳` a gerbe over `𝒴` is locally essentially surjective
(Stacks 06P1 (2)(a)). -/
theorem isJointlyLocallyEssSurj_of_isGerbeOver {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (hf : IsGerbeOver B S hS f) :
    IsJointlyLocallyEssSurj B S hS (fun _ : PUnit.{u + 2} => f.hom) := by
  intro U y
  obtain ⟨R', hR', hR'l⟩ := hf.locally_essSurj y.1 y.2
  exact ⟨R', hR', fun V l hl => by
    obtain ⟨x, ψ, hψ⟩ := hR'l l hl
    exact ⟨PUnit.unit, x, ψ, hψ⟩⟩

/-- Let `p` name an object `w₀` of `𝒲` over `W`, and let `ξ`, `ξ'` be restrictions along
`k : V ⟶ W` of `w₀` and of `s (π w₀)` joined by a vertical morphism `c`. Then the composites
`V ⟶ W ⟶ 𝒲 ⟶ 𝒵 ⟶ 𝒲` and `V ⟶ W ⟶ 𝒲` are 2-isomorphic. -/
theorem nonempty_iso_schemeStackMap_comp_of_isHomLift
    {𝒲 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (π : 𝒲 ⟶ 𝒵) (s : 𝒵 ⟶ 𝒲)
    {V W : BigFppfOver B S hS} (k : V ⟶ W) (p : Stack.schemeStack.{u, w} B S hS W ⟶ 𝒲)
    {x₁ x₁' : 𝒲.val.val.obj} (ξ : x₁ ⟶ (stackMapFibreObject B S hS W p).1)
    (ξ' : x₁' ⟶ (CatFiberedInGroupoids.homFunctor s.hom).obj
      ((CatFiberedInGroupoids.homFunctor π.hom).obj (stackMapFibreObject B S hS W p).1))
    (c : x₁ ⟶ x₁') (hξX : 𝒲.val.val.p.IsHomLift k ξ) (hξ'X : 𝒲.val.val.p.IsHomLift k ξ')
    (hcX : 𝒲.val.val.p.IsHomLift (𝟙 V) c) :
    Nonempty ((Stack.schemeStackMap B S hS k ≫ p ≫ π) ≫ s ≅
      Stack.schemeStackMap B S hS k ≫ p) := by
  let w₀ : 𝒲.val.val.p.Fiber W := stackMapFibreObject B S hS W p
  let ι := Stack.schemeStackMap B S hS k
  let πs : 𝒲 ⟶ 𝒲 := π ≫ s
  have hπs : 𝒲.val.val.p.IsHomLift k ((CatFiberedInGroupoids.homFunctor πs.hom).map ξ) :=
    PresheafOfCategories.isHomLift_map_of_comp
      (CatFiberedInGroupoids.homFunctor_comp_p πs.hom) k ξ hξX
  have := 𝒲.val.isFiberedInGroupoids.isStronglyCartesian_homLift k
    ((CatFiberedInGroupoids.homFunctor πs.hom).map ξ)
  let cξ' : x₁ ⟶ (CatFiberedInGroupoids.homFunctor πs.hom).obj w₀.1 := c ≫ ξ'
  have : 𝒲.val.val.p.IsHomLift k cξ' :=
    @IsHomLift.comp_lift_id_left' _ _ _ _ 𝒲.val.val.p _ _ _ _ _ hcX _ _ k ξ' hξ'X
  let ν := Functor.IsStronglyCartesian.map 𝒲.val.val.p k
    ((CatFiberedInGroupoids.homFunctor πs.hom).map ξ) (Category.id_comp k).symm cξ'
  have hν : 𝒲.val.val.p.IsHomLift (𝟙 V) ν := inferInstance
  have hνiso : IsIso ν := 𝒲.val.isFiberedInGroupoids.isIso_of_isHomLift_id ν hν
  have hνinv : 𝒲.val.val.p.IsHomLift (𝟙 V) (inv ν) := inferInstance
  have hx₁ : 𝒲.val.val.p.obj x₁ = V := IsHomLift.domain_eq 𝒲.val.val.p k ξ
  have hψ : 𝒲.val.val.p.IsHomLift k (inv ν ≫ ξ) :=
    @IsHomLift.comp_lift_id_left' _ _ _ _ 𝒲.val.val.p _ _ _ _ _ hνinv _ _ k ξ hξX
  let isoA := fibreObjectStackMapFactorIso B S hS (𝟙 𝒲) k ⟨x₁, hx₁⟩ w₀ ξ hξX
  let isoB := fibreObjectStackMapFactorIso B S hS πs k ⟨x₁, hx₁⟩ w₀ (inv ν ≫ ξ) hψ
  let isoP := fibreObjectStackMapEvaluationIso B S hS W p
  exact ⟨α_ ι (p ≫ π) s ≪≫ Bicategory.whiskerLeftIso ι (α_ p π s) ≪≫
    Bicategory.whiskerLeftIso ι (Bicategory.whiskerRightIso isoP.symm πs) ≪≫
    (α_ ι _ πs).symm ≪≫ Bicategory.whiskerRightIso isoA.symm πs ≪≫
    Bicategory.whiskerRightIso (ρ_ _) πs ≪≫ isoB ≪≫ Bicategory.whiskerLeftIso ι isoP⟩

/-- Let `π : 𝒲 ⟶ 𝒵` make `𝒲` a gerbe over `𝒵`, let `s` be a section of it and let `p` be a
1-morphism to `𝒲` from the stack of `W`. Over the members of some covering of `W`, the composites
with `p ≫ π ≫ s` and with `p` are 2-isomorphic (Stacks 06P1 (2)(b)). -/
theorem exists_mem_topology_nonempty_iso_of_section_of_isGerbeOver
    {𝒲 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (π : 𝒲 ⟶ 𝒵) (s : 𝒵 ⟶ 𝒲)
    (e : s ≫ π ≅ 𝟙 𝒵) (hπ : IsGerbeOver B S hS π) {W : BigFppfOver B S hS}
    (p : Stack.schemeStack.{u, w} B S hS W ⟶ 𝒲) :
    ∃ R ∈ BigFppfOver.topology B S hS W, ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ W⦄, R.arrows k →
      Nonempty ((Stack.schemeStackMap B S hS k ≫ p ≫ π) ≫ s ≅
        Stack.schemeStackMap B S hS k ≫ p) := by
  let w₀ : 𝒲.val.val.p.Fiber W := stackMapFibreObject B S hS W p
  let y₀ : 𝒵.val.val.obj := (CatFiberedInGroupoids.homFunctor π.hom).obj w₀.1
  have hy₀ : 𝒵.val.val.p.obj y₀ = W :=
    (Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p π.hom) w₀.1).trans w₀.2
  let w₁ : 𝒲.val.val.obj := (CatFiberedInGroupoids.homFunctor s.hom).obj y₀
  -- the vertical comparison `π p ⟶ π s π p` given by the section
  let b : (CatFiberedInGroupoids.homFunctor π.hom).obj w₀.1 ⟶
      (CatFiberedInGroupoids.homFunctor π.hom).obj w₁ := e.inv.hom.hom.toNatTrans.app y₀
  have hb : 𝒵.val.val.p.IsHomLift (𝟙 W) b := by
    have h := e.inv.hom.hom.isHomLift' y₀
    rwa [hy₀] at h
  obtain ⟨R, hR, hcov⟩ := hπ.locally_full b hb
  refine ⟨R, hR, fun V k hk => ?_⟩
  obtain ⟨x₁, x₁', ξ, ξ', c, hξ, hξ', hc, -⟩ := hcov k hk
  exact nonempty_iso_schemeStackMap_comp_of_isHomLift B S hS π s k p ξ ξ' c
    (isHomLift_of_isHomLift_homFunctor_comp_p B S hS π k ξ hξ)
    (isHomLift_of_isHomLift_homFunctor_comp_p B S hS π k ξ' hξ')
    (isHomLift_of_isHomLift_homFunctor_comp_p B S hS π (𝟙 V) c hc)

/-- **A section of a gerbe is flat and locally of finite presentation.** Let `π : 𝒲 ⟶ 𝒵` make
`𝒲` a gerbe over `𝒵` and let `s : 𝒵 ⟶ 𝒲` be a section of it, `s ≫ π ≅ 𝟙 𝒵`. Then `s` is flat
and locally of finite presentation.

This is the part of **Stacks 06QG** (3) that the library lacked, proved here for an arbitrary
algebraic stack `𝒵` and without the presentation `𝒲 ≅ [𝒵/G]` of the source. Choose a smooth
surjective presentation `p : W ⟶ 𝒲` by a scheme. By Stacks 06P1 (2)(b) applied to `p` and `s π p`
there is an fppf covering `{W i ⟶ W}` over each member of which `p` and `s π p` become
isomorphic; so the composites `W i ⟶ W ⟶ 𝒲 ⟶ 𝒵 ⟶ 𝒲` are 2-isomorphic to `W i ⟶ W ⟶ 𝒲`, which
are flat and locally of finite presentation. The family `W i ⟶ 𝒵` is jointly locally
essentially surjective, by Stacks 06QA for `p`, Stacks 06P1 (2)(a) for `π` and the covering, so
Stacks 06NR for that family
(`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_of_isJointlyLocallyEssSurj_of_isFlat_comp`)
concludes. -/
theorem isFlat_and_isLocallyOfFinitePresentation_of_section_of_isGerbeOver
    {𝒲 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (π : 𝒲 ⟶ 𝒵) (s : 𝒵 ⟶ 𝒲)
    (e : s ≫ π ≅ 𝟙 𝒵) (hπ : IsGerbeOver B S hS π) :
    IsFlat B S hS s ∧ IsLocallyOfFinitePresentation B S hS s := by
  classical
  obtain ⟨W, p, hpSmooth, hpSurj⟩ := Stack.exists_smooth_surjective_schemeStack B S hS 𝒲
  -- the 2-isomorphism `ι i ≫ p ≫ π ≫ s ≅ ι i ≫ p` over each member of the covering
  obtain ⟨R, hR, hiso⟩ :=
    exists_mem_topology_nonempty_iso_of_section_of_isGerbeOver B S hS π s e hπ p
  obtain ⟨I, Wi, m, hmR, hmflat, hmlfp, hmsurj⟩ := exists_family_of_mem_topology B S hS hR
  let k : ∀ i, (Over.mk (m i ≫ W.hom) : BigFppfOver B S hS) ⟶ W := fun i => Over.homMk (m i)
  let ι : ∀ i, Stack.schemeStack.{u, w} B S hS (Over.mk (m i ≫ W.hom)) ⟶
      Stack.schemeStack.{u, w} B S hS W := fun i => Stack.schemeStackMap B S hS (k i)
  have hιflat : ∀ i, IsFlat B S hS (ι i ≫ p) := fun i =>
    isFlat_comp B S hS (ι i) p (Stack.isFlat_schemeFibredCategoryMap.{u, w} B S hS (k i) (hmflat i))
      (isFlat_of_isSmooth B S hS p hpSmooth)
  have hιlfp : ∀ i, IsLocallyOfFinitePresentation B S hS (ι i ≫ p) := fun i =>
    isLocallyOfFinitePresentation_comp B S hS (ι i) p
      (Stack.isLocallyOfFinitePresentation_schemeFibredCategoryMap.{u, w} B S hS (k i) (hmlfp i))
      (isLocallyOfFinitePresentation_of_isSmooth B S hS p hpSmooth)
  -- the family `ι i ≫ p ≫ π` is jointly locally essentially surjective onto `𝒵`
  have hp : IsJointlyLocallyEssSurj B S hS (fun _ : PUnit.{u + 2} => p.hom) :=
    IsJointlyLocallyEssSurj.of_localEssSurj _ (Stack.exists_fppfCovering_fibre_lift B S hS p
      hpSurj (isFlat_of_isSmooth B S hS p hpSmooth)
      (isLocallyOfFinitePresentation_of_isSmooth B S hS p hpSmooth))
  have hjs := ((isJointlyLocallyEssSurj_of_isGerbeOver B S hS π hπ).comp fun _ => hp).comp
    fun _ => isJointlyLocallyEssSurj_schemeFibredCategoryMap B S hS (U := W) Wi m hmflat hmlfp
      hmsurj
  have hac : ∀ ji : (Σ _ : (Σ _ : PUnit.{u + 2}, PUnit.{u + 2}), I),
      IsFlat B S hS ((ι ji.2 ≫ p ≫ π) ≫ s) := fun ji =>
    (isFlat_iff_of_twoIso B S hS (ι ji.2 ≫ p) _
      (Bicategory.InducedBicategory.isoHom (hiso (hmR ji.2)).some.symm)).1 (hιflat ji.2)
  have hacl : ∀ ji : (Σ _ : (Σ _ : PUnit.{u + 2}, PUnit.{u + 2}), I),
      IsLocallyOfFinitePresentation B S hS ((ι ji.2 ≫ p ≫ π) ≫ s) := fun ji =>
    (isLocallyOfFinitePresentation_iff_of_twoIso B S hS (ι ji.2 ≫ p) _
      (Bicategory.InducedBicategory.isoHom (hiso (hmR ji.2)).some.symm)).1 (hιlfp ji.2)
  let a : ∀ ji : (Σ _ : (Σ _ : PUnit.{u + 2}, PUnit.{u + 2}), I),
      Stack.schemeStack.{u, w} B S hS (Over.mk (m ji.2 ≫ W.hom)) ⟶ 𝒵 :=
    fun ji => ι ji.2 ≫ p ≫ π
  have hjs' : IsJointlyLocallyEssSurj B S hS (fun ji => (a ji).hom) := hjs
  exact ⟨isFlat_of_isJointlyLocallyEssSurj_of_isFlat_comp B S hS s a hjs' hac,
    isLocallyOfFinitePresentation_of_isJointlyLocallyEssSurj_of_comp B S hS s a hjs' hacl⟩

/-! ### Gerbes and their relative diagonals -/

/-- **The relative diagonal of a gerbe is locally essentially surjective.** If `f : 𝒳 ⟶ 𝒴` makes
`𝒳` a gerbe over `𝒴`, every object `(x₁, x₂, φ)` of a fibre of `𝒳 ×_𝒴 𝒳` lifts along
`Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` over a covering sieve.

This is Stacks 06P1 (2)(b) read through the canonical 2-fibre product of Stacks 04T2: over a
member `g` of the covering it supplies restrictions `ξ`, `ξ'` of `x₁`, `x₂` along `g` and a
vertical `c` between them with `f c ≫ f ξ' = f ξ ≫ φ`, which is exactly a morphism to
`(x₁, x₂, φ)` out of the diagonal image of the source of `ξ`. -/
theorem localEssSurj_relativeDiagonal_of_isGerbeOver
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsGerbeOver B S hS f) :
    ∀ (U : BigFppfOver B S hS)
      (y : (Stack.twoFibreProductAlgebraicStack B S hS f f).val.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ z : 𝒳.val.val.obj, ∃ φ : (CatFiberedInGroupoids.homFunctor
              (Stack.relativeDiagonalAlgebraicStacks B S hS f).hom).obj z ⟶ y.1,
            (Stack.twoFibreProductAlgebraicStack B S hS f f).val.val.p.IsHomLift k φ := by
  rintro U ⟨P, hP⟩
  subst hP
  obtain ⟨R, hR, hcov⟩ := hf.locally_full P.iso.hom P.vertical
  refine ⟨R, hR, fun V g hgR => ?_⟩
  obtain ⟨x₁, x₂, ξ, ξ', c, hξ, hξ', hc, hcomm⟩ := hcov g hgR
  have hξX : 𝒳.val.val.p.IsHomLift g ξ :=
    isHomLift_of_isHomLift_homFunctor_comp_p B S hS f g ξ hξ
  have hξ'X : 𝒳.val.val.p.IsHomLift g ξ' :=
    isHomLift_of_isHomLift_homFunctor_comp_p B S hS f g ξ' hξ'
  have hcX : 𝒳.val.val.p.IsHomLift (𝟙 V) c :=
    isHomLift_of_isHomLift_homFunctor_comp_p B S hS f (𝟙 V) c hc
  have hx₁V : 𝒳.val.val.p.obj x₁ = V := IsHomLift.domain_eq 𝒳.val.val.p g ξ
  have hbX : 𝒳.val.val.p.IsHomLift g (c ≫ ξ') := by
    simpa using IsHomLift.comp 𝒳.val.val.p (𝟙 V) g c ξ'
  subst hx₁V
  have hw : f.hom.hom.toFunctor.map ξ ≫ P.iso.hom =
      𝟙 (f.hom.hom.toFunctor.obj x₁) ≫ f.hom.hom.toFunctor.map (c ≫ ξ') := by
    simpa using hcomm.symm
  exact ⟨x₁, ⟨g, ξ, c ≫ ξ', hξX, hbX, hw⟩,
    IsHomLift.map (Stack.twoFibreProductAlgebraicStack B S hS f f).val.val.p
      (⟨g, ξ, c ≫ ξ', hξX, hbX, hw⟩ :
        (Stack.relativeDiagonalAlgebraicStacks B S hS f).hom.hom.obj x₁ ⟶ P)⟩

/-- **Stacks 045D** for a smooth-local property `P`: a representable, locally essentially
surjective `g : 𝒲 ⟶ 𝒴` has `P` on some smooth diagram if its self base change `𝒲 ×_𝒴 𝒲 ⟶ 𝒲`
does. -/
private theorem hasPropertyOnSomeSmoothDiagram_of_twoFibreProductSquare_fst
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hP : Space.IsSmoothLocalOnSourceAndTarget B S hS P)
    [(Stack.spaceProperty B S hS P).IsStableUnderBaseChange]
    [(Stack.spaceProperty B S hS P).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    {𝒲 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (g : 𝒲 ⟶ 𝒴)
    (hgrep : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom)
    (hg : ∀ (U : BigFppfOver B S hS) (y : 𝒴.val.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ z : 𝒲.val.val.obj,
            ∃ φ : (CatFiberedInGroupoids.homFunctor g.hom).obj z ⟶ y.1,
              𝒴.val.val.p.IsHomLift k φ)
    (hQ : Stack.HasPropertyOnSomeSmoothDiagram B S hS P
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS g g).fst.hom) :
    Stack.HasPropertyOnSomeSmoothDiagram B S hS P g.hom := by
  let Q := Stack.twoFibreProductSquareAlgebraicStacks B S hS g g
  have hQrep : IsRepresentableByAlgebraicSpaces B S hS Q.fst.hom.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS 𝒲.val 𝒴.val 𝒲.val
      g.hom g.hom
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom g.hom)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        g.hom g.hom) hgrep
  refine (Stack.hasPropertyOnSomeSmoothDiagram_iff_relative B S hS P hP 𝒲.property 𝒴.property
    g.hom hgrep).2 ?_
  exact Stack.hasRelativeProperty_of_baseChange.{u, u, u, u} B S hS 𝒲.val 𝒴.val 𝒲.val _
    g.hom g.hom
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom g.hom)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      g.hom g.hom) hgrep hg
    ((Stack.hasPropertyOnSomeSmoothDiagram_iff_relative B S hS P hP Q.pt.property
      𝒲.property Q.fst.hom hQrep).1 hQ)

/-- **Stacks 045D for flatness.** A 1-morphism `g : 𝒲 ⟶ 𝒴` of algebraic stacks over `S` which
is representable by algebraic spaces and locally essentially surjective is flat as soon as its
base change `𝒲 ×_𝒴 𝒲 ⟶ 𝒲` along itself is. -/
theorem isFlat_of_twoFibreProductSquare_fst {𝒲 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (g : 𝒲 ⟶ 𝒴) (hgrep : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom)
    (hg : ∀ (U : BigFppfOver B S hS) (y : 𝒴.val.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ z : 𝒲.val.val.obj,
            ∃ φ : (CatFiberedInGroupoids.homFunctor g.hom).obj z ⟶ y.1,
              𝒴.val.val.p.IsHomLift k φ)
    (hQ : IsFlat B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g g).fst) :
    IsFlat B S hS g := by
  have hflatBC : (Stack.spaceProperty B S hS
      (fun _ _ h => Space.IsFlat B S hS h)).IsStableUnderBaseChange :=
    Space.isFlat_isStableUnderBaseChange B S hS
  have hflatLT : (Stack.spaceProperty B S hS
      (fun _ _ h => Space.IsFlat B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isFlat_isLocalAtTarget_fppf B S hS
  exact hasPropertyOnSomeSmoothDiagram_of_twoFibreProductSquare_fst B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) g hgrep hg hQ

/-- **Stacks 045D for local finite presentation.** A 1-morphism `g : 𝒲 ⟶ 𝒴` of algebraic stacks
over `S` which is representable by algebraic spaces and locally essentially surjective is locally
of finite presentation as soon as its base change `𝒲 ×_𝒴 𝒲 ⟶ 𝒲` along itself is. -/
theorem isLocallyOfFinitePresentation_of_twoFibreProductSquare_fst
    {𝒲 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (g : 𝒲 ⟶ 𝒴)
    (hgrep : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom)
    (hg : ∀ (U : BigFppfOver B S hS) (y : 𝒴.val.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ z : 𝒲.val.val.obj,
            ∃ φ : (CatFiberedInGroupoids.homFunctor g.hom).obj z ⟶ y.1,
              𝒴.val.val.p.IsHomLift k φ)
    (hQ : IsLocallyOfFinitePresentation B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS g g).fst) :
    IsLocallyOfFinitePresentation B S hS g := by
  have hlfpBC : (Stack.spaceProperty B S hS
      (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)).IsStableUnderBaseChange :=
    Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  have hlfpLT : (Stack.spaceProperty B S hS
      (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isLocallyOfFinitePresentation_isLocalAtTarget_fppf B S hS
  have hP := Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS
  exact (Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _ hP 𝒲.property
    𝒴.property g.hom).2
    (hasPropertyOnSomeSmoothDiagram_of_twoFibreProductSquare_fst B S hS _ hP g hgrep hg
      ((Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _ hP
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS g g).pt.property 𝒲.property
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS g g).fst.hom).1 hQ))

/-- **Stacks 06QI, flatness and local finite presentation.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of
algebraic stacks over `S` which makes `𝒳` a gerbe over `𝒴` is flat and locally of finite
presentation.

Choose a surjective, flat, locally finitely presented `p : 𝒲 ⟶ 𝒳` from an algebraic space. The
comparison `𝒲 ×_𝒳 𝒲 ⟶ 𝒲 ×_𝒴 𝒲` is a base change of the relative diagonal `Δ_f` by
**Stacks 04Z1**, hence locally essentially surjective by Stacks 06P1 (2)(b); its composite with
the first projection of `𝒲 ×_𝒴 𝒲` is the first projection of `𝒲 ×_𝒳 𝒲`, a base change of `p`. So
Stacks 06NR for 1-morphisms of algebraic stacks makes the first projection
`𝒲 ×_𝒴 𝒲 ⟶ 𝒲` flat and locally of finite presentation. That projection is the base change of
`p ≫ f` along itself, and `p ≫ f` is locally essentially surjective by Stacks 06QA for `p` and
Stacks 06P1 (2)(a); so **Stacks 045D** makes `p ≫ f` flat and locally of finite presentation,
and **Stacks 06Q0** and **Stacks 06Q9** cancel `p`. -/
@[stacks 06QI "flat and locally of finite presentation"]
theorem isFlat_and_isLocallyOfFinitePresentation_of_isGerbeOver
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : IsGerbeOver B S hS f) :
    IsFlat B S hS f ∧ IsLocallyOfFinitePresentation B S hS f := by
  obtain ⟨𝒲, p, h𝒲, hprep, hpsurj, hpflat, hplfp⟩ :=
    exists_isRepresentableByAlgebraicSpace_fppfCover B S hS 𝒳
  have hφrep : IsRepresentableByAlgebraicSpaces B S hS (p ≫ f).hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒴.property h𝒲 (p ≫ f).hom
  -- `p ≫ f` is locally essentially surjective
  have hp : IsJointlyLocallyEssSurj B S hS (fun _ : PUnit.{u + 2} => p.hom) :=
    IsJointlyLocallyEssSurj.of_localEssSurj _
      (localEssSurj_of_isSurjective_isFlat_isLocallyOfFinitePresentation B S hS p hprep hpsurj
        hpflat hplfp)
  have hφ : ∀ (U : BigFppfOver B S hS) (y : 𝒴.val.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ z : 𝒲.val.val.obj,
            ∃ φ : (CatFiberedInGroupoids.homFunctor (p ≫ f).hom).obj z ⟶ y.1,
              𝒴.val.val.p.IsHomLift k φ := by
    intro U y
    obtain ⟨R, hR, hRl⟩ :=
      (isJointlyLocallyEssSurj_of_isGerbeOver B S hS f hf).comp (fun _ => hp) U y
    exact ⟨R, hR, fun V k hk => by
      obtain ⟨_, z, φ, hφ⟩ := hRl hk
      exact ⟨z, φ, hφ⟩⟩
  -- the comparison of the two self-products of `𝒲` is locally essentially surjective
  have hΔ : IsJointlyLocallyEssSurj B S hS
      (fun _ : PUnit.{u + 2} => (Stack.relativeDiagonalAlgebraicStacks B S hS f).hom) :=
    IsJointlyLocallyEssSurj.of_localEssSurj _
      (localEssSurj_relativeDiagonal_of_isGerbeOver B S hS f hf)
  have hc : IsJointlyLocallyEssSurj B S hS
      (fun _ : PUnit.{u + 2} => (Stack.comparison B S hS p p f).hom) :=
    hΔ.fst_of_isTwoFibreProduct (Stack.comparisonCospanRight B S hS p p f).hom
      (fun _ => Stack.comparisonSquare B S hS p p f)
      (fun _ => Stack.isTwoFibreProduct_comparisonSquare B S hS p p f)
  let Q := Stack.twoFibreProductSquareAlgebraicStacks B S hS (p ≫ f) (p ≫ f)
  let R := Stack.twoFibreProductSquareAlgebraicStacks B S hS p p
  -- the base change of `p ≫ f` along itself is flat and locally of finite presentation
  have hQflat : IsFlat B S hS Q.fst :=
    isFlat_of_isJointlyLocallyEssSurj_of_isFlat_comp B S hS Q.fst
      (fun _ : PUnit.{u + 2} => Stack.comparison B S hS p p f) hc (fun _ =>
        isFlat_baseChange B S hS p p R
          (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS p p) hpflat)
  have hQlfp : IsLocallyOfFinitePresentation B S hS Q.fst :=
    isLocallyOfFinitePresentation_of_isJointlyLocallyEssSurj_of_comp B S hS Q.fst
      (fun _ : PUnit.{u + 2} => Stack.comparison B S hS p p f) hc (fun _ =>
        isLocallyOfFinitePresentation_baseChange B S hS p p R
          (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS p p) hplfp)
  -- Stacks 045D along `p ≫ f`
  have hφflat := isFlat_of_twoFibreProductSquare_fst B S hS (p ≫ f) hφrep hφ hQflat
  have hφlfp :=
    isLocallyOfFinitePresentation_of_twoFibreProductSquare_fst B S hS (p ≫ f) hφrep hφ hQlfp
  exact ⟨isFlat_of_isSurjective_of_isFlat_comp B S hS p f hφflat hpsurj hpflat,
    isLocallyOfFinitePresentation_of_comp_of_fppf B S hS p f hφlfp hpsurj hpflat hplfp⟩

/-- **Stacks 0CPR, part (2), flatness and local finite presentation.** If a 1-morphism
`f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` makes `𝒳` a gerbe over `𝒴`, then its relative diagonal
`Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is flat and locally of finite presentation.

The second projection `𝒳 ×_𝒴 𝒳 ⟶ 𝒳` is a base change of `f`, hence a gerbe by **Stacks 06QE**,
and `Δ_f` is a section of it; a section of a gerbe is flat and locally of finite presentation
(`isFlat_and_isLocallyOfFinitePresentation_of_section_of_isGerbeOver`). -/
theorem isFlat_and_isLocallyOfFinitePresentation_relativeDiagonal
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : IsGerbeOver B S hS f) :
    IsFlat B S hS (Stack.relativeDiagonalAlgebraicStacks B S hS f) ∧
      IsLocallyOfFinitePresentation B S hS (Stack.relativeDiagonalAlgebraicStacks B S hS f) :=
  isFlat_and_isLocallyOfFinitePresentation_of_section_of_isGerbeOver B S hS
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS f f).snd
    (Stack.relativeDiagonalAlgebraicStacks B S hS f)
    (Iso.refl _)
    (isGerbeOver_of_isTwoFibreProduct B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS f f)
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f f) hf)

/-- **A gerbe has a flat, locally finitely presented local section.** If `f : 𝒳 ⟶ 𝒴` makes `𝒳`
a gerbe over `𝒴`, then `f` itself is a surjective, flat, locally finitely presented 1-morphism
along which the base change `𝒳 ×_𝒴 𝒳 ⟶ 𝒳` of `f` admits a section which is flat and locally of
finite presentation, namely the relative diagonal.

This is the fppf-local input which the source extracts from **Stacks 06QH** (1) `⟹` (2) and
**Stacks 06QG** (3) in its proof of **Stacks 06QI**: surjectivity of `f` is Stacks 06QI, its
flatness and local finite presentation are
`isFlat_and_isLocallyOfFinitePresentation_of_isGerbeOver`, and those of the relative diagonal are
`isFlat_and_isLocallyOfFinitePresentation_relativeDiagonal`.
-/
theorem hasFlatLfpLocalSection_of_isGerbeOver
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : IsGerbeOver B S hS f) :
    HasFlatLfpLocalSection B S hS f :=
  ⟨𝒳, f, Stack.isSurjective_of_isGerbeOver B S hS f hf,
    (isFlat_and_isLocallyOfFinitePresentation_of_isGerbeOver B S hS f hf).1,
    (isFlat_and_isLocallyOfFinitePresentation_of_isGerbeOver B S hS f hf).2,
    Stack.relativeDiagonalAlgebraicStacks B S hS f, ⟨Iso.refl _⟩,
    (isFlat_and_isLocallyOfFinitePresentation_relativeDiagonal B S hS f hf).1,
    (isFlat_and_isLocallyOfFinitePresentation_relativeDiagonal B S hS f hf).2⟩

/-- **The relative diagonal of a gerbe is fppf-locally flat and locally of finite
presentation.** If `f : 𝒳 ⟶ 𝒴` makes `𝒳` a gerbe over `𝒴`, then for a smooth surjective
presentation `q` of `𝒳 ×_𝒴 𝒳` by a scheme — which is surjective, flat and locally of finite
presentation — the base change of the relative diagonal `Δ_f` along `q` is flat and locally of
finite presentation.

This is the fppf-local input which the source extracts from **Stacks 06QH** (1) `⟹` (2) and the
computation of the diagonal of a quotient stack in its proof of **Stacks 0CPR**, part (2). It is
the base change of
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_and_isLocallyOfFinitePresentation_relativeDiagonal`
by **Stacks 06PY** and **Stacks 06Q4**. -/
theorem hasFlatLfpLocalRelativeDiagonal_of_isGerbeOver
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : IsGerbeOver B S hS f) :
    HasFlatLfpLocalRelativeDiagonal B S hS f := by
  obtain ⟨V, q, hqSmooth, hqSurj⟩ := Stack.exists_smooth_surjective_schemeStack B S hS
    (Stack.twoFibreProductAlgebraicStack B S hS f f)
  obtain ⟨hΔflat, hΔlfp⟩ := isFlat_and_isLocallyOfFinitePresentation_relativeDiagonal B S hS f hf
  let P := Stack.twoFibreProductSquareAlgebraicStacks B S hS
    (Stack.relativeDiagonalAlgebraicStacks B S hS f) q
  have hP : Bicategory.IsTwoFibreProduct P.swap := Bicategory.isTwoFibreProduct_swap
    (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ q)
  exact ⟨Stack.schemeStack.{u, w} B S hS V, q, hqSurj, isFlat_of_isSmooth B S hS q hqSmooth,
    isLocallyOfFinitePresentation_of_isSmooth B S hS q hqSmooth,
    isFlat_baseChange B S hS _ q P.swap hP hΔflat,
    isLocallyOfFinitePresentation_baseChange B S hS _ q P.swap hP hΔlfp⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
