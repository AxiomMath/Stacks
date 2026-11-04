module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.AbelBundle.Charts
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.AbelBundle.SectionBasis
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyProjectiveSpaceSmooth
public import StacksFrontier.AlgebraicGeometry.Gluing.AffineCompatible
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.PicardOfCurve
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.AbelBundleExists

/-!
# The Abel morphism is Zariski-locally a projective space

Let `X` be a smooth proper geometrically irreducible curve of genus `g` over a field `k` with a
rational point `σ`, `θ` a class of degree `d ≥ 2g - 1`, `H` the Hilbert scheme of degree-`d`
divisors, `A` the group scheme representing `Pic⁰_{X/k,σ}` and `γ : H ⟶ A` the Abel morphism.
Around every point of `A` there are an open `V' ⊆ A` and sections `e₀, …, e_m` (`m = d - g`) of the
translated universal class forming a basis after every affine base change into `V'`
(`Stacks.RigidifiedPicard.exists_abelSectionBasis`). This file glues

* `ℙᵐ_{V'} ⟶ H` from the families `Z(∑ bᵢ eᵢ)` on the standard charts of `ℙᵐ`
  (`Stacks.RigidifiedPicard.exists_projectiveSpaceOver_hom_hilb`), and
* `γ⁻¹(V') ⟶ ℙᵐ_{V'}` from the coordinates `[c₀ : … : c_m]` of the divisors of `γ⁻¹(V')`
  (`Stacks.RigidifiedPicard.exists_abelPreimage_hom_projectiveSpaceOver`),

and shows they are mutually inverse over `V'`. Hence `γ` is Zariski-locally on `A` the projective
space `ℙ^{d-g}`, and in particular smooth: the clause of [Stacks, Tag 0BA0] (5) on the Abel
morphism.

## Main results

* `Stacks.RigidifiedPicard.exists_abelPreimage_iso`: `γ⁻¹(V') ≅ ℙᵐ_{V'}` over `V'`.
* `Stacks.RigidifiedPicard.isLocallyProjectiveSpace_abelMorphism`: `γ` is Zariski-locally on `A`
  the projective space `ℙ^{d-g}`, over any field.
* `Stacks.RigidifiedPicard.abelMorphismSmooth`: `AbelMorphismSmooth`.
* `Stacks.RigidifiedPicard.abelMorphismIsLocallyProjectiveSpace`:
  `AbelMorphismIsLocallyProjectiveSpace`.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.RigidifiedPicard

open Stacks.Picard Stacks.ProjectiveSpaceModuli

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIrreducible f]
  [Flat f] [LocallyOfFinitePresentation f] [LocallyOfFiniteType f]
  (hdim : ∀ s : Spec (.of k), topologicalKrullDim ↥(f.fiber s) ≤ 1)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
  (A : Grp (Over (Spec (.of k)))) (e : yonedaGrp.obj A ≅ functorZero f hdim σ hσ)
  (θ : Stacks.Picard.ofScheme X) {d : ℕ}
  (hθ : ∀ s : Spec (.of k), relativeInvertibleDegreeHomAt f hdim s θ = d)
  {H : Over (Spec (.of k))} (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H d)
  {B₀ : Over (Spec (.of k))} (L₀ : (bc f B₀).Modules)
  (hL₀ : Stacks.SheafOfModules.IsInvertible (bc f B₀).presheaf (bc f B₀).ringCatSheaf.2 L₀)
  {m : ℕ} (es : Fin (m + 1) → Γ(L₀, ⊤)) {V : B₀.left.Opens} (hbasis : IsSectionBasis f L₀ es V)
  (hdeg₀ : ∀ b : B₀.left, relativeInvertibleDegreeHomAt (bcProj f B₀)
    (topologicalKrullDim_fiber_bcProj_le f hdim B₀) b
    (Stacks.SheafOfModules.picardClass (bc f B₀).presheaf
      (Stacks.RingedSpace.structureIsSheaf (bc f B₀).toRingedSpace) L₀ hL₀) = d)
  (ι₀ : B₀ ⟶ A.X)
  (hclass : Stacks.SheafOfModules.picardClass (bc f B₀).presheaf
      (Stacks.RingedSpace.structureIsSheaf (bc f B₀).toRingedSpace) L₀ hL₀ =
    schemePullbackClass (bcMap f ι₀) (abelTranslatedClass f hdim σ hσ A e θ))
  (V' : A.X.left.Opens) (jV : V'.toScheme ⟶ B₀.left) (hj : jV ≫ ι₀.left = V'.ι)
  (hjV : Set.range jV ⊆ V)

/-- Given an open cover `y ∈ U y` of `Y` and `r : R ⟶ Y`, every point `ρ` of `R` has an affine
open neighbourhood on which `r` factors through `U (r ρ)`. -/
private theorem exists_isAffineOpen_mem_factor {R Y : Scheme.{u}} (r : R ⟶ Y) (U : Y → Y.Opens)
    (hxU : ∀ y, y ∈ U y) (ρ : R) :
    ∃ O : R.Opens, IsAffineOpen O ∧ ρ ∈ O ∧
      ∃ o : O.toScheme ⟶ U (r ρ), o ≫ (U (r ρ)).ι = O.ι ≫ r := by
  obtain ⟨O, hO, hρO, hOU⟩ := exists_isAffineOpen_mem_and_subset
    (show ρ ∈ r ⁻¹ᵁ U (r ρ) from hxU (r ρ))
  refine ⟨O, hO, hρO, IsOpenImmersion.lift (U (r ρ)).ι (O.ι ≫ r) ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact hOU z.2

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- `famHom` with the coefficient-tuple rewritten along an equality of base maps. -/
theorem famHom_congr_v {T : Over (Spec (.of k))} {v v' : T ⟶ B₀} (hvv : v = v')
    (hv : Set.range v.left ⊆ V) (hv' : Set.range v'.left ⊆ V)
    (c : Fin (m + 1) → Γ(T.left, ⊤)) (hc : Ideal.span (Set.range c) = ⊤) :
    famHom f L₀ hL₀ es hbasis hdim hdeg₀ hH v hv c hc =
      famHom f L₀ hL₀ es hbasis hdim hdeg₀ hH v' hv' c hc := by
  subst hvv
  rfl

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- `famHom` over two presentations of the same scheme over `k` with the same base map. -/
theorem famHom_left_congr {R : Scheme.{u}} {h₁ h₂ : R ⟶ Spec (.of k)} (hh : h₁ = h₂)
    (v₁ : Over.mk h₁ ⟶ B₀) (v₂ : Over.mk h₂ ⟶ B₀) (hv : v₁.left = v₂.left)
    (hv₁ : Set.range v₁.left ⊆ V) (hv₂ : Set.range v₂.left ⊆ V)
    (c : Fin (m + 1) → Γ(R, ⊤)) (hc : Ideal.span (Set.range c) = ⊤) :
    (famHom f L₀ hL₀ es hbasis hdim hdeg₀ hH v₁ hv₁ c hc).left =
      (famHom f L₀ hL₀ es hbasis hdim hdeg₀ hH v₂ hv₂ c hc).left := by
  subst hh
  obtain rfl : v₁ = v₂ := Over.OverMorphism.ext hv
  rfl


/-- The structure map of `ℙᵐ_{V'}` to `Spec k`. -/
abbrev chartStructure : projectiveSpaceOver m V'.toScheme ⟶ Spec (.of k) :=
  (projectiveSpaceOver m V'.toScheme ↘ V'.toScheme) ≫ V'.ι ≫ A.X.hom

include hj in
/-- The composite `R ⟶ ℙᵐ_{V'} ⟶ V' ⟶ B₀` commutes with the structure maps to `Spec k`. -/
theorem chartBase_w {R : Scheme.{u}} (r : R ⟶ projectiveSpaceOver m V'.toScheme) :
    (r ≫ (projectiveSpaceOver m V'.toScheme ↘ V'.toScheme) ≫ jV) ≫ B₀.hom =
      (Over.mk (r ≫ chartStructure A V' (m := m))).hom := by
  rw [← Over.w ι₀]
  simp only [Over.mk_hom, Category.assoc]
  rw [← Category.assoc jV, hj]

/-- The map `R ⟶ B₀` over `k` induced by `r : R ⟶ ℙᵐ_{V'}`. -/
abbrev chartBase {R : Scheme.{u}} (r : R ⟶ projectiveSpaceOver m V'.toScheme) :
    Over.mk (r ≫ chartStructure A V' (m := m)) ⟶ B₀ :=
  Over.homMk (r ≫ (projectiveSpaceOver m V'.toScheme ↘ V'.toScheme) ≫ jV)
    (chartBase_w A ι₀ V' jV hj r)

include hjV in
/-- The underlying morphism of `chartBase r` has range contained in `V`. -/
theorem range_chartBase {R : Scheme.{u}} (r : R ⟶ projectiveSpaceOver m V'.toScheme) :
    Set.range (chartBase A ι₀ V' jV hj r).left ⊆ V := by
  rintro _ ⟨x, rfl⟩
  exact hjV ⟨_, rfl⟩


omit [Flat f] [LocallyOfFinitePresentation f] in
include hbasis hjV in
/-- The key compatibility for the chart maps to the Hilbert scheme: restricting the classifying
map of a chart along `o` gives the classifying map of the restricted coordinates. -/
theorem comp_famHom_chartBase {R U : Scheme.{u}} (r : R ⟶ projectiveSpaceOver m V'.toScheme)
    (ιU : U ⟶ projectiveSpaceOver m V'.toScheme) (o : R ⟶ U) (ho : o ≫ ιU = r)
    (bU : Fin (m + 1) → Γ(U, ⊤)) (hbU : Ideal.span (Set.range bU) = ⊤)
    (b : Fin (m + 1) → Γ(R, ⊤)) (hb : Ideal.span (Set.range b) = ⊤)
    (hcoord : o ≫ homOfCoords bU hbU = homOfCoords b hb) :
    o ≫ (famHom f L₀ hL₀ es hbasis hdim hdeg₀ hH (chartBase A ι₀ V' jV hj ιU)
        (range_chartBase A ι₀ V' jV hj hjV ιU) bU hbU).left =
      (famHom f L₀ hL₀ es hbasis hdim hdeg₀ hH (chartBase A ι₀ V' jV hj r)
        (range_chartBase A ι₀ V' jV hj hjV r) b hb).left := by
  let a : Over.mk (r ≫ chartStructure A V' (m := m)) ⟶
      Over.mk (ιU ≫ chartStructure A V' (m := m)) :=
    Over.homMk o (by simp only [Over.mk_hom, ← ho, Category.assoc])
  have hv : Set.range (a ≫ chartBase A ι₀ V' jV hj ιU).left ⊆ V := by
    rintro _ ⟨x, rfl⟩; exact hjV ⟨_, rfl⟩
  have h1 := comp_famHom f L₀ hL₀ es hbasis hdim hdeg₀ hH a (chartBase A ι₀ V' jV hj ιU)
    (range_chartBase A ι₀ V' jV hj hjV ιU) bU hbU hv
  have h2 : a ≫ chartBase A ι₀ V' jV hj ιU = chartBase A ι₀ V' jV hj r := by
    ext1
    simp [a, ← ho]
  have h3 := congrArg CommaMorphism.left h1
  have h4 := congrArg CommaMorphism.left (famHom_congr_v f hdim hH L₀ hL₀ es hbasis hdeg₀ h2
    hv (range_chartBase A ι₀ V' jV hj hjV r)
    (fun i => a.left.appTop (bU i)) (span_range_appTop_comp a.left bU hbU))
  have h5 := famHom_congr f L₀ hL₀ es hbasis hdim hdeg₀ hH (chartBase A ι₀ V' jV hj r)
    (range_chartBase A ι₀ V' jV hj hjV r) (fun i => a.left.appTop (bU i)) b
    (span_range_appTop_comp a.left bU hbU) hb ((comp_homOfCoords o bU hbU).symm.trans hcoord)
  exact h3.trans (h4.trans (congrArg CommaMorphism.left h5))

end Stacks.RigidifiedPicard

namespace Stacks.RigidifiedPicard

open Stacks.Picard Stacks.ProjectiveSpaceModuli

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIrreducible f]
  [Flat f] [LocallyOfFinitePresentation f] [LocallyOfFiniteType f]
  (hdim : ∀ s : Spec (.of k), topologicalKrullDim ↥(f.fiber s) ≤ 1)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
  (A : Grp (Over (Spec (.of k)))) (e : yonedaGrp.obj A ≅ functorZero f hdim σ hσ)
  (θ : Stacks.Picard.ofScheme X) {d : ℕ}
  (hθ : ∀ s : Spec (.of k), relativeInvertibleDegreeHomAt f hdim s θ = d)
  {H : Over (Spec (.of k))} (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H d)
  {B₀ : Over (Spec (.of k))} (L₀ : (bc f B₀).Modules)
  (hL₀ : Stacks.SheafOfModules.IsInvertible (bc f B₀).presheaf (bc f B₀).ringCatSheaf.2 L₀)
  {m : ℕ} (es : Fin (m + 1) → Γ(L₀, ⊤)) {V : B₀.left.Opens} (hbasis : IsSectionBasis f L₀ es V)
  (hdeg₀ : ∀ b : B₀.left, relativeInvertibleDegreeHomAt (bcProj f B₀)
    (topologicalKrullDim_fiber_bcProj_le f hdim B₀) b
    (Stacks.SheafOfModules.picardClass (bc f B₀).presheaf
      (Stacks.RingedSpace.structureIsSheaf (bc f B₀).toRingedSpace) L₀ hL₀) = d)
  (ι₀ : B₀ ⟶ A.X)
  (V' : A.X.left.Opens) (jV : V'.toScheme ⟶ B₀.left) (hj : jV ≫ ι₀.left = V'.ι)
  (hjV : Set.range jV ⊆ V)

omit [Flat f] [LocallyOfFinitePresentation f] in
include hbasis hjV in
/-- **The map `ℙᵐ_{V'} ⟶ Hilb^d`**, glued from the classifying maps of the charts. -/
theorem exists_projectiveSpaceOver_hom_hilb : ∃ Ψ₀ : projectiveSpaceOver m V'.toScheme ⟶ H.left,
    ∀ {R : Scheme.{u}} (r : R ⟶ projectiveSpaceOver m V'.toScheme)
      (b : Fin (m + 1) → Γ(R, ⊤)) (hb : Ideal.span (Set.range b) = ⊤),
      r ≫ (pullback.snd _ _ : projectiveSpaceOver m V'.toScheme ⟶ _) = homOfCoords b hb →
      r ≫ Ψ₀ = (famHom f L₀ hL₀ es hbasis hdim hdeg₀ hH (chartBase A ι₀ V' jV hj r)
        (range_chartBase A ι₀ V' jV hj hjV r) b hb).left := by
  classical
  set s : projectiveSpaceOver m V'.toScheme ⟶ projectiveSpaceAtUniverse.{u} m := pullback.snd _ _
  choose U hxU hUaff b hb hUs using fun x => exists_isAffineOpen_comp_eq_homOfCoords s x
  let ψ : ∀ x, (U x).toScheme ⟶ H.left := fun x =>
    (famHom f L₀ hL₀ es hbasis hdim hdeg₀ hH (chartBase A ι₀ V' jV hj (U x).ι)
      (range_chartBase A ι₀ V' jV hj hjV (U x).ι) (b x) (hb x)).left
  have key : ∀ {R : Scheme.{u}} (r₀ : R ⟶ projectiveSpaceOver m V'.toScheme) (x)
      (o : R ⟶ U x) (ho : o ≫ (U x).ι = r₀) (b' : Fin (m + 1) → Γ(R, ⊤))
      (hb' : Ideal.span (Set.range b') = ⊤) (hrs : r₀ ≫ s = homOfCoords b' hb'),
      o ≫ ψ x = (famHom f L₀ hL₀ es hbasis hdim hdeg₀ hH (chartBase A ι₀ V' jV hj r₀)
        (range_chartBase A ι₀ V' jV hj hjV r₀) b' hb').left := by
    intro R r₀ x o ho b' hb' hrs
    refine comp_famHom_chartBase f hdim A hH L₀ hL₀ es hbasis hdeg₀ ι₀ V' jV hj hjV r₀ (U x).ι o ho
      (b x) (hb x) b' hb' ?_
    rw [← hrs, ← ho, Category.assoc, hUs]
  have hcoord : ∀ {R : Scheme.{u}} (x) (o : R ⟶ U x),
      homOfCoords (fun i => o.appTop (b x i)) (span_range_appTop_comp o (b x) (hb x)) =
        o ≫ (U x).ι ≫ s := fun x o =>
    (comp_homOfCoords o (b x) (hb x)).symm.trans (by rw [hUs x])
  obtain ⟨Ψ₀, hΨ⟩ := Scheme.exists_hom_of_affine_compat U hxU ψ (by
    intro x y R _ r r' h
    have h1 := key (r ≫ (U x).ι) x r rfl _ (span_range_appTop_comp r (b x) (hb x))
      (by rw [Category.assoc, hUs, comp_homOfCoords])
    have h2 := key (r ≫ (U x).ι) y r' h.symm _ (span_range_appTop_comp r' (b y) (hb y))
      (by rw [h, Category.assoc, hUs, comp_homOfCoords])
    rw [h1, h2]
    congr 1
    refine famHom_congr f L₀ hL₀ es hbasis hdim hdeg₀ hH _ _ _ _ _ _ ?_
    rw [hcoord, hcoord, reassoc_of% h])
  refine ⟨Ψ₀, fun {R} r b' hb' hrs => ?_⟩
  refine Scheme.hom_ext_of_forall _ _ fun ρ => ?_
  obtain ⟨O, -, hρO, o, ho⟩ := exists_isAffineOpen_mem_factor r U hxU ρ
  refine ⟨O, hρO, ?_⟩
  have hL : O.ι ≫ r ≫ Ψ₀ = o ≫ ψ (r ρ) := by
    rw [← hΨ (r ρ), ← Category.assoc, ← ho, Category.assoc]
  rw [hL, key (O.ι ≫ r) (r ρ) o ho _ (span_range_appTop_comp o (b (r ρ)) (hb (r ρ)))
    (by rw [← ho, Category.assoc, hUs, comp_homOfCoords]),
    comp_famHom_chartBase f hdim A hH L₀ hL₀ es hbasis hdeg₀ ι₀ V' jV hj hjV (O.ι ≫ r) r O.ι rfl
      b' hb' _ (span_range_appTop_comp O.ι b' hb') (comp_homOfCoords O.ι b' hb')]
  congr 1
  refine famHom_congr f L₀ hL₀ es hbasis hdim hdeg₀ hH _ _ _ _ _ _ ?_
  rw [hcoord, ← comp_homOfCoords O.ι b' hb', ← hrs, reassoc_of% ho]

end Stacks.RigidifiedPicard

namespace Stacks.RigidifiedPicard

open Stacks.Picard Stacks.ProjectiveSpaceModuli

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIrreducible f]
  [Flat f] [LocallyOfFinitePresentation f]
  (hdim : ∀ s : Spec (.of k), topologicalKrullDim ↥(f.fiber s) ≤ 1)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
  (A : Grp (Over (Spec (.of k)))) (e : yonedaGrp.obj A ≅ functorZero f hdim σ hσ)
  (θ : Stacks.Picard.ofScheme X) {d : ℕ}
  (hθ : ∀ s : Spec (.of k), relativeInvertibleDegreeHomAt f hdim s θ = d)
  {H : Over (Spec (.of k))} (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H d)
  {B₀ : Over (Spec (.of k))} (L₀ : (bc f B₀).Modules)
  (hL₀ : Stacks.SheafOfModules.IsInvertible (bc f B₀).presheaf (bc f B₀).ringCatSheaf.2 L₀)
  {m : ℕ} (es : Fin (m + 1) → Γ(L₀, ⊤)) {V : B₀.left.Opens} (hbasis : IsSectionBasis f L₀ es V)
  (hdeg₀ : ∀ b : B₀.left, relativeInvertibleDegreeHomAt (bcProj f B₀)
    (topologicalKrullDim_fiber_bcProj_le f hdim B₀) b
    (Stacks.SheafOfModules.picardClass (bc f B₀).presheaf
      (Stacks.RingedSpace.structureIsSheaf (bc f B₀).toRingedSpace) L₀ hL₀) = d)
  (ι₀ : B₀ ⟶ A.X)
  (hclass : Stacks.SheafOfModules.picardClass (bc f B₀).presheaf
      (Stacks.RingedSpace.structureIsSheaf (bc f B₀).toRingedSpace) L₀ hL₀ =
    schemePullbackClass (bcMap f ι₀) (abelTranslatedClass f hdim σ hσ A e θ))
  (V' : A.X.left.Opens) (jV : V'.toScheme ⟶ B₀.left) (hj : jV ≫ ι₀.left = V'.ι)
  (hjV : Set.range jV ⊆ V)

/-- The open `γ⁻¹(V')` of the Hilbert scheme. -/
abbrev abelPreimage : H.left.Opens := (abelMorphism f hdim σ hσ θ hθ hH A e).left ⁻¹ᵁ V'

/-- The structure map of `γ⁻¹(V')` to `Spec k`. -/
abbrev abelPreimageStructure : (abelPreimage f hdim σ hσ A e θ hθ hH V').toScheme ⟶ Spec (.of k) :=
  (abelPreimage f hdim σ hσ A e θ hθ hH V').ι ≫ H.hom

/-- `r : R ⟶ γ⁻¹(V')` as a morphism of `k`-schemes into `H`. -/
abbrev abelPreimageHilb {R : Scheme.{u}} (r : R ⟶ (abelPreimage f hdim σ hσ A e θ hθ hH
    V').toScheme) :
    Over.mk (r ≫ abelPreimageStructure f hdim σ hσ A e θ hθ hH V') ⟶ H :=
  Over.homMk (r ≫ (abelPreimage f hdim σ hσ A e θ hθ hH V').ι) (by simp)

omit [GeometricallyIrreducible f] in
include hj in
/-- The composite `R ⟶ γ⁻¹(V') ⟶ V' ⟶ B₀` commutes with the structure maps to `Spec k`. -/
theorem abelPreimageBase_w {R : Scheme.{u}} (r : R ⟶ (abelPreimage f hdim σ hσ A e θ hθ hH
    V').toScheme) :
    (r ≫ ((abelMorphism f hdim σ hσ θ hθ hH A e).left ∣_ V') ≫ jV) ≫ B₀.hom =
      (Over.mk (r ≫ abelPreimageStructure f hdim σ hσ A e θ hθ hH V')).hom := by
  rw [← Over.w ι₀]
  simp only [Over.mk_hom, Category.assoc]
  rw [← Category.assoc jV, hj, morphismRestrict_ι_assoc, Over.w]

/-- The map to `B₀` induced by `r : R ⟶ γ⁻¹(V')`. -/
abbrev abelPreimageBase {R : Scheme.{u}} (r : R ⟶ (abelPreimage f hdim σ hσ A e θ hθ hH
    V').toScheme) :
    Over.mk (r ≫ abelPreimageStructure f hdim σ hσ A e θ hθ hH V') ⟶ B₀ :=
  Over.homMk (r ≫ ((abelMorphism f hdim σ hσ θ hθ hH A e).left ∣_ V') ≫ jV)
    (abelPreimageBase_w f hdim σ hσ A e θ hθ hH ι₀ V' jV hj r)

omit [GeometricallyIrreducible f] in
include hjV in
/-- The underlying morphism of `abelPreimageBase r` has range contained in `V`. -/
theorem range_abelPreimageBase {R : Scheme.{u}} (r : R ⟶ (abelPreimage f hdim σ hσ A e θ hθ hH
    V').toScheme) :
    Set.range (abelPreimageBase f hdim σ hσ A e θ hθ hH ι₀ V' jV hj r).left ⊆ V := by
  rintro _ ⟨x, rfl⟩
  exact hjV ⟨_, rfl⟩


include hbasis hjV in
/-- Restricting a chart relation `abelPreimageHilb = famHom` along `o`. -/
theorem abelPreimageHilb_eq_famHom_of_comp {R U : Scheme.{u}}
    (r : R ⟶ (abelPreimage f hdim σ hσ A e θ hθ hH V').toScheme)
    (ιU : U ⟶ (abelPreimage f hdim σ hσ A e θ hθ hH V').toScheme) (o : R ⟶ U) (ho : o ≫ ιU = r)
    (cU : Fin (m + 1) → Γ(U, ⊤)) (hcU : Ideal.span (Set.range cU) = ⊤)
    (hU : abelPreimageHilb f hdim σ hσ A e θ hθ hH V' ιU = famHom f L₀ hL₀ es hbasis hdim hdeg₀ hH
      (abelPreimageBase f hdim σ hσ A e θ hθ hH ι₀ V' jV hj ιU) (range_abelPreimageBase f hdim σ hσ
          A e θ hθ hH ι₀ V' jV hj hjV ιU)
      cU hcU) :
    abelPreimageHilb f hdim σ hσ A e θ hθ hH V' r = famHom f L₀ hL₀ es hbasis hdim hdeg₀ hH
      (abelPreimageBase f hdim σ hσ A e θ hθ hH ι₀ V' jV hj r) (range_abelPreimageBase f hdim σ hσ
          A e θ hθ hH ι₀ V' jV hj hjV r)
      (fun i => o.appTop (cU i)) (span_range_appTop_comp o cU hcU) := by
  let a : Over.mk (r ≫ abelPreimageStructure f hdim σ hσ A e θ hθ hH V') ⟶
      Over.mk (ιU ≫ abelPreimageStructure f hdim σ hσ A e θ hθ hH V') :=
    Over.homMk o (by simp only [Over.mk_hom, ← ho, Category.assoc])
  have h1 : abelPreimageHilb f hdim σ hσ A e θ hθ hH V' r = a ≫ abelPreimageHilb f hdim σ hσ A e θ
      hθ hH V' ιU := by
    ext1
    simp [a, ← ho]
  have h2 : a ≫ abelPreimageBase f hdim σ hσ A e θ hθ hH ι₀ V' jV hj ιU =
      abelPreimageBase f hdim σ hσ A e θ hθ hH ι₀ V' jV hj r := by
    ext1
    simp [a, ← ho]
  rw [h1, hU, comp_famHom f L₀ hL₀ es hbasis hdim hdeg₀ hH a _ _ cU hcU
    (by rintro _ ⟨x, rfl⟩; exact hjV ⟨_, rfl⟩)]
  exact famHom_congr_v f hdim hH L₀ hL₀ es hbasis hdeg₀ h2 _ _ _ _

omit [GeometricallyIrreducible f] in
/-- The chart maps lie over `B₀`. -/
theorem abelPreimageHilb_comp_abelMorphism {R : Scheme.{u}}
    (r : R ⟶ (abelPreimage f hdim σ hσ A e θ hθ hH V').toScheme) :
    abelPreimageHilb f hdim σ hσ A e θ hθ hH V' r ≫ abelMorphism f hdim σ hσ θ hθ hH A e =
      abelPreimageBase f hdim σ hσ A e θ hθ hH ι₀ V' jV hj r ≫ ι₀ := by
  ext1
  simp only [Over.comp_left, Over.homMk_left, Category.assoc]
  rw [hj, morphismRestrict_ι]


omit [GeometricallyIrreducible f] in
include hclass in
/-- On a piece `r` of `γ⁻¹(V')` killing the twist `n`, the Abel class of the chart family is the
pull-back of the class of `L₀`. -/
private theorem abelClass_family_abelPreimageHilb_eq {R : Scheme.{u}}
    (r : R ⟶ (abelPreimage f hdim σ hσ A e θ hθ hH V').toScheme)
    (n : ofScheme (abelPreimage f hdim σ hσ A e θ hθ hH V').toScheme)
    (hn : abelClass f (hH.family (abelPreimageHilb f hdim σ hσ A e θ hθ hH V' (𝟙 _))) +
        schemePullbackClass
          (bcProj f (Over.mk (𝟙 _ ≫ abelPreimageStructure f hdim σ hσ A e θ hθ hH V'))) n =
      schemePullbackClass
        (bcMap f (abelPreimageBase f hdim σ hσ A e θ hθ hH ι₀ V' jV hj (𝟙 _) ≫ ι₀))
        (abelTranslatedClass f hdim σ hσ A e θ))
    (hr : schemePullbackClass r n = 0) :
    abelClass f (hH.family (abelPreimageHilb f hdim σ hσ A e θ hθ hH V' r)) =
      schemePullbackClass (bcMap f (abelPreimageBase f hdim σ hσ A e θ hθ hH ι₀ V' jV hj r))
        (Stacks.SheafOfModules.picardClass (bc f B₀).presheaf
          (Stacks.RingedSpace.structureIsSheaf (bc f B₀).toRingedSpace) L₀ hL₀) := by
  let a : Over.mk (r ≫ abelPreimageStructure f hdim σ hσ A e θ hθ hH V') ⟶
      Over.mk (𝟙 _ ≫ abelPreimageStructure f hdim σ hσ A e θ hθ hH V') :=
    Over.homMk r (by simp)
  have h1 : abelPreimageHilb f hdim σ hσ A e θ hθ hH V' r =
      a ≫ abelPreimageHilb f hdim σ hσ A e θ hθ hH V' (𝟙 _) := by
    ext1
    simp [a]
  have h2 : a ≫ abelPreimageBase f hdim σ hσ A e θ hθ hH ι₀ V' jV hj (𝟙 _) =
      abelPreimageBase f hdim σ hσ A e θ hθ hH ι₀ V' jV hj r := by
    ext1
    simp [a]
  have hz : schemePullbackClass a.left n = 0 := hr
  calc abelClass f (hH.family (abelPreimageHilb f hdim σ hσ A e θ hθ hH V' r))
      = abelClass f (hH.family (a ≫ abelPreimageHilb f hdim σ hσ A e θ hθ hH V' (𝟙 _))) := by
        rw [h1]
    _ = schemePullbackClass (bcMap f a)
          (abelClass f (hH.family (abelPreimageHilb f hdim σ hσ A e θ hθ hH V' (𝟙 _)))) := by
        rw [family_comp, abelClass_baseChange]
    _ = schemePullbackClass (bcMap f a)
          (schemePullbackClass
            (bcMap f (abelPreimageBase f hdim σ hσ A e θ hθ hH ι₀ V' jV hj (𝟙 _) ≫ ι₀))
            (abelTranslatedClass f hdim σ hσ A e θ) - schemePullbackClass (bcProj f _) n) := by
        rw [eq_sub_of_add_eq hn]
    _ = schemePullbackClass (bcMap f a)
          (schemePullbackClass
            (bcMap f (abelPreimageBase f hdim σ hσ A e θ hθ hH ι₀ V' jV hj (𝟙 _) ≫ ι₀))
            (abelTranslatedClass f hdim σ hσ A e θ)) -
          schemePullbackClass (bcProj f _) (schemePullbackClass a.left n) := by
        rw [schemePullbackClass_sub', schemePullbackClass_bcProj_natural]
    _ = _ := by
        rw [hz, show schemePullbackClass (bcProj f (Over.mk (r ≫
            abelPreimageStructure f hdim σ hσ A e θ hθ hH V'))) (0 : ofScheme R) = 0 from
            map_zero (schemePullbackClassHom _), sub_zero,
          schemePullbackClass_comp, ← bcMap_comp,
          show a ≫ abelPreimageBase f hdim σ hσ A e θ hθ hH ι₀ V' jV hj (𝟙 _) ≫ ι₀ =
            abelPreimageBase f hdim σ hσ A e θ hθ hH ι₀ V' jV hj r ≫ ι₀ from
            (Category.assoc _ _ _).symm.trans (congrArg (· ≫ ι₀) h2), hclass,
          schemePullbackClass_comp, ← bcMap_comp]

include hbasis hjV in
/-- Over an affine `R`, a chart relation `abelPreimageHilb = famHom` on `ιU` determines the
coordinates of any chart relation on `r = o ≫ ιU` up to `homOfCoords`. -/
private theorem comp_homOfCoords_eq_of_abelPreimageHilb_eq {R U : Scheme.{u}} [IsAffine R]
    (r : R ⟶ (abelPreimage f hdim σ hσ A e θ hθ hH V').toScheme)
    (ιU : U ⟶ (abelPreimage f hdim σ hσ A e θ hθ hH V').toScheme) (o : R ⟶ U) (ho : o ≫ ιU = r)
    (cU : Fin (m + 1) → Γ(U, ⊤)) (hcU : Ideal.span (Set.range cU) = ⊤)
    (hU : abelPreimageHilb f hdim σ hσ A e θ hθ hH V' ιU = famHom f L₀ hL₀ es hbasis hdim hdeg₀ hH
      (abelPreimageBase f hdim σ hσ A e θ hθ hH ι₀ V' jV hj ιU)
      (range_abelPreimageBase f hdim σ hσ A e θ hθ hH ι₀ V' jV hj hjV ιU) cU hcU)
    (c : Fin (m + 1) → Γ(R, ⊤)) (hc : Ideal.span (Set.range c) = ⊤)
    (hr : abelPreimageHilb f hdim σ hσ A e θ hθ hH V' r = famHom f L₀ hL₀ es hbasis hdim hdeg₀ hH
      (abelPreimageBase f hdim σ hσ A e θ hθ hH ι₀ V' jV hj r)
      (range_abelPreimageBase f hdim σ hσ A e θ hθ hH ι₀ V' jV hj hjV r) c hc) :
    o ≫ homOfCoords cU hcU = homOfCoords c hc := by
  have : IsAffine (Over.mk (r ≫ abelPreimageStructure f hdim σ hσ A e θ hθ hH V')).left :=
    ‹IsAffine R›
  rw [comp_homOfCoords]
  refine homOfCoords_eq_of_famHom_eq f L₀ hL₀ es hbasis hdim hdeg₀ hH
    (T := Over.mk (r ≫ abelPreimageStructure f hdim σ hσ A e θ hθ hH V'))
    (abelPreimageBase f hdim σ hσ A e θ hθ hH ι₀ V' jV hj r)
    (range_abelPreimageBase f hdim σ hσ A e θ hθ hH ι₀ V' jV hj hjV r) _ _ _ _ ?_
  rw [← abelPreimageHilb_eq_famHom_of_comp f hdim σ hσ A e θ hθ hH L₀ hL₀ es hbasis hdeg₀ ι₀ V'
    jV hj hjV r ιU o ho cU hcU hU, hr]

include hbasis hclass hjV in
/-- **The map `γ⁻¹(V') ⟶ ℙᵐ_{V'}`**, glued from the coordinates of the charts. -/
theorem exists_abelPreimage_hom_projectiveSpaceOver : ∃ Φ : (abelPreimage f hdim σ hσ A e θ hθ hH
    V').toScheme ⟶
      projectiveSpaceOver m V'.toScheme,
    Φ ≫ (projectiveSpaceOver m V'.toScheme ↘ V'.toScheme) =
        (abelMorphism f hdim σ hσ θ hθ hH A e).left ∣_ V' ∧
    (∀ {R : Scheme.{u}} [IsAffine R] (r : R ⟶ (abelPreimage f hdim σ hσ A e θ hθ hH V').toScheme)
      (c : Fin (m + 1) → Γ(R, ⊤)) (hc : Ideal.span (Set.range c) = ⊤),
      abelPreimageHilb f hdim σ hσ A e θ hθ hH V' r = famHom f L₀ hL₀ es hbasis hdim hdeg₀ hH
        (abelPreimageBase f hdim σ hσ A e θ hθ hH ι₀ V' jV hj r)
        (range_abelPreimageBase f hdim σ hσ A e θ hθ hH ι₀ V' jV hj hjV r) c hc →
      r ≫ Φ ≫ (pullback.snd _ _ : projectiveSpaceOver m V'.toScheme ⟶ _) = homOfCoords c hc) ∧
    ∀ x : abelPreimage f hdim σ hσ A e θ hθ hH V', ∃ (O : (abelPreimage f hdim σ hσ A e θ hθ hH
        V').toScheme.Opens)
      (_ : x ∈ O) (_ : IsAffineOpen O) (c : Fin (m + 1) → Γ(O, ⊤))
      (hc : Ideal.span (Set.range c) = ⊤),
      abelPreimageHilb f hdim σ hσ A e θ hθ hH V' O.ι = famHom f L₀ hL₀ es hbasis hdim hdeg₀ hH
        (abelPreimageBase f hdim σ hσ A e θ hθ hH ι₀ V' jV hj O.ι)
        (range_abelPreimageBase f hdim σ hσ A e θ hθ hH ι₀ V' jV hj hjV O.ι) c hc := by
  classical
  obtain ⟨nG, hnG⟩ := exists_abelClass_add_eq_of_comp_abelMorphism f hdim σ hσ A e θ hθ hH
    (abelPreimageHilb f hdim σ hσ A e θ hθ hH V' (𝟙 _)) (abelPreimageBase f hdim σ hσ A e θ hθ hH
        ι₀ V' jV hj (𝟙 _) ≫ ι₀)
    (abelPreimageHilb_comp_abelMorphism f hdim σ hσ A e θ hθ hH ι₀ V' jV hj (𝟙 _))
  choose U hUaff hxU hn0 using fun x =>
      AlgebraicGeometry.exists_isAffineOpen_schemePullbackClass_eq_zero nG x
  have hUa : ∀ x, IsAffine (Over.mk ((U x).ι ≫ abelPreimageStructure f hdim σ hσ A e θ hθ hH
      V')).left := hUaff
  choose c hc hcU using fun x => @exists_famHom_eq k _ X f _ _ _ B₀ L₀ hL₀ m es V hbasis _ hdim d
    hdeg₀ H hH _ (hUa x) (abelPreimageBase f hdim σ hσ A e θ hθ hH ι₀ V' jV hj (U x).ι)
    (range_abelPreimageBase f hdim σ hσ A e θ hθ hH ι₀ V' jV hj hjV (U x).ι)
    (abelPreimageHilb f hdim σ hσ A e θ hθ hH V' (U x).ι)
    (abelClass_family_abelPreimageHilb_eq f hdim σ hσ A e θ hθ hH L₀ hL₀ ι₀ hclass V' jV hj
      (U x).ι nG hnG (hn0 x))
  set γ' := (abelMorphism f hdim σ hσ θ hθ hH A e).left ∣_ V'
  let φ : ∀ x, (U x).toScheme ⟶ projectiveSpaceOver m V'.toScheme := fun x =>
    pullback.lift ((U x).ι ≫ γ') (homOfCoords (c x) (hc x)) (terminal.hom_ext _ _)
  obtain ⟨Φ, hΦ⟩ := Scheme.exists_hom_of_affine_compat U hxU φ (by
    intro x y R _ r r' h
    refine pullback.hom_ext ?_ ?_
    · simp only [φ, Category.assoc, pullback.lift_fst]
      rw [← Category.assoc, h, Category.assoc]
    · simp only [φ, Category.assoc, pullback.lift_snd]
      have hr := abelPreimageHilb_eq_famHom_of_comp f hdim σ hσ A e θ hθ hH L₀ hL₀ es hbasis hdeg₀
        ι₀ V' jV hj hjV (r ≫ (U x).ι) (U x).ι r rfl (c x) (hc x) (hcU x)
      rw [comp_homOfCoords_eq_of_abelPreimageHilb_eq f hdim σ hσ A e θ hθ hH L₀ hL₀ es hbasis
          hdeg₀ ι₀ V' jV hj hjV (r ≫ (U x).ι) (U x).ι r rfl (c x) (hc x) (hcU x) _ _ hr,
        comp_homOfCoords_eq_of_abelPreimageHilb_eq f hdim σ hσ A e θ hθ hH L₀ hL₀ es hbasis
          hdeg₀ ι₀ V' jV hj hjV (r ≫ (U x).ι) (U y).ι r' h.symm (c y) (hc y) (hcU y) _ _ hr])
  refine ⟨Φ, ?_, ?_, fun x => ⟨U x, hxU x, hUaff x, c x, hc x, hcU x⟩⟩
  · refine Scheme.hom_ext_of_forall _ _ fun x => ⟨U x, hxU x, ?_⟩
    rw [← Category.assoc, hΦ x]
    exact pullback.lift_fst _ _ _
  · intro R _ r c' hc' hr
    refine Scheme.hom_ext_of_forall _ _ fun ρ => ?_
    obtain ⟨O, hO, hρO, o, ho⟩ := exists_isAffineOpen_mem_factor r U hxU ρ
    refine ⟨O, hρO, ?_⟩
    have : IsAffine O.toScheme := hO
    have hr' := abelPreimageHilb_eq_famHom_of_comp f hdim σ hσ A e θ hθ hH L₀ hL₀ es hbasis hdeg₀
      ι₀ V' jV hj hjV (O.ι ≫ r) r O.ι rfl c' hc' hr
    rw [comp_homOfCoords, ← comp_homOfCoords_eq_of_abelPreimageHilb_eq f hdim σ hσ A e θ hθ hH L₀
        hL₀ es hbasis hdeg₀ ι₀ V' jV hj hjV (O.ι ≫ r) (U (r ρ)).ι o ho (c (r ρ)) (hc (r ρ))
        (hcU (r ρ)) _ _ hr', ← Category.assoc, ← Category.assoc, ← ho, Category.assoc o, hΦ]
    exact (Category.assoc _ _ _).trans (congrArg (o ≫ ·) (pullback.lift_snd _ _ _))

include hbasis hclass hjV in
/-- A map `ℙᵐ_{V'} ⟶ Hilb^d` restricting to the chart classifying maps factors through
`γ⁻¹(V')`, over `V'`. -/
private theorem exists_lift_abelPreimage (Ψ₀ : projectiveSpaceOver m V'.toScheme ⟶ H.left)
    (hΨ : ∀ {R : Scheme.{u}} (r : R ⟶ projectiveSpaceOver m V'.toScheme)
      (b : Fin (m + 1) → Γ(R, ⊤)) (hb : Ideal.span (Set.range b) = ⊤),
      r ≫ (pullback.snd _ _ : projectiveSpaceOver m V'.toScheme ⟶ _) = homOfCoords b hb →
      r ≫ Ψ₀ = (famHom f L₀ hL₀ es hbasis hdim hdeg₀ hH (chartBase A ι₀ V' jV hj r)
        (range_chartBase A ι₀ V' jV hj hjV r) b hb).left) :
    ∃ Ψ : projectiveSpaceOver m V'.toScheme ⟶ (abelPreimage f hdim σ hσ A e θ hθ hH V').toScheme,
      Ψ ≫ (abelPreimage f hdim σ hσ A e θ hθ hH V').ι = Ψ₀ ∧
      Ψ ≫ ((abelMorphism f hdim σ hσ θ hθ hH A e).left ∣_ V') =
        projectiveSpaceOver m V'.toScheme ↘ V'.toScheme := by
  set G := abelPreimage f hdim σ hσ A e θ hθ hH V'
  set γ := abelMorphism f hdim σ hσ θ hθ hH A e
  set s : projectiveSpaceOver m V'.toScheme ⟶ projectiveSpaceAtUniverse.{u} m := pullback.snd _ _
  choose U hxU hUaff b hb hUs using fun x => exists_isAffineOpen_comp_eq_homOfCoords s x
  have hA : Ψ₀ ≫ γ.left = (projectiveSpaceOver m V'.toScheme ↘ V'.toScheme) ≫ V'.ι := by
    refine Scheme.hom_ext_of_forall _ _ fun x => ⟨U x, hxU x, ?_⟩
    rw [← Category.assoc, hΨ (U x).ι (b x) (hb x) (hUs x)]
    have h := congrArg CommaMorphism.left (famHom_comp_abelMorphism (f := f) (hdim := hdim)
      (σ := σ) (hσ := hσ) (A := A) (eA := e) (θ := θ) (hθ := hθ) (hH := hH) (L₀ := L₀)
      (hL₀ := hL₀) (es := es) (hbasis := hbasis) (hdeg₀ := hdeg₀) (ι₀ := ι₀) hclass
      (chartBase A ι₀ V' jV hj (U x).ι) (range_chartBase A ι₀ V' jV hj hjV (U x).ι) (b x) (hb x))
    simp only [Over.comp_left, Over.homMk_left, Category.assoc] at h
    rw [h, hj]
  have hrange : Set.range Ψ₀ ⊆ Set.range G.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hy := congrArg (fun g : projectiveSpaceOver m V'.toScheme ⟶ A.X.left => g y) hA
    change γ.left (Ψ₀ y) = V'.ι ((projectiveSpaceOver m V'.toScheme ↘ V'.toScheme) y) at hy
    show γ.left (Ψ₀ y) ∈ V'
    rw [hy]
    exact ((projectiveSpaceOver m V'.toScheme ↘ V'.toScheme) y).2
  have hΨι : IsOpenImmersion.lift G.ι Ψ₀ hrange ≫ G.ι = Ψ₀ := IsOpenImmersion.lift_fac _ _ _
  have hγ' : ((γ.left ∣_ V') ≫ V'.ι) = G.ι ≫ γ.left := morphismRestrict_ι _ _
  refine ⟨_, hΨι, ?_⟩
  rw [← cancel_mono V'.ι, Category.assoc, hγ', ← Category.assoc, hΨι, hA]

/-- The classifying maps of a chart over `ℙᵐ_{V'}` and over `γ⁻¹(V')` agree when `r` and `r'` agree
over `V'`. -/
private theorem famHom_chartBase_eq_abelPreimageBase {R : Scheme.{u}}
    (r : R ⟶ projectiveSpaceOver m V'.toScheme) (r' : R ⟶ (abelPreimage f hdim σ hσ A e θ hθ hH
      V').toScheme)
    (h : r ≫ (projectiveSpaceOver m V'.toScheme ↘ V'.toScheme) =
      r' ≫ (abelMorphism f hdim σ hσ θ hθ hH A e).left ∣_ V')
    (c : Fin (m + 1) → Γ(R, ⊤)) (hc : Ideal.span (Set.range c) = ⊤) :
    (famHom f L₀ hL₀ es hbasis hdim hdeg₀ hH (chartBase A ι₀ V' jV hj r)
        (range_chartBase A ι₀ V' jV hj hjV r) c hc).left =
      (famHom f L₀ hL₀ es hbasis hdim hdeg₀ hH
        (abelPreimageBase f hdim σ hσ A e θ hθ hH ι₀ V' jV hj r')
        (range_abelPreimageBase f hdim σ hσ A e θ hθ hH ι₀ V' jV hj hjV r') c hc).left := by
  refine famHom_left_congr (f := f) (hdim := hdim) (hH := hH) (L₀ := L₀) (hL₀ := hL₀)
    (es := es) (hbasis := hbasis) (hdeg₀ := hdeg₀) ?_ _ _ ?_ _ _ c hc
  · simp only [chartStructure, abelPreimageStructure,
      ← Over.w (abelMorphism f hdim σ hσ θ hθ hH A e)]
    rw [reassoc_of% h, reassoc_of% (morphismRestrict_ι _ _)]
  · simp only [Over.homMk_left, ← Category.assoc, h]

include hbasis hdeg₀ hclass hj hjV in
/-- **`γ⁻¹(V') ≅ ℙᵐ_{V'}` over `V'`.** -/
theorem exists_abelPreimage_iso : ∃ eI : (abelPreimage f hdim σ hσ A e θ hθ hH V').toScheme ≅
      projectiveSpaceOver m V'.toScheme,
    eI.hom ≫ (projectiveSpaceOver m V'.toScheme ↘ V'.toScheme) =
      (abelMorphism f hdim σ hσ θ hθ hH A e).left ∣_ V' := by
  classical
  set G := abelPreimage f hdim σ hσ A e θ hθ hH V'
  set γ := abelMorphism f hdim σ hσ θ hθ hH A e
  set P := projectiveSpaceOver m V'.toScheme
  set s : P ⟶ projectiveSpaceAtUniverse.{u} m := pullback.snd _ _
  obtain ⟨Ψ₀, hΨ⟩ :=
    exists_projectiveSpaceOver_hom_hilb f hdim A hH L₀ hL₀ es hbasis hdeg₀ ι₀ V' jV hj hjV
  obtain ⟨Φ, hΦq, hΦ, hcov⟩ := exists_abelPreimage_hom_projectiveSpaceOver f hdim σ hσ A e θ hθ hH
    L₀ hL₀ es hbasis hdeg₀ ι₀ hclass V' jV hj hjV
  obtain ⟨Ψ, hΨι, hΨγ⟩ :=
    exists_lift_abelPreimage f hdim σ hσ A e θ hθ hH L₀ hL₀ es hbasis hdeg₀ ι₀ hclass V' jV hj hjV
      Ψ₀ hΨ
  replace hΨι : Ψ ≫ G.ι = Ψ₀ := hΨι
  replace hΨγ : Ψ ≫ (γ.left ∣_ V') = P ↘ V'.toScheme := hΨγ
  choose U hxU hUaff b hb hUs using fun x => exists_isAffineOpen_comp_eq_homOfCoords s x
  have h1 : Φ ≫ Ψ = 𝟙 _ := by
    rw [← cancel_mono G.ι, Category.assoc, hΨι, Category.id_comp]
    refine Scheme.hom_ext_of_forall _ _ fun x => ?_
    obtain ⟨O, hxO, hO, c, hc, hOc⟩ := hcov x
    refine ⟨O, hxO, ?_⟩
    have : IsAffine O.toScheme := hO
    have hs := hΦ O.ι c hc hOc
    rw [← Category.assoc, hΨ (O.ι ≫ Φ) c hc (by rw [Category.assoc, hs])]
    have hl := congrArg CommaMorphism.left hOc
    simp only [Over.homMk_left] at hl
    rw [hl]
    exact (famHom_chartBase_eq_abelPreimageBase f hdim σ hσ A e θ hθ hH L₀ hL₀ es hbasis hdeg₀ ι₀
      V' jV hj hjV (O.ι ≫ Φ) O.ι (by rw [Category.assoc, hΦq]) c hc)
  have h2 : Ψ ≫ Φ = 𝟙 _ := by
    refine pullback.hom_ext ?_ ?_
    · show (Ψ ≫ Φ) ≫ (P ↘ V'.toScheme) = 𝟙 _ ≫ (P ↘ V'.toScheme)
      rw [Category.assoc, hΦq, hΨγ, Category.id_comp]
    · show (Ψ ≫ Φ) ≫ s = 𝟙 _ ≫ s
      rw [Category.id_comp]
      refine Scheme.hom_ext_of_forall _ _ fun x => ⟨U x, hxU x, ?_⟩
      have : IsAffine (U x).toScheme := hUaff x
      rw [hUs x, Category.assoc, ← Category.assoc]
      refine hΦ ((U x).ι ≫ Ψ) (b x) (hb x) ?_
      ext1
      simp only [Over.homMk_left]
      refine (Category.assoc _ _ _).trans (((congrArg ((U x).ι ≫ ·) hΨι).trans
        (hΨ (U x).ι (b x) (hb x) (hUs x))).trans ?_)
      exact famHom_chartBase_eq_abelPreimageBase f hdim σ hσ A e θ hθ hH L₀ hL₀ es hbasis hdeg₀ ι₀
        V' jV hj hjV (U x).ι ((U x).ι ≫ Ψ) (by rw [Category.assoc, hΨγ]) (b x) (hb x)
  exact ⟨⟨Φ, Ψ, h1, h2⟩, hΦq⟩

end Stacks.RigidifiedPicard

namespace Stacks.RigidifiedPicard

open Stacks.Picard Stacks.ProjectiveSpaceModuli

/-- **The Abel morphism of degree `d ≥ 2g - 1` is Zariski-locally on `Pic⁰` the projective space
`ℙ^{d-g}`.** -/
theorem isLocallyProjectiveSpace_abelMorphism {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f] [GeometricallyIrreducible f]
    [SmoothOfRelativeDimension 1 f] (hdim : ∀ s, topologicalKrullDim ↥(f.fiber s) ≤ 1)
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _) (θ : Stacks.Picard.ofScheme X) {d : ℕ}
    (hθ : ∀ s, relativeInvertibleDegreeHomAt f hdim s θ = d) {H : Over (Spec (.of k))}
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H d)
    (A : Grp (Over (Spec (.of k)))) (e : yonedaGrp.obj A ≅ functorZero f hdim σ hσ)
    [LocallyOfFiniteType A.X.hom] (hd : 2 * (genus f : ℤ) - 1 ≤ d) :
    Stacks.ProjectiveBundle.IsLocallyProjectiveSpace
      (abelMorphism f hdim σ hσ θ hθ hH A e).left (d - genus f) := by
  intro y
  have hex := exists_abelSectionBasis f hdim σ hσ A e θ hθ hd y
  rw [show d + 1 - genus f = (d - genus f) + 1 by omega] at hex
  obtain ⟨W, hW, hyW, g, eW, hy, hbij⟩ := hex
  have : IsAffine W.toScheme := hW
  let B₀ : Over (Spec (.of k)) := Over.mk (W.ι ≫ A.X.hom)
  let ι₀ : B₀ ⟶ A.X := Over.homMk W.ι rfl
  let L := Stacks.Picard.picardRepresentative (bc f A.X).toRingedSpace
    (abelTranslatedClass f hdim σ hσ A e θ)
  have := L.property
  let L₀ := (Scheme.Modules.pullback (bcMap f ι₀)).obj L.obj
  have hL₀ : Stacks.SheafOfModules.IsInvertible (bc f B₀).presheaf (bc f B₀).ringCatSheaf.2 L₀ :=
    Stacks.Modules.isInvertible_pullback (bcMap f ι₀) L.obj
  have hclass : Stacks.SheafOfModules.picardClass (bc f B₀).presheaf
      (Stacks.RingedSpace.structureIsSheaf (bc f B₀).toRingedSpace) L₀ hL₀ =
      schemePullbackClass (bcMap f ι₀) (abelTranslatedClass f hdim σ hσ A e θ) := by
    rw [picardClass_pullback (bcMap f ι₀) L.obj L.property hL₀]
    exact congrArg _ (classOf_picardRepresentative _ _)
  have hdeg₀ : ∀ b : B₀.left, relativeInvertibleDegreeHomAt (bcProj f B₀)
      (topologicalKrullDim_fiber_bcProj_le f hdim B₀) b
      (Stacks.SheafOfModules.picardClass (bc f B₀).presheaf
        (Stacks.RingedSpace.structureIsSheaf (bc f B₀).toRingedSpace) L₀ hL₀) = d := fun b => by
    rw [hclass, relativeInvertibleDegreeHomAt_schemePullbackClass_of_isPullback
      (bcMap_isPullback_proj f ι₀) (topologicalKrullDim_fiber_bcProj_le f hdim A.X)]
    exact relativeInvertibleDegreeHomAt_abelTranslatedClass f hdim σ hσ A e θ hθ _
  let V : B₀.left.Opens := W.toScheme.basicOpen g
  have hbasis : IsSectionBasis f L₀ eW V := hbij
  let V' : A.X.left.Opens := W.ι ''ᵁ V
  have hrange : Set.range V'.ι ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  let jV : V'.toScheme ⟶ B₀.left := IsOpenImmersion.lift W.ι V'.ι hrange
  have hj : jV ≫ ι₀.left = V'.ι := IsOpenImmersion.lift_fac _ _ _
  have hjV : Set.range jV ⊆ V := by
    rintro _ ⟨z, rfl⟩
    have hz : W.ι (jV z) ∈ V' := by
      have hj' : jV ≫ W.ι = V'.ι := hj
      rw [← Scheme.Hom.comp_apply, hj']
      exact z.2
    obtain ⟨w, hw, hw'⟩ := hz
    rwa [← W.ι.isOpenEmbedding.injective hw']
  refine ⟨V', ⟨⟨y, hyW⟩, hy, rfl⟩, ?_⟩
  exact exists_abelPreimage_iso f hdim σ hσ A e θ hθ hH L₀ hL₀ eW hbasis hdeg₀ ι₀ hclass V' jV hj
    hjV

end Stacks.RigidifiedPicard

namespace Stacks.RigidifiedPicard

/-- **The Abel morphism of degree `d ≥ 2g - 1` is smooth**: `AbelMorphismSmooth`. -/
theorem abelMorphismSmooth : AbelMorphismSmooth.{u} := by
  intro k _ X f _ _ _ _ hdim σ hσ θ d hθ H hH A eA _ hd
  exact (isLocallyProjectiveSpace_abelMorphism f hdim σ hσ θ hθ hH A eA hd).smooth

/-- **The Abel morphism of degree `d ≥ 2g - 1` is Zariski-locally `ℙ^{d-g}`**:
`AbelMorphismIsLocallyProjectiveSpace`. -/
theorem abelMorphismIsLocallyProjectiveSpace : AbelMorphismIsLocallyProjectiveSpace.{u} := by
  intro k _ _ X f _ _ _ _ _ _ _ hdim σ hσ θ d hθ H hH A e _ hd
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  exact isLocallyProjectiveSpace_abelMorphism f hdim σ hσ θ hθ hH A e (by omega)

end Stacks.RigidifiedPicard

end
