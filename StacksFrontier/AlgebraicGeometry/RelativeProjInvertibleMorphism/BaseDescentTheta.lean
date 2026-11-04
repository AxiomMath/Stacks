module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.BaseDescent
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaSquareAssembly
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaClauseThree
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaUniqueClauseOne
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleThetaBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.TwistComparison

/-!
# The map `θ` of [Stacks, Tag 01O9] along a change of base

Let `q : X ⟶ Z`, `𝒜` a quasi-coherent graded `𝒪_Z`-algebra, `ψ : q^*𝒜 ⟶ ⨁_d ℒ^{⊗ d}`, and
`ψ↓ : 𝒜₁ ⟶ ⨁_d ℒ^{⊗ d}` the same map read over `X` through `Φ : 𝒜₁ ≅ q^*𝒜`
(`…baseDescent`).  By `…coveringOpen_baseDescent` and `…globalMorphism_baseDescent`,
`U(ψ) = U(ψ↓)` and `r_{ℒ,ψ} = e ≫ r_{ℒ,ψ↓} ≫ pc`, where `e : U(ψ) ⟶ U(ψ↓)` is the identification
of the two equal opens and `pc : Proj_X(𝒜₁) ≅ Proj_X(q^*𝒜) ⟶ Proj_Z(𝒜)` is the comparison of
the restricted algebras followed by the base-change morphism of [Stacks, Tag 01O3].  This file
proves that **the maps `θ` of Tag 01O9 for `ψ` and for `ψ↓` correspond** under

* `thetaDescentSourceIso`: `e^*r_{ψ↓}^*(⨁ 𝒪_{Proj_X(𝒜₁)}(d)) ≅ r_ψ^*(⨁ 𝒪_{Proj_Z(𝒜)}(d))`, the
  comparison of twists along `pc` (`…RelativeProjBaseChangeTwist.congrBaseChangeTwistIso`, built
  from the `θ` of Tag 01O3) and the pseudofunctoriality of the inverse image;
* `thetaDescentTargetIso`: `e^*(⨁ ℒ^{⊗ d}|_{U(ψ↓)}) ≅ ⨁ ℒ^{⊗ d}|_{U(ψ)}`.

The proof is the uniqueness of `θ` given clause (1) (`…GradedPowerMap.eq_theta_of_clauseOne`):
on the pullback of `ψ_{Proj}(a)` for a homogeneous section `a` of `𝒜` over an open `V` of `Z`,
the comparison of twists gives `ψ_{Proj}` of the pulled-back section `Φ⁻¹(q^*a)` of `𝒜₁`, clause
(1) for `ψ↓` evaluates `θ` on it, and `ψ↓(Φ⁻¹(q^*a)) = ψ(a)`.

## Main results

* `theta_baseDescent`: `θ_ψ = (source iso)⁻¹ ≫ e^*θ_{ψ↓} ≫ (target iso)`.

## References

* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules (pullbackSection)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare)
open Stacks.AlgebraicGeometry.ProjChartGradedTriple (laurentOn)
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist (baseChangeHom congrBaseChangeTwistIso
  pbAlgS)
open Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp (pullbackGradedAlgebraCompIso
  pullbackGradedAlgebraCongrIso)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

open GradedPowerMap (twD Otw psiU)

section Generic

variable {Y' U' T' : Scheme.{u}}

/-- **The target identification along an inclusion of opens, on a pulled-back section**: for
`j ≫ e = a` with `e`, `a` open immersions, `j^*(K|_e) ≅ K|_a` carries the pullback of a section
`t` of `K` over `e(O')` to its restriction. -/
theorem restrictPullbackIso_hom_pullbackSection (j : Y' ⟶ U') (e : U' ⟶ T')
    [IsOpenImmersion e] (a : Y' ⟶ T') [IsOpenImmersion a] (hja : j ≫ e = a) (K : T'.Modules)
    (O' : U'.Opens) (V : Y'.Opens) (h4 : V ≤ j ⁻¹ᵁ O') (t : Γ(K.restrict e, O'))
    (hV' : a ''ᵁ V ≤ e ''ᵁ O') :
    ((Scheme.Modules.pullback j).mapIso ((Scheme.Modules.restrictFunctorIsoPullback e).app K)
        ≪≫ (Scheme.Modules.pullbackComp j e).app _
        ≪≫ (Scheme.Modules.pullbackCongr hja).app _
        ≪≫ ((Scheme.Modules.restrictFunctorIsoPullback a).app K).symm).hom.val.app (op V)
      (pullbackSection j (K.restrict e) O' V h4 t) = K.val.map (homOfLE hV').op t := by
  have hO : O' ≤ e ⁻¹ᵁ (e ''ᵁ O') := (e.preimage_image_eq O').ge
  have h5 : V ≤ (j ≫ e) ⁻¹ᵁ (e ''ᵁ O') := h4.trans (j.preimage_mono hO)
  have h6 : V ≤ a ⁻¹ᵁ (e ''ᵁ O') := hja ▸ h5
  have g1 := (Scheme.Modules.pullbackSection_naturality j
    ((Scheme.Modules.restrictFunctorIsoPullback e).hom.app K) O' V h4 t).trans
      (congrArg (pullbackSection j _ O' V h4) (restrictFunctorIsoPullback_hom_val_app e K O' hO t))
  have g2 := Scheme.Modules.pullbackSection_comp j e K (e ''ᵁ O') O' V hO h4 h5 t
  have g3 := Scheme.Modules.pullbackSection_congr hja K (e ''ᵁ O') V h5 h6 t
  have g6 := Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection a K (e ''ᵁ O') V h6
    hV' t
  have g12 := (congrArg (((Scheme.Modules.pullbackComp j e).hom.app K).val.app (op V)) g1).trans g2
  have g123 := (congrArg (((Scheme.Modules.pullbackCongr hja).hom.app K).val.app (op V)) g12).trans
    g3
  exact (congrArg (((Scheme.Modules.restrictFunctorIsoPullback a).inv.app K).val.app (op V))
    g123).trans g6

/-- The inverse image along `k` of a composite in which the inverse image along `j` of a map
occurs, with that factor read as an inverse image along `k ≫ j`. -/
theorem pullbackGradedAlgebraMap_comp_pullback {Y₁ Y₂ Y₃ : Scheme.{u}} (k : Y₁ ⟶ Y₂)
    (j : Y₂ ⟶ Y₃)
    {A₀ B₀ C₀ D₀ : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y₂.toRingedSpace)}
    {G H : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y₃.toRingedSpace)}
    (a : A₀ ⟶ B₀) (b : B₀ ⟶ pullbackGradedAlgebra j.toLRSHom.toShHom G) (φ : G ⟶ H)
    (c : pullbackGradedAlgebra j.toLRSHom.toShHom H ⟶ C₀) (d : C₀ ⟶ D₀) :
    pullbackGradedAlgebraMap k.toLRSHom.toShHom
        ((a ≫ (b ≫ pullbackGradedAlgebraMap j.toLRSHom.toShHom φ ≫ c)) ≫ d) =
      pullbackGradedAlgebraMap k.toLRSHom.toShHom a ≫
        pullbackGradedAlgebraMap k.toLRSHom.toShHom b ≫
        (pullbackGradedAlgebraCompIso G k j).hom ≫
        pullbackGradedAlgebraMap (k ≫ j).toLRSHom.toShHom φ ≫
        (pullbackGradedAlgebraCompIso H k j).inv ≫
        pullbackGradedAlgebraMap k.toLRSHom.toShHom c ≫
        pullbackGradedAlgebraMap k.toLRSHom.toShHom d := by
  rw [pullbackGradedAlgebraMap_comp_eq φ k j]
  simp only [pullbackGradedAlgebraMap_comp, Category.assoc, Iso.hom_inv_id_assoc]

/-- `pullbackGradedAlgebraMap_comp_pullback` for a composite of isomorphisms, with every factor of
the right-hand side read as a component of an isomorphism. -/
theorem pullbackGradedAlgebraMap_comp_pullback_iso {Y₁ Y₂ Y₃ : Scheme.{u}} (k : Y₁ ⟶ Y₂)
    (j : Y₂ ⟶ Y₃)
    {P₀ P₁ Q₀ Q₁ : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y₂.toRingedSpace)}
    {G H : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y₃.toRingedSpace)}
    (σ₂ : P₀ ≅ P₁) (σ₁ : pullbackGradedAlgebra j.toLRSHom.toShHom G ≅ P₁) (φ : G ⟶ H)
    (τ₁ : pullbackGradedAlgebra j.toLRSHom.toShHom H ≅ Q₁) (τ₂ : Q₀ ≅ Q₁) :
    pullbackGradedAlgebraMap k.toLRSHom.toShHom
        ((σ₂.hom ≫ (σ₁.inv ≫ pullbackGradedAlgebraMap j.toLRSHom.toShHom φ ≫ τ₁.hom)) ≫ τ₂.inv) =
      (pullbackGradedAlgebraMapIso k.toLRSHom.toShHom σ₂.symm).inv ≫
        (pullbackGradedAlgebraMapIso k.toLRSHom.toShHom σ₁).inv ≫
        (pullbackGradedAlgebraCompIso G k j).symm.inv ≫
        pullbackGradedAlgebraMap (k ≫ j).toLRSHom.toShHom φ ≫
        (pullbackGradedAlgebraCompIso H k j).symm.hom ≫
        (pullbackGradedAlgebraMapIso k.toLRSHom.toShHom τ₁).hom ≫
        (pullbackGradedAlgebraMapIso k.toLRSHom.toShHom τ₂.symm).hom :=
  pullbackGradedAlgebraMap_comp_pullback k j σ₂.hom σ₁.inv φ τ₁.hom τ₂.inv

/-- A reassociation of a composite of thirteen morphisms. -/
theorem comp_assoc_thirteen {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ X₉ X₁₀ X₁₁ X₁₂
    X₁₃ : C} (f₁ : X₀ ⟶ X₁) (f₂ : X₁ ⟶ X₂) (f₃ : X₂ ⟶ X₃) (f₄ : X₃ ⟶ X₄) (f₅ : X₄ ⟶ X₅)
    (f₆ : X₅ ⟶ X₆) (f₇ : X₆ ⟶ X₇) (f₈ : X₇ ⟶ X₈) (f₉ : X₈ ⟶ X₉) (f₁₀ : X₉ ⟶ X₁₀)
    (f₁₁ : X₁₀ ⟶ X₁₁) (f₁₂ : X₁₁ ⟶ X₁₂) (f₁₃ : X₁₂ ⟶ X₁₃) :
    f₁ ≫ ((f₂ ≫ ((f₃ ≫ ((f₄ ≫ f₅ ≫ f₆ ≫ f₇ ≫ f₈ ≫ f₉ ≫ f₁₀) ≫ f₁₁)) ≫ f₁₂)) ≫ f₁₃) =
      (((((f₁ ≫ f₂) ≫ f₃) ≫ f₄) ≫ f₅) ≫ f₆) ≫ f₇ ≫ f₈ ≫ f₉ ≫ f₁₀ ≫ f₁₁ ≫ f₁₂ ≫ f₁₃ := by
  simp only [Category.assoc]

/-- Conjugating by two chains of six isomorphisms, reassociated. -/
theorem iso_chain_conj {C : Type*} [Category C] {P₀ P₁ P₂ P₃ P₄ P₅ P₆ Q₀ Q₁ Q₂ Q₃ Q₄ Q₅ Q₆ : C}
    (α₁ : P₀ ≅ P₁) (α₂ : P₁ ≅ P₂) (α₃ : P₂ ≅ P₃) (α₄ : P₃ ≅ P₄) (α₅ : P₄ ≅ P₅) (α₆ : P₅ ≅ P₆)
    (β₁ : Q₀ ≅ Q₁) (β₂ : Q₁ ≅ Q₂) (β₃ : Q₂ ≅ Q₃) (β₄ : Q₃ ≅ Q₄) (β₅ : Q₄ ≅ Q₅) (β₆ : Q₅ ≅ Q₆)
    (φ : P₀ ⟶ Q₀) :
    α₆.inv ≫ ((α₅.inv ≫ ((α₄.inv ≫ ((α₃.inv ≫ α₂.inv ≫ α₁.inv ≫ φ ≫ β₁.hom ≫ β₂.hom ≫ β₃.hom) ≫
        β₄.hom)) ≫ β₅.hom)) ≫ β₆.hom) =
      (α₁ ≪≫ α₂ ≪≫ α₃ ≪≫ α₄ ≪≫ α₅ ≪≫ α₆).inv ≫ φ ≫ (β₁ ≪≫ β₂ ≪≫ β₃ ≪≫ β₄ ≪≫ β₅ ≪≫ β₆).hom := by
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc]

end Generic

variable {Z X : Scheme.{u}} {A : SheafGradedAlgebra.{u} Z} (q : X ⟶ Z)
  {A₁ : SheafGradedAlgebra.{u} X}
  (Φ : (situationAlgebra A₁).UnitalHom (situationAlgebra (A.pullback q)))
  (hΦ : ∀ n : ℤ, IsIso (Φ.app n))
  {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]
  (ψ : Twisting q (situationAlgebra A) 1 L)

/-- The comparison `Proj_X(𝒜₁) ≅ Proj_X(q^*𝒜) ⟶ Proj_Z(𝒜)`: the isomorphism of the restricted
algebras followed by the base-change morphism of Tag 01O3. -/
abbrev descentProj : (relativeProj A₁).scheme ⟶ (relativeProj A).scheme :=
  (relativeProjCongr Φ hΦ).hom ≫ baseChangeHom A q

/-- The comparison of twists along `descentProj`: `pc^*(⨁ 𝒪_{Proj_Z(𝒜)}(d)) ≅ ⨁ 𝒪_{Proj_X(𝒜₁)}(d)`,
from the `θ` of Tag 01O3 and the transport along `Φ`. -/
def descentTwistIso :
    pbAlgS (descentProj q Φ hΦ) (twD A).algebra ≅ (twD A₁).algebra :=
  congrBaseChangeTwistIso A q Φ hΦ (descentProj q Φ hΦ) rfl

/-- The degree-`d` component of `descentTwistIso`, with its source read as an inverse image of
modules. -/
def descentTwistPieceHom (d : ℤ) :
    (Scheme.Modules.pullback (descentProj q Φ hΦ)).obj ((twD A).algebra.piece d) ⟶
      (twD A₁).algebra.piece d :=
  (descentTwistIso q Φ hΦ).hom.app d

/-- `pc` lies over `q`. -/
theorem descentProj_comp_toBase :
    descentProj q Φ hΦ ≫ (relativeProj A).toBase = (relativeProj A₁).toBase ≫ q := by
  rw [Category.assoc, RelativeProjBaseChangeTwist.baseChangeHom_comp_toBase,
    ← Category.assoc, relativeProjCongr_hom_comp_toBase]

/-- The homogeneous section `Φ⁻¹(q^*a)` of `𝒜₁` attached to a section `a` of `𝒜` over `V`. -/
abbrev descentSection {d : ℕ} {V : Z.Opens} (a : Γ(A.piece (d : ℤ), V)) :
    Γ(A₁.piece (d : ℤ), q ⁻¹ᵁ V) :=
  ((congrInvHom Φ hΦ).app (d : ℤ)).app (q ⁻¹ᵁ V)
    (pullbackSection q (A.piece (d : ℤ)) V (q ⁻¹ᵁ V) le_rfl a)

/-- `Φ` carries `Φ⁻¹(q^*a)` to the pullback of `a`. -/
private theorem unitalHom_app_descentSection {d : ℕ} {V : Z.Opens} (a : Γ(A.piece (d : ℤ), V)) :
    (Φ.app (d : ℤ)).val.app (op (q ⁻¹ᵁ V)) (descentSection q Φ hΦ a) =
      pullbackSection q (A.piece (d : ℤ)) V (q ⁻¹ᵁ V) le_rfl a :=
  val_app_roundtrip (@inv _ _ _ _ (Φ.app (d : ℤ)) (hΦ d)) (Φ.app (d : ℤ))
    (@IsIso.inv_hom_id _ _ _ _ (Φ.app (d : ℤ)) (hΦ d)) (op (q ⁻¹ᵁ V)) _

/-- **The comparison of twists along `pc` on the homogeneous sections**: it carries the inverse
image of `ψ(a)` to `ψ(Φ⁻¹(q^*a))`. -/
theorem descentTwistIso_hom_pullbackSection_psiU (d : ℕ) (V : Z.Opens) (a : Γ(A.piece (d : ℤ), V))
    (h' : (relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V) ≤
      descentProj q Φ hΦ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)) :
    Scheme.Modules.Hom.app ((descentTwistIso q Φ hΦ).hom.app (d : ℤ))
        ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V))
        (pullbackSection (descentProj q Φ hΦ) ((twD A).algebra.piece (d : ℤ))
          ((relativeProj A).toBase ⁻¹ᵁ V) ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V)) h'
          (((twD A).ψ d).val.app (op V) a)) =
      Scheme.Modules.Hom.app ((twD A₁).ψ d) (q ⁻¹ᵁ V) (descentSection q Φ hΦ a) := by
  have H := congrArg (fun φ => Scheme.Modules.Hom.app φ (q ⁻¹ᵁ V) (descentSection q Φ hΦ a))
    (RelativeProjBaseChangeTwist.congrBaseChangePsi_comp_congrBaseChangeTwistIso
      A q Φ hΦ (descentProj q Φ hΦ) rfl (descentProj_comp_toBase q Φ hΦ) d)
  have hround : ((congrHom Φ).app (d : ℤ)).app (q ⁻¹ᵁ V) (descentSection q Φ hΦ a) =
      pullbackSection q (A.piece (d : ℤ)) V (q ⁻¹ᵁ V) le_rfl a :=
    unitalHom_app_descentSection q Φ hΦ a
  have hb := Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.basePsi_pullbackSection
    (relativeProj A).toBase (relativeProj A₁).toBase q (descentProj q Φ hΦ)
    (descentProj_comp_toBase q Φ hΦ) ((twD A).ψ d) V (q ⁻¹ᵁ V) le_rfl h' a
  refine Eq.trans ?_ H
  show _ = Scheme.Modules.Hom.app ((descentTwistIso q Φ hΦ).hom.app (d : ℤ))
    ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V))
    ((Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.basePsi (relativeProj A).toBase
      (relativeProj A₁).toBase q (descentProj q Φ hΦ) (descentProj_comp_toBase q Φ hΦ)
      ((twD A).ψ d)).val.app (op (q ⁻¹ᵁ V))
        (((congrHom Φ).app (d : ℤ)).app (q ⁻¹ᵁ V) (descentSection q Φ hΦ a)))
  rw [hround, hb]

/-- `Φ` carries `Φ⁻¹(q^*a)`, read in any degree equal to `d`, to the pullback of `a`. -/
theorem unitalHom_descentSection {d : ℕ} {V : Z.Opens} (a : Γ(A.piece (d : ℤ), V)) (m : ℤ)
    (hm : (d : ℤ) = m) :
    (Φ.app m).val.app (op (q ⁻¹ᵁ V))
        ((eqToHom (congrArg (situationAlgebra A₁).piece hm)).val.app (op (q ⁻¹ᵁ V))
          (descentSection q Φ hΦ a)) =
      Twisting.baseUnit q (situationAlgebra A) m (op V)
        ((eqToHom (congrArg (situationAlgebra A).piece hm)).val.app (op V) a) := by
  subst hm
  simp only [eqToHom_refl]
  exact (unitalHom_app_descentSection q Φ hΦ a).trans
    (Stacks.Conormal.pullbackSection_self q (A.piece (d : ℤ)) V a)

/-- **`ψ↓(Φ⁻¹(q^*a)) = ψ(a)`**: the value of `ψ↓` at the section of `𝒜₁` attached to a
homogeneous section `a` of `𝒜` is the value of `ψ` at `a`. -/
theorem valueSec_baseDescent (d : ℕ) (V : Z.Opens) (a : Γ(A.piece (d : ℤ), V)) :
    valueSec (baseDescent q Φ ψ) d (q ⁻¹ᵁ V) (descentSection q Φ hΦ a) = valueSec ψ d V a := by
  have e1 := Twisting.algebraTransport_sectionHom Φ
    (Twisting.baseChangeDown q (𝟙 X) (situationAlgebra A) 1 ψ) (d : ℤ) (op (q ⁻¹ᵁ V))
    ((pieceCast (A := A₁) (d : ℤ)).val.app (op (q ⁻¹ᵁ V)) (descentSection q Φ hΦ a))
  have e2 := Twisting.baseChangeUp_sectionHom q (𝟙 X) (situationAlgebra A) 1
    (Twisting.baseChangeDown q (𝟙 X) (situationAlgebra A) 1 ψ) (d : ℤ) (op V)
    ((pieceCast (A := A) (d : ℤ)).val.app (op V) a)
  have e2' := (congrArg (fun t : Twisting (𝟙 X ≫ q) (situationAlgebra A) 1 L =>
    t.sectionHom (d : ℤ) (op V) ((pieceCast (A := A) (d : ℤ)).val.app (op V) a))
    (Twisting.baseChangeUp_baseChangeDown q (𝟙 X) (situationAlgebra A) 1 ψ)).symm.trans e2
  have e3 := unitalHom_descentSection q Φ hΦ a ((d : ℤ) * 1) (mul_one (d : ℤ)).symm
  unfold valueSec
  refine congrArg ((powCompare L d).inv.app _) ?_
  refine e1.trans (Eq.trans ?_ e2'.symm)
  exact congrArg _ e3

/-- The two readings of the action of a morphism of modules on a section agree. -/
theorem hom_app_eq_val_app {Y : Scheme.{u}} {M N : Y.Modules} (φ : M ⟶ N) (U : Y.Opens)
    (x : Γ(M, U)) : Scheme.Modules.Hom.app φ U x = φ.val.app (op U) x :=
  rfl

/-- The part of `Proj_X(𝒜₁)` over `q^{-1}(V)` lies in the inverse image under `pc` of the part of
`Proj_Z(𝒜)` over `V`. -/
theorem toBase_preimage_le_descentProj_preimage (V : Z.Opens) :
    (relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V) ≤
      descentProj q Φ hΦ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V) := by
  intro x hx
  have h : (descentProj q Φ hΦ ≫ (relativeProj A).toBase).base x ∈ V := by
    rw [descentProj_comp_toBase]
    exact hx
  exact h

/-- `descentTwistIso_hom_pullbackSection_psiU`, read on the homogeneous-section maps. -/
theorem descentTwistPieceHom_pullbackSection_psiU (d : ℕ) (V : Z.Opens)
    (a : Γ(A.piece (d : ℤ), V)) :
    (descentTwistPieceHom q Φ hΦ (d : ℤ)).val.app (op ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V)))
        (pullbackSection (descentProj q Φ hΦ) ((twD A).algebra.piece (d : ℤ))
          ((relativeProj A).toBase ⁻¹ᵁ V) ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V))
          (toBase_preimage_le_descentProj_preimage q Φ hΦ V) (psiU A d V a)) =
      psiU A₁ d (q ⁻¹ᵁ V) (descentSection q Φ hΦ a) :=
  descentTwistIso_hom_pullbackSection_psiU q Φ hΦ d V a
    (toBase_preimage_le_descentProj_preimage q Φ hΦ V)

section General

variable (χ : Twisting (𝟙 X) (situationAlgebra A₁) 1 L) (hχ : baseDescent q Φ ψ = χ)

include Φ hΦ hχ

/-- `U(χ) = U(ψ)` for `χ = ψ↓`. -/
theorem coveringOpen_of_baseDescent_eq : (toGradedPowerMap χ).coveringOpen =
    (toGradedPowerMap ψ).coveringOpen :=
  hχ ▸ coveringOpen_baseDescent q Φ hΦ ψ

/-- `r_ψ = e ≫ r_χ ≫ pc` for `χ = ψ↓`. -/
theorem globalMorphism_of_baseDescent_eq :
    X.homOfLE (coveringOpen_of_baseDescent_eq q Φ hΦ ψ χ hχ).ge ≫
        (toGradedPowerMap χ).globalMorphism (relativeProj A₁) ≫
          (relativeProjCongr Φ hΦ).hom ≫ baseChangeHom A q =
      (toGradedPowerMap ψ).globalMorphism (relativeProj A) := by
  subst hχ
  exact globalMorphism_baseDescent q Φ hΦ ψ

/-- `χ(Φ⁻¹(q^*a)) = ψ(a)` for `χ = ψ↓`. -/
theorem valueSec_of_baseDescent_eq (d : ℕ) (V : Z.Opens) (a : Γ(A.piece (d : ℤ), V)) :
    valueSec χ d (q ⁻¹ᵁ V) (descentSection q Φ hΦ a) = valueSec ψ d V a := by
  subst hχ
  exact valueSec_baseDescent q Φ hΦ ψ d V a

/-- The identification `U(ψ) ⟶ U(ψ↓)` of the two equal opens. -/
abbrev descentIncl :
    (toGradedPowerMap ψ).coveringOpen.toScheme ⟶
      (toGradedPowerMap (χ)).coveringOpen.toScheme :=
  X.homOfLE (coveringOpen_of_baseDescent_eq q Φ hΦ ψ χ hχ).ge

/-- **`e^*r_{ψ↓}^*(⨁ 𝒪(d)) ≅ r_ψ^*(⨁ 𝒪(d))`**: the comparison of twists along `pc`, followed by the
pseudofunctoriality of the inverse image along `r_ψ = e ≫ r_{ψ↓} ≫ pc`. -/
def thetaDescentSourceIso :
    Stacks.Conormal.gradedPullback (descentIncl q Φ hΦ ψ χ hχ)
        (Stacks.Conormal.gradedPullback
          ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁))
          (twD A₁).algebra) ≅
      Stacks.Conormal.gradedPullback ((toGradedPowerMap ψ).globalMorphism (relativeProj A))
        (twD A).algebra :=
  pullbackGradedAlgebraMapIso (descentIncl q Φ hΦ ψ χ hχ).toLRSHom.toShHom
      (pullbackGradedAlgebraMapIso
        ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁)).toLRSHom.toShHom
        (descentTwistIso q Φ hΦ).symm) ≪≫
    pullbackGradedAlgebraMapIso (descentIncl q Φ hΦ ψ χ hχ).toLRSHom.toShHom
      (pullbackGradedAlgebraCompIso (twD A).algebra
        ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁))
        (descentProj q Φ hΦ)) ≪≫
    pullbackGradedAlgebraCompIso (twD A).algebra (descentIncl q Φ hΦ ψ χ hχ)
      ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁) ≫
        descentProj q Φ hΦ) ≪≫
    pullbackGradedAlgebraCongrIso (twD A).algebra (globalMorphism_of_baseDescent_eq q Φ hΦ ψ χ hχ)

/-- **`e^*(ℒ^{⊗ n}|_{U(ψ↓)}) ≅ ℒ^{⊗ n}|_{U(ψ)}`**: the restriction to `U(ψ↓)` read as an inverse
image, the pseudofunctoriality of the inverse image along `e ≫ ι_{U(ψ↓)} = ι_{U(ψ)}`, and the
inverse image read back as a restriction. -/
def thetaDescentTargetPieceIso (n : ℤ) :
    (Scheme.Modules.pullback (descentIncl q Φ hΦ ψ χ hχ)).obj
        ((laurentOn L (toGradedPowerMap (χ)).coveringOpen).piece n) ≅
      (laurentOn L (toGradedPowerMap ψ).coveringOpen).piece n :=
  (Scheme.Modules.pullback (descentIncl q Φ hΦ ψ χ hχ)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback
        (toGradedPowerMap (χ)).coveringOpen.ι).app (tensorPowerModule X L n))
    ≪≫ (Scheme.Modules.pullbackComp (descentIncl q Φ hΦ ψ χ hχ)
          (toGradedPowerMap (χ)).coveringOpen.ι).app _
    ≪≫ (Scheme.Modules.pullbackCongr
        (Scheme.homOfLE_ι X (coveringOpen_of_baseDescent_eq q Φ hΦ ψ χ hχ).ge)).app _
    ≪≫ ((Scheme.Modules.restrictFunctorIsoPullback (toGradedPowerMap ψ).coveringOpen.ι).app
          (tensorPowerModule X L n)).symm

/-- The image in `X` of the preimage under `e` of an open of `U(ψ↓)` lies in the image of the
open. -/
theorem image_preimage_descentIncl_le (O' : (toGradedPowerMap (χ)).coveringOpen.toScheme.Opens) :
    (toGradedPowerMap ψ).coveringOpen.ι ''ᵁ (descentIncl q Φ hΦ ψ χ hχ ⁻¹ᵁ O') ≤
      (toGradedPowerMap (χ)).coveringOpen.ι ''ᵁ O' := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨(descentIncl q Φ hΦ ψ χ hχ).base x, hx, congrArg (fun h => h.base x)
    (Scheme.homOfLE_ι X (coveringOpen_of_baseDescent_eq q Φ hΦ ψ χ hχ).ge)⟩

/-- **The target identification on a pulled-back section** is the restriction. -/
theorem thetaDescentTargetPieceIso_hom_pullbackUnit (n : ℤ)
    (O' : (toGradedPowerMap (χ)).coveringOpen.toScheme.Opens)
    (t : Γ((tensorPowerModule X L n).restrict
      (toGradedPowerMap (χ)).coveringOpen.ι, O')) :
    (thetaDescentTargetPieceIso q Φ hΦ ψ χ hχ n).hom.val.app (op (descentIncl q Φ hΦ ψ χ hχ ⁻¹ᵁ O'))
        (pullbackUnit (descentIncl q Φ hΦ ψ χ hχ).toLRSHom.toShHom
          ((laurentOn L (toGradedPowerMap (χ)).coveringOpen).piece n) (op O') t) =
      (tensorPowerModule X L n).val.map
          (homOfLE (image_preimage_descentIncl_le q Φ hΦ ψ χ hχ O')).op
        t :=
  (congrArg ((thetaDescentTargetPieceIso q Φ hΦ ψ χ hχ n).hom.val.app
      (op (descentIncl q Φ hΦ ψ χ hχ ⁻¹ᵁ O')))
    (Stacks.Conormal.pullbackSection_self (descentIncl q Φ hΦ ψ χ hχ)
      ((laurentOn L (toGradedPowerMap (χ)).coveringOpen).piece n) O' t).symm).trans
    (restrictPullbackIso_hom_pullbackSection (descentIncl q Φ hΦ ψ χ hχ)
      (toGradedPowerMap (χ)).coveringOpen.ι (toGradedPowerMap ψ).coveringOpen.ι
      (Scheme.homOfLE_ι X (coveringOpen_of_baseDescent_eq q Φ hΦ ψ χ hχ).ge)
          (tensorPowerModule X L n) O'
      _ le_rfl t (image_preimage_descentIncl_le q Φ hΦ ψ χ hχ O'))

/-- **The target identification is multiplicative on pulled-back sections.** -/
theorem thetaDescentTargetPieceIso_hom_mul_pullbackUnit (i k : ℤ)
    (O' : (toGradedPowerMap (χ)).coveringOpen.toScheme.Opens)
    (a : Γ((tensorPowerModule X L i).restrict
      (toGradedPowerMap (χ)).coveringOpen.ι, O'))
    (b : Γ((tensorPowerModule X L k).restrict
      (toGradedPowerMap (χ)).coveringOpen.ι, O')) :
    (thetaDescentTargetPieceIso q Φ hΦ ψ χ hχ (i + k)).hom.val.app
        (op (descentIncl q Φ hΦ ψ χ hχ ⁻¹ᵁ O'))
        (pullbackUnit (descentIncl q Φ hΦ ψ χ hχ).toLRSHom.toShHom
          ((laurentOn L (toGradedPowerMap (χ)).coveringOpen).piece (i + k)) (op O')
          (Stacks.TensorPowerDivision.localMul L a b)) =
      Stacks.TensorPowerDivision.localMul L
        ((thetaDescentTargetPieceIso q Φ hΦ ψ χ hχ i).hom.val.app
            (op (descentIncl q Φ hΦ ψ χ hχ ⁻¹ᵁ O'))
          (pullbackUnit (descentIncl q Φ hΦ ψ χ hχ).toLRSHom.toShHom
            ((laurentOn L (toGradedPowerMap (χ)).coveringOpen).piece i) (op O') a))
        ((thetaDescentTargetPieceIso q Φ hΦ ψ χ hχ k).hom.val.app
            (op (descentIncl q Φ hΦ ψ χ hχ ⁻¹ᵁ O'))
          (pullbackUnit (descentIncl q Φ hΦ ψ χ hχ).toLRSHom.toShHom
            ((laurentOn L (toGradedPowerMap (χ)).coveringOpen).piece k) (op O') b)) := by
  refine (thetaDescentTargetPieceIso_hom_pullbackUnit q Φ hΦ ψ χ hχ (i + k) O' _).trans ?_
  refine (Stacks.TensorPowerDivision.map_localMul _
    (homOfLE (image_preimage_descentIncl_le q Φ hΦ ψ χ hχ O')) _ _).trans ?_
  exact congrArg₂ (Stacks.TensorPowerDivision.localMul L)
    (thetaDescentTargetPieceIso_hom_pullbackUnit q Φ hΦ ψ χ hχ i O' a).symm
    (thetaDescentTargetPieceIso_hom_pullbackUnit q Φ hΦ ψ χ hχ k O' b).symm

/-- **`e^*(⨁ ℒ^{⊗ d}|_{U(ψ↓)}) ≅ ⨁ ℒ^{⊗ d}|_{U(ψ)}`** as sheaves of graded algebras. -/
def thetaDescentTargetIso :
    Stacks.Conormal.gradedPullback (descentIncl q Φ hΦ ψ χ hχ)
        (laurentOn L (toGradedPowerMap (χ)).coveringOpen) ≅
      laurentOn L (toGradedPowerMap ψ).coveringOpen :=
  SheafOfModules.GradedAlgebra.isoOfPieceIso
    (A := Stacks.Conormal.gradedPullback (descentIncl q Φ hΦ ψ χ hχ)
      (laurentOn L (toGradedPowerMap (χ)).coveringOpen))
    (B := laurentOn L (toGradedPowerMap ψ).coveringOpen)
    (fun n => thetaDescentTargetPieceIso q Φ hΦ ψ χ hχ n)
    (fun i k U x y => map_mul_of_pullbackUnit (descentIncl q Φ hΦ ψ χ hχ).toLRSHom.toShHom
      (A := laurentOn L (toGradedPowerMap (χ)).coveringOpen)
      (B := laurentOn L (toGradedPowerMap ψ).coveringOpen)
      (fun n => (thetaDescentTargetPieceIso q Φ hΦ ψ χ hχ n).hom) i k
      (fun V a b => thetaDescentTargetPieceIso_hom_mul_pullbackUnit q Φ hΦ ψ χ hχ i k V a b) U x y)

/-- The degree-`d` component of the inverse of the source identification. -/
theorem thetaDescentSourceIso_inv_app (d : ℤ) :
    (thetaDescentSourceIso q Φ hΦ ψ χ hχ).inv.app d =
      (Scheme.Modules.pullbackCongr (globalMorphism_of_baseDescent_eq q Φ hΦ ψ χ hχ)).inv.app
          ((twD A).algebra.piece d) ≫
        (Scheme.Modules.pullbackComp (descentIncl q Φ hΦ ψ χ hχ)
          ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁) ≫
            descentProj q Φ hΦ)).inv.app ((twD A).algebra.piece d) ≫
        (Scheme.Modules.pullback (descentIncl q Φ hΦ ψ χ hχ)).map
          ((Scheme.Modules.pullbackComp
            ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁))
            (descentProj q Φ hΦ)).inv.app ((twD A).algebra.piece d)) ≫
        (Scheme.Modules.pullback (descentIncl q Φ hΦ ψ χ hχ)).map
          ((Scheme.Modules.pullback
            ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁))).map
            (descentTwistPieceHom q Φ hΦ d)) :=
  rfl

/-- `r_ψ^{-1}(π^{-1}(V)) ⊆ e^{-1}(r_{ψ↓}^{-1}(π₁^{-1}(q^{-1}(V))))`. -/
theorem globalMorphism_preimage_le_descent (V : Z.Opens) :
    (toGradedPowerMap ψ).globalMorphism (relativeProj A) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V) ≤
      descentIncl q Φ hΦ ψ χ hχ ⁻¹ᵁ ((toGradedPowerMap (χ)).globalMorphism
        (relativeProj A₁) ⁻¹ᵁ ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V))) := by
  rw [← globalMorphism_of_baseDescent_eq q Φ hΦ ψ χ hχ]
  intro x hx
  exact toBase_preimage_le_descentProj_preimage q Φ hΦ V |>.trans le_rfl |> fun _ => by
    have hx' : (descentProj q Φ hΦ ≫ (relativeProj A).toBase).base
        (((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁)).base
          ((descentIncl q Φ hΦ ψ χ hχ).base x)) ∈ V := hx
    rw [descentProj_comp_toBase] at hx'
    exact hx'

/-- **The inverse of the source identification on a pulled-back section** undoes the
pseudofunctoriality and applies the comparison of twists. -/
theorem thetaDescentSourceIso_inv_app_pullbackSection (d : ℕ) (V : Z.Opens)
    (x : Γ((twD A).algebra.piece (d : ℤ), (relativeProj A).toBase ⁻¹ᵁ V)) :
    ((thetaDescentSourceIso q Φ hΦ ψ χ hχ).inv.app (d : ℤ)).val.app
        (op ((toGradedPowerMap ψ).globalMorphism (relativeProj A) ⁻¹ᵁ
          ((relativeProj A).toBase ⁻¹ᵁ V)))
        (pullbackSection ((toGradedPowerMap ψ).globalMorphism (relativeProj A))
          ((twD A).algebra.piece (d : ℤ)) ((relativeProj A).toBase ⁻¹ᵁ V)
          ((toGradedPowerMap ψ).globalMorphism (relativeProj A) ⁻¹ᵁ
            ((relativeProj A).toBase ⁻¹ᵁ V)) le_rfl x) =
      pullbackSection (descentIncl q Φ hΦ ψ χ hχ)
        ((Scheme.Modules.pullback ((toGradedPowerMap (χ)).globalMorphism
          (relativeProj A₁))).obj ((twD A₁).algebra.piece (d : ℤ)))
        ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁) ⁻¹ᵁ
          ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V)))
        ((toGradedPowerMap ψ).globalMorphism (relativeProj A) ⁻¹ᵁ
          ((relativeProj A).toBase ⁻¹ᵁ V))
        (globalMorphism_preimage_le_descent q Φ hΦ ψ χ hχ V)
        (pullbackSection ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁))
          ((twD A₁).algebra.piece (d : ℤ)) ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V))
          ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁) ⁻¹ᵁ
            ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V))) le_rfl
          ((descentTwistPieceHom q Φ hΦ (d : ℤ)).val.app
            (op ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V)))
            (pullbackSection (descentProj q Φ hΦ) ((twD A).algebra.piece (d : ℤ))
              ((relativeProj A).toBase ⁻¹ᵁ V) ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V))
              (toBase_preimage_le_descentProj_preimage q Φ hΦ V) x))) := by
  have hr : (descentIncl q Φ hΦ ψ χ hχ) ≫
      ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁)) ≫ (descentProj q Φ hΦ) =
      ((toGradedPowerMap ψ).globalMorphism (relativeProj A)) :=
    globalMorphism_of_baseDescent_eq q Φ hΦ ψ χ hχ
  have hf : (((toGradedPowerMap ψ).globalMorphism (relativeProj A)) ⁻¹ᵁ
      ((relativeProj A).toBase ⁻¹ᵁ V)) ≤
      ((descentIncl q Φ hΦ ψ χ hχ) ≫ ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁)) ≫
      (descentProj q Φ hΦ)) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V) := by rw [hr]
  have hg : (((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁)) ⁻¹ᵁ
      ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V))) ≤
      (((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁)) ≫ (descentProj q Φ hΦ)) ⁻¹ᵁ
      ((relativeProj A).toBase ⁻¹ᵁ V) :=
    ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁)).preimage_mono
        (toBase_preimage_le_descentProj_preimage q Φ hΦ V)
  have hle1 : (((toGradedPowerMap ψ).globalMorphism (relativeProj A)) ⁻¹ᵁ
      ((relativeProj A).toBase ⁻¹ᵁ V)) ≤ (descentIncl q Φ hΦ ψ χ hχ) ⁻¹ᵁ
      (((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁)) ⁻¹ᵁ
      ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V))) :=
    globalMorphism_preimage_le_descent q Φ hΦ ψ χ hχ V
  have s1 := pullbackSection_congr_inv hr ((twD A).algebra.piece (d : ℤ))
    ((relativeProj A).toBase ⁻¹ᵁ V)
        (((toGradedPowerMap ψ).globalMorphism (relativeProj A)) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))
        hf le_rfl x
  have s2 := Stacks.AlgebraicGeometry.ModuleLimits.pullbackComp_inv_val_app_pullbackSection
      (descentIncl q Φ hΦ ψ χ hχ)
    (((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁)) ≫ (descentProj q Φ hΦ))
        ((twD A).algebra.piece (d : ℤ)) ((relativeProj A).toBase ⁻¹ᵁ V)
        (((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁)) ⁻¹ᵁ
        ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V)))
        (((toGradedPowerMap ψ).globalMorphism (relativeProj A)) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))
        hg hle1 hf x
  have s3 := Scheme.Modules.pullbackSection_naturality (descentIncl q Φ hΦ ψ χ hχ)
    ((Scheme.Modules.pullbackComp ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁))
        (descentProj q Φ hΦ)).inv.app ((twD A).algebra.piece (d : ℤ)))
        (((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁)) ⁻¹ᵁ
        ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V)))
        (((toGradedPowerMap ψ).globalMorphism (relativeProj A)) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))
        hle1
    (pullbackSection (((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁)) ≫
        (descentProj q Φ hΦ)) ((twD A).algebra.piece (d : ℤ)) ((relativeProj A).toBase ⁻¹ᵁ V)
      (((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁)) ⁻¹ᵁ
          ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V))) hg x)
  have s4 := Stacks.AlgebraicGeometry.ModuleLimits.pullbackComp_inv_val_app_pullbackSection
      ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁)) (descentProj q Φ hΦ)
    ((twD A).algebra.piece (d : ℤ)) ((relativeProj A).toBase ⁻¹ᵁ V)
        ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V))
        (((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁)) ⁻¹ᵁ
        ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V)))
    (toBase_preimage_le_descentProj_preimage q Φ hΦ V) le_rfl hg x
  have s5 := Scheme.Modules.pullbackSection_naturality (descentIncl q Φ hΦ ψ χ hχ)
    (F := (Scheme.Modules.pullback ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁))).obj
      ((Scheme.Modules.pullback (descentProj q Φ hΦ)).obj ((twD A).algebra.piece (d : ℤ))))
    (G := (Scheme.Modules.pullback ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁))).obj
        ((twD A₁).algebra.piece (d : ℤ)))
    ((Scheme.Modules.pullback ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁))).map
        (descentTwistPieceHom q Φ hΦ (d : ℤ)))
        (((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁)) ⁻¹ᵁ
        ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V)))
        (((toGradedPowerMap ψ).globalMorphism (relativeProj A)) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))
        hle1
    (pullbackSection ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁))
        ((Scheme.Modules.pullback (descentProj q Φ hΦ)).obj ((twD A).algebra.piece (d : ℤ)))
        ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V))
        (((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁)) ⁻¹ᵁ
        ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V)))
      le_rfl (pullbackSection (descentProj q Φ hΦ) ((twD A).algebra.piece (d : ℤ))
          ((relativeProj A).toBase ⁻¹ᵁ V)
        ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V))
          (toBase_preimage_le_descentProj_preimage q Φ hΦ V) x))
  have s6 := Scheme.Modules.pullbackSection_naturality
      ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁))
    (F := (Scheme.Modules.pullback (descentProj q Φ hΦ)).obj ((twD A).algebra.piece (d : ℤ)))
    (G := (twD A₁).algebra.piece (d : ℤ)) (descentTwistPieceHom q Φ hΦ (d : ℤ))
    ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V))
        (((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁)) ⁻¹ᵁ
        ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V))) le_rfl
        (pullbackSection (descentProj q Φ hΦ) ((twD A).algebra.piece (d : ℤ))
      ((relativeProj A).toBase ⁻¹ᵁ V) ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V))
          (toBase_preimage_le_descentProj_preimage q Φ hΦ V) x)
  rw [thetaDescentSourceIso_inv_app]
  show ((Scheme.Modules.pullback (descentIncl q Φ hΦ ψ χ hχ)).map
      ((Scheme.Modules.pullback ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁))).map
      (descentTwistPieceHom q Φ hΦ (d : ℤ)))).val.app
          (op (((toGradedPowerMap ψ).globalMorphism (relativeProj A)) ⁻¹ᵁ
          ((relativeProj A).toBase ⁻¹ᵁ V)))
    (((Scheme.Modules.pullback (descentIncl q Φ hΦ ψ χ hχ)).map
        ((Scheme.Modules.pullbackComp ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁))
        (descentProj q Φ hΦ)).inv.app
      ((twD A).algebra.piece (d : ℤ)))).val.app
          (op (((toGradedPowerMap ψ).globalMorphism (relativeProj A)) ⁻¹ᵁ
          ((relativeProj A).toBase ⁻¹ᵁ V)))
      (((Scheme.Modules.pullbackComp (descentIncl q Φ hΦ ψ χ hχ)
          (((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁)) ≫
          (descentProj q Φ hΦ))).inv.app
        ((twD A).algebra.piece (d : ℤ))).val.app
            (op (((toGradedPowerMap ψ).globalMorphism (relativeProj A)) ⁻¹ᵁ
            ((relativeProj A).toBase ⁻¹ᵁ V)))
        (((Scheme.Modules.pullbackCongr hr).inv.app ((twD A).algebra.piece (d : ℤ))).val.app
            (op (((toGradedPowerMap ψ).globalMorphism (relativeProj A)) ⁻¹ᵁ
            ((relativeProj A).toBase ⁻¹ᵁ V)))
          (pullbackSection ((toGradedPowerMap ψ).globalMorphism (relativeProj A))
              ((twD A).algebra.piece (d : ℤ)) ((relativeProj A).toBase ⁻¹ᵁ V)
              (((toGradedPowerMap ψ).globalMorphism (relativeProj A)) ⁻¹ᵁ
              ((relativeProj A).toBase ⁻¹ᵁ V))
            le_rfl x)))) = _
  rw [s1, s2, s3, s4]
  simp only
  refine s5.trans ?_
  exact congrArg (pullbackSection (descentIncl q Φ hΦ ψ χ hχ)
    ((Scheme.Modules.pullback ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁))).obj
        ((twD A₁).algebra.piece (d : ℤ)))
        (((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁)) ⁻¹ᵁ
        ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V)))
        (((toGradedPowerMap ψ).globalMorphism (relativeProj A)) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))
        hle1) s6

/-- The image in `X` of `r_ψ^{-1}(π^{-1}(V))` lies in that of `r_{ψ↓}^{-1}(π₁^{-1}(q^{-1}(V)))`. -/
theorem image_globalMorphism_preimage_le_descent (V : Z.Opens) :
    (toGradedPowerMap ψ).coveringOpen.ι ''ᵁ
        ((toGradedPowerMap ψ).globalMorphism (relativeProj A) ⁻¹ᵁ
          ((relativeProj A).toBase ⁻¹ᵁ V)) ≤
      (toGradedPowerMap (χ)).coveringOpen.ι ''ᵁ
        ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁) ⁻¹ᵁ
          ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V))) := by
  exact ((toGradedPowerMap ψ).coveringOpen.ι.image_mono
    (globalMorphism_preimage_le_descent q Φ hΦ ψ χ hχ V)).trans
    (image_preimage_descentIncl_le q Φ hΦ ψ χ hχ _)

/-- **`θ` of [Stacks, Tag 01O9] along a change of base**: the map `θ` for `ψ` is the inverse image
along `e : U(ψ) ⟶ U(ψ↓)` of the map `θ` for `ψ↓`, read through the comparison of twists along
`pc` (`thetaDescentSourceIso`) and the identification of the restricted tensor powers
(`thetaDescentTargetIso`). -/
theorem theta_baseDescent :
    (toGradedPowerMap ψ).theta =
      (thetaDescentSourceIso q Φ hΦ ψ χ hχ).inv ≫
        pullbackGradedAlgebraMap (descentIncl q Φ hΦ ψ χ hχ).toLRSHom.toShHom
          (toGradedPowerMap (χ)).theta ≫
        (thetaDescentTargetIso q Φ hΦ ψ χ hχ).hom := by
  refine ((toGradedPowerMap ψ).eq_theta_of_clauseOne fun V d a => ?_).symm
  have s0 : pullbackUnit ((toGradedPowerMap ψ).globalMorphism (relativeProj A)).toLRSHom.toShHom
      (Otw A d) (op ((relativeProj A).toBase ⁻¹ᵁ V)) (psiU A d V a) =
        pullbackSection ((toGradedPowerMap ψ).globalMorphism (relativeProj A))
          ((twD A).algebra.piece (d : ℤ)) ((relativeProj A).toBase ⁻¹ᵁ V)
          ((toGradedPowerMap ψ).globalMorphism (relativeProj A) ⁻¹ᵁ
            ((relativeProj A).toBase ⁻¹ᵁ V)) le_rfl (psiU A d V a) :=
    (Stacks.Conormal.pullbackSection_self _ _ _ _).symm
  have hθ : ∀ x, (((thetaDescentSourceIso q Φ hΦ ψ χ hχ).inv ≫
        pullbackGradedAlgebraMap (descentIncl q Φ hΦ ψ χ hχ).toLRSHom.toShHom
          (toGradedPowerMap (χ)).theta ≫
        (thetaDescentTargetIso q Φ hΦ ψ χ hχ).hom).app (d : ℤ)).val.app
        (op ((toGradedPowerMap ψ).globalMorphism (relativeProj A) ⁻¹ᵁ
          ((relativeProj A).toBase ⁻¹ᵁ V))) x =
      (thetaDescentTargetPieceIso q Φ hΦ ψ χ hχ (d : ℤ)).hom.val.app
        (op ((toGradedPowerMap ψ).globalMorphism (relativeProj A) ⁻¹ᵁ
          ((relativeProj A).toBase ⁻¹ᵁ V)))
        (((Scheme.Modules.pullback (descentIncl q Φ hΦ ψ χ hχ)).map
          (X := (Scheme.Modules.pullback ((toGradedPowerMap (χ)).globalMorphism
            (relativeProj A₁))).obj ((twD A₁).algebra.piece (d : ℤ)))
          (Y := (laurentOn L (toGradedPowerMap (χ)).coveringOpen).piece (d : ℤ))
          ((toGradedPowerMap (χ)).theta.app (d : ℤ))).val.app
          (op ((toGradedPowerMap ψ).globalMorphism (relativeProj A) ⁻¹ᵁ
            ((relativeProj A).toBase ⁻¹ᵁ V)))
          (((thetaDescentSourceIso q Φ hΦ ψ χ hχ).inv.app (d : ℤ)).val.app
            (op ((toGradedPowerMap ψ).globalMorphism (relativeProj A) ⁻¹ᵁ
              ((relativeProj A).toBase ⁻¹ᵁ V))) x)) := fun _ => rfl
  have key := (hθ (pullbackSection ((toGradedPowerMap ψ).globalMorphism (relativeProj A))
      ((twD A).algebra.piece (d : ℤ)) ((relativeProj A).toBase ⁻¹ᵁ V)
      ((toGradedPowerMap ψ).globalMorphism (relativeProj A) ⁻¹ᵁ
        ((relativeProj A).toBase ⁻¹ᵁ V)) le_rfl (psiU A d V a)))
  rw [thetaDescentSourceIso_inv_app_pullbackSection,
    descentTwistPieceHom_pullbackSection_psiU] at key
  have h5 := Scheme.Modules.pullbackSection_naturality (descentIncl q Φ hΦ ψ χ hχ)
    (F := (Scheme.Modules.pullback ((toGradedPowerMap (χ)).globalMorphism
      (relativeProj A₁))).obj ((twD A₁).algebra.piece (d : ℤ)))
    (G := (laurentOn L (toGradedPowerMap (χ)).coveringOpen).piece (d : ℤ))
    ((toGradedPowerMap (χ)).theta.app (d : ℤ))
    ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁) ⁻¹ᵁ
      ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V)))
    ((toGradedPowerMap ψ).globalMorphism (relativeProj A) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))
    (globalMorphism_preimage_le_descent q Φ hΦ ψ χ hχ V)
    (pullbackSection ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁))
      ((twD A₁).algebra.piece (d : ℤ)) ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V))
      ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁) ⁻¹ᵁ
        ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V))) le_rfl
      (psiU A₁ d (q ⁻¹ᵁ V) (descentSection q Φ hΦ a)))
  have h6 : ((toGradedPowerMap (χ)).theta.app (d : ℤ)).val.app
      (op ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁) ⁻¹ᵁ
        ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V))))
      (pullbackSection ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁))
        ((twD A₁).algebra.piece (d : ℤ)) ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V))
        ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁) ⁻¹ᵁ
          ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V))) le_rfl
        (psiU A₁ d (q ⁻¹ᵁ V) (descentSection q Φ hΦ a))) =
      Scheme.Modules.Hom.app ((toGradedPowerMap (χ)).thetaPush (d : ℤ))
        ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V)) (psiU A₁ d (q ⁻¹ᵁ V) (descentSection q Φ hΦ a)) :=
    (toGradedPowerMap (χ)).theta_app_pullbackSection (d : ℤ)
      ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V)) (psiU A₁ d (q ⁻¹ᵁ V) (descentSection q Φ hΦ a))
  have h7 := (toGradedPowerMap (χ)).thetaPush_psiU (q ⁻¹ᵁ V) d
    (descentSection q Φ hΦ a)
  rw [h5] at key
  have key2 := key.trans (congrArg (fun z =>
    (thetaDescentTargetPieceIso q Φ hΦ ψ χ hχ (d : ℤ)).hom.val.app
      (op ((toGradedPowerMap ψ).globalMorphism (relativeProj A) ⁻¹ᵁ
        ((relativeProj A).toBase ⁻¹ᵁ V)))
      (pullbackSection (descentIncl q Φ hΦ ψ χ hχ)
        ((laurentOn L (toGradedPowerMap (χ)).coveringOpen).piece (d : ℤ))
        ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁) ⁻¹ᵁ
          ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V)))
        ((toGradedPowerMap ψ).globalMorphism (relativeProj A) ⁻¹ᵁ
          ((relativeProj A).toBase ⁻¹ᵁ V))
        (globalMorphism_preimage_le_descent q Φ hΦ ψ χ hχ V) z)) (h6.trans h7))
  have h8 := restrictPullbackIso_hom_pullbackSection (descentIncl q Φ hΦ ψ χ hχ)
    (toGradedPowerMap (χ)).coveringOpen.ι (toGradedPowerMap ψ).coveringOpen.ι
    (Scheme.homOfLE_ι X (coveringOpen_of_baseDescent_eq q Φ hΦ ψ χ hχ).ge) (tensorPowerModule X L d)
    ((toGradedPowerMap (χ)).globalMorphism (relativeProj A₁) ⁻¹ᵁ
      ((relativeProj A₁).toBase ⁻¹ᵁ (q ⁻¹ᵁ V)))
    ((toGradedPowerMap ψ).globalMorphism (relativeProj A) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))
    (globalMorphism_preimage_le_descent q Φ hΦ ψ χ hχ V)
    ((tensorPowerModule X L d).presheaf.map (homOfLE
      ((toGradedPowerMap (χ)).image_preimage_preimage_le (q ⁻¹ᵁ V))).op
      ((powCompare L d).hom.app ((𝟙 X) ⁻¹ᵁ (q ⁻¹ᵁ V))
        ((toGradedPowerMap (χ)).value d (q ⁻¹ᵁ V) (descentSection q Φ hΦ a))))
    (image_globalMorphism_preimage_le_descent q Φ hΦ ψ χ hχ V)
  have key3 := key2.trans h8
  rw [s0]
  refine (congrArg (fun z => ((toGradedPowerMap ψ).powK (d : ℤ)).presheaf.map
    (eqToHom ((toGradedPowerMap ψ).toBase_preimage_eq V)).op z) key3).trans ?_
  have hv : (toGradedPowerMap (χ)).value d (q ⁻¹ᵁ V) (descentSection q Φ hΦ a) =
      (toGradedPowerMap ψ).value d V a :=
    (toGradedPowerMap_value (χ) d (q ⁻¹ᵁ V) (descentSection q Φ hΦ a)).trans
      ((valueSec_of_baseDescent_eq q Φ hΦ ψ χ hχ d V a).trans (toGradedPowerMap_value ψ d V a).symm)
  refine (congrArg (fun z => ((toGradedPowerMap ψ).powK (d : ℤ)).presheaf.map
    (eqToHom ((toGradedPowerMap ψ).toBase_preimage_eq V)).op
    ((tensorPowerModule X L d).val.map
      (homOfLE (image_globalMorphism_preimage_le_descent q Φ hΦ ψ χ hχ V)).op
      ((tensorPowerModule X L d).presheaf.map (homOfLE
        ((toGradedPowerMap (χ)).image_preimage_preimage_le (q ⁻¹ᵁ V))).op
        ((powCompare L d).hom.app ((𝟙 X) ⁻¹ᵁ (q ⁻¹ᵁ V)) z)))) hv).trans ?_
  exact map_map3 (tensorPowerModule X L d)
    (homOfLE ((toGradedPowerMap (χ)).image_preimage_preimage_le (q ⁻¹ᵁ V))).op
    (homOfLE (image_globalMorphism_preimage_le_descent q Φ hΦ ψ χ hχ V)).op
    ((toGradedPowerMap ψ).coveringOpen.ι.opensFunctor.map
      (eqToHom ((toGradedPowerMap ψ).toBase_preimage_eq V))).op
    (homOfLE ((toGradedPowerMap ψ).coveringOpen.ι.image_preimage_le (q ⁻¹ᵁ V))).op _


end General

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
