module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LaurentAlgebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.FunctorialityTwist

/-!
# A multiplicative family of maps on twists is determined by its degree-one member

Let `r : X ⟶ Proj_S(𝒜)` be a morphism and `ℒ` an invertible `𝒪_X`-module. A family
`Θ_n : r^* 𝒪(n) ⟶ ℒ^{⊗ n}`, `n ∈ ℤ`, multiplicative on inverse images of sections
(`TwistSections.UnitMul`), whose degree-one member `Θ_1` is an isomorphism, is determined by
`Θ_1`: two such families with the same degree-one member agree in every degree. In particular
they agree on the inverse image of the section `ψ(a)` of `𝒪(d)` attached to a homogeneous section
`a` of `𝒜_d` over an affine open of the base. This is the step "a multiplicative family is
determined by its degree-one member" of [Stacks, Tag 0D4F].

## Main definitions

* `…TwistDegreeOne.mulSection`: multiplication by a local section of `ℒ^{⊗ n}` over an open `W`,
  as a morphism of sheaves of modules `ℒ^{⊗ k} ⟶ j_* j^*(ℒ^{⊗ (n + k)})`.
* `…TwistDegreeOne.chartInvPow`: the inverse `g⁻ᵏ` of `ψ(g ^ k)` over the image of a standard
  open `D₊(g)` of a chart.

## Main results

* `…TwistDegreeOne.eq_of_mulSection_one_eq`: a local section of `ℒ^{⊗ n}` is determined by
  multiplication by it on `ℒ`.
* `…TwistDegreeOne.eq_of_le_one`: two such families agree in every degree `n ≤ 1`.
* `…TwistDegreeOne.eq_of_unitMul_of_app_one`: **they agree in every degree.**
* `…ProjectiveDeformation.psiU_eq_of_unitMul_of_app_one`: they agree on the inverse image of
  `ψ(a)`.

## Implementation notes

*Degrees `n ≤ 1`.* By downward induction from degree one: multiplicativity in bidegree `(n, 1)`
gives `Θ_n(r^* s) · Θ_1(r^* t) = Θ'_n(r^* s) · Θ_1(r^* t)`. Multiplication by
`Θ_n(r^* s)` is a morphism `mulSection` out of `ℒ`, so, `Θ_1` being an isomorphism and a
morphism out of `r^* 𝒪(1)` being determined by its values on inverse images of sections
(`…GradedPowerMap.hom_ext_unitApp`), multiplication by `Θ_n(r^* s)` and by `Θ'_n(r^* s)` agree
on every local section of `ℒ`. They then agree on `ℒ^{⊗ 1} ⊗ ℒ^{⊗ -1} ≅ ℒ^{⊗ 0}` (checked on
pure tensors by associativity), hence on the unit section, which recovers the factor.

*Positive degrees.* Over the image of a standard open `D₊(g)` of a chart, `g` homogeneous of
degree `e > 0`, the section `ψ(g)ᵏ` of `𝒪(k e)` has an inverse `g⁻ᵏ` of degree `-(k e)`, read
off from the description of the sections of the twists over `D₊(g)` as fractions. Writing
`ψ(g)ᵏ = (ψ(g)ᵏ · g⁻ᵏ) · ψ(g)ᵏ`, the values `X = Θ(ψ(g)ᵏ)` and `X' = Θ'(ψ(g)ᵏ)` satisfy
`X = Z X`, `X' = Z X'` and `X Y = X' Y = Z` for the common values `Y` on `g⁻ᵏ` and `Z` on
`ψ(g)ᵏ g⁻ᵏ` (degrees `≤ 1`), whence `X = X'` by associativity and commutativity. Every section
`s` is `(s · g⁻ᵏ) · ψ(g)ᵏ` with `s · g⁻ᵏ` of degree `≤ 1`, and the images of the standard opens
of the charts cover `Proj_S(𝒜)`.

No fibre or stalk argument is needed: the only geometric input besides the chart description
is that sections of a sheaf are determined locally.

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap (psiU Otw twD
  chartIso_inv_mul chartIso_inv_degreeSection chart_image_le)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf degreeSection)
open Stacks.AlgebraicGeometry.Tag07ZGTwist
open Stacks.AlgebraicGeometry.SectionRingBaseChange (unitApp unitApp_map hom_app_map
  map_map_homOfLE)
open Stacks.AlgebraicGeometry.ProjTwistAwayPiece (sectionsTwistEquivGradedPiece
  coe_sectionsTwistEquivGradedPiece_mul coe_sectionsTwistEquivGradedPiece_degreeSection)

universe u w

namespace Stacks.AlgebraicGeometry.ProjectiveDeformation

namespace TwistDegreeOne

section Absolute

variable {σ : Type w} {R : Type u} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {g : R} {e : ℕ}

/-- The fraction `1 / g ^ k` lies in the degree `-(k e)` piece of `A_g`, for `g` homogeneous of
degree `e`. -/
theorem mk_one_pow_mem_gradedPiece (hg : g ∈ 𝒜 e) (k : ℕ) :
    (LocalizedModule.mk (1 : R) (⟨g ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers g) :
        LocalizedModule.Away g R) ∈
      Stacks.GradedLocalization.gradedPiece 𝒜
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.integerGrading (S := R) 𝒜)
        g (-((k * e : ℕ) : ℤ)) := by
  refine (Stacks.GradedLocalization.mem_gradedPiece_iff 𝒜 _ hg _ _).2 ⟨k, 1, ?_, rfl⟩
  have h0 : -((k * e : ℕ) : ℤ) + k • (e : ℤ) = ((0 : ℕ) : ℤ) := by push_cast; simp
  rw [h0, AlgebraicGeometry.ProjectiveSpectrum.Proj.integerGrading_natCast,
    AlgebraicGeometry.ProjectiveSpectrum.Proj.mem_homogeneousSubmodule]
  exact SetLike.GradedOne.one_mem

/-- **The section `1 / g ^ k` of `𝒪(-(k e))` over `D₊(g)`**, for `g` homogeneous of positive degree
`e`. -/
def invPowSection (hg : g ∈ 𝒜 e) (he : 0 < e) (k : ℕ) :
    (twistingSheaf 𝒜 (-((k * e : ℕ) : ℤ))).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 g)) :=
  (sectionsTwistEquivGradedPiece 𝒜 hg he _).symm ⟨_, mk_one_pow_mem_gradedPiece 𝒜 hg k⟩

/-- The restriction to `D₊(g)` of the global section `g ^ k` of `𝒪(k e)`. -/
def powSection (hg : g ∈ 𝒜 e) (k : ℕ) :
    (twistingSheaf 𝒜 ((k * e : ℕ) : ℤ)).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 g)) :=
  (twistingSheaf 𝒜 ((k * e : ℕ) : ℤ)).val.map
    (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ⊤)).op
    (degreeSection 𝒜 (k * e) ⟨g ^ k, by
      simpa [smul_eq_mul] using SetLike.pow_mem_graded k hg⟩)

/-- **`(x · g⁻ᵏ) · gᵏ = x`** for a section `x` of `𝒪(n)` over `D₊(g)`, as a heterogeneous equality
(the left side sits in degree `(n - k e) + k e`). -/
theorem mul_invPowSection_mul_powSection (hg : g ∈ 𝒜 e) (he : 0 < e) (k : ℕ) (n : ℤ)
    (x : (twistingSheaf 𝒜 n).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 g))) :
    HEq (((Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜).mul
        (n + -((k * e : ℕ) : ℤ)) ((k * e : ℕ) : ℤ)).app (op (ProjectiveSpectrum.basicOpen 𝒜 g))
        (((Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜).mul n
          (-((k * e : ℕ) : ℤ))).app (op (ProjectiveSpectrum.basicOpen 𝒜 g)) x
          (invPowSection 𝒜 hg he k)) (powSection 𝒜 hg k)) x := by
  refine Stacks.AlgebraicGeometry.ProjTwistBasicOpenDecomposition.heq_of_coe_eq 𝒜 hg he
    (by ring) _ _ ?_
  refine (coe_sectionsTwistEquivGradedPiece_mul 𝒜 hg he _ _ _ _).trans ?_
  refine (congrArg (fun z => z * _)
    (coe_sectionsTwistEquivGradedPiece_mul 𝒜 hg he _ _ _ _)).trans ?_
  have h1 : (sectionsTwistEquivGradedPiece 𝒜 hg he ((k * e : ℕ) : ℤ) (powSection 𝒜 hg k) :
      LocalizedModule.Away g R) = LocalizedModule.mk (g ^ k) 1 :=
    coe_sectionsTwistEquivGradedPiece_degreeSection 𝒜 hg he (k * e) _
  have h2 : (sectionsTwistEquivGradedPiece 𝒜 hg he (-((k * e : ℕ) : ℤ))
      (invPowSection 𝒜 hg he k) : LocalizedModule.Away g R) =
      LocalizedModule.mk 1 (⟨g ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers g) := by
    unfold invPowSection
    rw [AddEquiv.apply_symm_apply]
  rw [h1, h2, mul_assoc]
  have h3 : (LocalizedModule.mk 1 (⟨g ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers g) *
      LocalizedModule.mk (g ^ k) 1 : LocalizedModule.Away g R) = 1 := by
    refine (LocalizedModule.mk_mul_mk (R := R) (S := Submonoid.powers g) (A := R)).trans ?_
    refine (((LocalizedModule.mk_eq).2 ⟨1, ?_⟩ :
      _ = (LocalizedModule.mk 1 1 : LocalizedModule.Away g R))).trans
      OreLocalization.one_def.symm
    simp only [Submonoid.smul_def, smul_eq_mul, OneMemClass.coe_one, one_mul, mul_one]
  rw [h3, mul_one]

end Absolute

section Chart

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S}

/-- The image in `Proj_S(𝒜)` of the standard open `D₊(g)` of the chart over an affine open `V`. -/
abbrev chartOpen (V : S.Opens) (hV : IsAffineOpen V) (g : A.sectionRing V) :
    (relativeProj A).scheme.Opens :=
  (relativeProj A).chart V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen (A.grading V) g

/-- The restriction of `ψ(g ^ k)` to the image of `D₊(g)`, a section of `𝒪(k e)`. -/
def chartPow (V : S.Opens) (hV : IsAffineOpen V) {e : ℕ} {g : A.sectionRing V}
    (hg : g ∈ A.grading V e) (k : ℕ) : Γ(Otw A ((k * e : ℕ) : ℤ), chartOpen V hV g) :=
  (Otw A (k * e : ℕ)).presheaf.map (homOfLE (chart_image_le V hV
      (AlgebraicGeometry.Proj.basicOpen (A.grading V) g))).op
    (psiU A (k * e) V (A.componentEquiv V (k * e)
      ⟨g ^ k, Stacks.MorphismToProj.HomogeneousRatios.pow_mem hg k⟩))

/-- **The inverse `g⁻ᵏ` of `ψ(g ^ k)` over the image of `D₊(g)`**: the section `1 / g ^ k` of
`𝒪(-(k e))` carried by the chart identification of [Stacks, Tag 01NR]. -/
def chartInvPow (V : S.Opens) (hV : IsAffineOpen V) {e : ℕ} {g : A.sectionRing V}
    (hg : g ∈ A.grading V e) (he : 0 < e) (k : ℕ) :
    Γ(Otw A (-((k * e : ℕ) : ℤ)), chartOpen V hV g) :=
  ((twD A).chartData.chartIso V hV (-((k * e : ℕ) : ℤ))).inv.app
    (AlgebraicGeometry.Proj.basicOpen (A.grading V) g) (invPowSection (A.grading V) hg he k)

/-- The chart identification carries the section `g ^ k` of the absolute twist to `chartPow`. -/
theorem chartIso_inv_powSection (V : S.Opens) (hV : IsAffineOpen V) {e : ℕ}
    {g : A.sectionRing V} (hg : g ∈ A.grading V e) (k : ℕ) :
    ((twD A).chartData.chartIso V hV ((k * e : ℕ) : ℤ)).inv.app
      (AlgebraicGeometry.Proj.basicOpen (A.grading V) g) (powSection (A.grading V) hg k) =
      chartPow V hV hg k :=
  chartIso_inv_degreeSection V hV (k * e) (AlgebraicGeometry.Proj.basicOpen (A.grading V) g)
    ⟨g ^ k, Stacks.MorphismToProj.HomogeneousRatios.pow_mem hg k⟩

/-- The inverse chart identification respects heterogeneous equalities across equal degrees. -/
theorem chartIso_inv_heq (V : S.Opens) (hV : IsAffineOpen V)
    (D : (AlgebraicGeometry.Proj (A.grading V)).Opens) {k k' : ℤ} (hk : k = k')
    {a : (twistingSheaf (A.grading V) k).val.obj (op D)}
    {b : (twistingSheaf (A.grading V) k').val.obj (op D)} (hab : HEq a b) :
    HEq (((twD A).chartData.chartIso V hV k).inv.app D a)
      (((twD A).chartData.chartIso V hV k').inv.app D b) := by
  subst hk
  exact heq_of_eq (congrArg _ (eq_of_heq hab))

/-- **`(s · g⁻ᵏ) · ψ(g)ᵏ = s`** for every section `s` of `𝒪(n)` over the image of `D₊(g)`, as a
heterogeneous equality. -/
theorem mul_chartInvPow_mul_chartPow (V : S.Opens) (hV : IsAffineOpen V) {e : ℕ}
    {g : A.sectionRing V} (hg : g ∈ A.grading V e) (he : 0 < e) (k : ℕ) (n : ℤ)
    (s : Γ(Otw A n, chartOpen V hV g)) :
    HEq (((twD A).algebra.mul (n + -((k * e : ℕ) : ℤ)) ((k * e : ℕ) : ℤ)).app
        (op (chartOpen V hV g))
        (((twD A).algebra.mul n (-((k * e : ℕ) : ℤ))).app (op (chartOpen V hV g)) s
          (chartInvPow V hV hg he k))
        (chartPow V hV hg k)) s := by
  obtain ⟨σ, rfl⟩ : ∃ σ, ((twD A).chartData.chartIso V hV n).inv.app
      (AlgebraicGeometry.Proj.basicOpen (A.grading V) g) σ = s :=
    ⟨_, (ConcreteCategory.congr_hom (congrArg (fun φ => Scheme.Modules.Hom.app φ
      (AlgebraicGeometry.Proj.basicOpen (A.grading V) g))
      ((twD A).chartData.chartIso V hV n).hom_inv_id) s).trans rfl⟩
  have h2a := chartIso_inv_mul V hV n (-((k * e : ℕ) : ℤ))
    (AlgebraicGeometry.Proj.basicOpen (A.grading V) g) σ (invPowSection (A.grading V) hg he k)
  have h2b := chartIso_inv_mul V hV (n + -((k * e : ℕ) : ℤ)) ((k * e : ℕ) : ℤ)
    (AlgebraicGeometry.Proj.basicOpen (A.grading V) g)
    (((Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra (A.grading V)).mul n
      (-((k * e : ℕ) : ℤ))).app (op (AlgebraicGeometry.Proj.basicOpen (A.grading V) g)) σ
      (invPowSection (A.grading V) hg he k)) (powSection (A.grading V) hg k)
  have h4 : ((twD A).algebra.mul (n + -((k * e : ℕ) : ℤ)) ((k * e : ℕ) : ℤ)).app
        (op (chartOpen V hV g))
        (((twD A).algebra.mul n (-((k * e : ℕ) : ℤ))).app (op (chartOpen V hV g))
          (((twD A).chartData.chartIso V hV n).inv.app
            (AlgebraicGeometry.Proj.basicOpen (A.grading V) g) σ) (chartInvPow V hV hg he k))
        (chartPow V hV hg k) =
      ((twD A).chartData.chartIso V hV (n + -((k * e : ℕ) : ℤ) + ((k * e : ℕ) : ℤ))).inv.app
        (AlgebraicGeometry.Proj.basicOpen (A.grading V) g)
        (((Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra (A.grading V)).mul
          (n + -((k * e : ℕ) : ℤ)) ((k * e : ℕ) : ℤ)).app
          (op (AlgebraicGeometry.Proj.basicOpen (A.grading V) g))
          (((Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra (A.grading V)).mul n
            (-((k * e : ℕ) : ℤ))).app (op (AlgebraicGeometry.Proj.basicOpen (A.grading V) g)) σ
            (invPowSection (A.grading V) hg he k)) (powSection (A.grading V) hg k)) := by
    refine Eq.trans ?_ h2b.symm
    exact congrArg₂ (fun a b => ((twD A).algebra.mul (n + -((k * e : ℕ) : ℤ))
      ((k * e : ℕ) : ℤ)).app (op (chartOpen V hV g)) a b) h2a.symm
      (chartIso_inv_powSection V hV hg k).symm
  exact (heq_of_eq h4).trans (chartIso_inv_heq V hV _ (by ring)
    (mul_invPowSection_mul_powSection (A.grading V) hg he k n σ))

end Chart


section Cancel

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- Tag 01CU's invertibility class, supplied from the ampleness theory's one, as in
`StacksFrontier/AlgebraicGeometry/TensorPowerDivision/LocalProduct.lean`. -/
local instance isInvertibleTwistDegreeOne :
    Stacks.SheafOfModules.IsInvertible X.presheaf (Stacks.TensorPowerDivision.hStruct X) L :=
  Stacks.PowerFamilyBridge.instIsInvertible X.presheaf (Stacks.TensorPowerDivision.hStruct X) L

/-- `j_* j^*(ℒ^{⊗ m})` for the inclusion `j` of an open `W`: its sections over `V` are those of
`ℒ^{⊗ m}` over `V ∩ W`. -/
abbrev restrictPush (W : X.Opens) (m : ℤ) : X.Modules :=
  (Scheme.Modules.pushforward W.ι).obj ((tensorPowerModule X L m).restrict W.ι)

/-- The image of the preimage of `V` under the inclusion of `W` lies in `W`. -/
theorem image_preimage_ι_le (W V : X.Opens) : W.ι ''ᵁ (W.ι ⁻¹ᵁ V) ≤ W :=
  (Scheme.Hom.image_mono _ le_top).trans (by simp)

/-- The image of the preimage of `V ≤ W` under the inclusion of `W` is `V`. -/
alias image_preimage_ι_eq := Stacks.AlgebraicGeometry.ModuleLimits.image_preimage_of_le

/-- Multiplication by a section `c` of `ℒ^{⊗ n}` over `W`, on the sections of `ℒ^{⊗ k}` over `V`:
`ℓ ↦ c|_{V ∩ W} · ℓ|_{V ∩ W}`. -/
def mulSectionsApp (W : X.Opens) {n : ℤ} (c : Γ(tensorPowerModule X L n, W)) (k : ℤ)
    (V : X.Opens) (ℓ : Γ(tensorPowerModule X L k, V)) : Γ(restrictPush L W (n + k), V) :=
  Stacks.TensorPowerDivision.localMul L
    ((tensorPowerModule X L n).presheaf.map (homOfLE (image_preimage_ι_le W V)).op c)
    ((tensorPowerModule X L k).presheaf.map (homOfLE (W.ι.image_preimage_le V)).op ℓ)

/-- `mulSectionsApp` is linear. -/
theorem mulSectionsApp_smul (W : X.Opens) {n : ℤ} (c : Γ(tensorPowerModule X L n, W)) (k : ℤ)
    (V : X.Opens) (r : Γ(X, V)) (ℓ : Γ(tensorPowerModule X L k, V)) :
    mulSectionsApp L W c k V (r • ℓ) = r • mulSectionsApp L W c k V ℓ := by
  have hsm : ∀ (M : X.Modules) (z : Γ(M, W.ι ''ᵁ (W.ι ⁻¹ᵁ V))),
      @Eq Γ(M, W.ι ''ᵁ (W.ι ⁻¹ᵁ V))
        (@HSMul.hSMul Γ(X, V) Γ((Scheme.Modules.pushforward W.ι).obj (M.restrict W.ι), V)
          Γ((Scheme.Modules.pushforward W.ι).obj (M.restrict W.ι), V) _ r z)
        (X.presheaf.map (homOfLE (W.ι.image_preimage_le V)).op r • z) := by
    intro M z
    have h := congrArg (fun φ => (ConcreteCategory.hom φ) r) (Scheme.Hom.app_appIso_inv W.ι V)
    exact (congrArg (fun q => q • z) h :)
  unfold mulSectionsApp
  rw [hsm, Scheme.Modules.map_smul]
  exact (Stacks.TensorPowerDivision.localMulBilinear L n k).map_smul_right _ _ _ _

/-- `mulSectionsApp` is additive. -/
theorem mulSectionsApp_add (W : X.Opens) {n : ℤ} (c : Γ(tensorPowerModule X L n, W)) (k : ℤ)
    (V : X.Opens) (ℓ₁ ℓ₂ : Γ(tensorPowerModule X L k, V)) :
    mulSectionsApp L W c k V (ℓ₁ + ℓ₂) =
      mulSectionsApp L W c k V ℓ₁ + mulSectionsApp L W c k V ℓ₂ := by
  unfold mulSectionsApp
  rw [map_add]
  exact map_add ((Stacks.TensorPowerDivision.localMulBilinear L n k).app (op _) _) _ _

/-- `mulSectionsApp` commutes with restriction. -/
theorem mulSectionsApp_map (W : X.Opens) {n : ℤ} (c : Γ(tensorPowerModule X L n, W)) (k : ℤ)
    {V V' : X.Opens} (h : V' ≤ V) (ℓ : Γ(tensorPowerModule X L k, V)) :
    mulSectionsApp L W c k V' ((tensorPowerModule X L k).presheaf.map (homOfLE h).op ℓ) =
      (restrictPush L W (n + k)).presheaf.map (homOfLE h).op (mulSectionsApp L W c k V ℓ) := by
  have hU : W.ι ''ᵁ (W.ι ⁻¹ᵁ V') ≤ W.ι ''ᵁ (W.ι ⁻¹ᵁ V) :=
    Scheme.Hom.image_mono _ (W.ι.preimage_mono h)
  show _ = (tensorPowerModule X L (n + k)).presheaf.map (homOfLE hU).op _
  unfold mulSectionsApp
  rw [Stacks.TensorPowerDivision.map_localMul,
    Stacks.AlgebraicGeometry.SectionRingBaseChange.map_map_homOfLE _ _ _
      (image_preimage_ι_le W V'),
    Stacks.AlgebraicGeometry.SectionRingBaseChange.map_map_homOfLE _ _ _
      ((W.ι.image_preimage_le V').trans h),
    Stacks.AlgebraicGeometry.SectionRingBaseChange.map_map_homOfLE _ _ _
      ((W.ι.image_preimage_le V').trans h)]

/-- `mulSectionsApp` comes from a unique morphism of sheaves of modules. -/
theorem existsUnique_mulSection (W : X.Opens) {n : ℤ} (c : Γ(tensorPowerModule X L n, W))
    (k : ℤ) :
    ∃! φ : tensorPowerModule X L k ⟶ restrictPush L W (n + k),
      ∀ (i : PUnit.{u + 1}) (V : X.Opens) (hV : V ≤ (fun _ : PUnit.{u + 1} => (⊤ : X.Opens)) i),
        φ.app V = AddCommGrpCat.ofHom (AddMonoidHom.mk' (mulSectionsApp L W c k V)
          (mulSectionsApp_add L W c k V)) :=
  Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_cover_app (ι := PUnit.{u + 1})
    (U := fun _ => ⊤) iSup_const
    (fun _ V _ => AddCommGrpCat.ofHom (AddMonoidHom.mk' (mulSectionsApp L W c k V)
      (mulSectionsApp_add L W c k V)))
    (fun _ V _ r ℓ => mulSectionsApp_smul L W c k V r ℓ)
    (fun _ _ _ _ h ℓ => mulSectionsApp_map L W c k h ℓ) (fun _ _ _ _ _ => rfl)

/-- **Multiplication by a local section `c` of `ℒ^{⊗ n}` over `W`**, as a morphism
`ℒ^{⊗ k} ⟶ j_* j^*(ℒ^{⊗ (n + k)})`. -/
def mulSection (W : X.Opens) {n : ℤ} (c : Γ(tensorPowerModule X L n, W)) (k : ℤ) :
    tensorPowerModule X L k ⟶ restrictPush L W (n + k) :=
  (existsUnique_mulSection L W c k).exists.choose

/-- `mulSection` on sections is `mulSectionsApp`. -/
theorem mulSection_app (W : X.Opens) {n : ℤ} (c : Γ(tensorPowerModule X L n, W)) (k : ℤ)
    (V : X.Opens) (ℓ : Γ(tensorPowerModule X L k, V)) :
    (mulSection L W c k).app V ℓ = mulSectionsApp L W c k V ℓ :=
  ConcreteCategory.congr_hom
    ((existsUnique_mulSection L W c k).exists.choose_spec PUnit.unit V le_top) ℓ

/-- Transport of an equality of `mulSection`s along an equality of degrees. -/
theorem mulSection_congr_degree (W : X.Opens) {n : ℤ} (a b : Γ(tensorPowerModule X L n, W))
    {k k' : ℤ} (hk : k = k') (h : mulSection L W a k = mulSection L W b k) :
    mulSection L W a k' = mulSection L W b k' := by
  subst hk
  exact h

/-- **A local section of `ℒ^{⊗ n}` is determined by multiplication by it on `ℒ`**: if
`a · ℓ = b · ℓ` for every local section `ℓ` of `ℒ`, then `a = b`. Multiplication by `a` on
`ℒ^{⊗ 1} ⊗ ℒ^{⊗ -1} ≅ ℒ^{⊗ 0}` is then that of `b`, and `a = a · 1`. -/
theorem eq_of_mulSection_one_eq (W : X.Opens) {n : ℤ} (a b : Γ(tensorPowerModule X L n, W))
    (h : mulSection L W a 1 = mulSection L W b 1) : a = b := by
  have hm : (Stacks.SheafOfModules.TensorPower.coherentMulIso X.presheaf
        (Stacks.TensorPowerDivision.hStruct X) L 1 (-1)).hom ≫ mulSection L W a (1 + -1) =
      (Stacks.SheafOfModules.TensorPower.coherentMulIso X.presheaf
        (Stacks.TensorPowerDivision.hStruct X) L 1 (-1)).hom ≫ mulSection L W b (1 + -1) := by
    refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := X.sheaf) fun U ℓ ℓ' => ?_
    change Γ(tensorPowerModule X L 1, U.unop) at ℓ
    change Γ(tensorPowerModule X L (-1), U.unop) at ℓ'
    show (mulSection L W a (1 + -1)).app U.unop (Stacks.TensorPowerDivision.localMul L ℓ ℓ') =
      (mulSection L W b (1 + -1)).app U.unop (Stacks.TensorPowerDivision.localMul L ℓ ℓ')
    have h1 := ConcreteCategory.congr_hom (congrArg (fun φ => Scheme.Modules.Hom.app φ U.unop) h) ℓ
    replace h1 := (mulSection_app L W a 1 U.unop ℓ).symm.trans
      (h1.trans (mulSection_app L W b 1 U.unop ℓ))
    refine (mulSection_app L W a _ U.unop _).trans
      (Eq.trans ?_ (mulSection_app L W b _ U.unop _).symm)
    unfold mulSectionsApp at h1 ⊢
    rw [Stacks.TensorPowerDivision.map_localMul]
    refine eq_of_heq ((Stacks.TensorPowerDivision.localMul_assoc_heq L _ _ _).symm.trans
      (HEq.trans ?_ (Stacks.TensorPowerDivision.localMul_assoc_heq L _ _ _)))
    exact heq_of_eq (congrArg (fun z => Stacks.TensorPowerDivision.localMul L z _) h1)
  have h0 := mulSection_congr_degree L W a b (show (1 : ℤ) + -1 = 0 by norm_num)
    ((Iso.cancel_iso_hom_left _ _ _).mp hm)
  have hone := ConcreteCategory.congr_hom (congrArg (fun φ => Scheme.Modules.Hom.app φ W) h0)
    ((Stacks.SheafOfModules.TensorPower.oneSection X.presheaf
      (Stacks.TensorPowerDivision.hStruct X) L).eval (op W))
  replace hone := (mulSection_app L W a 0 W _).symm.trans (hone.trans (mulSection_app L W b 0 W _))
  unfold mulSectionsApp at hone
  have hres : (tensorPowerModule X L 0).presheaf.map
      (homOfLE (W.ι.image_preimage_le W)).op
      ((Stacks.SheafOfModules.TensorPower.oneSection X.presheaf
        (Stacks.TensorPowerDivision.hStruct X) L).eval (op W)) =
      (Stacks.SheafOfModules.TensorPower.oneSection X.presheaf
        (Stacks.TensorPowerDivision.hStruct X) L).eval (op (W.ι ''ᵁ (W.ι ⁻¹ᵁ W))) :=
    PresheafOfModules.sections_property (Stacks.SheafOfModules.TensorPower.oneSection X.presheaf
      (Stacks.TensorPowerDivision.hStruct X) L) (homOfLE (W.ι.image_preimage_le W)).op
  rw [hres] at hone
  have hmul := fun c : Γ(tensorPowerModule X L n, W) =>
    Stacks.SheafOfModules.TensorPower.mulBilinear_mul_one X.presheaf
    (Stacks.TensorPowerDivision.hStruct X) L n (op (W.ι ''ᵁ (W.ι ⁻¹ᵁ W)))
    ((tensorPowerModule X L n).presheaf.map (homOfLE (image_preimage_ι_le W W)).op c)
  exact (Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.map_bijective_of_eq _
    (image_preimage_ι_le W W) (image_preimage_ι_eq le_rfl).symm).1
    (eq_of_heq ((hmul a).symm.trans ((heq_of_eq hone).trans (hmul b))))

/-- **Cancellation of an isomorphism `θ : r^* M ≅ ℒ`**: if `a · θ(r^* t) = b · θ(r^* t)` for every
section `t` of `M`, then `a = b`. -/
theorem eq_of_mulSectionsApp_unitApp_eq {P : Scheme.{u}} (r : X ⟶ P) (M : P.Modules)
    (θ : (Scheme.Modules.pullback r).obj M ⟶ tensorPowerModule X L 1) [IsIso θ]
    (W : X.Opens) {n : ℤ} (a b : Γ(tensorPowerModule X L n, W))
    (h : ∀ (O : P.Opens) (t : Γ(M, O)),
      mulSectionsApp L W a 1 (r ⁻¹ᵁ O) (θ.app (r ⁻¹ᵁ O) (unitApp r M O t)) =
        mulSectionsApp L W b 1 (r ⁻¹ᵁ O) (θ.app (r ⁻¹ᵁ O) (unitApp r M O t))) : a = b := by
  refine eq_of_mulSection_one_eq L W a b ((cancel_epi θ).mp ?_)
  refine Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap.hom_ext_unitApp
    r _ _ fun O t => ?_
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, mulSection_app, mulSection_app]
  exact h O t

/-- Restricting the value of a morphism out of `r^* M` on `r^* s` is evaluating on `r^*(s|)`. -/
theorem restrict_app_unitApp {P : Scheme.{u}} (r : X ⟶ P) {M : P.Modules} {N : X.Modules}
    (φ : (Scheme.Modules.pullback r).obj M ⟶ N) {O₁ O₂ : P.Opens} (hO : O₁ ≤ O₂)
    (s : Γ(M, O₂)) {U : X.Opens} (h₁ : U ≤ r ⁻¹ᵁ O₁) (h₂ : U ≤ r ⁻¹ᵁ O₂) :
    N.presheaf.map (homOfLE h₂).op (φ.app (r ⁻¹ᵁ O₂) (unitApp r M O₂ s)) =
      N.presheaf.map (homOfLE h₁).op
        (φ.app (r ⁻¹ᵁ O₁) (unitApp r M O₁ (M.presheaf.map (homOfLE hO).op s))) := by
  rw [unitApp_map, hom_app_map, map_map_homOfLE]

end Cancel

section Family

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {S X : Scheme.{u}} {A : SheafGradedAlgebra.{u} S}
  (r : X ⟶ (relativeProj A).scheme) (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (Θ Θ' : ∀ n : ℤ, (Scheme.Modules.pullback r).obj (Otw A n) ⟶ tensorPowerModule X L n)

/-- **The downward step**: a multiplicative family with `Θ 1` an isomorphism is determined in
degree `n` by its members in degrees `n + 1` and `1`. -/
theorem eq_of_eq_succ (hΘ : TwistSections.UnitMul L r (twistAlgebra A) Θ)
    (hΘ' : TwistSections.UnitMul L r (twistAlgebra A) Θ') (h1 : Θ 1 = Θ' 1) [IsIso (Θ 1)]
    (n : ℤ) (hn : Θ (n + 1) = Θ' (n + 1)) : Θ n = Θ' n := by
  refine Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap.hom_ext_unitApp
    r _ _ fun O s => ?_
  refine eq_of_mulSectionsApp_unitApp_eq L r (Otw A 1) (Θ 1) (r ⁻¹ᵁ O) _ _ fun O' t => ?_
  have hU : (r ⁻¹ᵁ O).ι ''ᵁ ((r ⁻¹ᵁ O).ι ⁻¹ᵁ (r ⁻¹ᵁ O')) ≤ r ⁻¹ᵁ (O ⊓ O') :=
    le_inf (image_preimage_ι_le _ _) (Scheme.Hom.image_preimage_le _ _)
  unfold mulSectionsApp
  rw [restrict_app_unitApp r (Θ n) inf_le_left s hU, restrict_app_unitApp r (Θ 1) inf_le_right t hU,
    restrict_app_unitApp r (Θ' n) inf_le_left s hU, ← Stacks.TensorPowerDivision.map_localMul,
    ← Stacks.TensorPowerDivision.map_localMul, ← hΘ n 1, h1, ← hΘ' n 1, hn]

/-- Transport of an equality of members of two families along an equality of degrees. -/
theorem eq_congr_degree {k k' : ℤ} (hk : k = k') (h : Θ k = Θ' k) : Θ k' = Θ' k' := by
  subst hk
  exact h

/-- **Two multiplicative families with the same invertible degree-one member agree in every degree
`n ≤ 1`.** -/
theorem eq_of_le_one (hΘ : TwistSections.UnitMul L r (twistAlgebra A) Θ)
    (hΘ' : TwistSections.UnitMul L r (twistAlgebra A) Θ') (h1 : Θ 1 = Θ' 1) [IsIso (Θ 1)]
    (n : ℤ) (hn : n ≤ 1) : Θ n = Θ' n := by
  have key : ∀ m : ℕ, Θ (1 - m) = Θ' (1 - m) := by
    intro m
    induction m with
    | zero => exact eq_congr_degree r L Θ Θ' (by norm_num) h1
    | succ m ih =>
        exact eq_of_eq_succ r L Θ Θ' hΘ hΘ' h1 _
          (eq_congr_degree r L Θ Θ' (by push_cast; ring) ih)
  exact eq_congr_degree r L Θ Θ' (by omega) (key (1 - n).toNat)

/-- The members of a family on heterogeneously equal sections in equal degrees. -/
theorem app_unitApp_heq {O : (relativeProj A).scheme.Opens} {k k' : ℤ} (hk : k = k')
    {x : Γ(Otw A k, O)} {x' : Γ(Otw A k', O)} (hx : HEq x x') :
    HEq ((Θ k).app (r ⁻¹ᵁ O) (unitApp r (Otw A k) O x))
      ((Θ k').app (r ⁻¹ᵁ O) (unitApp r (Otw A k') O x')) := by
  subst hk
  rw [eq_of_heq hx]

/-- A multiplicative family evaluates a product of sections as the product of the values. -/
private theorem app_unitApp_heq_localMul {Φ : ∀ n : ℤ, (Scheme.Modules.pullback r).obj (Otw A n) ⟶
      tensorPowerModule X L n} (hΦ : TwistSections.UnitMul L r (twistAlgebra A) Φ)
    {O : (relativeProj A).scheme.Opens} {k k₁ k₂ : ℤ} (hk : k = k₁ + k₂)
    {x : Γ(Otw A k, O)} (y : Γ(Otw A k₁, O)) (z : Γ(Otw A k₂, O))
    (h : HEq (((twD A).algebra.mul k₁ k₂).app (op O) y z) x) :
    HEq ((Φ k).app (r ⁻¹ᵁ O) (unitApp r (Otw A k) O x))
      (Stacks.TensorPowerDivision.localMul L
        ((Φ k₁).app (r ⁻¹ᵁ O) (unitApp r (Otw A k₁) O y))
        ((Φ k₂).app (r ⁻¹ᵁ O) (unitApp r (Otw A k₂) O z))) :=
  (app_unitApp_heq r L Φ hk h.symm).trans (heq_of_eq (hΦ _ _ _ _ _))

/-- **The two families agree on `ψ(g)ᵏ` over the image of `D₊(g)`**: both values are inverse to
the common value on `g⁻ᵏ`, the families agreeing in degrees `≤ 1`. -/
theorem app_chartPow_eq (hΘ : TwistSections.UnitMul L r (twistAlgebra A) Θ)
    (hΘ' : TwistSections.UnitMul L r (twistAlgebra A) Θ') (h1 : Θ 1 = Θ' 1) [IsIso (Θ 1)]
    (V : S.Opens) (hV : IsAffineOpen V) {e : ℕ} {g : A.sectionRing V}
    (hg : g ∈ A.grading V e) (he : 0 < e) (k : ℕ) :
    (Θ ((k * e : ℕ) : ℤ)).app (r ⁻¹ᵁ chartOpen V hV g)
        (unitApp r (Otw A ((k * e : ℕ) : ℤ)) (chartOpen V hV g) (chartPow V hV hg k)) =
      (Θ' ((k * e : ℕ) : ℤ)).app (r ⁻¹ᵁ chartOpen V hV g)
        (unitApp r (Otw A ((k * e : ℕ) : ℤ)) (chartOpen V hV g) (chartPow V hV hg k)) := by
  have hdeg : ((k * e : ℕ) : ℤ) = ((k * e : ℕ) : ℤ) + -((k * e : ℕ) : ℤ) + ((k * e : ℕ) : ℤ) := by
    ring
  have hneg : Θ (-((k * e : ℕ) : ℤ)) = Θ' (-((k * e : ℕ) : ℤ)) :=
    eq_of_le_one r L Θ Θ' hΘ hΘ' h1 _ (by omega)
  have hzero : Θ (((k * e : ℕ) : ℤ) + -((k * e : ℕ) : ℤ)) =
      Θ' (((k * e : ℕ) : ℤ) + -((k * e : ℕ) : ℤ)) :=
    eq_of_le_one r L Θ Θ' hΘ hΘ' h1 _ (by omega)
  have hcf := mul_chartInvPow_mul_chartPow V hV hg he k ((k * e : ℕ) : ℤ) (chartPow V hV hg k)
  have hZ := hΘ ((k * e : ℕ) : ℤ) (-((k * e : ℕ) : ℤ)) (chartOpen V hV g) (chartPow V hV hg k)
    (chartInvPow V hV hg he k)
  have hZ' := hΘ' ((k * e : ℕ) : ℤ) (-((k * e : ℕ) : ℤ)) (chartOpen V hV g) (chartPow V hV hg k)
    (chartInvPow V hV hg he k)
  rw [← hneg, ← hzero] at hZ'
  have e1 := app_unitApp_heq_localMul r L hΘ' hdeg _ _ hcf
  rw [← hzero, hZ] at e1
  have e2 := app_unitApp_heq_localMul r L hΘ hdeg _ _ hcf
  rw [hZ] at e2
  have hXY := hZ'.symm.trans hZ
  refine eq_of_heq (e2.trans (HEq.trans (HEq.symm ?_) e1.symm))
  refine (Stacks.TensorPowerDivision.localMul_assoc_heq L _ _ _).trans ?_
  refine (Stacks.TensorPowerDivision.localMul_congr_heq_right L (add_comm _ _) _
    (Stacks.TensorPowerDivision.localMul_comm_heq L _ _)).trans ?_
  rw [hXY]
  exact Stacks.TensorPowerDivision.localMul_comm_heq L _ _

/-- The two families agree on every section over the image of a standard open of a chart:
`s = (s · g⁻ᵏ) · ψ(g)ᵏ` with `s · g⁻ᵏ` of degree `≤ 1`. -/
theorem app_chart_eq (hΘ : TwistSections.UnitMul L r (twistAlgebra A) Θ)
    (hΘ' : TwistSections.UnitMul L r (twistAlgebra A) Θ') (h1 : Θ 1 = Θ' 1) [IsIso (Θ 1)]
    (V : S.Opens) (hV : IsAffineOpen V) {e : ℕ} {g : A.sectionRing V}
    (hg : g ∈ A.grading V e) (he : 0 < e) (n : ℤ) (s : Γ(Otw A n, chartOpen V hV g)) :
    (Θ n).app (r ⁻¹ᵁ chartOpen V hV g) (unitApp r (Otw A n) (chartOpen V hV g) s) =
      (Θ' n).app (r ⁻¹ᵁ chartOpen V hV g) (unitApp r (Otw A n) (chartOpen V hV g) s) := by
  have hcf := mul_chartInvPow_mul_chartPow V hV hg he n.toNat n s
  have hdeg : n = n + -((n.toNat * e : ℕ) : ℤ) + ((n.toNat * e : ℕ) : ℤ) := by ring
  have hle : n.toNat ≤ n.toNat * e := Nat.le_mul_of_pos_right _ he
  have hlow : Θ (n + -((n.toNat * e : ℕ) : ℤ)) = Θ' (n + -((n.toNat * e : ℕ) : ℤ)) := by
    refine eq_of_le_one r L Θ Θ' hΘ hΘ' h1 _ ?_
    generalize n.toNat * e = m at hle
    omega
  have e1 := app_unitApp_heq_localMul r L hΘ hdeg _ _ hcf
  have e2 := app_unitApp_heq_localMul r L hΘ' hdeg _ _ hcf
  rw [hlow, app_chartPow_eq r L Θ Θ' hΘ hΘ' h1 V hV hg he] at e1
  exact eq_of_heq (e1.trans e2.symm)

/-- **A multiplicative family `r^* 𝒪(n) ⟶ ℒ^{⊗ n}` is determined by its degree-one member**, as
soon as that member is an isomorphism: two such families with the same member in degree one agree
in every degree. -/
theorem eq_of_unitMul_of_app_one (hΘ : TwistSections.UnitMul L r (twistAlgebra A) Θ)
    (hΘ' : TwistSections.UnitMul L r (twistAlgebra A) Θ') (h1 : Θ 1 = Θ' 1) [IsIso (Θ 1)]
    (n : ℤ) : Θ n = Θ' n := by
  refine Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap.hom_ext_unitApp
    r _ _ fun O s => ?_
  let ι := {k : (V : S.affineOpens) ×
      Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.Idx (A.grading V.1) //
    chartOpen k.1.1 k.1.2 (k.2.1.2 : A.sectionRing k.1.1) ≤ O}
  let U : ι → X.Opens := fun k =>
    r ⁻¹ᵁ chartOpen k.1.1.1 k.1.1.2 (k.1.2.1.2 : A.sectionRing k.1.1.1)
  have hUO : ∀ k, U k ≤ r ⁻¹ᵁ O := fun k => r.preimage_mono k.2
  have hcov : r ⁻¹ᵁ O ≤ ⨆ k, U k := by
    intro x hx
    obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset
      (Opens.mem_top ((relativeProj A).toBase.base (r.base x)))
    have hzr : r.base x ∈ ((relativeProj A).chart V hV).opensRange := by
      rw [Stacks.AlgebraicGeometry.RelativeProjTwistQcoh.opensRange_chart]; exact hzV
    obtain ⟨w, hw'⟩ := hzr
    have hw : w ∈ (relativeProj A).chart V hV ⁻¹ᵁ O :=
      show ((relativeProj A).chart V hV).base w ∈ O from hw' ▸ hx
    obtain ⟨d, g, hd, hg, hwg, hgW⟩ :=
      Stacks.AlgebraicGeometry.ProjShared.exists_basicOpen_homogeneous_le (A.grading V) hw
    have hle : chartOpen V hV g ≤ O :=
      le_trans (Scheme.Hom.image_mono ((relativeProj A).chart V hV) hgW)
        (((relativeProj A).chart V hV).image_preimage_le O)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨⟨V, hV⟩, ⟨⟨d, ⟨g, hg⟩⟩, hd⟩⟩, hle⟩,
      show r.base x ∈ chartOpen V hV g from hw' ▸ ⟨w, hwg, rfl⟩⟩
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf (tensorPowerModule X L n).isSheaf U hUO
    hcov fun k => ?_
  refine (restrict_app_unitApp r (Θ n) k.2 s le_rfl (hUO k)).trans
    (Eq.trans ?_ (restrict_app_unitApp r (Θ' n) k.2 s le_rfl (hUO k)).symm)
  exact congrArg _ (app_chart_eq r L Θ Θ' hΘ hΘ' h1 k.1.1.1 k.1.1.2 k.1.2.1.2.2 k.1.2.2 n _)

end Family

end TwistDegreeOne

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

/-- (G1) A multiplicative family is determined, on the sections attached to homogeneous elements
of positive degree, by its degree-one member, as soon as that member is an isomorphism onto an
invertible module. -/
theorem psiU_eq_of_unitMul_of_app_one {S X : Scheme.{u}} {A : SheafGradedAlgebra.{u} S}
    (r : X ⟶ (relativeProj A).scheme) (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (Θ Θ' : ∀ n : ℤ, (Scheme.Modules.pullback r).obj (Otw A n) ⟶ tensorPowerModule X L n)
    (hΘ : TwistSections.UnitMul L r (twistAlgebra A) Θ)
    (hΘ' : TwistSections.UnitMul L r (twistAlgebra A) Θ')
    (h1 : Θ 1 = Θ' 1) [IsIso (Θ 1)]
    (V : S.Opens) (hV : IsAffineOpen V) (d : ℕ) (hd : 0 < d) (a : Γ(A.piece (d : ℤ), V)) :
    (Θ d).app (r ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))
        (unitApp r (Otw A d) ((relativeProj A).toBase ⁻¹ᵁ V) (psiU A d V a)) =
      (Θ' d).app (r ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))
        (unitApp r (Otw A d) ((relativeProj A).toBase ⁻¹ᵁ V) (psiU A d V a)) := by
  rw [TwistDegreeOne.eq_of_unitMul_of_app_one r L Θ Θ' hΘ hΘ' h1 (d : ℤ)]

end Stacks.AlgebraicGeometry.ProjectiveDeformation

end
