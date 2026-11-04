module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiChartSourceMonoidal

/-!
# The identification of the source of `ψ` on the atlas is monoidal, stated with the identification

In Situation 0849 let `π : P ⟶ X` be the relative Proj, `X = U/R` a presentation of the base and
`c : P_U ⟶ P` the atlas of the induced presentation of `P`.  The inverse image along `c` of the
source `π^*𝒜` of the homomorphism `ψ` of Stacks 084D is identified degreewise with the module
attached to `π_U^*(u^*𝒜)_n` (`AlgebraicGeometry.Space.RelativeProjPoints.chartPullbackIso`, in
Situation 0849 `AlgebraicGeometry.Space.RelativeProjSituation.psiChartSourceIso`).
`AlgebraicGeometry.Space.RelativeProjPoints.chartPullbackIso_trans_hom_mul` proves that the
composite of the factors of this identification is multiplicative, and
`AlgebraicGeometry.Space.RelativeProjPoints.chartPullbackIso_trans_hom_one` that it is unital; this
file states the same with the identification itself.

## Main results

* `AlgebraicGeometry.Space.comp_hom_eq_tensorHom_comp_of_trans`: a family of isomorphisms equal
  to a composite of four factors is multiplicative when the composite is.
* `AlgebraicGeometry.Space.RelativeProjPoints.chartPullbackIso_hom_mul`: **the identification
  `c^*π^*𝒜_n ≅ (π_U^*Z_n)^a` carries the multiplication of `c^*π^*𝒜` to the multiplication
  `π_U^*Z_i ⊗ π_U^*Z_j ≅ π_U^*(Z_i ⊗ Z_j) ⟶ π_U^*Z_{i+j}`**, for a multiplication of the Zariski
  readings `Z_n` that the identification `u^*𝒜_n ≅ (Z_n)^a` carries the multiplication of
  `u^*𝒜` to.
* `AlgebraicGeometry.Space.RelativeProjSituation.psiChartSourceIso_hom_mul`: the same in
  Situation 0849.
* `AlgebraicGeometry.Space.RelativeProjPoints.chartPullbackIso_hom_one`,
  `AlgebraicGeometry.Space.RelativeProjSituation.psiChartSourceIso_hom_one`: **the identification
  carries the unit of `c^*π^*𝒜` to the morphism attached to the pulled-back unit
  `𝒪 ≅ π_U^*𝒪_U ⟶ π_U^*Z_0`**, for a morphism `𝒪_U ⟶ Z_0` that `u^*𝒜_0 ≅ (Z_0)^a` carries the
  pulled-back unit of `𝒜` to.

## Implementation notes

The statements are the types of their proofs: the abstract lemma takes the multiplicativity of
the composite of the factors first, so that its objects and factors are read off that hypothesis,
and the identification is matched with the composite of the same factors by `rfl` at the level of
isomorphisms.  This keeps every comparison between the spellings of the represented algebraic
space of `U ×_X P` at the level of objects and isomorphisms.

## References

* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Space

section Abstract

variable {D : Type*} [Category D] [MonoidalCategory D]

/-- **A family of isomorphisms equal to a composite of four factors is multiplicative when the
composite is**: if `σ_n = a_n ≪≫ b_n ≪≫ c_n⁻¹ ≪≫ e_n` for `n = i, j, k` and the composites of
the factors carry `x` to `μ`, then `x ≫ σ_k = (σ_i ⊗ σ_j) ≫ μ`. -/
theorem comp_hom_eq_tensorHom_comp_of_trans
    {X0i X0j X0k X1i X1j X1k X2i X2j X2k X3i X3j X3k X4i X4j X4k : D}
    {ai : X0i ≅ X1i} {aj : X0j ≅ X1j} {ak : X0k ≅ X1k}
    {bi : X1i ≅ X2i} {bj : X1j ≅ X2j} {bk : X1k ≅ X2k}
    {ci : X3i ≅ X2i} {cj : X3j ≅ X2j} {ck : X3k ≅ X2k}
    {ei : X3i ≅ X4i} {ej : X3j ≅ X4j} {ek : X3k ≅ X4k}
    {x : X0i ⊗ X0j ⟶ X0k} {μ : X4i ⊗ X4j ⟶ X4k}
    (h : x ≫ ak.hom ≫ bk.hom ≫ ck.inv ≫ ek.hom =
      ((ai.hom ≫ bi.hom ≫ ci.inv ≫ ei.hom) ⊗ₘ (aj.hom ≫ bj.hom ≫ cj.inv ≫ ej.hom)) ≫ μ)
    (σi : X0i ≅ X4i) (σj : X0j ≅ X4j) (σk : X0k ≅ X4k)
    (hσi : σi = ai ≪≫ bi ≪≫ ci.symm ≪≫ ei)
    (hσj : σj = aj ≪≫ bj ≪≫ cj.symm ≪≫ ej)
    (hσk : σk = ak ≪≫ bk ≪≫ ck.symm ≪≫ ek) :
    x ≫ σk.hom = (σi.hom ⊗ₘ σj.hom) ≫ μ := by
  subst hσi hσj hσk
  exact h

end Abstract

attribute [local instance] modulesMonoidalCategory

/- The sheafification instances of the small étale site at the universe of the modules. -/
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

namespace RelativeProjPoints

section ChartSourceMul

attribute [local irreducible] CategoryTheory.yoneda

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {π : P ⟶ X.obj} (d : RelativeProjPoints B S hS π) (Px : Presentation B S hS X.obj X.property)
  (hP : IsAlgebraicSpace B S hS P)
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
  (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite)

include d hP in
/-- **The identification `c^*π^*𝒜_n ≅ (π_U^*Z_n)^a` of the source of `ψ` on the atlas is
multiplicative.**  Let `Z_n` be the Zariski reading of `u^*𝒜_n` on the scheme of `U` and
`m : Z_i ⊗ Z_j ⟶ Z_{i+j}` a morphism that the identification `u^*𝒜_n ≅ (Z_n)^a` carries the
multiplication of `u^*𝒜` to (`AlgebraicGeometry.Space.ZariskiReadingIsoMulCompat`).  Then, with
`σ_n = AlgebraicGeometry.Space.RelativeProjPoints.chartPullbackIso` and `T` Stacks 03EL,

`(T_c⁻¹ ≫ c^*(T_π⁻¹ ≫ π^*m_𝒜)) ≫ σ_{i+j} = (σ_i ⊗ σ_j) ≫ T_E⁻¹ ≫ E(T_{π_U}⁻¹ ≫ π_U^*m)`,

the multiplication of `c^*π^*𝒜` followed by `σ_{i+j}` is `σ_i ⊗ σ_j` followed by the morphism
attached to `π_U^*Z_i ⊗ π_U^*Z_j ≅ π_U^*(Z_i ⊗ Z_j) ⟶ π_U^*Z_{i+j}`.  The statement is the type of
its proof; the algebraic space of `U ×_X P` is spelled as the represented algebraic space of the
fibre throughout. -/
theorem chartPullbackIso_hom_mul (i j : ℤ)
    (mZ : quasicoherentTensorObj B S hS Px.U
        (zariskiReadingQcoh Px.U ((etalePointAlgebra A Px.U Px.toSpace).piece i)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace i))
        (zariskiReadingQcoh Px.U ((etalePointAlgebra A Px.U Px.toSpace).piece j)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace j)) ⟶
      (zariskiReadingQcoh Px.U ((etalePointAlgebra A Px.U Px.toSpace).piece (i + j))
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace (i + j))))
    (hζ : ZariskiReadingIsoMulCompat B S hS Px.U (etalePointAlgebra A Px.U Px.toSpace) i j
      (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace i)
      (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace j)
      (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace (i + j)) mZ) :
    type_of% (comp_hom_eq_tensorHom_comp_of_trans
      (chartPullbackIso_trans_hom_mul d Px hP A hA i j mZ hζ)
      (d.chartPullbackIso Px hP A hA i) (d.chartPullbackIso Px hP A hA j)
      (d.chartPullbackIso Px hP A hA (i + j)) rfl rfl rfl) :=
  comp_hom_eq_tensorHom_comp_of_trans (chartPullbackIso_trans_hom_mul d Px hP A hA i j mZ hζ)
    (d.chartPullbackIso Px hP A hA i) (d.chartPullbackIso Px hP A hA j)
    (d.chartPullbackIso Px hP A hA (i + j)) rfl rfl rfl

include d hP in
/-- **The identification `c^*π^*𝒜_n ≅ (π_U^*Z_n)^a` of the source of `ψ` on the atlas is
unital.**  Let `Z_0` be the Zariski reading of `u^*𝒜_0` on the scheme of `U` and
`v : 𝒪_U ⟶ Z_0` a morphism that the identification `u^*𝒜_0 ≅ (Z_0)^a` carries the pulled-back
unit `𝒪 ≅ u^*𝒪 ⟶ u^*𝒜_0` to (`AlgebraicGeometry.Space.ZariskiReadingIsoOneCompat`).  Then, with
`σ_0 = AlgebraicGeometry.Space.RelativeProjPoints.chartPullbackIso` in degree `0` and
`ν_f(w) = (𝒪 ≅ f^*𝒪) ≫ f^*w` the pulled-back unit (Stacks 03LU),

`ν_c(ν_π(1_𝒜)) ≫ σ_0 = (𝒪 ≅ (𝒪_{P_U})^a) ≫ E(ν_{π_U}(v))`:

the unit of `c^*π^*𝒜` followed by `σ_0` is the morphism attached to the pulled-back unit
`𝒪 ≅ π_U^*𝒪_U ⟶ π_U^*Z_0` (`AlgebraicGeometry.Space.representedUnitChartHom`).  The statement is
the type of its proof. -/
theorem chartPullbackIso_hom_one
    (vZ : quasicoherentUnitObj B S hS Px.U ⟶
      zariskiReadingQcoh Px.U ((etalePointAlgebra A Px.U Px.toSpace).piece 0)
        (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace 0))
    (hζ : ZariskiReadingIsoOneCompat B S hS Px.U (etalePointAlgebra A Px.U Px.toSpace)
      (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace 0)
      ((modulePullbackUnitIso B S hS (pointHom Px.toSpace)).inv ≫
        (modulePullback B S hS (pointHom Px.toSpace)).map
          (SheafOfModules.GradedAlgebra.oneHom A)) vZ) :
    type_of% (comp_hom_eq_of_trans (chartPullbackIso_trans_hom_one d Px hP A hA vZ hζ)
      (d.chartPullbackIso Px hP A hA 0) rfl) :=
  comp_hom_eq_of_trans (chartPullbackIso_trans_hom_one d Px hP A hA vZ hζ)
    (d.chartPullbackIso Px hP A hA 0) rfl

end ChartSourceMul

end RelativeProjPoints

namespace RelativeProjSituation

section ChartSourceMul

attribute [local irreducible] CategoryTheory.yoneda

variable (s : RelativeProjSituation.{u, m})
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

/-- **The identification `c^*π^*𝒜_n ≅ (π_U^*Z_n)^a` of the source of `ψ` on the atlas is
multiplicative, in Situation 0849**
(`AlgebraicGeometry.Space.RelativeProjSituation.psiChartSourceIso`;
`AlgebraicGeometry.Space.RelativeProjPoints.chartPullbackIso_hom_mul` for the relative Proj of the
situation): for a multiplication `m` of the Zariski readings `Z_n` of `u^*𝒜_n` that the
identification `u^*𝒜_n ≅ (Z_n)^a` carries the multiplication of `u^*𝒜` to, the multiplication of
`c^*π^*𝒜` followed by `σ_{i+j}` is `σ_i ⊗ σ_j` followed by the morphism attached to
`π_U^*Z_i ⊗ π_U^*Z_j ≅ π_U^*(Z_i ⊗ Z_j) ⟶ π_U^*Z_{i+j}`.  The statement is the type of its
proof. -/
theorem psiChartSourceIso_hom_mul (i j : ℤ)
    (mZ : quasicoherentTensorObj s.site s.base s.containsBase Px.U
        (presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent i)
        (presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent j) ⟶
      presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent (i + j))
    (hζ : ZariskiReadingIsoMulCompat s.site s.base s.containsBase Px.U
      (etalePointAlgebra s.shrink.algebra Px.U Px.toSpace) i j
      (isQuasicoherentOnSite_etalePointAlgebra_piece s.shrink.algebra s.shrink.isQuasicoherent
        Px.toSpace i)
      (isQuasicoherentOnSite_etalePointAlgebra_piece s.shrink.algebra s.shrink.isQuasicoherent
        Px.toSpace j)
      (isQuasicoherentOnSite_etalePointAlgebra_piece s.shrink.algebra s.shrink.isQuasicoherent
        Px.toSpace (i + j)) mZ) :
    type_of% (comp_hom_eq_tensorHom_comp_of_trans
      (RelativeProjPoints.chartPullbackIso_trans_hom_mul s.relativeProjPoints Px
        s.isAlgebraicSpace_relativeProjFunctor s.shrink.algebra s.shrink.isQuasicoherent i j mZ hζ)
      (s.psiChartSourceIso Px i) (s.psiChartSourceIso Px j) (s.psiChartSourceIso Px (i + j))
      rfl rfl rfl) :=
  comp_hom_eq_tensorHom_comp_of_trans
    (RelativeProjPoints.chartPullbackIso_trans_hom_mul s.relativeProjPoints Px
      s.isAlgebraicSpace_relativeProjFunctor s.shrink.algebra s.shrink.isQuasicoherent i j mZ hζ)
    (s.psiChartSourceIso Px i) (s.psiChartSourceIso Px j) (s.psiChartSourceIso Px (i + j))
    rfl rfl rfl

/-- **The identification `c^*π^*𝒜_n ≅ (π_U^*Z_n)^a` of the source of `ψ` on the atlas is
unital, in Situation 0849** (`AlgebraicGeometry.Space.RelativeProjSituation.psiChartSourceIso`;
`AlgebraicGeometry.Space.RelativeProjPoints.chartPullbackIso_hom_one` for the relative Proj of
the situation): for a morphism `v : 𝒪_U ⟶ Z_0` that the identification `u^*𝒜_0 ≅ (Z_0)^a`
carries the pulled-back unit of `𝒜` to, the unit of `c^*π^*𝒜` followed by `σ_0` is the morphism
attached to the pulled-back unit `𝒪 ≅ π_U^*𝒪_U ⟶ π_U^*Z_0`.  The statement is the type of its
proof. -/
theorem psiChartSourceIso_hom_one
    (vZ : quasicoherentUnitObj s.site s.base s.containsBase Px.U ⟶
      presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent 0)
    (hζ : ZariskiReadingIsoOneCompat s.site s.base s.containsBase Px.U
      (etalePointAlgebra s.shrink.algebra Px.U Px.toSpace)
      (isQuasicoherentOnSite_etalePointAlgebra_piece s.shrink.algebra s.shrink.isQuasicoherent
        Px.toSpace 0)
      ((modulePullbackUnitIso s.site s.base s.containsBase (pointHom Px.toSpace)).inv ≫
        (modulePullback s.site s.base s.containsBase (pointHom Px.toSpace)).map
          (SheafOfModules.GradedAlgebra.oneHom s.shrink.algebra)) vZ) :
    type_of% (comp_hom_eq_of_trans
      (RelativeProjPoints.chartPullbackIso_trans_hom_one s.relativeProjPoints Px
        s.isAlgebraicSpace_relativeProjFunctor s.shrink.algebra s.shrink.isQuasicoherent vZ hζ)
      (s.psiChartSourceIso Px 0) rfl) :=
  comp_hom_eq_of_trans
    (RelativeProjPoints.chartPullbackIso_trans_hom_one s.relativeProjPoints Px
      s.isAlgebraicSpace_relativeProjFunctor s.shrink.algebra s.shrink.isQuasicoherent vZ hζ)
    (s.psiChartSourceIso Px 0) rfl

end ChartSourceMul

end RelativeProjSituation

end AlgebraicGeometry.Space

end
