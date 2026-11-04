module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartMap
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartSchemeThetaMul
public import StacksFrontier.AlgebraicGeometry.Spaces.PointFamilyDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PointTwistGradedMulPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiChartSourceMonoidal
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiMultiplicativeAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.TwistGradedAlgebra

/-!
# The graded-algebra laws of `θ` of Stacks 0D2Z on `U(ψ)`: the source and the generic steps

Let `r = r_{ℒ,ψ} : U(ψ) ⟶ P = Proj_Y(𝒜)` be the morphism of Stacks 0D2Z on the open subspace
`U(ψ)` of an algebraic space `X` over the algebraic space `Y` of Situation 0849.  The source
`r^*𝒪_P(d)` of the degree-`d` part of `θ` carries the multiplication
`r^*𝒪_P(i) ⊗ r^*𝒪_P(j) ≅ r^*(𝒪_P(i) ⊗ 𝒪_P(j)) ⟶ r^*𝒪_P(i + j)` (Stacks 03EL followed by the
inverse image of the multiplication of the graded algebra `⨁_n 𝒪_P(n)` of Stacks 084D) and the
unit `𝒪 ≅ r^*𝒪 ⟶ r^*𝒪_P(0)` (Stacks 03LU); this file defines them.  The multiplicativity of `θ`
is checked on the chart maps `χ_w = σ_w ≫ m_w ≫ τ_w`
(`AlgebraicGeometry.Space.mul_comp_pointFamilyDescendedHom`), and this file provides the steps
for that at free variables: the comparisons `a^*b^* ≅ a'^*b'^*` of Stacks 03LU, followed by
multiplicative identifications along `a'` (such as the base change identification of Stacks 084D,
`…RelativeProjSituation.fibreToSpaceTwistModuleIso`, and Stacks 03DX (2)), are multiplicative and
unital; and three multiplicative factors give the pointwise hypothesis.

## Main definitions

* `…InvertibleTwistingRestriction.thetaSourceMul`: `r^*𝒪(i) ⊗ r^*𝒪(j) ⟶ r^*𝒪(i + j)`.
* `…InvertibleTwistingRestriction.thetaSourceUnit`: `𝒪_{U(ψ)} ⟶ r^*𝒪(0)`.
* `AlgebraicGeometry.Space.laurentRestrictMul`, `AlgebraicGeometry.Space.laurentRestrictUnit`: the
  multiplication and unit of the restriction of `⨁_n ℒ^{⊗ n}` along a morphism `j : U ⟶ X`.
* `…InvertibleTwistingRestriction.thetaTargetMul`,
  `…InvertibleTwistingRestriction.thetaTargetUnit`: the multiplication and unit of the target
  `⨁_d ℒ^{⊗ d}|_{U(ψ)}` of `θ`.

## Main results

* `AlgebraicGeometry.Space.modulePullbackCompTransportIso_hom_mul`,
  `AlgebraicGeometry.Space.modulePullbackCompTransportIso_hom_one`: the comparisons
  `a^*b^* ≅ a'^*b'^*` for `a ≫ b = a' ≫ b'` (Stacks 03LU) carry pulled-back multiplications and
  units to pulled-back multiplications and units.
* `AlgebraicGeometry.Space.compTransportTrans_hom_mul`,
  `AlgebraicGeometry.Space.compTransportTrans_hom_one`: the same for the comparison followed by
  multiplicative identifications along `a'`.
* `AlgebraicGeometry.Space.mul_of_factor_squares`, `AlgebraicGeometry.Space.one_of_factor_squares`:
  the pointwise hypotheses of `AlgebraicGeometry.Space.mul_comp_pointFamilyDescendedHom` and
  `AlgebraicGeometry.Space.comp_pointFamilyDescendedHom_eq` for a chart map `σ ≫ m ≫ τ` from
  squares of its three factors.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

section Abstract

variable {D : Type*} [Category D]

/-- **A composite of three multiplicative families of isomorphisms is multiplicative**: if
`σ_n = α_n ≪≫ β_n ≪≫ γ_n` and `α`, `β`, `γ` carry `μ_0` to `μ_1`, `μ_1` to `μ_2` and `μ_2` to
`μ_3`, then `σ` carries `μ_0` to `μ_3`. -/
theorem mulSquare_of_trans_three [MonoidalCategory D]
    {X0i X0j X0k X1i X1j X1k X2i X2j X2k X3i X3j X3k : D}
    {μ0 : X0i ⊗ X0j ⟶ X0k} {μ1 : X1i ⊗ X1j ⟶ X1k} {μ2 : X2i ⊗ X2j ⟶ X2k}
    {μ3 : X3i ⊗ X3j ⟶ X3k}
    {αi : X0i ≅ X1i} {αj : X0j ≅ X1j} {αk : X0k ≅ X1k}
    {βi : X1i ≅ X2i} {βj : X1j ≅ X2j} {βk : X1k ≅ X2k}
    {γi : X2i ≅ X3i} {γj : X2j ≅ X3j} {γk : X2k ≅ X3k}
    {σi : X0i ≅ X3i} {σj : X0j ≅ X3j} {σk : X0k ≅ X3k}
    (hσi : σi = αi ≪≫ βi ≪≫ γi) (hσj : σj = αj ≪≫ βj ≪≫ γj) (hσk : σk = αk ≪≫ βk ≪≫ γk)
    (hα : μ0 ≫ αk.hom = (αi.hom ⊗ₘ αj.hom) ≫ μ1) (hβ : μ1 ≫ βk.hom = (βi.hom ⊗ₘ βj.hom) ≫ μ2)
    (hγ : μ2 ≫ γk.hom = (γi.hom ⊗ₘ γj.hom) ≫ μ3) :
    μ0 ≫ σk.hom = (σi.hom ⊗ₘ σj.hom) ≫ μ3 := by
  subst hσi hσj hσk
  simp only [Iso.trans_hom]
  exact mulSquare_comp _ _ _ _ _ _ _ _ _ hα (mulSquare_comp _ _ _ _ _ _ _ _ _ hβ hγ)

/-- **A composite of three isomorphisms carrying `u_0` to `u_1`, `u_1` to `u_2` and `u_2` to `u_3`
carries `u_0` to `u_3`** (the unit companion of
`AlgebraicGeometry.Space.mulSquare_of_trans_three`). -/
theorem unitSquare_of_trans_three {O X0 X1 X2 X3 : D} {u0 : O ⟶ X0} {u1 : O ⟶ X1}
    {u2 : O ⟶ X2} {u3 : O ⟶ X3} {α : X0 ≅ X1} {β : X1 ≅ X2} {γ : X2 ≅ X3} {σ : X0 ≅ X3}
    (hσ : σ = α ≪≫ β ≪≫ γ) (hα : u0 ≫ α.hom = u1) (hβ : u1 ≫ β.hom = u2)
    (hγ : u2 ≫ γ.hom = u3) :
    u0 ≫ σ.hom = u3 := by
  subst hσ
  simp only [Iso.trans_hom]
  exact unitSquare_comp _ _ _ _ _ hα (unitSquare_comp _ _ _ _ _ hβ hγ)

/-- **The shape of the pointwise multiplicativity of a chart map**: if `χ_n = σ_n ≫ m_n ≫ τ_n`
and `σ` carries `T_G⁻¹ ≫ x_G` to `μ_M`, `m` carries `μ_M` to `μ_N` and `τ` carries `μ_N` to
`T_H⁻¹ ≫ x_H`, then `x_G ≫ χ_k = T_G ≫ (χ_i ⊗ χ_j) ≫ T_H⁻¹ ≫ x_H`. -/
theorem mul_of_factor_squares [MonoidalCategory D]
    {GG Gi Gj Gk Mi Mj Mk Ni Nj Nk Hi Hj Hk HH : D} (TG : GG ≅ Gi ⊗ Gj) (TH : HH ≅ Hi ⊗ Hj)
    (xG : GG ⟶ Gk) (xH : HH ⟶ Hk) {σi : Gi ⟶ Mi} {σj : Gj ⟶ Mj} {σk : Gk ⟶ Mk}
    {mi : Mi ⟶ Ni} {mj : Mj ⟶ Nj} {mk : Mk ⟶ Nk} {τi : Ni ⟶ Hi} {τj : Nj ⟶ Hj} {τk : Nk ⟶ Hk}
    {μM : Mi ⊗ Mj ⟶ Mk} {μN : Ni ⊗ Nj ⟶ Nk}
    (hσ : (TG.inv ≫ xG) ≫ σk = (σi ⊗ₘ σj) ≫ μM) (hm : μM ≫ mk = (mi ⊗ₘ mj) ≫ μN)
    (hτ : μN ≫ τk = (τi ⊗ₘ τj) ≫ TH.inv ≫ xH) :
    xG ≫ σk ≫ mk ≫ τk = TG.hom ≫ ((σi ≫ mi ≫ τi) ⊗ₘ (σj ≫ mj ≫ τj)) ≫ TH.inv ≫ xH :=
  (Iso.inv_comp_eq TG).1 ((Category.assoc _ _ _).symm.trans
    (mulSquare_comp _ _ _ _ _ _ _ _ _ hσ (mulSquare_comp _ _ _ _ _ _ _ _ _ hm hτ)))

/-- The unit companion of `AlgebraicGeometry.Space.mul_of_factor_squares`: if `σ` carries
`U_G⁻¹ ≫ x_G` to `ν_M`, `m` carries `ν_M` to `ν_N` and `τ` carries `ν_N` to `U_H⁻¹ ≫ x_H`, then
`x_G ≫ σ ≫ m ≫ τ = x_H` after `U_G⁻¹`. -/
theorem one_of_factor_squares {O O' G M N H : D} (UG : O' ≅ O) (UH : O' ≅ O) (xG : O ⟶ G)
    (xH : O ⟶ H) {σ : G ⟶ M} {m : M ⟶ N} {τ : N ⟶ H} {νM : O' ⟶ M} {νN : O' ⟶ N}
    (hσ : (UG.hom ≫ xG) ≫ σ = νM) (hm : νM ≫ m = νN) (hτ : νN ≫ τ = UH.hom ≫ xH)
    (hU : UG = UH) :
    xG ≫ σ ≫ m ≫ τ = xH := by
  subst hU
  exact (cancel_epi UG.hom).1 ((Category.assoc _ _ _).symm.trans
    (unitSquare_comp _ _ _ _ _ hσ (unitSquare_comp _ _ _ _ _ hm hτ)))

end Abstract

section CompTransport

open RelativeProjSituation.InvertibleTwistingRestriction (modulePullbackCompTransportIso)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A Y Z P : AlgebraicSpaces B S hS} (a : A ⟶ Y) (b : Y ⟶ P) (a' : A ⟶ Z) (b' : Z ⟶ P)
  (h : a ≫ b = a' ≫ b')

/-- The comparison `a^*b^* ≅ a'^*b'^*` as the composite of its three factors, at the level of
isomorphisms. -/
theorem modulePullbackCompTransportIso_eq_trans (M : Modules.{u, u} B S hS P.1 P.2) :
    modulePullbackCompTransportIso a b a' b' h M =
      (modulePullbackCompIso B S hS a b).app M ≪≫
        eqToIso (congrArg (fun k => (modulePullback B S hS k).obj M) h) ≪≫
        ((modulePullbackCompIso B S hS a' b').app M).symm :=
  rfl

/-- **The comparison `a^*b^* ≅ a'^*b'^*` for `a ≫ b = a' ≫ b'` carries the iterated pulled-back
multiplication to the iterated pulled-back multiplication**: for `μ : T_i ⊗ T_j ⟶ T_k` of
`𝒪_P`-modules, `a^*b^*T_i ⊗ a^*b^*T_j ≅ a^*(b^*T_i ⊗ b^*T_j) ≅ a^*b^*(T_i ⊗ T_j) ⟶ a^*b^*T_k`
followed by the comparison at `T_k` is the tensor product of the comparisons at `T_i` and `T_j`
followed by the same morphism for `a'` and `b'` (Stacks 03EL and 03LU). -/
theorem modulePullbackCompTransportIso_hom_mul (Ti Tj Tk : Modules.{u, u} B S hS P.1 P.2)
    (μ : Ti ⊗ Tj ⟶ Tk) :
    ((modulePullbackTensorIso B S hS a ((modulePullback B S hS b).obj Ti)
        ((modulePullback B S hS b).obj Tj)).inv ≫
      (modulePullback B S hS a).map ((modulePullbackTensorIso B S hS b Ti Tj).inv ≫
        (modulePullback B S hS b).map μ)) ≫
      (modulePullbackCompTransportIso a b a' b' h Tk).hom =
    ((modulePullbackCompTransportIso a b a' b' h Ti).hom ⊗ₘ
        (modulePullbackCompTransportIso a b a' b' h Tj).hom) ≫
      (modulePullbackTensorIso B S hS a' ((modulePullback B S hS b').obj Ti)
        ((modulePullback B S hS b').obj Tj)).inv ≫
      (modulePullback B S hS a').map ((modulePullbackTensorIso B S hS b' Ti Tj).inv ≫
        (modulePullback B S hS b').map μ) := by
  rw [modulePullbackCompTransportIso_eq_trans a b a' b' h Ti,
    modulePullbackCompTransportIso_eq_trans a b a' b' h Tj,
    modulePullbackCompTransportIso_eq_trans a b a' b' h Tk]
  exact mulSquare_of_trans_three rfl rfl rfl
    (modulePullbackTensorIso_inv_comp_map_comp_modulePullbackCompIso_hom_app B S hS a b
      Ti Tj Tk μ)
    (modulePullbackTensorIso_inv_comp_map_comp_eqToIso B S hS h Ti Tj Tk μ)
    (mulSquare_inv _ _ ((modulePullbackCompIso B S hS a' b').app Ti)
      ((modulePullbackCompIso B S hS a' b').app Tj)
      ((modulePullbackCompIso B S hS a' b').app Tk)
      (modulePullbackTensorIso_inv_comp_map_comp_modulePullbackCompIso_hom_app B S hS a' b'
        Ti Tj Tk μ))

/-- **The comparison `a^*b^* ≅ a'^*b'^*` for `a ≫ b = a' ≫ b'` carries the iterated pulled-back
unit to the iterated pulled-back unit**: for `ν : 𝒪_P ⟶ T`, `𝒪_A ≅ a^*𝒪_Y ≅ a^*b^*𝒪_P ⟶ a^*b^*T`
followed by the comparison at `T` is the same morphism for `a'` and `b'` (Stacks 03LU). -/
theorem modulePullbackCompTransportIso_hom_one (T : Modules.{u, u} B S hS P.1 P.2)
    (ν : SheafOfModules.unit (structureRingSheaf B S hS P) ⟶ T) :
    ((modulePullbackUnitIso B S hS a).inv ≫
      (modulePullback B S hS a).map ((modulePullbackUnitIso B S hS b).inv ≫
        (modulePullback B S hS b).map ν)) ≫
      (modulePullbackCompTransportIso a b a' b' h T).hom =
    (modulePullbackUnitIso B S hS a').inv ≫
      (modulePullback B S hS a').map ((modulePullbackUnitIso B S hS b').inv ≫
        (modulePullback B S hS b').map ν) := by
  rw [modulePullbackCompTransportIso_eq_trans a b a' b' h T]
  exact unitSquare_of_trans_three rfl
    (modulePullbackUnitIso_inv_comp_map_comp_modulePullbackCompIso_hom_app B S hS a b T ν)
    (modulePullbackUnitIso_inv_comp_map_comp_eqToIso B S hS h T ν)
    (unitSquare_inv _ _ ((modulePullbackCompIso B S hS a' b').app T)
      (modulePullbackUnitIso_inv_comp_map_comp_modulePullbackCompIso_hom_app B S hS a' b' T ν))

variable {Ti Tj Tk : Modules.{u, u} B S hS P.1 P.2} {Fi Fj Fk : Modules.{u, u} B S hS Z.1 Z.2}
  {Ei Ej Ek : Modules.{u, u} B S hS A.1 A.2}
  {ιi : (modulePullback B S hS b').obj Ti ≅ Fi} {ιj : (modulePullback B S hS b').obj Tj ≅ Fj}
  {ιk : (modulePullback B S hS b').obj Tk ≅ Fk}
  {κi : (modulePullback B S hS a').obj Fi ≅ Ei} {κj : (modulePullback B S hS a').obj Fj ≅ Ej}
  {κk : (modulePullback B S hS a').obj Fk ≅ Ek}

/-- **The comparison `a^*b^* ≅ a'^*b'^*`, followed by the inverse image along `a'` of
identifications `ι_n : b'^*T_n ≅ F_n` and by identifications `κ_n : a'^*F_n ≅ E_n`, is
multiplicative** as soon as `ι` carries `b'^*μ` (read through Stacks 03EL) to `μ_F` and `κ` carries
`a'^*μ_F` to `μ_E`. -/
theorem compTransportTrans_hom_mul {σi : (modulePullback B S hS a).obj
      ((modulePullback B S hS b).obj Ti) ≅ Ei}
    {σj : (modulePullback B S hS a).obj ((modulePullback B S hS b).obj Tj) ≅ Ej}
    {σk : (modulePullback B S hS a).obj ((modulePullback B S hS b).obj Tk) ≅ Ek}
    (hσi : σi = modulePullbackCompTransportIso a b a' b' h Ti ≪≫
      (modulePullback B S hS a').mapIso ιi ≪≫ κi)
    (hσj : σj = modulePullbackCompTransportIso a b a' b' h Tj ≪≫
      (modulePullback B S hS a').mapIso ιj ≪≫ κj)
    (hσk : σk = modulePullbackCompTransportIso a b a' b' h Tk ≪≫
      (modulePullback B S hS a').mapIso ιk ≪≫ κk)
    {μ : Ti ⊗ Tj ⟶ Tk} {μF : Fi ⊗ Fj ⟶ Fk} {μE : Ei ⊗ Ej ⟶ Ek}
    (hι : (modulePullbackTensorIso B S hS b' Ti Tj).inv ≫ (modulePullback B S hS b').map μ ≫
      ιk.hom = (ιi.hom ⊗ₘ ιj.hom) ≫ μF)
    (hκ : (modulePullbackTensorIso B S hS a' Fi Fj).inv ≫ (modulePullback B S hS a').map μF ≫
      κk.hom = (κi.hom ⊗ₘ κj.hom) ≫ μE) :
    ((modulePullbackTensorIso B S hS a ((modulePullback B S hS b).obj Ti)
        ((modulePullback B S hS b).obj Tj)).inv ≫
      (modulePullback B S hS a).map ((modulePullbackTensorIso B S hS b Ti Tj).inv ≫
        (modulePullback B S hS b).map μ)) ≫ σk.hom = (σi.hom ⊗ₘ σj.hom) ≫ μE :=
  mulSquare_of_trans_three hσi hσj hσk
    (modulePullbackCompTransportIso_hom_mul a b a' b' h Ti Tj Tk μ)
    (modulePullbackTensorIso_inv_comp_map_comp_map_of_comp_eq B S hS a' _ μF ιi.hom ιj.hom
      ιk.hom ((Category.assoc _ _ _).trans hι))
    ((Category.assoc _ _ _).trans hκ)

/-- The unit companion of `AlgebraicGeometry.Space.compTransportTrans_hom_mul`. -/
theorem compTransportTrans_hom_one
    {σk : (modulePullback B S hS a).obj ((modulePullback B S hS b).obj Tk) ≅ Ek}
    (hσk : σk = modulePullbackCompTransportIso a b a' b' h Tk ≪≫
      (modulePullback B S hS a').mapIso ιk ≪≫ κk)
    {ν : SheafOfModules.unit (structureRingSheaf B S hS P) ⟶ Tk}
    {νF : SheafOfModules.unit (structureRingSheaf B S hS Z) ⟶ Fk}
    {νE : SheafOfModules.unit (structureRingSheaf B S hS A) ⟶ Ek}
    (hι : (modulePullbackUnitIso B S hS b').inv ≫ (modulePullback B S hS b').map ν ≫ ιk.hom =
      νF)
    (hκ : (modulePullbackUnitIso B S hS a').inv ≫ (modulePullback B S hS a').map νF ≫ κk.hom =
      νE) :
    ((modulePullbackUnitIso B S hS a).inv ≫
      (modulePullback B S hS a).map ((modulePullbackUnitIso B S hS b).inv ≫
        (modulePullback B S hS b).map ν)) ≫ σk.hom = νE :=
  unitSquare_of_trans_three hσk
    (modulePullbackCompTransportIso_hom_one a b a' b' h Tk ν)
    (modulePullbackUnitIso_inv_comp_map_comp_map_of_comp_eq B S hS a' _ νF ιk.hom
      ((Category.assoc _ _ _).trans hι))
    ((Category.assoc _ _ _).trans hκ)

end CompTransport

section Represented

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {V U : BigFppfOver B S hS}
  (g : V ⟶ U)

/-- `AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso_hom_mul`, reassociated. -/
theorem modulePullbackRepresentedQuasicoherentIso_hom_mul_assoc
    {M N K : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (m : quasicoherentTensorObj B S hS U M N ⟶ K) :
    (modulePullbackTensorIso B S hS (representedSpaceMap B S hS g)
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj N).obj).inv ≫
      (modulePullback B S hS (representedSpaceMap B S hS g)).map
        (representedTensorChartMul B S hS m) ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS g K).hom =
    ((modulePullbackRepresentedQuasicoherentIso B S hS g M).hom ⊗ₘ
        (modulePullbackRepresentedQuasicoherentIso B S hS g N).hom) ≫
      representedTensorChartMul B S hS
        ((quasicoherentPullbackTensorIso B S hS g M N).inv ≫ quasicoherentPullbackMap B S hS g m) :=
  (Category.assoc _ _ _).symm.trans (modulePullbackRepresentedQuasicoherentIso_hom_mul B S hS g m)

/-- `AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso_hom_one`, reassociated. -/
theorem modulePullbackRepresentedQuasicoherentIso_hom_one_assoc
    {K : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (u : quasicoherentUnitObj B S hS U ⟶ K) :
    (modulePullbackUnitIso B S hS (representedSpaceMap B S hS g)).inv ≫
      (modulePullback B S hS (representedSpaceMap B S hS g)).map
        (representedUnitChartHom B S hS u) ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS g K).hom =
    representedUnitChartHom B S hS
      ((quasicoherentPullbackUnitIso B S hS g).inv ≫ quasicoherentPullbackMap B S hS g u) :=
  (Category.assoc _ _ _).symm.trans (modulePullbackRepresentedQuasicoherentIso_hom_one B S hS g u)

end Represented

section Target

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (laurent unitalHom_mulSheaf_comp
  oneHom_comp_app_zero)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X U : AlgebraicSpaces B S hS}
  (L : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O))
  [hL : Stacks.SheafOfModules.IsInvertible (smallEtaleRingedTopos B S hS X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L]

/-- **The unit `𝒪_T ⟶ (x^*ℒ)^{⊗ 0}`** of the Laurent algebra of the restriction `x^*ℒ` of `ℒ` to
a scheme point `x : T ⟶ X`, as a morphism of quasi-coherent modules on `T`. -/
def pointLaurentPieceUnit (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :
    quasicoherentUnitObj B S hS T ⟶ pointLaurentPieceQcoh L T x 0 :=
  ObjectProperty.homMk (SheafOfModules.GradedAlgebra.oneHom (laurent (pointLine B S hS L T x)))

/-- **The identification of the Zariski reading of `x^*(ℒ^{⊗ n})` with `(x^*ℒ)^{⊗ n}` is
multiplicative**: it carries the multiplication of the Zariski reading of `x^*(⨁_n ℒ^{⊗ n})` to
the multiplication of the Laurent algebra of `x^*ℒ` (`AlgebraicGeometry.Space.pointLaurentHom` is
a homomorphism of graded algebras). -/
theorem pointLaurentReadingIso_hom_mul (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1)
    (i j : ℤ) :
    (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf
        (zariskiReading T (etalePointAlgebra (Stacks.SheafOfModules.TensorPower.laurentAlgebra
          (smallEtaleRingedTopos B S hS X).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L)
            T x)) i j) :
        quasicoherentTensorObj B S hS T (pointLaurentReadingQcoh L T x i)
          (pointLaurentReadingQcoh L T x j) ⟶ pointLaurentReadingQcoh L T x (i + j)) ≫
      (pointLaurentReadingIso L T x (i + j)).hom =
    quasicoherentTensorHom B S hS T (pointLaurentReadingIso L T x i).hom
        (pointLaurentReadingIso L T x j).hom ≫ pointLaurentPieceMul L T x i j :=
  ObjectProperty.hom_ext _
    (mulSheaf_comp_tensorSheafMap_of_hom (W := (BigFppfOver.toScheme B S hS).obj T)
      (pointLaurentHom B S hS L T x).toHom i j)

/-- **The identification of the Zariski reading of `x^*(ℒ^{⊗ 0})` with `(x^*ℒ)^{⊗ 0}` is
unital** (the unit companion of `AlgebraicGeometry.Space.pointLaurentReadingIso_hom_mul`). -/
theorem pointLaurentReadingIso_hom_one (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :
    (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.oneHom
        (zariskiReading T (etalePointAlgebra (Stacks.SheafOfModules.TensorPower.laurentAlgebra
          (smallEtaleRingedTopos B S hS X).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L)
            T x))) :
        quasicoherentUnitObj B S hS T ⟶ pointLaurentReadingQcoh L T x 0) ≫
      (pointLaurentReadingIso L T x 0).hom = pointLaurentPieceUnit L T x :=
  ObjectProperty.hom_ext _ (oneHom_comp_app_zero (pointLaurentHom B S hS L T x))

/-- **The identification `N ≅ (N_Zar)^a`, followed by the module attached to an identification
of the Zariski readings, is multiplicative**: for a sheaf of graded algebras `G` on the represented
algebraic space of `T` with quasi-coherent pieces and isomorphisms `φ_n : (G_n)_Zar ≅ Q_n` of
quasi-coherent modules on `T` carrying the multiplication of the Zariski reading of `G` to
`m_Q`, the composites `G_n ≅ ((G_n)_Zar)^a ≅ Q_n^a` carry the multiplication of `G` to the
morphism attached to `m_Q` (Stacks 03DX (2)). -/
theorem zariskiReadingQuasicoherentIso_trans_hom_mul {T : BigFppfOver B S hS}
    (G : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS (yonedaSpace B S hS T)))
    (hG : ∀ n, (G.piece n).IsQuasicoherentOnSite)
    {Q : ℤ → (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf).FullSubcategory}
    (φ : ∀ n, zariskiReadingQcoh T (G.piece n) (hG n) ≅ Q n)
    (mQ : ∀ i j, quasicoherentTensorObj B S hS T (Q i) (Q j) ⟶ Q (i + j))
    (hφ : ∀ i j, (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf
        (zariskiReading T G) i j) :
        quasicoherentTensorObj B S hS T (zariskiReadingQcoh T (G.piece i) (hG i))
          (zariskiReadingQcoh T (G.piece j) (hG j)) ⟶
            zariskiReadingQcoh T (G.piece (i + j)) (hG (i + j))) ≫ (φ (i + j)).hom =
      quasicoherentTensorHom B S hS T (φ i).hom (φ j).hom ≫ mQ i j) (i j : ℤ) :
    ((modulesTensorObjIso B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) (G.piece i)
        (G.piece j)).hom ≫ SheafOfModules.GradedAlgebra.mulSheaf G i j) ≫
      (zariskiReadingQuasicoherentIso T (G.piece (i + j)) (hG (i + j)) ≪≫
        (ObjectProperty.ι _).mapIso
          ((representedQuasicoherentSchemeEquivalence B S hS T).functor.mapIso (φ (i + j)))).hom =
    ((zariskiReadingQuasicoherentIso T (G.piece i) (hG i) ≪≫ (ObjectProperty.ι _).mapIso
          ((representedQuasicoherentSchemeEquivalence B S hS T).functor.mapIso (φ i))).hom ⊗ₘ
        (zariskiReadingQuasicoherentIso T (G.piece j) (hG j) ≪≫ (ObjectProperty.ι _).mapIso
          ((representedQuasicoherentSchemeEquivalence B S hS T).functor.mapIso (φ j))).hom) ≫
      representedTensorChartMul B S hS (mQ i j) :=
  mulSquare_comp _ _ _ _ _ _ _ _ _
    ((Category.assoc _ _ _).trans (zariskiReadingQuasicoherentIso_mulSheaf T G hG i j))
    (representedTensorChartMul_comp_map_hom_of_comp_eq _ _ _ _ _ (hφ i j))

/-- **The identification `x^*(ℒ^{⊗ n}) ≅ ((x^*ℒ)^{⊗ n})^a` is multiplicative**: at a scheme
point `x : T ⟶ X`, `AlgebraicGeometry.Space.pointTargetIso` carries the inverse image along `x` of
the multiplication of `⨁_n ℒ^{⊗ n}`, read through Stacks 03EL, to the morphism attached by
Stacks 03DX (2) to the multiplication of the Laurent algebra of `x^*ℒ`. -/
theorem pointTargetIso_hom_mul (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) (i j : ℤ) :
    ((modulePullbackTensorIso B S hS (pointHom x)
        (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) i)
        (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) j)).inv ≫
      (modulePullback B S hS (pointHom x)).map
        ((modulesTensorObjIso B S hS X.1 X.2
          (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
            (Stacks.SheafOfModules.TensorPower.laurentAlgebra
              (smallEtaleRingedTopos B S hS X).O.obj
              (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
                L) i)
          (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
            (Stacks.SheafOfModules.TensorPower.laurentAlgebra
              (smallEtaleRingedTopos B S hS X).O.obj
              (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
                L) j)).hom ≫
          SheafOfModules.GradedAlgebra.mulSheaf
              (Stacks.SheafOfModules.TensorPower.laurentAlgebra
                (smallEtaleRingedTopos B S hS X).O.obj
              (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
                L : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) i j)) ≫
      (pointTargetIso L T x (i + j)).hom =
    ((pointTargetIso L T x i).hom ⊗ₘ (pointTargetIso L T x j).hom) ≫
      representedTensorChartMul B S hS (pointLaurentPieceMul L T x i j) :=
  (congrArg (fun t => t ≫ (pointTargetIso L T x (i + j)).hom)
    (modulePullbackTensorIso_inv_comp_map_mulSheaf B S hS _ (pointHom x) i j)).trans
    (zariskiReadingQuasicoherentIso_trans_hom_mul _
      (isQuasicoherentOnSite_etalePointAlgebra_piece _
        (isQuasicoherentOnSite_laurentAlgebra_piece_of_isInvertible L) x)
      (pointLaurentReadingIso L T x) (pointLaurentPieceMul L T x)
      (pointLaurentReadingIso_hom_mul L T x) i j)

/-- **The identification `x^*(ℒ^{⊗ 0}) ≅ ((x^*ℒ)^{⊗ 0})^a` is unital**: at a scheme point
`x : T ⟶ X`, `AlgebraicGeometry.Space.pointTargetIso` carries the inverse image along `x` of the
unit of `⨁_n ℒ^{⊗ n}`, read through Stacks 03LU, to the morphism attached by Stacks 03DX (2) to
the unit of the Laurent algebra of `x^*ℒ`. -/
theorem pointTargetIso_hom_one (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :
    ((modulePullbackUnitIso B S hS (pointHom x)).inv ≫
      (modulePullback B S hS (pointHom x)).map
        (SheafOfModules.GradedAlgebra.oneHom
              (Stacks.SheafOfModules.TensorPower.laurentAlgebra
                (smallEtaleRingedTopos B S hS X).O.obj
              (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
                L : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)))) ≫
      (pointTargetIso L T x 0).hom =
    representedUnitChartHom B S hS (pointLaurentPieceUnit L T x) :=
  unitSquare_comp _ _ _ _ _
    (zariskiReadingIsoOneCompat_modulePullbackUnitIso_inv_comp_map_oneHom _
      (isQuasicoherentOnSite_laurentAlgebra_piece_of_isInvertible L) T x)
    (representedUnitChartHom_comp_map_hom_of_comp_eq _ _ _ (pointLaurentReadingIso_hom_one L T x))

section Comparison

variable {Y : AlgebraicSpaces B S hS} (j : U ⟶ X) (w : Y ⟶ U) (x : Y ⟶ X) (h : x = w ≫ j)

/-- **The inverse of a multiplicative identification `x^*T_n ≅ N_n`, followed by the comparison
`x^*T_n = (j ∘ w)^*T_n ≅ w^*j^*T_n` of Stacks 03LU, is multiplicative**: if `e` carries
`x^*μ` (read through Stacks 03EL) to `μ_N`, then the composites `τ_n` carry `μ_N` to the
iterated inverse image of `μ` along `j` and `w`. -/
theorem symmTransComp_hom_mul {Ti Tk Tik : Modules.{u, u} B S hS X.1 X.2}
    {Ni Nk Nik : Modules.{u, u} B S hS Y.1 Y.2} {ei : (modulePullback B S hS x).obj Ti ≅ Ni}
    {ek : (modulePullback B S hS x).obj Tk ≅ Nk} {eik : (modulePullback B S hS x).obj Tik ≅ Nik}
    {τi : Ni ≅ (modulePullback B S hS w).obj ((modulePullback B S hS j).obj Ti)}
    {τk : Nk ≅ (modulePullback B S hS w).obj ((modulePullback B S hS j).obj Tk)}
    {τik : Nik ≅ (modulePullback B S hS w).obj ((modulePullback B S hS j).obj Tik)}
    (hτi : τi = ei.symm ≪≫ eqToIso (congrArg (fun g => (modulePullback B S hS g).obj Ti) h) ≪≫
      ((modulePullbackCompIso B S hS w j).app Ti).symm)
    (hτk : τk = ek.symm ≪≫ eqToIso (congrArg (fun g => (modulePullback B S hS g).obj Tk) h) ≪≫
      ((modulePullbackCompIso B S hS w j).app Tk).symm)
    (hτik : τik = eik.symm ≪≫
      eqToIso (congrArg (fun g => (modulePullback B S hS g).obj Tik) h) ≪≫
      ((modulePullbackCompIso B S hS w j).app Tik).symm)
    {μ : Ti ⊗ Tk ⟶ Tik} {μN : Ni ⊗ Nk ⟶ Nik}
    (he : ((modulePullbackTensorIso B S hS x Ti Tk).inv ≫ (modulePullback B S hS x).map μ) ≫
      eik.hom = (ei.hom ⊗ₘ ek.hom) ≫ μN) :
    μN ≫ τik.hom = (τi.hom ⊗ₘ τk.hom) ≫
      (modulePullbackTensorIso B S hS w ((modulePullback B S hS j).obj Ti)
        ((modulePullback B S hS j).obj Tk)).inv ≫
      (modulePullback B S hS w).map ((modulePullbackTensorIso B S hS j Ti Tk).inv ≫
        (modulePullback B S hS j).map μ) :=
  mulSquare_of_trans_three hτi hτk hτik (mulSquare_inv _ _ ei ek eik he)
    (modulePullbackTensorIso_inv_comp_map_comp_eqToIso B S hS h Ti Tk Tik μ)
    (mulSquare_inv _ _ ((modulePullbackCompIso B S hS w j).app Ti)
      ((modulePullbackCompIso B S hS w j).app Tk) ((modulePullbackCompIso B S hS w j).app Tik)
      (modulePullbackTensorIso_inv_comp_map_comp_modulePullbackCompIso_hom_app B S hS w j
        Ti Tk Tik μ))

/-- The unit companion of `AlgebraicGeometry.Space.symmTransComp_hom_mul`. -/
theorem symmTransComp_hom_one {T : Modules.{u, u} B S hS X.1 X.2}
    {N : Modules.{u, u} B S hS Y.1 Y.2} {e : (modulePullback B S hS x).obj T ≅ N}
    {τ : N ≅ (modulePullback B S hS w).obj ((modulePullback B S hS j).obj T)}
    (hτ : τ = e.symm ≪≫ eqToIso (congrArg (fun g => (modulePullback B S hS g).obj T) h) ≪≫
      ((modulePullbackCompIso B S hS w j).app T).symm)
    {ν : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶ T}
    {νN : SheafOfModules.unit (structureRingSheaf B S hS Y) ⟶ N}
    (he : ((modulePullbackUnitIso B S hS x).inv ≫ (modulePullback B S hS x).map ν) ≫ e.hom =
      νN) :
    νN ≫ τ.hom = (modulePullbackUnitIso B S hS w).inv ≫
      (modulePullback B S hS w).map ((modulePullbackUnitIso B S hS j).inv ≫
        (modulePullback B S hS j).map ν) := by
  have h2 := modulePullbackUnitIso_inv_comp_map_comp_eqToIso B S hS h T ν
  have h3 := unitSquare_inv _ _ ((modulePullbackCompIso B S hS w j).app T)
    (modulePullbackUnitIso_inv_comp_map_comp_modulePullbackCompIso_hom_app B S hS w j T ν)
  have h4 := unitSquare_comp _ _ _ _ _ h2 h3
  have h5 := unitSquare_inv _ _ e he
  subst hτ
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun t => t ≫ _) h5).trans h4)

end Comparison

variable (j : U ⟶ X) {W : BigFppfOver B S hS} (w : yoneda.obj W ⟶ U.1) (x : yoneda.obj W ⟶ X.1)
  (h : pointHom x = pointHom w ≫ j)

/-- **The target factor of a chart map is multiplicative** (Stacks 0D2Z): for a morphism
`j : U ⟶ X` of algebraic spaces, a scheme point `w : W ⟶ U` and `x = j ∘ w`, the composite
`((x^*ℒ)^{⊗ n})^a ≅ x^*(ℒ^{⊗ n}) = (j ∘ w)^*(ℒ^{⊗ n}) ≅ w^*(j^*(ℒ^{⊗ n}))` of the inverse of
`AlgebraicGeometry.Space.pointTargetIso` and the comparison of Stacks 03LU carries the morphism
attached to the multiplication of the Laurent algebra of `x^*ℒ` to the inverse image along `w` of
the multiplication `j^*ℒ^{⊗ i} ⊗ j^*ℒ^{⊗ k} ≅ j^*(ℒ^{⊗ i} ⊗ ℒ^{⊗ k}) ⟶ j^*ℒ^{⊗ (i + k)}` of
the restriction of `⨁_n ℒ^{⊗ n}` to `U`, read through Stacks 03EL. -/
theorem pointTargetIso_symm_trans_hom_mul (i k : ℤ)
    {τi : ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj
        (pointLaurentPieceQcoh L W x i)).obj ≅
      (modulePullback B S hS (pointHom w)).obj ((modulePullback B S hS j).obj
        (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) i))}
    {τk : ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj
        (pointLaurentPieceQcoh L W x k)).obj ≅
      (modulePullback B S hS (pointHom w)).obj ((modulePullback B S hS j).obj
        (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) k))}
    {τik : ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj
        (pointLaurentPieceQcoh L W x (i + k))).obj ≅
      (modulePullback B S hS (pointHom w)).obj ((modulePullback B S hS j).obj
        (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) (i + k)))}
    (hτi : τi = (pointTargetIso L W x i).symm ≪≫
      eqToIso (congrArg (fun g => (modulePullback B S hS g).obj
        (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) i)) h) ≪≫
      ((modulePullbackCompIso B S hS (pointHom w) j).app _).symm)
    (hτk : τk = (pointTargetIso L W x k).symm ≪≫
      eqToIso (congrArg (fun g => (modulePullback B S hS g).obj
        (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) k)) h) ≪≫
      ((modulePullbackCompIso B S hS (pointHom w) j).app _).symm)
    (hτik : τik = (pointTargetIso L W x (i + k)).symm ≪≫
      eqToIso (congrArg (fun g => (modulePullback B S hS g).obj
        (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) (i + k))) h) ≪≫
      ((modulePullbackCompIso B S hS (pointHom w) j).app _).symm)
    :
    representedTensorChartMul B S hS (pointLaurentPieceMul L W x i k) ≫ τik.hom =
      MonoidalCategoryStruct.tensorHom (C := Modules.{u, u} B S hS (yonedaSpace B S hS W).1
        (yonedaSpace B S hS W).2) τi.hom τk.hom ≫
        (modulePullbackTensorIso B S hS (pointHom w) ((modulePullback B S hS j).obj
          (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) i))
          ((modulePullback B S hS j).obj
            (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) k))).inv ≫
        (modulePullback B S hS (pointHom w)).map
          ((modulePullbackTensorIso B S hS j
            (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) i)
            (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) k)).inv ≫
          (modulePullback B S hS j).map ((modulesTensorObjIso B S hS X.1 X.2
            (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) i) (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) k)).hom ≫
      SheafOfModules.GradedAlgebra.mulSheaf (Stacks.SheafOfModules.TensorPower.laurentAlgebra
        (smallEtaleRingedTopos B S hS X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
        L : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) i k)) :=
  symmTransComp_hom_mul j (pointHom w) (pointHom x) h hτi hτk hτik
    (pointTargetIso_hom_mul L W x i k)

/-- **The target factor of a chart map is unital** (Stacks 0D2Z; the unit companion of
`AlgebraicGeometry.Space.pointTargetIso_symm_trans_hom_mul`): the composite
`((x^*ℒ)^{⊗ 0})^a ≅ x^*(ℒ^{⊗ 0}) = (j ∘ w)^*(ℒ^{⊗ 0}) ≅ w^*(j^*(ℒ^{⊗ 0}))` carries the morphism
attached to the unit of the Laurent algebra of `x^*ℒ` to the inverse image along `w` of the unit
`𝒪_U ≅ j^*𝒪_X ⟶ j^*ℒ^{⊗ 0}` of the restriction of `⨁_n ℒ^{⊗ n}` to `U`, read through
Stacks 03LU. -/
theorem pointTargetIso_symm_trans_hom_one
    {τ : ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj
        (pointLaurentPieceQcoh L W x 0)).obj ≅
      (modulePullback B S hS (pointHom w)).obj ((modulePullback B S hS j).obj
        (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) 0))}
    (hτ : τ = (pointTargetIso L W x 0).symm ≪≫
      eqToIso (congrArg (fun g => (modulePullback B S hS g).obj
        (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) 0)) h) ≪≫
      ((modulePullbackCompIso B S hS (pointHom w) j).app _).symm)
    :
    representedUnitChartHom B S hS (pointLaurentPieceUnit L W x) ≫ τ.hom =
      (modulePullbackUnitIso B S hS (pointHom w)).inv ≫
        (modulePullback B S hS (pointHom w)).map
          ((modulePullbackUnitIso B S hS j).inv ≫ (modulePullback B S hS j).map
            (SheafOfModules.GradedAlgebra.oneHom (Stacks.SheafOfModules.TensorPower.laurentAlgebra
            (smallEtaleRingedTopos B S hS X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
        L : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)))) :=
  symmTransComp_hom_one j (pointHom w) (pointHom x) h hτ (pointTargetIso_hom_one L W x)

/-- **The multiplication of the restriction of `⨁_n ℒ^{⊗ n}` along `j : U ⟶ X`**:
`j^*ℒ^{⊗ i} ⊗ j^*ℒ^{⊗ k} ≅ j^*(ℒ^{⊗ i} ⊗ ℒ^{⊗ k}) ⟶ j^*ℒ^{⊗ (i + k)}`, Stacks 03EL followed by
the inverse image of the multiplication of the Laurent algebra. -/
def laurentRestrictMul (i k : ℤ) :=
  (modulePullbackTensorIso B S hS j
    (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) i)
      (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) k)).inv ≫
    (modulePullback B S hS j).map ((modulesTensorObjIso B S hS X.1 X.2
      (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) i)
        (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) k)).hom ≫
      SheafOfModules.GradedAlgebra.mulSheaf (Stacks.SheafOfModules.TensorPower.laurentAlgebra
        (smallEtaleRingedTopos B S hS X).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
        L : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) i k)

/-- **The unit of the restriction of `⨁_n ℒ^{⊗ n}` along `j : U ⟶ X`**:
`𝒪_U ≅ j^*𝒪_X ⟶ j^*ℒ^{⊗ 0}`, Stacks 03LU followed by the inverse image of the unit of the Laurent
algebra. -/
def laurentRestrictUnit :=
  (modulePullbackUnitIso B S hS j).inv ≫ (modulePullback B S hS j).map
    (SheafOfModules.GradedAlgebra.oneHom (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos B S hS X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
        L : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)))

/-- `AlgebraicGeometry.Space.pointTargetIso_symm_trans_hom_mul` with the multiplication of the
restriction named (`AlgebraicGeometry.Space.laurentRestrictMul`). -/
theorem pointTargetIso_symm_trans_hom_mul_restrict (i k : ℤ)
    {τi : ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj
        (pointLaurentPieceQcoh L W x i)).obj ≅
      (modulePullback B S hS (pointHom w)).obj ((modulePullback B S hS j).obj
        (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) i))}
    {τk : ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj
        (pointLaurentPieceQcoh L W x k)).obj ≅
      (modulePullback B S hS (pointHom w)).obj ((modulePullback B S hS j).obj
        (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) k))}
    {τik : ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj
        (pointLaurentPieceQcoh L W x (i + k))).obj ≅
      (modulePullback B S hS (pointHom w)).obj ((modulePullback B S hS j).obj
        (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) (i + k)))}
    (hτi : τi = (pointTargetIso L W x i).symm ≪≫
      eqToIso (congrArg (fun g => (modulePullback B S hS g).obj
        (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) i)) h) ≪≫
      ((modulePullbackCompIso B S hS (pointHom w) j).app _).symm)
    (hτk : τk = (pointTargetIso L W x k).symm ≪≫
      eqToIso (congrArg (fun g => (modulePullback B S hS g).obj
        (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) k)) h) ≪≫
      ((modulePullbackCompIso B S hS (pointHom w) j).app _).symm)
    (hτik : τik = (pointTargetIso L W x (i + k)).symm ≪≫
      eqToIso (congrArg (fun g => (modulePullback B S hS g).obj
        (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) (i + k))) h) ≪≫
      ((modulePullbackCompIso B S hS (pointHom w) j).app _).symm) :
    representedTensorChartMul B S hS (pointLaurentPieceMul L W x i k) ≫ τik.hom =
      MonoidalCategoryStruct.tensorHom (C := Modules.{u, u} B S hS (yonedaSpace B S hS W).1
        (yonedaSpace B S hS W).2) τi.hom τk.hom ≫
        (modulePullbackTensorIso B S hS (pointHom w) ((modulePullback B S hS j).obj
          (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) i))
          ((modulePullback B S hS j).obj
            (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) k))).inv ≫
        (modulePullback B S hS (pointHom w)).map (laurentRestrictMul L j i k) :=
  pointTargetIso_symm_trans_hom_mul L j w x h i k hτi hτk hτik

/-- `AlgebraicGeometry.Space.pointTargetIso_symm_trans_hom_one` with the unit of the restriction
named (`AlgebraicGeometry.Space.laurentRestrictUnit`). -/
theorem pointTargetIso_symm_trans_hom_one_restrict
    {τ : ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj
        (pointLaurentPieceQcoh L W x 0)).obj ≅
      (modulePullback B S hS (pointHom w)).obj ((modulePullback B S hS j).obj
        (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) 0))}
    (hτ : τ = (pointTargetIso L W x 0).symm ≪≫
      eqToIso (congrArg (fun g => (modulePullback B S hS g).obj
        (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) 0)) h) ≪≫
      ((modulePullbackCompIso B S hS (pointHom w) j).app _).symm) :
    representedUnitChartHom B S hS (pointLaurentPieceUnit L W x) ≫ τ.hom =
      (modulePullbackUnitIso B S hS (pointHom w)).inv ≫
        (modulePullback B S hS (pointHom w)).map (laurentRestrictUnit L j) :=
  pointTargetIso_symm_trans_hom_one L j w x h hτ

end Target

namespace RelativeProjSituation.InvertibleTwistingRestriction

section Source

variable {s : RelativeProjSituation.{u, m}}
  {X : (BigFppfOver s.site s.base s.containsBase)ᵒᵖ ⥤ Type u} {f : X ⟶ s.space.1}
  (R : s.InvertibleTwistingRestriction f) (hX : IsAlgebraicSpace s.site s.base s.containsBase X)
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

/-- **The multiplication `r^*𝒪(i) ⊗ r^*𝒪(j) ⟶ r^*𝒪(i + j)` of the source of `θ`**: Stacks 03EL
for `r = r_{ℒ,ψ} : U(ψ) ⟶ Proj_Y(𝒜)` followed by the inverse image of the multiplication of the
twists (`…RelativeProjSituation.twistAlgebraMul`). -/
def thetaSourceMul (i j : ℤ) :
    (R.thetaSource hX Px i).obj ⊗ (R.thetaSource hX Px j).obj ⟶
      (R.thetaSource hX Px (i + j)).obj :=
  (modulePullbackTensorIso s.site s.base s.containsBase (R.invertibleSpaceMorphism hX)
      (s.twistModule Px i).obj (s.twistModule Px j).obj).inv ≫
    (modulePullback s.site s.base s.containsBase (R.invertibleSpaceMorphism hX)).map
      (s.twistAlgebraMul Px i j)

/-- **The unit `𝒪_{U(ψ)} ⟶ r^*𝒪(0)` of the source of `θ`**: Stacks 03LU for
`r = r_{ℒ,ψ} : U(ψ) ⟶ Proj_Y(𝒜)` followed by the inverse image of the unit of the twists
(`…RelativeProjSituation.twistAlgebraUnit`). -/
def thetaSourceUnit :
    SheafOfModules.unit (structureRingSheaf s.site s.base s.containsBase (R.locusSpace hX)) ⟶
      (R.thetaSource hX Px 0).obj :=
  (modulePullbackUnitIso s.site s.base s.containsBase (R.invertibleSpaceMorphism hX)).inv ≫
    (modulePullback s.site s.base s.containsBase (R.invertibleSpaceMorphism hX)).map
      (s.twistAlgebraUnit Px)

end Source

section TargetOfTheta

variable (s : RelativeProjSituation.{u, m})
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} (f : X ⟶ s.shrink.space)
  (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O))
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L))

/-- **The multiplication `ℒ^{⊗ i}|_{U(ψ)} ⊗ ℒ^{⊗ j}|_{U(ψ)} ⟶ ℒ^{⊗ (i + j)}|_{U(ψ)}` of the target
of `θ`**: the multiplication of the restriction of `⨁_n ℒ^{⊗ n}` along the inclusion
`U(ψ) ⊆ X` (`AlgebraicGeometry.Space.laurentRestrictMul`). -/
abbrev thetaTargetMul (i j : ℤ) :=
  laurentRestrictMul L (locusInclusionOfUnitalHom s f L ψ) i j

/-- **The unit `𝒪_{U(ψ)} ⟶ ℒ^{⊗ 0}|_{U(ψ)}` of the target of `θ`**: the unit of the restriction of
`⨁_n ℒ^{⊗ n}` along the inclusion `U(ψ) ⊆ X` (`AlgebraicGeometry.Space.laurentRestrictUnit`). -/
abbrev thetaTargetUnit :=
  laurentRestrictUnit L (locusInclusionOfUnitalHom s f L ψ)

end TargetOfTheta

end RelativeProjSituation.InvertibleTwistingRestriction

end AlgebraicGeometry.Space

end
