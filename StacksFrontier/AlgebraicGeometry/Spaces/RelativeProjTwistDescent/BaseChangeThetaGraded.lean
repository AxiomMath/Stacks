module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.BaseChangeTheta
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PointTwistGraded
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PullbackComparisonCompat
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.TwistGradedAlgebra

/-!
# Inverse images of descended sheaves of graded algebras along a morphism of relative Projs

In Situation 0849 let `g : X' ⟶ X` be a morphism of algebraic spaces, `P = Proj_X(𝒜)` and
`P' = Proj_{X'}(g^*𝒜)` the two relative Projs of Stacks 084B, and `h : P' ⟶ P` the morphism of
Stacks 085C.  The degreewise isomorphisms `h^*D(M_n) ≅ D(M''_n)` of descended modules
(`AlgebraicGeometry.Space.RelativeProjPoints.pullbackAlongDescendedIso`, the construction of
`θ_n` of Stacks 085C) are built from identifications `Θ_n : y^*M_n ≅ M''_n` along a morphism
`y : U' ×_{X'} P' ⟶ U ×_X P` of the presenting schemes.  This file shows that, when the `Θ_n`
carry the multiplications and the unit on the presenting schemes to one another, the isomorphisms
`h^*D(M_n) ≅ D(M''_n)` carry the descended multiplication, pulled back along `h` and read through
Stacks 03EL, to the descended multiplication, and likewise for the unit through Stacks 03LU: this
is checked on the atlas of `P'`, on which a morphism of quasi-coherent modules is determined.

## Main definitions

* `AlgebraicGeometry.Space.ModulePullbackGradedAlgebraIso f 𝒜 𝒜'`: an isomorphism of sheaves of
  `ℤ`-graded algebras `f^*𝒜 ≅ 𝒜'` along a morphism of algebraic spaces: isomorphisms in every
  degree carrying the pulled-back multiplication (through Stacks 03EL) and unit (through
  Stacks 03LU) to the multiplication and unit of `𝒜'`.
* `AlgebraicGeometry.Space.ModulePullbackGradedAlgebraHom f 𝒜 𝒜'`: the same with the degreewise
  isomorphisms weakened to morphisms: a morphism of sheaves of `ℤ`-graded algebras
  `f^*𝒜 ⟶ 𝒜'`.
* `AlgebraicGeometry.Space.modulesGradedAlgebraMul`, `…modulesGradedAlgebraOne`: the
  multiplication and the unit of a sheaf of graded algebras as morphisms of `𝒪`-modules.
* `AlgebraicGeometry.Space.RelativeProjPoints.pullbackAlongDescendedModuleIso`: the isomorphism
  `h^*D(M_n) ≅ D(M''_n)` between the pieces of the descended sheaves of graded algebras.

## Main results

* `AlgebraicGeometry.Space.pullbackMulCompat_of_chartReadings`,
  `…pullbackUnitCompat_of_chartReadings`: identifications read from chart identifications carry
  multiplications and units to multiplications and units, with the readings named.
* `AlgebraicGeometry.Space.RelativeProjPoints.pullbackMulCompat_pullbackAlongDescendedModuleIso`
  and `…pullbackUnitCompat_pullbackAlongDescendedModuleIso`: **the isomorphisms
  `h^*D(M_n) ≅ D(M''_n)` carry the multiplication and the unit of the descended sheaf of graded
  algebras on `P` to those on `P'`.**

## Implementation notes

The equations on the atlas compare terms produced by lemmas stated in different contexts, whose
implicit arguments are spelled differently (the object space of a presentation groupoid against
the represented algebraic space, a relative Proj against its underlying presheaf); such
comparisons inside composites exhaust the elaborator's budget.  Every reading is therefore
stated as a named proposition (`AlgebraicGeometry.Space.ChartMulReading`, `…ChartUnitReading`,
`…AtlasChartReading`, `…SquareReading`, `…PullbackMulCompat`, …), which is compared argument by
argument, and the readings whose sources are spelled differently pass through heterogeneous
equalities (`…ChartMulReadingHEq`, `…ChartUnitReadingHEq`) or through isomorphisms
(`…squareReading_of_iso_eq`).  The construction is carried out for arbitrary descent data on
presentations of two relative Projs; it is instantiated at the twists in
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjTwistDescent/BaseChangeThetaAlgebra.lean`.

## References

* [Stacks Project, Tag 085C](https://stacks.math.columbia.edu/tag/085C)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

/-! ### Readings along a square, as named propositions -/

section Readings

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A multiplication `μ_K` read along `Y` through `ℓ` as `μ_L`, through Stacks 03EL. -/
def ChartMulReading {U'' U : AlgebraicSpaces B S hS} (Y : U'' ⟶ U)
    {Ki Kj Kk : Modules.{u, u} B S hS U.1 U.2} {Li Lj Lk : Modules.{u, u} B S hS U''.1 U''.2}
    (μK : Ki ⊗ Kj ⟶ Kk) (ℓi : (modulePullback B S hS Y).obj Ki ⟶ Li)
    (ℓj : (modulePullback B S hS Y).obj Kj ⟶ Lj) (ℓk : (modulePullback B S hS Y).obj Kk ⟶ Lk)
    (μL : Li ⊗ Lj ⟶ Lk) : Prop :=
  (modulePullback B S hS Y).map μK ≫ ℓk =
    (modulePullbackTensorIso B S hS Y Ki Kj).hom ≫ (ℓi ⊗ₘ ℓj) ≫ μL

/-- A morphism `ν_K` out of the structure sheaf read along `Y` through `ℓ` as `ν_L`, through
Stacks 03LU. -/
def ChartUnitReading {U'' U : AlgebraicSpaces B S hS} (Y : U'' ⟶ U)
    {K : Modules.{u, u} B S hS U.1 U.2} (νK : SheafOfModules.unit (structureRingSheaf B S hS U) ⟶ K)
    {L : Modules.{u, u} B S hS U''.1 U''.2} (ℓ : (modulePullback B S hS Y).obj K ⟶ L)
    (νL : SheafOfModules.unit (structureRingSheaf B S hS U'') ⟶ L) : Prop :=
  (modulePullback B S hS Y).map νK ≫ ℓ = (modulePullbackUnitIso B S hS Y).hom ≫ νL

/-- A morphism `e` read along `c` through `ρ` as `χ`. -/
def AtlasChartReading {U'' X'' : AlgebraicSpaces B S hS} (c : U'' ⟶ X'')
    {A G : Modules.{u, u} B S hS X''.1 X''.2} {L : Modules.{u, u} B S hS U''.1 U''.2} (e : A ⟶ G)
    (ρ : (modulePullback B S hS c).obj G ⟶ L) (χ : (modulePullback B S hS c).obj A ⟶ L) : Prop :=
  (modulePullback B S hS c).map e ≫ ρ = χ

/-- `χ` is the identification along the square `c'' ≫ h = Y ≫ c` followed by `κ` and `ℓ`. -/
def SquareReading {U'' U X'' X : AlgebraicSpaces B S hS} (c'' : U'' ⟶ X'') (c : U ⟶ X)
    (h : X'' ⟶ X) (Y : U'' ⟶ U) (hY : c'' ≫ h = Y ≫ c) (T : Modules.{u, u} B S hS X.1 X.2)
    {K : Modules.{u, u} B S hS U.1 U.2} {L : Modules.{u, u} B S hS U''.1 U''.2}
    (κ : (modulePullback B S hS c).obj T ⟶ K) (ℓ : (modulePullback B S hS Y).obj K ⟶ L)
    (χ : (modulePullback B S hS c'').obj ((modulePullback B S hS h).obj T) ⟶ L) : Prop :=
  χ = pullbackSquareHom c'' c h Y hY T ≫ (modulePullback B S hS Y).map κ ≫ ℓ

/-- Inverse image along `c` is injective on morphisms `A ⟶ G`. -/
def AtlasInjective {U'' X'' : AlgebraicSpaces B S hS} (c : U'' ⟶ X'')
    (A G : Modules.{u, u} B S hS X''.1 X''.2) : Prop :=
  ∀ φ ψ : A ⟶ G, (modulePullback B S hS c).map φ = (modulePullback B S hS c).map ψ → φ = ψ

/-- **Morphisms `e_n : h^*𝒯_n ⟶ 𝒢_n` carry the multiplication `μ` of the `𝒯_n`, pulled back along
`h` and read through Stacks 03EL, to the multiplication `μ_𝒢` of the `𝒢_n`.** -/
def PullbackMulCompat {X'' X : AlgebraicSpaces B S hS} (h : X'' ⟶ X)
    {Ti Tj Tk : Modules.{u, u} B S hS X.1 X.2} {Gi Gj Gk : Modules.{u, u} B S hS X''.1 X''.2}
    (μ : Ti ⊗ Tj ⟶ Tk) (ei : (modulePullback B S hS h).obj Ti ⟶ Gi)
    (ej : (modulePullback B S hS h).obj Tj ⟶ Gj) (ek : (modulePullback B S hS h).obj Tk ⟶ Gk)
    (μG : Gi ⊗ Gj ⟶ Gk) : Prop :=
  (modulePullbackTensorIso B S hS h Ti Tj).inv ≫ (modulePullback B S hS h).map μ ≫ ek =
    (ei ⊗ₘ ej) ≫ μG

/-- **A morphism `e : h^*𝒯 ⟶ 𝒢` carries `ν : 𝒪 ⟶ 𝒯`, pulled back along `h` and read through
Stacks 03LU, to `ν_𝒢 : 𝒪 ⟶ 𝒢`.** -/
def PullbackUnitCompat {X'' X : AlgebraicSpaces B S hS} (h : X'' ⟶ X)
    {T : Modules.{u, u} B S hS X.1 X.2} {G : Modules.{u, u} B S hS X''.1 X''.2}
    (ν : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶ T)
    (e : (modulePullback B S hS h).obj T ⟶ G)
    (νG : SheafOfModules.unit (structureRingSheaf B S hS X'') ⟶ G) : Prop :=
  (modulePullbackUnitIso B S hS h).inv ≫ (modulePullback B S hS h).map ν ≫ e = νG

/-- `AlgebraicGeometry.Space.ChartMulReading` with the source `KK` of `μ_K` given separately, as
a heterogeneous equality: the form in which it is read off a multiplication whose source is
spelled differently from `K_i ⊗ K_j`. -/
def ChartMulReadingHEq {U'' U : AlgebraicSpaces B S hS} (Y : U'' ⟶ U)
    {Ki Kj Kk KK : Modules.{u, u} B S hS U.1 U.2} {Li Lj Lk : Modules.{u, u} B S hS U''.1 U''.2}
    (μK : KK ⟶ Kk) (ℓi : (modulePullback B S hS Y).obj Ki ⟶ Li)
    (ℓj : (modulePullback B S hS Y).obj Kj ⟶ Lj) (ℓk : (modulePullback B S hS Y).obj Kk ⟶ Lk)
    (μL : Li ⊗ Lj ⟶ Lk) : Prop :=
  HEq ((modulePullback B S hS Y).map μK ≫ ℓk)
    ((modulePullbackTensorIso B S hS Y Ki Kj).hom ≫ (ℓi ⊗ₘ ℓj) ≫ μL)

/-- A heterogeneous multiplication reading whose source is `K_i ⊗ K_j` is a reading. -/
theorem ChartMulReadingHEq.chartMulReading {U'' U : AlgebraicSpaces B S hS} {Y : U'' ⟶ U}
    {Ki Kj Kk : Modules.{u, u} B S hS U.1 U.2} {Li Lj Lk : Modules.{u, u} B S hS U''.1 U''.2}
    {μK : Ki ⊗ Kj ⟶ Kk} {ℓi : (modulePullback B S hS Y).obj Ki ⟶ Li}
    {ℓj : (modulePullback B S hS Y).obj Kj ⟶ Lj} {ℓk : (modulePullback B S hS Y).obj Kk ⟶ Lk}
    {μL : Li ⊗ Lj ⟶ Lk} (h : ChartMulReadingHEq Y (KK := Ki ⊗ Kj) μK ℓi ℓj ℓk μL) :
    ChartMulReading Y μK ℓi ℓj ℓk μL :=
  eq_of_heq h

/-- A heterogeneous multiplication reading through `ℓ'` is one through any `ℓ = ℓ'`. -/
theorem ChartMulReadingHEq.of_eq {U'' U : AlgebraicSpaces B S hS} {Y : U'' ⟶ U}
    {Ki Kj Kk KK : Modules.{u, u} B S hS U.1 U.2} {Li Lj Lk : Modules.{u, u} B S hS U''.1 U''.2}
    {μK : KK ⟶ Kk} {ℓi ℓi' : (modulePullback B S hS Y).obj Ki ⟶ Li}
    {ℓj ℓj' : (modulePullback B S hS Y).obj Kj ⟶ Lj} {ℓk ℓk' : (modulePullback B S hS Y).obj Kk ⟶
        Lk}
    {μL : Li ⊗ Lj ⟶ Lk} (h : ChartMulReadingHEq Y μK ℓi' ℓj' ℓk' μL) (hi : ℓi' = ℓi)
    (hj : ℓj' = ℓj) (hk : ℓk' = ℓk) : ChartMulReadingHEq Y μK ℓi ℓj ℓk μL := by
  subst hi hj hk
  exact h

/-- `AlgebraicGeometry.Space.ChartUnitReading` with the source `O` of `ν_K` given separately, as
a heterogeneous equality. -/
def ChartUnitReadingHEq {U'' U : AlgebraicSpaces B S hS} (Y : U'' ⟶ U)
    {O K : Modules.{u, u} B S hS U.1 U.2} (νK : O ⟶ K)
    {L : Modules.{u, u} B S hS U''.1 U''.2} (ℓ : (modulePullback B S hS Y).obj K ⟶ L)
    (νL : SheafOfModules.unit (structureRingSheaf B S hS U'') ⟶ L) : Prop :=
  HEq ((modulePullback B S hS Y).map νK ≫ ℓ) ((modulePullbackUnitIso B S hS Y).hom ≫ νL)

/-- A heterogeneous unit reading whose source is the structure sheaf is a reading. -/
theorem ChartUnitReadingHEq.chartUnitReading {U'' U : AlgebraicSpaces B S hS} {Y : U'' ⟶ U}
    {K : Modules.{u, u} B S hS U.1 U.2}
    {νK : SheafOfModules.unit (structureRingSheaf B S hS U) ⟶ K}
    {L : Modules.{u, u} B S hS U''.1 U''.2} {ℓ : (modulePullback B S hS Y).obj K ⟶ L}
    {νL : SheafOfModules.unit (structureRingSheaf B S hS U'') ⟶ L}
    (h : ChartUnitReadingHEq Y νK ℓ νL) : ChartUnitReading Y νK ℓ νL :=
  eq_of_heq h

/-- A heterogeneous unit reading through `ℓ'` is one through any `ℓ = ℓ'`. -/
theorem ChartUnitReadingHEq.of_eq {U'' U : AlgebraicSpaces B S hS} {Y : U'' ⟶ U}
    {O K : Modules.{u, u} B S hS U.1 U.2} {νK : O ⟶ K}
    {L : Modules.{u, u} B S hS U''.1 U''.2} {ℓ ℓ' : (modulePullback B S hS Y).obj K ⟶ L}
    {νL : SheafOfModules.unit (structureRingSheaf B S hS U'') ⟶ L}
    (h : ChartUnitReadingHEq Y νK ℓ' νL) (hℓ : ℓ' = ℓ) : ChartUnitReadingHEq Y νK ℓ νL := by
  subst hℓ
  exact h

/-- An identification `χ` on `c''` given as the identification along the square followed by
`Y^*κ` and `ℓ`, as isomorphisms, is read along the square in the sense of
`AlgebraicGeometry.Space.SquareReading`. -/
theorem squareReading_of_iso_eq {U'' U X'' X : AlgebraicSpaces B S hS} {c'' : U'' ⟶ X''}
    {c : U ⟶ X} {h : X'' ⟶ X} {Y : U'' ⟶ U} {hY : c'' ≫ h = Y ≫ c}
    {T : Modules.{u, u} B S hS X.1 X.2} {K : Modules.{u, u} B S hS U.1 U.2}
    {L : Modules.{u, u} B S hS U''.1 U''.2} {κ : (modulePullback B S hS c).obj T ≅ K}
    {ℓ : (modulePullback B S hS Y).obj K ≅ L}
    {χ : (modulePullback B S hS c'').obj ((modulePullback B S hS h).obj T) ≅ L}
    (hχ : χ = pullbackSquareIso c'' c h Y hY T ≪≫ (modulePullback B S hS Y).mapIso κ ≪≫ ℓ) :
    SquareReading c'' c h Y hY T κ.hom ℓ.hom χ.hom := by
  subst hχ
  rfl

end Readings

/-! ### Identifications read from chart identifications, with the readings named -/

section Assembly

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U'' U X'' X : AlgebraicSpaces B S hS} (c'' : U'' ⟶ X'') (c : U ⟶ X) (h : X'' ⟶ X)
  (Y : U'' ⟶ U) (hY : c'' ≫ h = Y ≫ c)

/-- `AlgebraicGeometry.Space.pullbackTensorIso_inv_comp_map_comp_of_chart` with its readings
given as the named propositions above. -/
theorem pullbackMulCompat_of_chartReadings
    {Ti Tj Tk : Modules.{u, u} B S hS X.1 X.2} (μ : Ti ⊗ Tj ⟶ Tk)
    {Ki Kj Kk : Modules.{u, u} B S hS U.1 U.2}
    (κi : (modulePullback B S hS c).obj Ti ⟶ Ki) (κj : (modulePullback B S hS c).obj Tj ⟶ Kj)
    (κk : (modulePullback B S hS c).obj Tk ⟶ Kk) (μK : Ki ⊗ Kj ⟶ Kk)
    (hμ : ChartMulReading c μ κi κj κk μK)
    {Li Lj Lk : Modules.{u, u} B S hS U''.1 U''.2}
    (ℓi : (modulePullback B S hS Y).obj Ki ⟶ Li) (ℓj : (modulePullback B S hS Y).obj Kj ⟶ Lj)
    (ℓk : (modulePullback B S hS Y).obj Kk ⟶ Lk) (μL : Li ⊗ Lj ⟶ Lk)
    (hℓ : ChartMulReading Y μK ℓi ℓj ℓk μL)
    {Gi Gj Gk : Modules.{u, u} B S hS X''.1 X''.2}
    (ρi : (modulePullback B S hS c'').obj Gi ⟶ Li) (ρj : (modulePullback B S hS c'').obj Gj ⟶ Lj)
    (ρk : (modulePullback B S hS c'').obj Gk ≅ Lk) (μG : Gi ⊗ Gj ⟶ Gk)
    (hρ : ChartMulReading c'' μG ρi ρj ρk.hom μL)
    (ei : (modulePullback B S hS h).obj Ti ⟶ Gi) (ej : (modulePullback B S hS h).obj Tj ⟶ Gj)
    (ek : (modulePullback B S hS h).obj Tk ⟶ Gk)
    (χi : (modulePullback B S hS c'').obj ((modulePullback B S hS h).obj Ti) ⟶ Li)
    (χj : (modulePullback B S hS c'').obj ((modulePullback B S hS h).obj Tj) ⟶ Lj)
    (χk : (modulePullback B S hS c'').obj ((modulePullback B S hS h).obj Tk) ⟶ Lk)
    (hei : AtlasChartReading c'' ei ρi χi) (hej : AtlasChartReading c'' ej ρj χj)
    (hek : AtlasChartReading c'' ek ρk.hom χk)
    (hχi : SquareReading c'' c h Y hY Ti κi ℓi χi) (hχj : SquareReading c'' c h Y hY Tj κj ℓj χj)
    (hχk : SquareReading c'' c h Y hY Tk κk ℓk χk)
    (hinj : AtlasInjective c''
      ((modulePullback B S hS h).obj Ti ⊗ (modulePullback B S hS h).obj Tj) Gk) :
    PullbackMulCompat h μ ei ej ek μG :=
  pullbackTensorIso_inv_comp_map_comp_of_chart c'' c h Y hY μ κi κj κk μK hμ ℓi ℓj ℓk μL hℓ
    ρi ρj ρk μG hρ ei ej ek χi χj χk hei hej hek hχi hχj hχk hinj

/-- `AlgebraicGeometry.Space.pullbackUnitIso_inv_comp_map_comp_of_chart` with its readings
given as the named propositions above. -/
theorem pullbackUnitCompat_of_chartReadings
    {T : Modules.{u, u} B S hS X.1 X.2}
    (ν : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶ T)
    {K : Modules.{u, u} B S hS U.1 U.2} (κ : (modulePullback B S hS c).obj T ⟶ K)
    (νK : SheafOfModules.unit (structureRingSheaf B S hS U) ⟶ K)
    (hν : ChartUnitReading c ν κ νK)
    {L : Modules.{u, u} B S hS U''.1 U''.2} (ℓ : (modulePullback B S hS Y).obj K ⟶ L)
    (νL : SheafOfModules.unit (structureRingSheaf B S hS U'') ⟶ L)
    (hℓ : ChartUnitReading Y νK ℓ νL)
    {G : Modules.{u, u} B S hS X''.1 X''.2} (ρ : (modulePullback B S hS c'').obj G ≅ L)
    (νG : SheafOfModules.unit (structureRingSheaf B S hS X'') ⟶ G)
    (hρ : ChartUnitReading c'' νG ρ.hom νL)
    (e : (modulePullback B S hS h).obj T ⟶ G)
    (χ : (modulePullback B S hS c'').obj ((modulePullback B S hS h).obj T) ⟶ L)
    (he : AtlasChartReading c'' e ρ.hom χ) (hχ : SquareReading c'' c h Y hY T κ ℓ χ)
    (hinj : AtlasInjective c'' (SheafOfModules.unit (structureRingSheaf B S hS X'')) G) :
    PullbackUnitCompat h ν e νG :=
  pullbackUnitIso_inv_comp_map_comp_of_chart c'' c h Y hY ν κ νK hν ℓ νL hℓ ρ νG hρ e χ he hχ
    hinj

end Assembly

/-! ### Isomorphisms of sheaves of graded algebras along inverse images -/

section GradedIso

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X'' X : AlgebraicSpaces B S hS}

/-- **The multiplication `𝒜_i ⊗ 𝒜_j ⟶ 𝒜_{i+j}` of a sheaf of `ℤ`-graded `𝒪_X`-algebras**, as a
morphism out of the tensor product of `𝒪_X`-modules
(`AlgebraicGeometry.Space.modulesMonoidalCategory`): `SheafOfModules.GradedAlgebra.mulSheaf`
read through `AlgebraicGeometry.Space.modulesTensorObjIso`. -/
def modulesGradedAlgebraMul
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) (i j : ℤ) :
    MonoidalCategoryStruct.tensorObj (C := Modules.{u, u} B S hS X.1 X.2) (A.piece i)
      (A.piece j) ⟶ A.piece (i + j) :=
  haveI := SmallEtale.instHasSheafify B S hS X.1 AddCommGrpCat.{u}
  haveI := SmallEtale.instWEqualsLocallyBijective B S hS X.1 AddCommGrpCat.{u}
  (modulesTensorObjIso B S hS X.1 X.2 (A.piece i) (A.piece j)).hom ≫
    SheafOfModules.GradedAlgebra.mulSheaf.{u, u + 1, u, u} (J := SmallEtale.topology B S hS X.1) A
      i j

/-- **The unit `𝒪_X ⟶ 𝒜_0` of a sheaf of `ℤ`-graded `𝒪_X`-algebras**, as a morphism of
`𝒪_X`-modules (`SheafOfModules.GradedAlgebra.oneHom`). -/
def modulesGradedAlgebraOne
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) :
    SheafOfModules.unit (structureRingSheaf B S hS X) ⟶ A.piece 0 :=
  haveI := SmallEtale.instHasSheafify B S hS X.1 AddCommGrpCat.{u}
  haveI := SmallEtale.instWEqualsLocallyBijective B S hS X.1 AddCommGrpCat.{u}
  SheafOfModules.GradedAlgebra.oneHom.{u, u + 1, u} (J := SmallEtale.topology B S hS X.1) A

/-- **An isomorphism of sheaves of `ℤ`-graded algebras `f^*𝒜 ≅ 𝒜'`** along a morphism
`f : X'' ⟶ X` of algebraic spaces: isomorphisms `f^*𝒜_n ≅ 𝒜'_n` of `𝒪_{X''}`-modules in every
degree which carry the inverse image of the multiplication of `𝒜`, read through Stacks 03EL
(`f^*(𝒜_i ⊗ 𝒜_j) ≅ f^*𝒜_i ⊗ f^*𝒜_j`), to the multiplication of `𝒜'`, and the inverse image of
the unit of `𝒜`, read through Stacks 03LU (`f^*𝒪_X ≅ 𝒪_{X''}`), to the unit of `𝒜'`.  These
are exactly the conditions for `⨁_n f^*𝒜_n`, with the multiplication and unit induced from `𝒜`,
to be isomorphic to `𝒜'` as a sheaf of graded algebras through the given isomorphisms. -/
structure ModulePullbackGradedAlgebraIso (f : X'' ⟶ X)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (A' : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X'')) where
  /-- The isomorphism in degree `n`. -/
  iso (n : ℤ) : (modulePullback B S hS f).obj (A.piece n) ≅ A'.piece n
  /-- The isomorphisms carry the pulled-back multiplication to the multiplication. -/
  mul_comp (i j : ℤ) : PullbackMulCompat f (modulesGradedAlgebraMul A i j) (iso i).hom
    (iso j).hom (iso (i + j)).hom (modulesGradedAlgebraMul A' i j)
  /-- The isomorphism in degree `0` carries the pulled-back unit to the unit. -/
  unit_comp : PullbackUnitCompat f (modulesGradedAlgebraOne A) (iso 0).hom
    (modulesGradedAlgebraOne A')

/-- **A morphism of sheaves of `ℤ`-graded algebras `f^*𝒜 ⟶ 𝒜'`** along a morphism
`f : X'' ⟶ X` of algebraic spaces: morphisms `f^*𝒜_d ⟶ 𝒜'_d` of `𝒪_{X''}`-modules in every degree
which carry the inverse image of the multiplication of `𝒜`, read through Stacks 03EL, to the
multiplication of `𝒜'`, and likewise for the unit through Stacks 03LU. -/
structure ModulePullbackGradedAlgebraHom (f : X'' ⟶ X)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (A' : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X'')) where
  /-- The morphism in degree `d`. -/
  hom (d : ℤ) : (modulePullback B S hS f).obj (A.piece d) ⟶ A'.piece d
  /-- The morphisms carry the pulled-back multiplication to the multiplication. -/
  mul_comp (i j : ℤ) : PullbackMulCompat f (modulesGradedAlgebraMul A i j) (hom i) (hom j)
    (hom (i + j)) (modulesGradedAlgebraMul A' i j)
  /-- The morphism in degree `0` carries the pulled-back unit to the unit. -/
  unit_comp : PullbackUnitCompat f (modulesGradedAlgebraOne A) (hom 0)
    (modulesGradedAlgebraOne A')

end GradedIso

/-! ### The readings on a presentation of a relative Proj -/

namespace RelativeProjPoints

section DescendedReadings

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X.obj}
  (d : RelativeProjPoints B S hS π) (Px : Presentation B S hS X.obj X.property)
  (hP : IsAlgebraicSpace B S hS P)
  {M N K : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj (d.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory}
  (τ : quasicoherentPullbackObj B S hS (d.spaceTarget Px hP) M ⟶
    quasicoherentPullbackObj B S hS (d.spaceSource Px hP) M)
  (σ : quasicoherentPullbackObj B S hS (d.spaceTarget Px hP) N ⟶
    quasicoherentPullbackObj B S hS (d.spaceSource Px hP) N)
  (κ : quasicoherentPullbackObj B S hS (d.spaceTarget Px hP) K ⟶
    quasicoherentPullbackObj B S hS (d.spaceSource Px hP) K)
  (m : quasicoherentTensorObj B S hS (d.fibre Px.U Px.toSpace) M N ⟶ K)
  (ν : quasicoherentUnitObj B S hS (d.fibre Px.U Px.toSpace) ⟶ K)
  (hc : PresentationSchemeCocycle (d.spacePresentation Px hP) M τ)
  (hu : PresentationSchemeUnit (d.spacePresentation Px hP) M τ)
  (hc' : PresentationSchemeCocycle (d.spacePresentation Px hP) N σ)
  (hu' : PresentationSchemeUnit (d.spacePresentation Px hP) N σ)
  (hc'' : PresentationSchemeCocycle (d.spacePresentation Px hP) K κ)
  (hu'' : PresentationSchemeUnit (d.spacePresentation Px hP) K κ)
  (hbt : RepresentedC3TensorCompat B S hS (d.spaceTarget Px hP) M N)
  (hbs : RepresentedC3TensorCompat B S hS (d.spaceSource Px hP) M N)
  (hm : d.TransitionMulCompat Px hP τ σ κ m)
  (hbtu : RepresentedC3UnitCompat B S hS (d.spaceTarget Px hP))
  (hbsu : RepresentedC3UnitCompat B S hS (d.spaceSource Px hP))
  (hmu : d.TransitionUnitCompat Px hP κ ν)

/-- The descended multiplication is read on the atlas as the attached multiplication. -/
theorem chartMulReading_spacePresentationDescendedMul :
    ChartMulReading (presentationAtlas (d.spacePresentation Px hP))
      (Ki := (presentationDescendedModule (d.spacePresentation Px hP) M τ hc hu).obj)
      (Kj := (presentationDescendedModule (d.spacePresentation Px hP) N σ hc' hu').obj)
      (Kk := (presentationDescendedModule (d.spacePresentation Px hP) K κ hc'' hu'').obj)
      (Li := ((representedQuasicoherentSchemeEquivalence B S hS
        (d.spacePresentation Px hP).U).functor.obj M).obj)
      (Lj := ((representedQuasicoherentSchemeEquivalence B S hS
        (d.spacePresentation Px hP).U).functor.obj N).obj)
      (Lk := ((representedQuasicoherentSchemeEquivalence B S hS
        (d.spacePresentation Px hP).U).functor.obj K).obj)
      (d.spacePresentationDescendedMul Px hP τ σ κ m hc hu hc' hu' hc'' hu'' hbt hbs hm)
      (presentationDescendedModuleChartIso (d.spacePresentation Px hP) M τ hc hu).hom
      (presentationDescendedModuleChartIso (d.spacePresentation Px hP) N σ hc' hu').hom
      (presentationDescendedModuleChartIso (d.spacePresentation Px hP) K κ hc'' hu'').hom
      (representedTensorChartMul B S hS m) :=
  d.spacePresentationDescendedMul_spec Px hP τ σ κ m hc hu hc' hu' hc'' hu'' hbt hbs hm

/-- The descended unit is read on the atlas as the attached unit. -/
theorem chartUnitReading_spacePresentationDescendedUnit :
    ChartUnitReading (presentationAtlas (d.spacePresentation Px hP))
      (K := (presentationDescendedModule (d.spacePresentation Px hP) K κ hc'' hu'').obj)
      (L := ((representedQuasicoherentSchemeEquivalence B S hS
        (d.spacePresentation Px hP).U).functor.obj K).obj)
      (d.spacePresentationDescendedUnit Px hP κ ν hc'' hu'' hbtu hbsu hmu)
      (presentationDescendedModuleChartIso (d.spacePresentation Px hP) K κ hc'' hu'').hom
      (representedUnitChartHom B S hS ν) :=
  d.spacePresentationDescendedUnit_spec Px hP κ ν hc'' hu'' hbtu hbsu hmu

end DescendedReadings

section GradedReadings

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X.obj}
  (d : RelativeProjPoints B S hS π) (Px : Presentation B S hS X.obj X.property)
  (hP : IsAlgebraicSpace B S hS P) {Mn : ℤ → (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj (d.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory}
  (τ : ∀ n, quasicoherentPullbackObj B S hS (d.spaceTarget Px hP) (Mn n) ⟶
    quasicoherentPullbackObj B S hS (d.spaceSource Px hP) (Mn n))
  (hc : ∀ n, PresentationSchemeCocycle (d.spacePresentation Px hP) (Mn n) (τ n))
  (hu : ∀ n, PresentationSchemeUnit (d.spacePresentation Px hP) (Mn n) (τ n))
  (m : ∀ i j, quasicoherentTensorObj B S hS (d.fibre Px.U Px.toSpace) (Mn i) (Mn j) ⟶ Mn (i + j))
  (hbt : ∀ i j, RepresentedC3TensorCompat B S hS (d.spaceTarget Px hP) (Mn i) (Mn j))
  (hbs : ∀ i j, RepresentedC3TensorCompat B S hS (d.spaceSource Px hP) (Mn i) (Mn j))
  (hm : ∀ i j, d.TransitionMulCompat Px hP (τ i) (τ j) (τ (i + j)) (m i j))
  (ν : quasicoherentUnitObj B S hS (d.fibre Px.U Px.toSpace) ⟶ Mn 0)
  (hbtu : RepresentedC3UnitCompat B S hS (d.spaceTarget Px hP))
  (hbsu : RepresentedC3UnitCompat B S hS (d.spaceSource Px hP))
  (hmu : d.TransitionUnitCompat Px hP (τ 0) ν)
  (hassoc : QuasicoherentMulAssoc (d.fibre Px.U Px.toSpace) m)
  (hone : QuasicoherentOneMul (d.fibre Px.U Px.toSpace) m ν)
  (hcomm : QuasicoherentMulComm (d.fibre Px.U Px.toSpace) m)

/-- The multiplication of `spacePresentationGradedAlgebra`, out of the tensor product of
modules, is the descended multiplication. -/
theorem modulesGradedAlgebraMul_spacePresentationGradedAlgebra (i j : ℤ) :
    modulesGradedAlgebraMul (d.spacePresentationGradedAlgebra Px hP τ hc hu m hbt hbs hm ν hbtu
        hbsu hmu hassoc hone hcomm) i j =
      d.spacePresentationDescendedMul Px hP (τ i) (τ j) (τ (i + j)) (m i j) (hc i) (hu i)
        (hc j) (hu j) (hc (i + j)) (hu (i + j)) (hbt i j) (hbs i j) (hm i j) := by
  unfold modulesGradedAlgebraMul
  rw [mulSheaf_spacePresentationGradedAlgebra]
  exact Iso.hom_inv_id_assoc _ _

/-- The unit of `spacePresentationGradedAlgebra` is the descended unit. -/
theorem modulesGradedAlgebraOne_spacePresentationGradedAlgebra :
    modulesGradedAlgebraOne (d.spacePresentationGradedAlgebra Px hP τ hc hu m hbt hbs hm ν hbtu
        hbsu hmu hassoc hone hcomm) =
      d.spacePresentationDescendedUnit Px hP (τ 0) ν (hc 0) (hu 0) hbtu hbsu hmu :=
  d.oneHom_spacePresentationGradedAlgebra Px hP τ hc hu m hbt hbs hm ν hbtu hbsu hmu hassoc hone
    hcomm

end GradedReadings

section PullbackAlongReadings

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {XA XA' : AlgebraicSpaces B S hS} {PA PA' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {πA : PA ⟶ XA.obj} {πA' : PA' ⟶ XA'.obj} {dA : RelativeProjPoints B S hS πA}
  {dA' : RelativeProjPoints B S hS πA'} {hA : PA' ⟶ PA}
  (Px : Presentation B S hS XA.obj XA.property)
  (Px' : Presentation B S hS XA'.obj XA'.property) (hP : IsAlgebraicSpace B S hS PA)
  (hP' : IsAlgebraicSpace B S hS PA') {ℓ : Px'.U ⟶ Px.U} {ℓR : Px'.R ⟶ Px.R}
  (hℓt : ℓR ≫ Px.target = Px'.target ≫ ℓ) (hℓs : ℓR ≫ Px.source = Px'.source ≫ ℓ)
  (yU : dA'.fibre Px'.U Px'.toSpace ⟶ dA.fibre Px.U Px.toSpace)
  (hyU : dA'.LiesOverAlong dA hA yU ℓ)
  (yR : dA'.fibre Px'.R (relationPoint Px') ⟶ dA.fibre Px.R (relationPoint Px))
  (hyR : dA'.LiesOverAlong dA hA yR ℓR)
  {Mn : ℤ → (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj (dA.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory}
  (τ : ∀ n, quasicoherentPullbackObj B S hS (dA.spaceTarget Px hP) (Mn n) ⟶
    quasicoherentPullbackObj B S hS (dA.spaceSource Px hP) (Mn n))
  (hc : ∀ n, PresentationSchemeCocycle (dA.spacePresentation Px hP) (Mn n) (τ n))
  (hu : ∀ n, PresentationSchemeUnit (dA.spacePresentation Px hP) (Mn n) (τ n))
  (m : ∀ i j, quasicoherentTensorObj B S hS (dA.fibre Px.U Px.toSpace) (Mn i) (Mn j) ⟶
    Mn (i + j))
  (ν : quasicoherentUnitObj B S hS (dA.fibre Px.U Px.toSpace) ⟶ Mn 0)
  {Mn'' : ℤ → (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj (dA'.fibre Px'.U Px'.toSpace)).ringCatSheaf).FullSubcategory}
  (τ'' : ∀ n, quasicoherentPullbackObj B S hS (dA'.spaceTarget Px' hP') (Mn'' n) ⟶
    quasicoherentPullbackObj B S hS (dA'.spaceSource Px' hP') (Mn'' n))
  (hc'' : ∀ n, PresentationSchemeCocycle (dA'.spacePresentation Px' hP') (Mn'' n) (τ'' n))
  (hu'' : ∀ n, PresentationSchemeUnit (dA'.spacePresentation Px' hP') (Mn'' n) (τ'' n))
  (m'' : ∀ i j, quasicoherentTensorObj B S hS (dA'.fibre Px'.U Px'.toSpace) (Mn'' i) (Mn'' j) ⟶
    Mn'' (i + j))
  (ν'' : quasicoherentUnitObj B S hS (dA'.fibre Px'.U Px'.toSpace) ⟶ Mn'' 0)
  (Θ : ∀ n, quasicoherentPullbackObj B S hS yU (Mn n) ≅ Mn'' n)
  (hΘ : ∀ n, PullbackTransitionCompatible Px Px' hP hP' hℓt hℓs yU hyU yR hyR (τ n) (τ'' n)
    (Θ n))
  (hΘm : ∀ i j, QuasicoherentPullbackMulCompat yU (m i j) (Θ i) (Θ j) (Θ (i + j)) (m'' i j))
  (hΘu : QuasicoherentPullbackUnitCompat yU ν (Θ 0) ν'')
  (hbt : ∀ i j, RepresentedC3TensorCompat B S hS (dA.spaceTarget Px hP) (Mn i) (Mn j))
  (hbs : ∀ i j, RepresentedC3TensorCompat B S hS (dA.spaceSource Px hP) (Mn i) (Mn j))
  (hm : ∀ i j, dA.TransitionMulCompat Px hP (τ i) (τ j) (τ (i + j)) (m i j))
  (hbtu : RepresentedC3UnitCompat B S hS (dA.spaceTarget Px hP))
  (hbsu : RepresentedC3UnitCompat B S hS (dA.spaceSource Px hP))
  (hmu : dA.TransitionUnitCompat Px hP (τ 0) ν)
  (hassoc : QuasicoherentMulAssoc (dA.fibre Px.U Px.toSpace) m)
  (hone : QuasicoherentOneMul (dA.fibre Px.U Px.toSpace) m ν)
  (hcomm : QuasicoherentMulComm (dA.fibre Px.U Px.toSpace) m)
  (hbt'' : ∀ i j, RepresentedC3TensorCompat B S hS (dA'.spaceTarget Px' hP') (Mn'' i) (Mn'' j))
  (hbs'' : ∀ i j, RepresentedC3TensorCompat B S hS (dA'.spaceSource Px' hP') (Mn'' i) (Mn'' j))
  (hm'' : ∀ i j, dA'.TransitionMulCompat Px' hP' (τ'' i) (τ'' j) (τ'' (i + j)) (m'' i j))
  (hbtu'' : RepresentedC3UnitCompat B S hS (dA'.spaceTarget Px' hP'))
  (hbsu'' : RepresentedC3UnitCompat B S hS (dA'.spaceSource Px' hP'))
  (hmu'' : dA'.TransitionUnitCompat Px' hP' (τ'' 0) ν'')
  (hassoc'' : QuasicoherentMulAssoc (dA'.fibre Px'.U Px'.toSpace) m'')
  (hone'' : QuasicoherentOneMul (dA'.fibre Px'.U Px'.toSpace) m'' ν'')
  (hcomm'' : QuasicoherentMulComm (dA'.fibre Px'.U Px'.toSpace) m'')

/-- The comparison of attached modules along `yU` followed by `Θ_n^a`, as an isomorphism. -/
abbrev chartComparisonIso (n : ℤ) :
    (modulePullback B S hS (X := (presentationGroupoid (dA'.spacePresentation Px' hP')).objects)
        (Y := (presentationGroupoid (dA.spacePresentation Px hP)).objects)
        (representedSpaceMap B S hS (T' := (dA'.spacePresentation Px' hP').U) (T :=
            (dA.spacePresentation Px hP).U) yU)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS (dA.spacePresentation Px
            hP).U).functor.obj (Mn n)).obj ≅
      ((representedQuasicoherentSchemeEquivalence B S hS (dA'.spacePresentation Px'
          hP').U).functor.obj (Mn'' n)).obj :=
  modulePullbackRepresentedQuasicoherentIso B S hS (V := (dA'.spacePresentation Px' hP').U) (U :=
      (dA.spacePresentation Px hP).U) yU (Mn n) ≪≫
    (ObjectProperty.ι _).mapIso
      ((representedQuasicoherentSchemeEquivalence B S hS (dA'.spacePresentation Px'
          hP').U).functor.mapIso (Θ n))

/-- The comparison of attached modules followed by `Θ_n^a`, written out as it is read along the
represented morphism, is `chartComparisonIso`. -/
theorem chartComparison_eq (n : ℤ) :
    ((modulePullbackRepresentedQuasicoherentIso B S hS (V := (dA'.spacePresentation Px' hP').U) (U
        := (dA.spacePresentation Px hP).U) yU
          (Mn n)).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS (dA'.spacePresentation Px'
            hP').U).functor.map
          (Θ n).hom).hom :
      (modulePullback B S hS (representedSpaceMap B S hS (T' := (dA'.spacePresentation Px' hP').U)
          (T := (dA.spacePresentation Px hP).U) yU)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS (dA.spacePresentation Px
            hP).U).functor.obj (Mn n)).obj ⟶
      ((representedQuasicoherentSchemeEquivalence B S hS (dA'.spacePresentation Px'
          hP').U).functor.obj (Mn'' n)).obj) =
    ((chartComparisonIso Px Px' hP hP' yU Θ n).hom :
      (modulePullback B S hS (X := (presentationGroupoid (dA'.spacePresentation Px' hP')).objects)
        (Y := (presentationGroupoid (dA.spacePresentation Px hP)).objects)
        (representedSpaceMap B S hS (T' := (dA'.spacePresentation Px' hP').U) (T :=
            (dA.spacePresentation Px hP).U) yU)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS (dA.spacePresentation Px
            hP).U).functor.obj (Mn n)).obj ⟶
      ((representedQuasicoherentSchemeEquivalence B S hS (dA'.spacePresentation Px'
          hP').U).functor.obj (Mn'' n)).obj) :=
  rfl

include hΘm in
/-- The multiplications of the attached twists are read along the represented morphism
`yU` through the comparisons, as a heterogeneous equality. -/
theorem chartMulReadingHEq_representedSpaceMap (i j : ℤ) :
    ChartMulReadingHEq (representedSpaceMap B S hS (T' := (dA'.spacePresentation Px' hP').U) (T :=
        (dA.spacePresentation Px hP).U) yU)
        (Ki := ((representedQuasicoherentSchemeEquivalence B S hS (dA.spacePresentation Px
            hP).U).functor.obj (Mn i)).obj)
        (Kj := ((representedQuasicoherentSchemeEquivalence B S hS (dA.spacePresentation Px
            hP).U).functor.obj (Mn j)).obj)
        (Kk := ((representedQuasicoherentSchemeEquivalence B S hS (dA.spacePresentation Px
            hP).U).functor.obj (Mn (i + j))).obj)
        (KK := MonoidalCategoryStruct.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj
            (dA.spacePresentation Px hP).U)
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (dA.spacePresentation Px hP).U))
          ((representedQuasicoherentSchemeEquivalence B S hS (dA.spacePresentation Px
              hP).U).functor.obj (Mn i)).obj ((representedQuasicoherentSchemeEquivalence B S hS
                  (dA.spacePresentation Px hP).U).functor.obj (Mn j)).obj)
        (Li := ((representedQuasicoherentSchemeEquivalence B S hS (dA'.spacePresentation Px'
            hP').U).functor.obj (Mn'' i)).obj)
        (Lj := ((representedQuasicoherentSchemeEquivalence B S hS (dA'.spacePresentation Px'
            hP').U).functor.obj (Mn'' j)).obj)
        (Lk := ((representedQuasicoherentSchemeEquivalence B S hS (dA'.spacePresentation Px'
            hP').U).functor.obj (Mn'' (i + j))).obj)
        (representedTensorChartMul B S hS (m i j))
        ((modulePullbackRepresentedQuasicoherentIso B S hS (V := (dA'.spacePresentation Px' hP').U)
            (U := (dA.spacePresentation Px hP).U) yU
            (Mn i)).hom ≫
          ((representedQuasicoherentSchemeEquivalence B S hS (dA'.spacePresentation Px'
              hP').U).functor.map (Θ i).hom).hom)
        ((modulePullbackRepresentedQuasicoherentIso B S hS (V := (dA'.spacePresentation Px' hP').U)
            (U := (dA.spacePresentation Px hP).U) yU
            (Mn j)).hom ≫
          ((representedQuasicoherentSchemeEquivalence B S hS (dA'.spacePresentation Px'
              hP').U).functor.map (Θ j).hom).hom)
        ((modulePullbackRepresentedQuasicoherentIso B S hS (V := (dA'.spacePresentation Px' hP').U)
            (U := (dA.spacePresentation Px hP).U) yU
            (Mn (i + j))).hom ≫
          ((representedQuasicoherentSchemeEquivalence B S hS (dA'.spacePresentation Px'
              hP').U).functor.map
            (Θ (i + j)).hom).hom)
        (representedTensorChartMul B S hS (m'' i j)) :=
  heq_of_eq (modulePullback_map_representedTensorChartMul_comp B S hS
      (V := (dA'.spacePresentation Px' hP').U) (U := (dA.spacePresentation Px hP).U) yU (m i j)
          (m'' i j) (Θ i).hom (Θ j).hom (Θ (i + j)).hom
      (representedC3TensorCompat B S hS _ _ _)
      (@id (QuasicoherentPullbackMulCompat (V := (dA'.spacePresentation Px' hP').U) (U :=
          (dA.spacePresentation Px hP).U) yU (m i j) (Θ i) (Θ j)
        (Θ (i + j)) (m'' i j)) (hΘm i j)).eq)

include hΘm in
/-- The multiplications of the attached twists are read along `yU` through the comparisons. -/
theorem chartMulReading_chartComparison (i j : ℤ) :
    ChartMulReading (U'' := (presentationGroupoid (dA'.spacePresentation Px' hP')).objects)
      (U := (presentationGroupoid (dA.spacePresentation Px hP)).objects)
      (representedSpaceMap B S hS (T' := (dA'.spacePresentation Px' hP').U) (T :=
          (dA.spacePresentation Px hP).U) yU)
      (Ki := ((representedQuasicoherentSchemeEquivalence B S hS (dA.spacePresentation Px
          hP).U).functor.obj (Mn i)).obj)
      (Kj := ((representedQuasicoherentSchemeEquivalence B S hS (dA.spacePresentation Px
          hP).U).functor.obj (Mn j)).obj)
      (Kk := ((representedQuasicoherentSchemeEquivalence B S hS (dA.spacePresentation Px
          hP).U).functor.obj (Mn (i + j))).obj)
      (Li := ((representedQuasicoherentSchemeEquivalence B S hS (dA'.spacePresentation Px'
          hP').U).functor.obj (Mn'' i)).obj)
      (Lj := ((representedQuasicoherentSchemeEquivalence B S hS (dA'.spacePresentation Px'
          hP').U).functor.obj (Mn'' j)).obj)
      (Lk := ((representedQuasicoherentSchemeEquivalence B S hS (dA'.spacePresentation Px'
          hP').U).functor.obj (Mn'' (i + j))).obj)
      (representedTensorChartMul B S hS (m i j)) (chartComparisonIso Px Px' hP hP' yU Θ i).hom
      (chartComparisonIso Px Px' hP hP' yU Θ j).hom (chartComparisonIso Px Px' hP hP' yU Θ (i +
          j)).hom
      (representedTensorChartMul B S hS (m'' i j)) :=
  ChartMulReadingHEq.chartMulReading (ChartMulReadingHEq.of_eq
    (chartMulReadingHEq_representedSpaceMap Px Px' hP hP' yU m m'' Θ hΘm i j)
    (chartComparison_eq Px Px' hP hP' yU Θ i) (chartComparison_eq Px Px' hP hP' yU Θ j)
    (chartComparison_eq Px Px' hP hP' yU Θ (i + j)))

include hΘu in
/-- The units of the attached twists are read along `yU` through the comparison. -/
theorem chartUnitReading_chartComparison :
    ChartUnitReading (U'' := (presentationGroupoid (dA'.spacePresentation Px' hP')).objects)
      (U := (presentationGroupoid (dA.spacePresentation Px hP)).objects)
      (representedSpaceMap B S hS (T' := (dA'.spacePresentation Px' hP').U) (T :=
          (dA.spacePresentation Px hP).U) yU)
      (K := ((representedQuasicoherentSchemeEquivalence B S hS (dA.spacePresentation Px
          hP).U).functor.obj (Mn 0)).obj) (L := ((representedQuasicoherentSchemeEquivalence B S hS
              (dA'.spacePresentation Px' hP').U).functor.obj (Mn'' 0)).obj)
      (representedUnitChartHom B S hS ν) ((modulePullbackRepresentedQuasicoherentIso B S hS (V :=
          (dA'.spacePresentation Px' hP').U) (U := (dA.spacePresentation Px hP).U) yU
          (Mn 0)).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS (dA'.spacePresentation Px'
            hP').U).functor.map
          (Θ 0).hom).hom)
      (representedUnitChartHom B S hS ν'') :=
  ChartUnitReadingHEq.chartUnitReading (ChartUnitReadingHEq.of_eq
    (@id (ChartUnitReadingHEq (representedSpaceMap B S hS (T' := (dA'.spacePresentation Px' hP').U)
        (T := (dA.spacePresentation Px hP).U) yU)
      (O := SheafOfModules.unit (representedStructureRingSheaf B S hS (dA.spacePresentation Px
          hP).U))
      (K := ((representedQuasicoherentSchemeEquivalence B S hS (dA.spacePresentation Px
          hP).U).functor.obj (Mn 0)).obj) (L := ((representedQuasicoherentSchemeEquivalence B S hS
              (dA'.spacePresentation Px' hP').U).functor.obj (Mn'' 0)).obj)
      (representedUnitChartHom B S hS ν)
      ((modulePullbackRepresentedQuasicoherentIso B S hS (V := (dA'.spacePresentation Px' hP').U)
          (U := (dA.spacePresentation Px hP).U) yU
          (Mn 0)).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS (dA'.spacePresentation Px'
            hP').U).functor.map (Θ 0).hom).hom)
      (representedUnitChartHom B S hS ν''))
    (heq_of_eq (modulePullback_map_representedUnitChartHom_comp B S hS
      (V := (dA'.spacePresentation Px' hP').U) (U := (dA.spacePresentation Px hP).U) yU ν ν'' (Θ
          0).hom (representedC3UnitCompat B S hS _)
      (@id (QuasicoherentPullbackUnitCompat (V := (dA'.spacePresentation Px' hP').U) (U :=
          (dA.spacePresentation Px hP).U) yU ν (Θ 0) ν'') hΘu).eq)))
    (chartComparison_eq Px Px' hP hP' yU Θ 0))


include hΘ in
/-- The inverse image of `pullbackAlongDescendedIso` along the atlas is the identification on the
atlas, as an `AlgebraicGeometry.Space.AtlasChartReading`. -/
theorem atlasChartReading_pullbackAlongDescendedIso (n : ℤ) :
    AtlasChartReading (presentationAtlas (dA'.spacePresentation Px' hP'))
        (pullbackAlongDescendedIso Px Px' hP hP' hℓt hℓs yU hyU yR hyR (presentationDescendedModule
            (dA.spacePresentation Px hP) (Mn n) (τ n) (hc n) (hu n))
        (isQuasicoherentOnSite_presentationDescendedModule _ _ _ _ _) (τ n)
            (presentationDescendedModuleChartIso (dA.spacePresentation Px hP) (Mn n) (τ n) (hc n)
                (hu n))
        (presentationDescendedModuleChartIso_comm_spaceBaseDescent _ _ _ _) (τ'' n) (Θ n)
        (hΘ n) (hc'' n) (hu'' n)).hom.hom (presentationDescendedModuleChartIso
            (dA'.spacePresentation Px' hP') (Mn'' n) (τ'' n) (hc'' n) (hu'' n)).hom
      (presentationPullbackChartIso (dA'.spacePresentation Px' hP') (dA.spacePresentation Px hP)
          (ObjectProperty.homMk hA) yU
        (presentationAtlas_comp_homMk_of_liesOverAlong Px Px' hP hP' yU hyU)
            (presentationDescendedModule (dA.spacePresentation Px hP) (Mn n) (τ n) (hc n) (hu n))
                (presentationDescendedModuleChartIso (dA.spacePresentation Px hP) (Mn n) (τ n) (hc
                    n) (hu n))
        (Θ n)).hom :=
  pullbackAlongDescendedIso_spec Px Px' hP hP' hℓt hℓs yU hyU yR hyR _ _ (τ n) _ _ (τ'' n) (Θ n)
    (hΘ n) (hc'' n) (hu'' n)

/-- The identification on the atlas is read along the square of atlases. -/
theorem squareReading_presentationPullbackChartIso (n : ℤ) :
    SquareReading (presentationAtlas (dA'.spacePresentation Px' hP')) (presentationAtlas
        (dA.spacePresentation Px hP)) (ObjectProperty.homMk hA : (⟨PA', hP'⟩ : AlgebraicSpaces B S
            hS) ⟶ ⟨PA, hP⟩) (representedSpaceMap B S hS (T' := (dA'.spacePresentation Px' hP').U)
                (T := (dA.spacePresentation Px hP).U) yU)
      (presentationAtlas_comp_homMk_of_liesOverAlong Px Px' hP hP' yU hyU)
          (presentationDescendedModule (dA.spacePresentation Px hP) (Mn n) (τ n) (hc n) (hu n)).obj
      (presentationDescendedModuleChartIso (dA.spacePresentation Px hP) (Mn n) (τ n) (hc n) (hu
          n)).hom (chartComparisonIso Px Px' hP hP' yU Θ n).hom (presentationPullbackChartIso
              (dA'.spacePresentation Px' hP') (dA.spacePresentation Px hP) (ObjectProperty.homMk
                  hA) yU
        (presentationAtlas_comp_homMk_of_liesOverAlong Px Px' hP hP' yU hyU)
            (presentationDescendedModule (dA.spacePresentation Px hP) (Mn n) (τ n) (hc n) (hu n))
                (presentationDescendedModuleChartIso (dA.spacePresentation Px hP) (Mn n) (τ n) (hc
                    n) (hu n))
        (Θ n)).hom :=
  squareReading_of_iso_eq rfl

/-- Inverse image along the atlas of `P'` is injective on morphisms
`h^*D(M_i) ⊗ h^*D(M_j) ⟶ D(M''_k)`. -/
theorem atlasInjective_pullbackDescendedModule (i j k : ℤ) :
    AtlasInjective (presentationAtlas (dA'.spacePresentation Px' hP'))
      ((modulePullback B S hS (ObjectProperty.homMk hA : (⟨PA', hP'⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨PA, hP⟩)).obj (presentationDescendedModule (dA.spacePresentation Px hP) (Mn i) (τ i) (hc
              i) (hu i)).obj ⊗
        (modulePullback B S hS (ObjectProperty.homMk hA : (⟨PA', hP'⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨PA, hP⟩)).obj (presentationDescendedModule (dA.spacePresentation Px hP) (Mn j) (τ j)
                (hc j) (hu j)).obj) (presentationDescendedModule (dA'.spacePresentation Px' hP')
                    (Mn'' k) (τ'' k) (hc'' k) (hu'' k)).obj := by
  intro φ ψ hφψ
  have hq := fun n => isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (ObjectProperty.homMk hA : (⟨PA', hP'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨PA, hP⟩) _
    (isQuasicoherentOnSite_presentationDescendedModule (dA.spacePresentation Px hP) (Mn n) (τ n)
      (hc n) (hu n))
  exact @presentationAtlas_map_injective _ _ _ _ (dA'.spacePresentation Px' hP') _ _
    (@isQuasicoherentOnSite_tensorObj B S hS _ _ _ _ (hq i) (hq j))
    (isQuasicoherentOnSite_presentationDescendedModule _ _ _ _ _) _ _ hφψ


include hΘ hΘm in
/-- **The isomorphisms `h^*D(M_n) ≅ D(M''_n)` carry the descended multiplications to one
another**, through Stacks 03EL: this is checked on the atlas of `P'`, where both are the attached
multiplications, compared through `Θ`. -/
theorem pullbackMulCompat_pullbackAlongDescendedIso (i j : ℤ) :
    PullbackMulCompat (ObjectProperty.homMk hA : (⟨PA', hP'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨PA, hP⟩)
        (Ti := (presentationDescendedModule (dA.spacePresentation Px hP) (Mn i) (τ i) (hc i) (hu
            i)).obj) (Tj := (presentationDescendedModule (dA.spacePresentation Px hP) (Mn j) (τ j)
                (hc j) (hu j)).obj)
      (Tk := (presentationDescendedModule (dA.spacePresentation Px hP) (Mn (i + j)) (τ (i + j)) (hc
          (i + j)) (hu (i + j))).obj) (Gi := (presentationDescendedModule (dA'.spacePresentation
              Px' hP') (Mn'' i) (τ'' i) (hc'' i) (hu'' i)).obj) (Gj := (presentationDescendedModule
                  (dA'.spacePresentation Px' hP') (Mn'' j) (τ'' j) (hc'' j) (hu'' j)).obj)
      (Gk := (presentationDescendedModule (dA'.spacePresentation Px' hP') (Mn'' (i + j)) (τ'' (i +
          j)) (hc'' (i + j)) (hu'' (i + j))).obj) (dA.spacePresentationDescendedMul Px hP (τ i) (τ
              j) (τ (i + j)) (m i j) (hc i) (hu i) (hc j)
        (hu j) (hc (i + j)) (hu (i + j)) (hbt i j) (hbs i j) (hm i j))
      (pullbackAlongDescendedIso Px Px' hP hP' hℓt hℓs yU hyU yR hyR (presentationDescendedModule
          (dA.spacePresentation Px hP) (Mn i) (τ i) (hc i) (hu i))
        (isQuasicoherentOnSite_presentationDescendedModule _ _ _ _ _) (τ i)
            (presentationDescendedModuleChartIso (dA.spacePresentation Px hP) (Mn i) (τ i) (hc i)
                (hu i))
        (presentationDescendedModuleChartIso_comm_spaceBaseDescent _ _ _ _) (τ'' i) (Θ i)
        (hΘ i) (hc'' i) (hu'' i)).hom.hom
      (pullbackAlongDescendedIso Px Px' hP hP' hℓt hℓs yU hyU yR hyR (presentationDescendedModule
          (dA.spacePresentation Px hP) (Mn j) (τ j) (hc j) (hu j))
        (isQuasicoherentOnSite_presentationDescendedModule _ _ _ _ _) (τ j)
            (presentationDescendedModuleChartIso (dA.spacePresentation Px hP) (Mn j) (τ j) (hc j)
                (hu j))
        (presentationDescendedModuleChartIso_comm_spaceBaseDescent _ _ _ _) (τ'' j) (Θ j)
        (hΘ j) (hc'' j) (hu'' j)).hom.hom
      (pullbackAlongDescendedIso Px Px' hP hP' hℓt hℓs yU hyU yR hyR (presentationDescendedModule
          (dA.spacePresentation Px hP) (Mn (i + j)) (τ (i + j)) (hc (i + j)) (hu (i + j)))
        (isQuasicoherentOnSite_presentationDescendedModule _ _ _ _ _) (τ (i + j))
            (presentationDescendedModuleChartIso (dA.spacePresentation Px hP) (Mn (i + j)) (τ (i +
                j)) (hc (i + j)) (hu (i + j)))
        (presentationDescendedModuleChartIso_comm_spaceBaseDescent _ _ _ _) (τ'' (i + j)) (Θ (i +
            j))
        (hΘ (i + j)) (hc'' (i + j)) (hu'' (i + j))).hom.hom
      (dA'.spacePresentationDescendedMul Px' hP' (τ'' i) (τ'' j) (τ'' (i + j)) (m'' i j) (hc'' i)
        (hu'' i) (hc'' j) (hu'' j) (hc'' (i + j)) (hu'' (i + j)) (hbt'' i j) (hbs'' i j) (hm'' i
            j)) :=
  pullbackMulCompat_of_chartReadings _ _ _ _ _ _ _ _ _ _
    (chartMulReading_spacePresentationDescendedMul dA Px hP _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _
    (chartMulReading_chartComparison Px Px' hP hP' yU m m'' Θ hΘm i j) _ _ _ _
    (chartMulReading_spacePresentationDescendedMul dA' Px' hP' _ _ _ _ _ _ _ _ _ _ _ _ _)
    _ _ _ _ _ _
    (atlasChartReading_pullbackAlongDescendedIso Px Px' hP hP' hℓt hℓs yU hyU yR hyR τ hc hu τ''
      hc'' hu'' Θ hΘ i)
    (atlasChartReading_pullbackAlongDescendedIso Px Px' hP hP' hℓt hℓs yU hyU yR hyR τ hc hu τ''
      hc'' hu'' Θ hΘ j)
    (atlasChartReading_pullbackAlongDescendedIso Px Px' hP hP' hℓt hℓs yU hyU yR hyR τ hc hu τ''
      hc'' hu'' Θ hΘ (i + j))
    (squareReading_presentationPullbackChartIso Px Px' hP hP' yU hyU τ hc hu Θ i)
    (squareReading_presentationPullbackChartIso Px Px' hP hP' yU hyU τ hc hu Θ j)
    (squareReading_presentationPullbackChartIso Px Px' hP hP' yU hyU τ hc hu Θ (i + j))
    (atlasInjective_pullbackDescendedModule Px Px' hP hP' τ hc hu τ'' hc'' hu'' i j (i + j))


/-- Inverse image along the atlas of `P'` is injective on morphisms `𝒪 ⟶ D(M''_0)`. -/
theorem atlasInjective_unit_presentationDescendedModule :
    AtlasInjective (presentationAtlas (dA'.spacePresentation Px' hP'))
      (SheafOfModules.unit (structureRingSheaf B S hS ⟨PA', hP'⟩)) (presentationDescendedModule
          (dA'.spacePresentation Px' hP') (Mn'' 0) (τ'' 0) (hc'' 0) (hu'' 0)).obj := by
  intro φ ψ hφψ
  exact @presentationAtlas_map_injective _ _ _ _ (dA'.spacePresentation Px' hP') _ _
    (SheafOfModules.isQuasicoherentOnSite_unit _)
    (isQuasicoherentOnSite_presentationDescendedModule _ _ _ _ _) _ _ hφψ

include hΘ hΘu in
/-- **The isomorphism `h^*D(M_0) ≅ D(M''_0)` carries the descended unit to the descended unit**,
through Stacks 03LU: this is checked on the atlas of `P'`, where both are the attached units,
compared through `Θ_0`. -/
theorem pullbackUnitCompat_pullbackAlongDescendedIso :
    PullbackUnitCompat (ObjectProperty.homMk hA : (⟨PA', hP'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨PA, hP⟩)
        (T := (presentationDescendedModule (dA.spacePresentation Px hP) (Mn 0) (τ 0) (hc 0) (hu
            0)).obj) (G := (presentationDescendedModule (dA'.spacePresentation Px' hP') (Mn'' 0)
                (τ'' 0) (hc'' 0) (hu'' 0)).obj) (dA.spacePresentationDescendedUnit Px hP (τ 0) ν
                    (hc 0) (hu 0) hbtu hbsu hmu)
      (pullbackAlongDescendedIso Px Px' hP hP' hℓt hℓs yU hyU yR hyR (presentationDescendedModule
          (dA.spacePresentation Px hP) (Mn 0) (τ 0) (hc 0) (hu 0))
        (isQuasicoherentOnSite_presentationDescendedModule _ _ _ _ _) (τ 0)
            (presentationDescendedModuleChartIso (dA.spacePresentation Px hP) (Mn 0) (τ 0) (hc 0)
                (hu 0))
        (presentationDescendedModuleChartIso_comm_spaceBaseDescent _ _ _ _) (τ'' 0) (Θ 0)
        (hΘ 0) (hc'' 0) (hu'' 0)).hom.hom (dA'.spacePresentationDescendedUnit Px' hP' (τ'' 0) ν''
            (hc'' 0) (hu'' 0) hbtu'' hbsu'' hmu'') :=
  pullbackUnitCompat_of_chartReadings _ _ _ _ _ _ _ _
    (chartUnitReading_spacePresentationDescendedUnit dA Px hP _ _ _ _ _ _ _) _ _
    (chartUnitReading_chartComparison Px Px' hP hP' yU ν ν'' Θ hΘu) _ _
    (chartUnitReading_spacePresentationDescendedUnit dA' Px' hP' _ _ _ _ _ _ _) _ _
    (atlasChartReading_pullbackAlongDescendedIso Px Px' hP hP' hℓt hℓs yU hyU yR hyR τ hc hu τ''
      hc'' hu'' Θ hΘ 0)
    (squareReading_presentationPullbackChartIso Px Px' hP hP' yU hyU τ hc hu Θ 0)
    (atlasInjective_unit_presentationDescendedModule Px' hP' τ'' hc'' hu'')


/-- The isomorphism `h^*D(M_n) ≅ D(M''_n)` of
`AlgebraicGeometry.Space.RelativeProjPoints.pullbackAlongDescendedIso`,
as an isomorphism of `𝒪_{P'}`-modules. -/
abbrev pullbackAlongDescendedModuleIso (n : ℤ) :
    (modulePullback B S hS (ObjectProperty.homMk hA : (⟨PA', hP'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨PA,
        hP⟩)).obj ((dA.spacePresentationGradedAlgebra Px hP τ hc hu m hbt hbs hm ν hbtu hbsu hmu
            hassoc hone
        hcomm).piece n) ≅ (dA'.spacePresentationGradedAlgebra Px' hP' τ'' hc'' hu'' m'' hbt'' hbs''
            hm'' ν'' hbtu''
        hbsu'' hmu'' hassoc'' hone'' hcomm'').piece n :=
  ((ObjectProperty.ι _).mapIso (pullbackAlongDescendedIso Px Px' hP hP' hℓt hℓs yU
        hyU yR hyR (presentationDescendedModule (dA.spacePresentation Px hP) (Mn n) (τ n) (hc n)
            (hu n))
        (isQuasicoherentOnSite_presentationDescendedModule _ _ _ _ _) (τ n)
        (presentationDescendedModuleChartIso (dA.spacePresentation Px hP) (Mn n) (τ n) (hc n) (hu
            n))
        (presentationDescendedModuleChartIso_comm_spaceBaseDescent _ _ _ _) (τ'' n) (Θ n)
        (hΘ n) (hc'' n) (hu'' n)) : _)

include hℓt hℓs hyU hyR hΘ hΘm in
/-- The isomorphisms `h^*D(M_n) ≅ D(M''_n)` carry the multiplication of the descended graded
algebra to the multiplication of the descended graded algebra. -/
theorem pullbackMulCompat_pullbackAlongDescendedModuleIso (i j : ℤ) :
    PullbackMulCompat (ObjectProperty.homMk hA : (⟨PA', hP'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨PA, hP⟩)
        (modulesGradedAlgebraMul (dA.spacePresentationGradedAlgebra Px hP τ hc hu m hbt hbs hm ν
            hbtu hbsu hmu hassoc hone
        hcomm) i j)
      (pullbackAlongDescendedModuleIso Px Px' hP hP' hℓt hℓs yU hyU yR hyR τ hc hu m ν τ'' hc'' hu''
        m'' ν'' Θ hΘ hbt hbs hm hbtu hbsu hmu hassoc hone hcomm hbt'' hbs'' hm'' hbtu'' hbsu'' hmu''
        hassoc'' hone'' hcomm'' i).hom
      (pullbackAlongDescendedModuleIso Px Px' hP hP' hℓt hℓs yU hyU yR hyR τ hc hu m ν τ'' hc'' hu''
        m'' ν'' Θ hΘ hbt hbs hm hbtu hbsu hmu hassoc hone hcomm hbt'' hbs'' hm'' hbtu'' hbsu'' hmu''
        hassoc'' hone'' hcomm'' j).hom
      (pullbackAlongDescendedModuleIso Px Px' hP hP' hℓt hℓs yU hyU yR hyR τ hc hu m ν τ'' hc'' hu''
        m'' ν'' Θ hΘ hbt hbs hm hbtu hbsu hmu hassoc hone hcomm hbt'' hbs'' hm'' hbtu'' hbsu'' hmu''
        hassoc'' hone'' hcomm'' (i + j)).hom
      (modulesGradedAlgebraMul (dA'.spacePresentationGradedAlgebra Px' hP' τ'' hc'' hu'' m'' hbt''
          hbs'' hm'' ν'' hbtu''
        hbsu'' hmu'' hassoc'' hone'' hcomm'') i j) := by
  rw [modulesGradedAlgebraMul_spacePresentationGradedAlgebra,
    modulesGradedAlgebraMul_spacePresentationGradedAlgebra]
  exact pullbackMulCompat_pullbackAlongDescendedIso Px Px' hP hP' hℓt hℓs yU hyU yR hyR τ hc hu m
    τ'' hc'' hu'' m'' Θ hΘ hΘm hbt hbs hm hbt'' hbs'' hm'' i j

include hℓt hℓs hyU hyR hΘ hΘu in
/-- The isomorphism `h^*D(M_0) ≅ D(M''_0)` carries the unit of the descended graded algebra to
the unit of the descended graded algebra. -/
theorem pullbackUnitCompat_pullbackAlongDescendedModuleIso :
    PullbackUnitCompat (ObjectProperty.homMk hA : (⟨PA', hP'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨PA, hP⟩)
        (modulesGradedAlgebraOne (dA.spacePresentationGradedAlgebra Px hP τ hc hu m hbt hbs hm ν
            hbtu hbsu hmu hassoc hone
        hcomm))
      (pullbackAlongDescendedModuleIso Px Px' hP hP' hℓt hℓs yU hyU yR hyR τ hc hu m ν τ'' hc'' hu''
        m'' ν'' Θ hΘ hbt hbs hm hbtu hbsu hmu hassoc hone hcomm hbt'' hbs'' hm'' hbtu'' hbsu'' hmu''
        hassoc'' hone'' hcomm'' 0).hom
      (modulesGradedAlgebraOne (dA'.spacePresentationGradedAlgebra Px' hP' τ'' hc'' hu'' m'' hbt''
          hbs'' hm'' ν'' hbtu''
        hbsu'' hmu'' hassoc'' hone'' hcomm'')) := by
  rw [modulesGradedAlgebraOne_spacePresentationGradedAlgebra,
    modulesGradedAlgebraOne_spacePresentationGradedAlgebra]
  exact pullbackUnitCompat_pullbackAlongDescendedIso Px Px' hP hP' hℓt hℓs yU hyU yR hyR τ hc hu ν
    τ'' hc'' hu'' ν'' Θ hΘ hΘu hbtu hbsu hmu hbtu'' hbsu'' hmu''

end PullbackAlongReadings

end RelativeProjPoints

end AlgebraicGeometry.Space

end
