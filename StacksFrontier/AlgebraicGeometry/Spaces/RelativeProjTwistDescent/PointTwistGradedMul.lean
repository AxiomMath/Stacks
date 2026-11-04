module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PointTwistGraded

/-!
# The base change identification of `𝒪_P(n)` is multiplicative

In Situation 0849 let `P = Proj_X(𝒜)` be the relative homogeneous spectrum of Stacks 084B with
twists `𝒪_P(n)` (Stacks 084D), and let `f : T ⟶ X` be a scheme point.  This file shows that the
identifications along a morphism from a representable algebraic space of modules descended from a
presentation (Stacks 03M3), described on the atlas by chart identifications, carry
multiplications and units read on the charts to multiplications and units.  This is the step of
the base change clause of Stacks 084D which identifies the base change of `⨁_n 𝒪_P(n)` with the
graded algebra of Stacks 01NR, and not only its pieces.

## Main results

* `AlgebraicGeometry.Space.modulePullbackTensorIso_inv_comp_map_comp_of_ofIsoYoneda_spec`,
  `AlgebraicGeometry.Space.modulePullbackUnitIso_inv_comp_map_comp_of_ofIsoYoneda_spec`: **the
  identifications `h^*𝒯_n ≅ N_n^a` described on the atlas carry multiplications and units to
  multiplications and units.**
* `AlgebraicGeometry.Space.RelativeProjSituation.fibreToSpaceTwistModuleIso_unit`: **the base
  change identification of Stacks 084D carries the unit of the twists of `P` to the unit of the
  twists of Stacks 01NR on `T ×_X P`.**

## Implementation notes

Every input enters through a lemma stated at free variables in which each spelling of a space, an
object or a morphism is a variable, related to the canonical one by an equation proved by `rfl`
in the instance (the `…_of_heq` lemmas); no equation between two spellings of a composite is
checked anywhere else.

## References

* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

section Spelled

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {V U : BigFppfOver B S hS} (g : V ⟶ U)

/-- `AlgebraicGeometry.Space.modulePullback_map_representedTensorChartMul_comp` with every
ingredient given in its own spelling: the morphism `a` of algebraic spaces, the objects and the
chart readings are variables, equal (heterogeneously) to the represented ones. -/
theorem modulePullback_map_representedTensorChartMul_comp_of_heq
    {M N K : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    {M' N' K' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf).FullSubcategory}
    (m : quasicoherentTensorObj B S hS U M N ⟶ K) (m' : quasicoherentTensorObj B S hS V M' N' ⟶ K')
    (ΘM : quasicoherentPullbackObj B S hS g M ⟶ M') (ΘN : quasicoherentPullbackObj B S hS g N ⟶ N')
    (ΘK : quasicoherentPullbackObj B S hS g K ⟶ K')
    (hb : RepresentedC3TensorCompat B S hS g M N)
    (hm : (quasicoherentPullbackTensorIso B S hS g M N).inv ≫
        quasicoherentPullbackMap B S hS g m ≫ ΘK =
      quasicoherentTensorHom B S hS V ΘM ΘN ≫ m')
    {X Y : AlgebraicSpaces B S hS} (a : X ⟶ Y)
    {Gi Gj Gk : Modules.{u, u} B S hS Y.1 Y.2} {Li Lj Lk : Modules.{u, u} B S hS X.1 X.2}
    (ρi : (modulePullback B S hS a).obj Gi ⟶ Li) (ρj : (modulePullback B S hS a).obj Gj ⟶ Lj)
    (ρk : (modulePullback B S hS a).obj Gk ⟶ Lk) (μG : Gi ⊗ Gj ⟶ Gk) (μL : Li ⊗ Lj ⟶ Lk)
    (hX : X = ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
    (hY : Y = ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    (ha : HEq a (representedSpaceMap B S hS g))
    (hGi : HEq Gi ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj)
    (hGj : HEq Gj ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj N).obj)
    (hGk : HEq Gk ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj K).obj)
    (hLi : HEq Li ((representedQuasicoherentSchemeEquivalence B S hS V).functor.obj M').obj)
    (hLj : HEq Lj ((representedQuasicoherentSchemeEquivalence B S hS V).functor.obj N').obj)
    (hLk : HEq Lk ((representedQuasicoherentSchemeEquivalence B S hS V).functor.obj K').obj)
    (hρi : HEq ρi ((modulePullbackRepresentedQuasicoherentIso B S hS g M).hom ≫
      ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map ΘM).hom))
    (hρj : HEq ρj ((modulePullbackRepresentedQuasicoherentIso B S hS g N).hom ≫
      ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map ΘN).hom))
    (hρk : HEq ρk ((modulePullbackRepresentedQuasicoherentIso B S hS g K).hom ≫
      ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map ΘK).hom))
    (hμG : HEq μG (representedTensorChartMul B S hS m))
    (hμL : HEq μL (representedTensorChartMul B S hS m')) :
    (modulePullback B S hS a).map μG ≫ ρk =
      (modulePullbackTensorIso B S hS a Gi Gj).hom ≫ (ρi ⊗ₘ ρj) ≫ μL := by
  subst hX hY ha hGi hGj hGk hLi hLj hLk hρi hρj hρk hμG hμL
  exact modulePullback_map_representedTensorChartMul_comp B S hS g m m' ΘM ΘN ΘK hb hm

/-- `AlgebraicGeometry.Space.modulePullback_map_representedUnitChartHom_comp` with every ingredient
given in its own spelling, as in
`AlgebraicGeometry.Space.modulePullback_map_representedTensorChartMul_comp_of_heq`. -/
theorem modulePullback_map_representedUnitChartHom_comp_of_heq
    {K : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    {K' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf).FullSubcategory}
    (ν : quasicoherentUnitObj B S hS U ⟶ K) (ν' : quasicoherentUnitObj B S hS V ⟶ K')
    (ΘK : quasicoherentPullbackObj B S hS g K ⟶ K')
    (hb : RepresentedC3UnitCompat B S hS g)
    (hν : (quasicoherentPullbackUnitIso B S hS g).inv ≫ quasicoherentPullbackMap B S hS g ν ≫ ΘK =
      ν')
    {X Y : AlgebraicSpaces B S hS} (a : X ⟶ Y)
    {G : Modules.{u, u} B S hS Y.1 Y.2} {L : Modules.{u, u} B S hS X.1 X.2}
    (ρ : (modulePullback B S hS a).obj G ⟶ L)
    (νG : SheafOfModules.unit (structureRingSheaf B S hS Y) ⟶ G)
    (νL : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶ L)
    (hX : X = ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
    (hY : Y = ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    (ha : HEq a (representedSpaceMap B S hS g))
    (hG : HEq G ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj K).obj)
    (hL : HEq L ((representedQuasicoherentSchemeEquivalence B S hS V).functor.obj K').obj)
    (hρ : HEq ρ ((modulePullbackRepresentedQuasicoherentIso B S hS g K).hom ≫
      ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map ΘK).hom))
    (hνG : HEq νG (representedUnitChartHom B S hS ν))
    (hνL : HEq νL (representedUnitChartHom B S hS ν')) :
    (modulePullback B S hS a).map νG ≫ ρ = (modulePullbackUnitIso B S hS a).hom ≫ νL := by
  subst hX hY ha hG hL hρ hνG hνL
  exact modulePullback_map_representedUnitChartHom_comp B S hS g ν ν' ΘK hb hν

end Spelled


section Eta

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A unit square `h^*𝒪 ≅ 𝒪`, `h^*ν`, `e` transported along equations of the two spaces, the
morphism `h` and the data; used to pass between two spellings of the spaces of `h`. -/
theorem modulePullbackUnitIso_inv_comp_map_comp_eq_of_heq {Z Z₂ X X₂ : AlgebraicSpaces B S hS}
    {h₂ : Z₂ ⟶ X₂} {T₂ : Modules.{u, u} B S hS X₂.1 X₂.2}
    {ν₂ : SheafOfModules.unit (structureRingSheaf B S hS X₂) ⟶ T₂}
    {G₂ : Modules.{u, u} B S hS Z₂.1 Z₂.2} {e₂ : (modulePullback B S hS h₂).obj T₂ ⟶ G₂}
    {νG₂ : SheafOfModules.unit (structureRingSheaf B S hS Z₂) ⟶ G₂}
    (H : (modulePullbackUnitIso B S hS h₂).inv ≫ (modulePullback B S hS h₂).map ν₂ ≫ e₂ = νG₂)
    (h : Z ⟶ X) {T : Modules.{u, u} B S hS X.1 X.2}
    (ν : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶ T)
    {G : Modules.{u, u} B S hS Z.1 Z.2} (e : (modulePullback B S hS h).obj T ⟶ G)
    (νG : SheafOfModules.unit (structureRingSheaf B S hS Z) ⟶ G)
    (hZ : Z₂ = Z) (hX : X₂ = X) (hh : HEq h₂ h) (hT : HEq T₂ T) (hν : HEq ν₂ ν) (hG : HEq G₂ G)
    (he : HEq e₂ e) (hνG : HEq νG₂ νG) :
    (modulePullbackUnitIso B S hS h).inv ≫ (modulePullback B S hS h).map ν ≫ e = νG := by
  subst hZ hX hh hT hν hG he hνG
  exact H

/-- A multiplication square through Stacks 03EL transported along equations of the two spaces,
the morphism `h` and the data; used to pass between two spellings of the spaces of `h`. -/
theorem modulePullbackTensorIso_inv_comp_map_comp_eq_of_heq {Z Z₂ X X₂ : AlgebraicSpaces B S hS}
    {h₂ : Z₂ ⟶ X₂} {T₁' T₂' T₃' : Modules.{u, u} B S hS X₂.1 X₂.2} {μ' : T₁' ⊗ T₂' ⟶ T₃'}
    {G₁' G₂' G₃' : Modules.{u, u} B S hS Z₂.1 Z₂.2}
    {e₁' : (modulePullback B S hS h₂).obj T₁' ⟶ G₁'} {e₂' : (modulePullback B S hS h₂).obj T₂' ⟶
        G₂'}
    {e₃' : (modulePullback B S hS h₂).obj T₃' ⟶ G₃'} {μG' : G₁' ⊗ G₂' ⟶ G₃'}
    (H : (modulePullbackTensorIso B S hS h₂ T₁' T₂').inv ≫ (modulePullback B S hS h₂).map μ' ≫ e₃' =
      (e₁' ⊗ₘ e₂') ≫ μG')
    (h : Z ⟶ X) {T₁ T₂ T₃ : Modules.{u, u} B S hS X.1 X.2} (μ : T₁ ⊗ T₂ ⟶ T₃)
    {G₁ G₂ G₃ : Modules.{u, u} B S hS Z.1 Z.2}
    (e₁ : (modulePullback B S hS h).obj T₁ ⟶ G₁) (e₂ : (modulePullback B S hS h).obj T₂ ⟶ G₂)
    (e₃ : (modulePullback B S hS h).obj T₃ ⟶ G₃) (μG : G₁ ⊗ G₂ ⟶ G₃)
    (hZ : Z₂ = Z) (hX : X₂ = X) (hh : HEq h₂ h) (hT₁ : HEq T₁' T₁) (hT₂ : HEq T₂' T₂)
    (hT₃ : HEq T₃' T₃) (hμ : HEq μ' μ) (hG₁ : HEq G₁' G₁) (hG₂ : HEq G₂' G₂) (hG₃ : HEq G₃' G₃)
    (he₁ : HEq e₁' e₁) (he₂ : HEq e₂' e₂) (he₃ : HEq e₃' e₃) (hμG : HEq μG' μG) :
    (modulePullbackTensorIso B S hS h T₁ T₂).inv ≫ (modulePullback B S hS h).map μ ≫ e₃ =
      (e₁ ⊗ₘ e₂) ≫ μG := by
  subst hZ hX hh hT₁ hT₂ hT₃ hμ hG₁ hG₂ hG₃ he₁ he₂ he₃ hμG
  exact H

/-- An equation `c''^*e ≫ ρ = χ` transported along equations of the spaces, the morphisms and the
data; used to pass a chart description between two spellings of the spaces of `h`. -/
theorem modulePullback_map_comp_eq_of_heq {Z Z₂ X X₂ U'' : AlgebraicSpaces B S hS}
    {c''₁ : U'' ⟶ Z} {h : Z ⟶ X} {T : Modules.{u, u} B S hS X.1 X.2}
    {G : Modules.{u, u} B S hS Z.1 Z.2} {L₁ : Modules.{u, u} B S hS U''.1 U''.2}
    {e : (modulePullback B S hS h).obj T ⟶ G} {ρ₁ : (modulePullback B S hS c''₁).obj G ⟶ L₁}
    {χ₁ : (modulePullback B S hS c''₁).obj ((modulePullback B S hS h).obj T) ⟶ L₁}
    (H : (modulePullback B S hS c''₁).map e ≫ ρ₁ = χ₁)
    (c'' : U'' ⟶ Z₂) (h₂ : Z₂ ⟶ X₂) {T₂ : Modules.{u, u} B S hS X₂.1 X₂.2}
    {G₂ : Modules.{u, u} B S hS Z₂.1 Z₂.2} {L : Modules.{u, u} B S hS U''.1 U''.2}
    (e₂ : (modulePullback B S hS h₂).obj T₂ ⟶ G₂)
    (ρ : (modulePullback B S hS c'').obj G₂ ⟶ L)
    (χ : (modulePullback B S hS c'').obj ((modulePullback B S hS h₂).obj T₂) ⟶ L)
    (hZ : Z₂ = Z) (hX : X₂ = X) (hc : HEq c'' c''₁) (hh : HEq h₂ h) (hT : HEq T₂ T)
    (hG : HEq G₂ G) (hL : L = L₁) (he : HEq e₂ e) (hρ : HEq ρ ρ₁) (hχ : HEq χ χ₁) :
    (modulePullback B S hS c'').map e₂ ≫ ρ = χ := by
  subst hZ hX hc hh hT hG hL he hρ hχ
  exact H

/-- The inverse image along the atlas of a presentation is injective on morphisms out of a tensor
product of two inverse images of quasi-coherent modules into a quasi-coherent module. -/
theorem presentationAtlas_map_injective_of_tensorObj {X Y : AlgebraicSpaces B S hS}
    (P : Presentation B S hS X.obj X.property)
    (h : (⟨X.obj, X.property⟩ : AlgebraicSpaces B S hS) ⟶ Y)
    {T₁ T₂ : Modules.{u, u} B S hS Y.1 Y.2} (hT₁ : T₁.IsQuasicoherentOnSite)
    (hT₂ : T₂.IsQuasicoherentOnSite)
    {G : Modules.{u, u} B S hS (⟨X.obj, X.property⟩ : AlgebraicSpaces B S hS).1
      (⟨X.obj, X.property⟩ : AlgebraicSpaces B S hS).2}
    (hG : G.IsQuasicoherentOnSite) :
    ∀ φ ψ : (modulePullback B S hS h).obj T₁ ⊗ (modulePullback B S hS h).obj T₂ ⟶ G,
      (modulePullback B S hS (presentationAtlas P)).map φ =
        (modulePullback B S hS (presentationAtlas P)).map ψ → φ = ψ :=
  fun _ _ hφψ => @presentationAtlas_map_injective _ _ _ _ P _ _
    (@isQuasicoherentOnSite_tensorObj B S hS _ _ _ _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _ hT₁)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _ hT₂))
    hG _ _ hφψ

end Eta

section SchemeAdapter

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A scheme-level multiplication square through Stacks 03EL transported along equations of the
schemes, the morphism and the data; used to pass between two spellings of the schemes. -/
theorem quasicoherentPullbackTensorIso_inv_comp_map_comp_eq_of_heq {U U₂ V V₂ : BigFppfOver B S hS}
    {y : V ⟶ U}
    {M N K : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    {M' N' K' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf).FullSubcategory}
    {m : quasicoherentTensorObj B S hS U M N ⟶ K} {m' : quasicoherentTensorObj B S hS V M' N' ⟶ K'}
    {ΘM : quasicoherentPullbackObj B S hS y M ⟶ M'} {ΘN : quasicoherentPullbackObj B S hS y N ⟶ N'}
    {ΘK : quasicoherentPullbackObj B S hS y K ⟶ K'}
    (H : (quasicoherentPullbackTensorIso B S hS y M N).inv ≫
        quasicoherentPullbackMap B S hS y m ≫ ΘK =
      quasicoherentTensorHom B S hS V ΘM ΘN ≫ m')
    {y₂ : V₂ ⟶ U₂}
    {M₂ N₂ K₂ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U₂).ringCatSheaf).FullSubcategory}
    {M'₂ N'₂ K'₂ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj V₂).ringCatSheaf).FullSubcategory}
    {m₂ : quasicoherentTensorObj B S hS U₂ M₂ N₂ ⟶ K₂}
    {m'₂ : quasicoherentTensorObj B S hS V₂ M'₂ N'₂ ⟶ K'₂}
    {ΘM₂ : quasicoherentPullbackObj B S hS y₂ M₂ ⟶ M'₂}
    {ΘN₂ : quasicoherentPullbackObj B S hS y₂ N₂ ⟶ N'₂}
    {ΘK₂ : quasicoherentPullbackObj B S hS y₂ K₂ ⟶ K'₂}
    (hU : U₂ = U) (hV : V₂ = V) (hy : HEq y₂ y) (hM : HEq M₂ M) (hN : HEq N₂ N) (hK : HEq K₂ K)
    (hM' : HEq M'₂ M') (hN' : HEq N'₂ N') (hK' : HEq K'₂ K') (hm : HEq m₂ m) (hm' : HEq m'₂ m')
    (hΘM : HEq ΘM₂ ΘM) (hΘN : HEq ΘN₂ ΘN) (hΘK : HEq ΘK₂ ΘK) :
    (quasicoherentPullbackTensorIso B S hS y₂ M₂ N₂).inv ≫
        quasicoherentPullbackMap B S hS y₂ m₂ ≫ ΘK₂ =
      quasicoherentTensorHom B S hS V₂ ΘM₂ ΘN₂ ≫ m'₂ := by
  subst hU hV hy hM hN hK hM' hN' hK' hm hm' hΘM hΘN hΘK
  exact H

/-- A scheme-level unit square through Stacks 03LU transported along equations of the schemes, the
morphism and the data; used to pass between two spellings of the schemes. -/
theorem quasicoherentPullbackUnitIso_inv_comp_map_comp_eq_of_heq {U U₂ V V₂ : BigFppfOver B S hS}
    {y : V ⟶ U}
    {K : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    {K' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf).FullSubcategory}
    {ν : quasicoherentUnitObj B S hS U ⟶ K} {ν' : quasicoherentUnitObj B S hS V ⟶ K'}
    {ΘK : quasicoherentPullbackObj B S hS y K ⟶ K'}
    (H : (quasicoherentPullbackUnitIso B S hS y).inv ≫ quasicoherentPullbackMap B S hS y ν ≫ ΘK =
      ν')
    {y₂ : V₂ ⟶ U₂}
    {K₂ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U₂).ringCatSheaf).FullSubcategory}
    {K'₂ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj V₂).ringCatSheaf).FullSubcategory}
    {ν₂ : quasicoherentUnitObj B S hS U₂ ⟶ K₂} {ν'₂ : quasicoherentUnitObj B S hS V₂ ⟶ K'₂}
    {ΘK₂ : quasicoherentPullbackObj B S hS y₂ K₂ ⟶ K'₂}
    (hU : U₂ = U) (hV : V₂ = V) (hy : HEq y₂ y) (hK : HEq K₂ K) (hK' : HEq K'₂ K')
    (hν : HEq ν₂ ν) (hν' : HEq ν'₂ ν') (hΘK : HEq ΘK₂ ΘK) :
    (quasicoherentPullbackUnitIso B S hS y₂).inv ≫ quasicoherentPullbackMap B S hS y₂ ν₂ ≫ ΘK₂ =
      ν'₂ := by
  subst hU hV hy hK hK' hν hν' hΘK
  exact H

end SchemeAdapter

section ChartHom

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X'' X : AlgebraicSpaces B S hS} (P'' : Presentation B S hS X''.obj X''.property)
  (P : Presentation B S hS X.obj X.property) (h : X'' ⟶ X) (yU : P''.U ⟶ P.U)
  (hY : presentationAtlas P'' ≫ h = representedSpaceMap B S hS yU ≫ presentationAtlas P)
  (T : QuasicoherentSheaves.{u, u} B S hS X.obj X.property)
  {M : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj P.U).ringCatSheaf).FullSubcategory}
  (κ : (modulePullback B S hS (presentationAtlas P)).obj T.obj ≅
    ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj M).obj)
  {M'' : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj P''.U).ringCatSheaf).FullSubcategory}
  (Θ : quasicoherentPullbackObj B S hS yU M ≅ M'')

/-- The identification on the atlas of `h^*𝒯` is the identification along the square followed by
the inverse image of `κ` and the reading `yU^*(M^a) ≅ (yU^*M)^a ≅ M''^a`, as morphisms. -/
theorem presentationPullbackChartIso_hom_eq_pullbackSquareHom_comp :
    (presentationPullbackChartIso P'' P h yU hY T κ Θ).hom =
      pullbackSquareHom (presentationAtlas P'') (presentationAtlas P) h
          (representedSpaceMap B S hS yU) hY T.obj ≫
        (modulePullback B S hS (X := (presentationGroupoid P'').objects)
            (Y := (presentationGroupoid P).objects) (representedSpaceMap B S hS yU)).map κ.hom ≫
          ((modulePullbackRepresentedQuasicoherentIso B S hS yU M).hom ≫
            ((representedQuasicoherentSchemeEquivalence B S hS P''.U).functor.map Θ.hom).hom) :=
  (presentationPullbackChartIso_hom_eq_trans_hom P'' P h yU hY T κ Θ).trans rfl

end ChartHom

/-! ### Multiplications and units along a representable algebraic space -/

section OfIsoYonedaMul

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
  (P0 : Presentation B S hS F hF) {W : BigFppfOver B S hS} (e : F ≅ yoneda.obj W)
  (c : P0.U ⟶ W) (hc : yoneda.map c = P0.toSpace ≫ e.hom)
  {XA : AlgebraicSpaces B S hS} (Pb : Presentation B S hS XA.obj XA.property)
  (hA : representedAlgebraicSpace B S hS W ⟶ XA) (yU : (P0.ofIsoYoneda e c hc).U ⟶ Pb.U)
  (hY : presentationAtlas (P0.ofIsoYoneda e c hc) ≫ hA =
    representedSpaceMap B S hS yU ≫ presentationAtlas Pb)

/-- The identification of `N_n^a` on the atlas of the transported presentation carries the inverse
image of the attached multiplication on `W` to the attached multiplication on the presenting
scheme. -/
theorem ofIsoYonedaChartIso_mul_reading
    {M''₁ M''₂ M''₃ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj (P0.ofIsoYoneda e c hc).U).ringCatSheaf).FullSubcategory}
    {N₁ N₂ N₃ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf).FullSubcategory}
    (ΘB₁ : quasicoherentPullbackObj B S hS c N₁ ≅ M''₁)
    (ΘB₂ : quasicoherentPullbackObj B S hS c N₂ ≅ M''₂)
    (ΘB₃ : quasicoherentPullbackObj B S hS c N₃ ≅ M''₃)
    (m'' : quasicoherentTensorObj B S hS (P0.ofIsoYoneda e c hc).U M''₁ M''₂ ⟶ M''₃)
    (mN : quasicoherentTensorObj B S hS W N₁ N₂ ⟶ N₃)
    (hbW : RepresentedC3TensorCompat B S hS c N₁ N₂)
    (hmN : (quasicoherentPullbackTensorIso B S hS c N₁ N₂).inv ≫
        quasicoherentPullbackMap B S hS c mN ≫ ΘB₃.hom =
      quasicoherentTensorHom B S hS P0.U ΘB₁.hom ΘB₂.hom ≫ m'') :
    type_of% (modulePullback_map_representedTensorChartMul_comp_of_heq B S hS c mN m'' ΘB₁.hom
      ΘB₂.hom ΘB₃.hom hbW hmN (presentationAtlas (P0.ofIsoYoneda e c hc))
      (Li := ((representedQuasicoherentSchemeEquivalence B S hS (P0.ofIsoYoneda e c
          hc).U).functor.obj M''₁).obj)
      (Lj := ((representedQuasicoherentSchemeEquivalence B S hS (P0.ofIsoYoneda e c
          hc).U).functor.obj M''₂).obj)
      (Lk := ((representedQuasicoherentSchemeEquivalence B S hS (P0.ofIsoYoneda e c
          hc).U).functor.obj M''₃).obj)
      (ofIsoYonedaChartIso P0 e c hc N₁ ΘB₁).hom (ofIsoYonedaChartIso P0 e c hc N₂ ΘB₂).hom
      (ofIsoYonedaChartIso P0 e c hc N₃ ΘB₃).hom (representedTensorChartMul B S hS mN)
      (representedTensorChartMul B S hS m'')
      rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
      HEq.rfl HEq.rfl) :=
  modulePullback_map_representedTensorChartMul_comp_of_heq B S hS c mN m'' ΘB₁.hom
      ΘB₂.hom ΘB₃.hom hbW hmN (presentationAtlas (P0.ofIsoYoneda e c hc))
      (Li := ((representedQuasicoherentSchemeEquivalence B S hS (P0.ofIsoYoneda e c
          hc).U).functor.obj M''₁).obj)
      (Lj := ((representedQuasicoherentSchemeEquivalence B S hS (P0.ofIsoYoneda e c
          hc).U).functor.obj M''₂).obj)
      (Lk := ((representedQuasicoherentSchemeEquivalence B S hS (P0.ofIsoYoneda e c
          hc).U).functor.obj M''₃).obj)
      (ofIsoYonedaChartIso P0 e c hc N₁ ΘB₁).hom (ofIsoYonedaChartIso P0 e c hc N₂ ΘB₂).hom
      (ofIsoYonedaChartIso P0 e c hc N₃ ΘB₃).hom (representedTensorChartMul B S hS mN)
      (representedTensorChartMul B S hS m'')
      rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
      HEq.rfl HEq.rfl

/-- The readings `yU^*(M_n^a) ≅ M''_n^a` carry the inverse image of the attached multiplication on
`Pb.U` to the attached multiplication on the presenting scheme. -/
theorem presentationPullbackChartIso_mul_reading
    {M₁ M₂ M₃ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Pb.U).ringCatSheaf).FullSubcategory}
    {M''₁ M''₂ M''₃ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj (P0.ofIsoYoneda e c hc).U).ringCatSheaf).FullSubcategory}
    (Θ₁ : quasicoherentPullbackObj B S hS yU M₁ ≅ M''₁)
    (Θ₂ : quasicoherentPullbackObj B S hS yU M₂ ≅ M''₂)
    (Θ₃ : quasicoherentPullbackObj B S hS yU M₃ ≅ M''₃)
    (m : quasicoherentTensorObj B S hS Pb.U M₁ M₂ ⟶ M₃)
    (m'' : quasicoherentTensorObj B S hS (P0.ofIsoYoneda e c hc).U M''₁ M''₂ ⟶ M''₃)
    (hbU : RepresentedC3TensorCompat B S hS yU M₁ M₂)
    (hm : (quasicoherentPullbackTensorIso B S hS yU M₁ M₂).inv ≫
        quasicoherentPullbackMap B S hS yU m ≫ Θ₃.hom =
      quasicoherentTensorHom B S hS (P0.ofIsoYoneda e c hc).U Θ₁.hom Θ₂.hom ≫ m'') :
    type_of% (modulePullback_map_representedTensorChartMul_comp_of_heq B S hS yU m m'' Θ₁.hom Θ₂.hom
      Θ₃.hom hbU hm (X := (presentationGroupoid (P0.ofIsoYoneda e c hc)).objects)
      (Y := (presentationGroupoid Pb).objects) (representedSpaceMap B S hS yU)
      ((modulePullbackRepresentedQuasicoherentIso B S hS yU M₁).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS (P0.ofIsoYoneda e c hc).U).functor.map
          Θ₁.hom).hom)
      ((modulePullbackRepresentedQuasicoherentIso B S hS yU M₂).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS (P0.ofIsoYoneda e c hc).U).functor.map
          Θ₂.hom).hom)
      ((modulePullbackRepresentedQuasicoherentIso B S hS yU M₃).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS (P0.ofIsoYoneda e c hc).U).functor.map
          Θ₃.hom).hom)
      (representedTensorChartMul B S hS m) (representedTensorChartMul B S hS m'')
      rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
      HEq.rfl HEq.rfl) :=
  modulePullback_map_representedTensorChartMul_comp_of_heq B S hS yU m m'' Θ₁.hom Θ₂.hom
      Θ₃.hom hbU hm (X := (presentationGroupoid (P0.ofIsoYoneda e c hc)).objects)
      (Y := (presentationGroupoid Pb).objects) (representedSpaceMap B S hS yU)
      ((modulePullbackRepresentedQuasicoherentIso B S hS yU M₁).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS (P0.ofIsoYoneda e c hc).U).functor.map
          Θ₁.hom).hom)
      ((modulePullbackRepresentedQuasicoherentIso B S hS yU M₂).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS (P0.ofIsoYoneda e c hc).U).functor.map
          Θ₂.hom).hom)
      ((modulePullbackRepresentedQuasicoherentIso B S hS yU M₃).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS (P0.ofIsoYoneda e c hc).U).functor.map
          Θ₃.hom).hom)
      (representedTensorChartMul B S hS m) (representedTensorChartMul B S hS m'')
      rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
      HEq.rfl HEq.rfl

/-- The description on the atlas of an identification `h^*𝒯 ≅ N^a`, restated with the spaces of
`h` spelled as the target of the transported atlas. -/
theorem modulePullback_map_comp_ofIsoYonedaChartIso_eq
    {Tm : QuasicoherentSheaves.{u, u} B S hS XA.obj XA.property}
    {M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Pb.U).ringCatSheaf).FullSubcategory}
    {κ : (modulePullback B S hS (presentationAtlas Pb)).obj Tm.obj ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Pb.U).functor.obj M).obj}
    {M'' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj (P0.ofIsoYoneda e c hc).U).ringCatSheaf).FullSubcategory}
    {Θ : quasicoherentPullbackObj B S hS yU M ≅ M''}
    {N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf).FullSubcategory}
    {ΘB : quasicoherentPullbackObj B S hS c N ≅ M''}
    {e₀ : (modulePullback B S hS hA).obj Tm.obj ≅
      ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N).obj}
    (he₀ : (modulePullback B S hS (presentationAtlas (P0.ofIsoYoneda e c hc))).map e₀.hom ≫
        (ofIsoYonedaChartIso P0 e c hc N ΘB).hom =
      (presentationPullbackChartIso (P0.ofIsoYoneda e c hc) Pb hA yU hY Tm κ Θ).hom) :
    type_of% (modulePullback_map_comp_eq_of_heq (Z₂ := (⟨(representedAlgebraicSpace B S hS W).obj,
        (representedAlgebraicSpace B S hS W).property⟩ :
        AlgebraicSpaces B S hS))
      (X₂ := (⟨XA.obj, XA.property⟩ : AlgebraicSpaces B S hS)) (c''₁ := presentationAtlas
          (P0.ofIsoYoneda e c hc)) he₀
      (presentationAtlas (P0.ofIsoYoneda e c hc)) hA (T₂ := Tm.obj)
      (G₂ := ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N).obj)
      (L := ((representedQuasicoherentSchemeEquivalence B S hS (P0.ofIsoYoneda e c
          hc).U).functor.obj M'').obj) e₀.hom
      (ofIsoYonedaChartIso P0 e c hc N ΘB).hom
      (presentationPullbackChartIso (P0.ofIsoYoneda e c hc) Pb hA yU hY Tm κ Θ).hom
      rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl rfl HEq.rfl HEq.rfl HEq.rfl) :=
  modulePullback_map_comp_eq_of_heq (Z₂ := (⟨(representedAlgebraicSpace B S hS W).obj,
      (representedAlgebraicSpace B S hS W).property⟩ :
        AlgebraicSpaces B S hS))
      (X₂ := (⟨XA.obj, XA.property⟩ : AlgebraicSpaces B S hS)) (c''₁ := presentationAtlas
          (P0.ofIsoYoneda e c hc)) he₀
      (presentationAtlas (P0.ofIsoYoneda e c hc)) hA (T₂ := Tm.obj)
      (G₂ := ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N).obj)
      (L := ((representedQuasicoherentSchemeEquivalence B S hS (P0.ofIsoYoneda e c
          hc).U).functor.obj M'').obj) e₀.hom
      (ofIsoYonedaChartIso P0 e c hc N ΘB).hom
      (presentationPullbackChartIso (P0.ofIsoYoneda e c hc) Pb hA yU hY Tm κ Θ).hom
      rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl rfl HEq.rfl HEq.rfl HEq.rfl

/-- `AlgebraicGeometry.Space.modulePullbackTensorIso_inv_comp_map_comp_of_ofIsoYoneda_spec` with
the spaces of `hA` spelled as the targets of the atlases. -/
theorem modulePullbackTensorIso_inv_comp_map_comp_of_ofIsoYoneda_spec_aux
    {Tm₁ Tm₂ Tm₃ : QuasicoherentSheaves.{u, u} B S hS XA.obj XA.property}
    {M₁ M₂ M₃ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Pb.U).ringCatSheaf).FullSubcategory}
    (κ₁ : (modulePullback B S hS (presentationAtlas Pb)).obj Tm₁.obj ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Pb.U).functor.obj M₁).obj)
    (κ₂ : (modulePullback B S hS (presentationAtlas Pb)).obj Tm₂.obj ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Pb.U).functor.obj M₂).obj)
    (κ₃ : (modulePullback B S hS (presentationAtlas Pb)).obj Tm₃.obj ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Pb.U).functor.obj M₃).obj)
    {M''₁ M''₂ M''₃ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj (P0.ofIsoYoneda e c hc).U).ringCatSheaf).FullSubcategory}
    (Θ₁ : quasicoherentPullbackObj B S hS yU M₁ ≅ M''₁)
    (Θ₂ : quasicoherentPullbackObj B S hS yU M₂ ≅ M''₂)
    (Θ₃ : quasicoherentPullbackObj B S hS yU M₃ ≅ M''₃)
    {N₁ N₂ N₃ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf).FullSubcategory}
    (ΘB₁ : quasicoherentPullbackObj B S hS c N₁ ≅ M''₁)
    (ΘB₂ : quasicoherentPullbackObj B S hS c N₂ ≅ M''₂)
    (ΘB₃ : quasicoherentPullbackObj B S hS c N₃ ≅ M''₃)
    (e₁ : (modulePullback B S hS hA).obj Tm₁.obj ≅
      ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N₁).obj)
    (e₂ : (modulePullback B S hS hA).obj Tm₂.obj ≅
      ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N₂).obj)
    (e₃ : (modulePullback B S hS hA).obj Tm₃.obj ≅
      ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N₃).obj)
    (he₁ : (modulePullback B S hS (presentationAtlas (P0.ofIsoYoneda e c hc))).map e₁.hom ≫
        (ofIsoYonedaChartIso P0 e c hc N₁ ΘB₁).hom =
      (presentationPullbackChartIso (P0.ofIsoYoneda e c hc) Pb hA yU hY Tm₁ κ₁ Θ₁).hom)
    (he₂ : (modulePullback B S hS (presentationAtlas (P0.ofIsoYoneda e c hc))).map e₂.hom ≫
        (ofIsoYonedaChartIso P0 e c hc N₂ ΘB₂).hom =
      (presentationPullbackChartIso (P0.ofIsoYoneda e c hc) Pb hA yU hY Tm₂ κ₂ Θ₂).hom)
    (he₃ : (modulePullback B S hS (presentationAtlas (P0.ofIsoYoneda e c hc))).map e₃.hom ≫
        (ofIsoYonedaChartIso P0 e c hc N₃ ΘB₃).hom =
      (presentationPullbackChartIso (P0.ofIsoYoneda e c hc) Pb hA yU hY Tm₃ κ₃ Θ₃).hom)
    (μ : Tm₁.obj ⊗ Tm₂.obj ⟶ Tm₃.obj)
    (m : quasicoherentTensorObj B S hS Pb.U M₁ M₂ ⟶ M₃)
    (m'' : quasicoherentTensorObj B S hS (P0.ofIsoYoneda e c hc).U M''₁ M''₂ ⟶ M''₃)
    (mN : quasicoherentTensorObj B S hS W N₁ N₂ ⟶ N₃)
    (hμ : (modulePullback B S hS (presentationAtlas Pb)).map μ ≫ κ₃.hom =
      (modulePullbackTensorIso B S hS (presentationAtlas Pb) Tm₁.obj Tm₂.obj).hom ≫
        (κ₁.hom ⊗ₘ κ₂.hom) ≫ representedTensorChartMul B S hS m)
    (hbU : RepresentedC3TensorCompat B S hS yU M₁ M₂)
    (hm : (quasicoherentPullbackTensorIso B S hS yU M₁ M₂).inv ≫
        quasicoherentPullbackMap B S hS yU m ≫ Θ₃.hom =
      quasicoherentTensorHom B S hS (P0.ofIsoYoneda e c hc).U Θ₁.hom Θ₂.hom ≫ m'')
    (hbW : RepresentedC3TensorCompat B S hS c N₁ N₂)
    (hmN : (quasicoherentPullbackTensorIso B S hS c N₁ N₂).inv ≫
        quasicoherentPullbackMap B S hS c mN ≫ ΘB₃.hom =
      quasicoherentTensorHom B S hS P0.U ΘB₁.hom ΘB₂.hom ≫ m'') :
    type_of% (pullbackTensorIso_inv_comp_map_comp_of_chart (presentationAtlas (P0.ofIsoYoneda e c
        hc))
    (presentationAtlas Pb) hA (representedSpaceMap B S hS yU) hY μ κ₁.hom κ₂.hom κ₃.hom
    (representedTensorChartMul B S hS m) hμ
    ((modulePullbackRepresentedQuasicoherentIso B S hS yU M₁).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS (P0.ofIsoYoneda e c hc).U).functor.map
          Θ₁.hom).hom)
    ((modulePullbackRepresentedQuasicoherentIso B S hS yU M₂).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS (P0.ofIsoYoneda e c hc).U).functor.map
          Θ₂.hom).hom)
    ((modulePullbackRepresentedQuasicoherentIso B S hS yU M₃).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS (P0.ofIsoYoneda e c hc).U).functor.map
          Θ₃.hom).hom)
    (representedTensorChartMul B S hS m'')
    (presentationPullbackChartIso_mul_reading P0 e c hc Pb yU Θ₁ Θ₂ Θ₃ m m'' hbU hm)
    (ofIsoYonedaChartIso P0 e c hc N₁ ΘB₁).hom (ofIsoYonedaChartIso P0 e c hc N₂ ΘB₂).hom
    (ofIsoYonedaChartIso P0 e c hc N₃ ΘB₃) (representedTensorChartMul B S hS mN)
    (ofIsoYonedaChartIso_mul_reading P0 e c hc ΘB₁ ΘB₂ ΘB₃ m'' mN hbW hmN)
    e₁.hom e₂.hom e₃.hom
    (presentationPullbackChartIso (P0.ofIsoYoneda e c hc) Pb hA yU hY Tm₁ κ₁ Θ₁).hom
    (presentationPullbackChartIso (P0.ofIsoYoneda e c hc) Pb hA yU hY Tm₂ κ₂ Θ₂).hom
    (presentationPullbackChartIso (P0.ofIsoYoneda e c hc) Pb hA yU hY Tm₃ κ₃ Θ₃).hom
    (modulePullback_map_comp_ofIsoYonedaChartIso_eq P0 e c hc Pb hA yU hY he₁)
    (modulePullback_map_comp_ofIsoYonedaChartIso_eq P0 e c hc Pb hA yU hY he₂)
    (modulePullback_map_comp_ofIsoYonedaChartIso_eq P0 e c hc Pb hA yU hY he₃)
    (presentationPullbackChartIso_hom_eq_pullbackSquareHom_comp _ _ _ _ _ _ _ _)
    (presentationPullbackChartIso_hom_eq_pullbackSquareHom_comp _ _ _ _ _ _ _ _)
    (presentationPullbackChartIso_hom_eq_pullbackSquareHom_comp _ _ _ _ _ _ _ _)
    (presentationAtlas_map_injective_of_tensorObj (P0.ofIsoYoneda e c hc)
      (Y := (⟨XA.obj, XA.property⟩ : AlgebraicSpaces B S hS)) hA Tm₁.property Tm₂.property
      ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N₃).property)) :=
  pullbackTensorIso_inv_comp_map_comp_of_chart (presentationAtlas (P0.ofIsoYoneda e c hc))
    (presentationAtlas Pb) hA (representedSpaceMap B S hS yU) hY μ κ₁.hom κ₂.hom κ₃.hom
    (representedTensorChartMul B S hS m) hμ
    ((modulePullbackRepresentedQuasicoherentIso B S hS yU M₁).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS (P0.ofIsoYoneda e c hc).U).functor.map
          Θ₁.hom).hom)
    ((modulePullbackRepresentedQuasicoherentIso B S hS yU M₂).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS (P0.ofIsoYoneda e c hc).U).functor.map
          Θ₂.hom).hom)
    ((modulePullbackRepresentedQuasicoherentIso B S hS yU M₃).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS (P0.ofIsoYoneda e c hc).U).functor.map
          Θ₃.hom).hom)
    (representedTensorChartMul B S hS m'')
    (presentationPullbackChartIso_mul_reading P0 e c hc Pb yU Θ₁ Θ₂ Θ₃ m m'' hbU hm)
    (ofIsoYonedaChartIso P0 e c hc N₁ ΘB₁).hom (ofIsoYonedaChartIso P0 e c hc N₂ ΘB₂).hom
    (ofIsoYonedaChartIso P0 e c hc N₃ ΘB₃) (representedTensorChartMul B S hS mN)
    (ofIsoYonedaChartIso_mul_reading P0 e c hc ΘB₁ ΘB₂ ΘB₃ m'' mN hbW hmN)
    e₁.hom e₂.hom e₃.hom
    (presentationPullbackChartIso (P0.ofIsoYoneda e c hc) Pb hA yU hY Tm₁ κ₁ Θ₁).hom
    (presentationPullbackChartIso (P0.ofIsoYoneda e c hc) Pb hA yU hY Tm₂ κ₂ Θ₂).hom
    (presentationPullbackChartIso (P0.ofIsoYoneda e c hc) Pb hA yU hY Tm₃ κ₃ Θ₃).hom
    (modulePullback_map_comp_ofIsoYonedaChartIso_eq P0 e c hc Pb hA yU hY he₁)
    (modulePullback_map_comp_ofIsoYonedaChartIso_eq P0 e c hc Pb hA yU hY he₂)
    (modulePullback_map_comp_ofIsoYonedaChartIso_eq P0 e c hc Pb hA yU hY he₃)
    (presentationPullbackChartIso_hom_eq_pullbackSquareHom_comp _ _ _ _ _ _ _ _)
    (presentationPullbackChartIso_hom_eq_pullbackSquareHom_comp _ _ _ _ _ _ _ _)
    (presentationPullbackChartIso_hom_eq_pullbackSquareHom_comp _ _ _ _ _ _ _ _)
    (presentationAtlas_map_injective_of_tensorObj (P0.ofIsoYoneda e c hc)
      (Y := (⟨XA.obj, XA.property⟩ : AlgebraicSpaces B S hS)) hA Tm₁.property Tm₂.property
      ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N₃).property)

/-- **Identifications of descended modules along a representable algebraic space carry
multiplications to multiplications.**  Let `e_n : hA^*𝒯_n ≅ N_n^a` be identifications whose inverse
images along the atlas of the presentation of `W` transported from `P0` are the composites of the
identifications along the square, the chart identifications `κ_n` and the comparisons `Θ_n`.  If
`κ` carries a multiplication `μ` to an attached multiplication `m^a`, and `Θ`, `Θ_B` carry `m` and
`m_N` to the same multiplication `m''` on the presenting scheme (through Stacks 03EL), then the
`e_n` carry the inverse image of `μ` to `m_N^a`. -/
theorem modulePullbackTensorIso_inv_comp_map_comp_of_ofIsoYoneda_spec
    {Tm₁ Tm₂ Tm₃ : QuasicoherentSheaves.{u, u} B S hS XA.obj XA.property}
    {M₁ M₂ M₃ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Pb.U).ringCatSheaf).FullSubcategory}
    (κ₁ : (modulePullback B S hS (presentationAtlas Pb)).obj Tm₁.obj ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Pb.U).functor.obj M₁).obj)
    (κ₂ : (modulePullback B S hS (presentationAtlas Pb)).obj Tm₂.obj ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Pb.U).functor.obj M₂).obj)
    (κ₃ : (modulePullback B S hS (presentationAtlas Pb)).obj Tm₃.obj ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Pb.U).functor.obj M₃).obj)
    {M''₁ M''₂ M''₃ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj (P0.ofIsoYoneda e c hc).U).ringCatSheaf).FullSubcategory}
    (Θ₁ : quasicoherentPullbackObj B S hS yU M₁ ≅ M''₁)
    (Θ₂ : quasicoherentPullbackObj B S hS yU M₂ ≅ M''₂)
    (Θ₃ : quasicoherentPullbackObj B S hS yU M₃ ≅ M''₃)
    {N₁ N₂ N₃ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf).FullSubcategory}
    (ΘB₁ : quasicoherentPullbackObj B S hS c N₁ ≅ M''₁)
    (ΘB₂ : quasicoherentPullbackObj B S hS c N₂ ≅ M''₂)
    (ΘB₃ : quasicoherentPullbackObj B S hS c N₃ ≅ M''₃)
    (e₁ : (modulePullback B S hS hA).obj Tm₁.obj ≅
      ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N₁).obj)
    (e₂ : (modulePullback B S hS hA).obj Tm₂.obj ≅
      ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N₂).obj)
    (e₃ : (modulePullback B S hS hA).obj Tm₃.obj ≅
      ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N₃).obj)
    (he₁ : (modulePullback B S hS (presentationAtlas (P0.ofIsoYoneda e c hc))).map e₁.hom ≫
        (ofIsoYonedaChartIso P0 e c hc N₁ ΘB₁).hom =
      (presentationPullbackChartIso (P0.ofIsoYoneda e c hc) Pb hA yU hY Tm₁ κ₁ Θ₁).hom)
    (he₂ : (modulePullback B S hS (presentationAtlas (P0.ofIsoYoneda e c hc))).map e₂.hom ≫
        (ofIsoYonedaChartIso P0 e c hc N₂ ΘB₂).hom =
      (presentationPullbackChartIso (P0.ofIsoYoneda e c hc) Pb hA yU hY Tm₂ κ₂ Θ₂).hom)
    (he₃ : (modulePullback B S hS (presentationAtlas (P0.ofIsoYoneda e c hc))).map e₃.hom ≫
        (ofIsoYonedaChartIso P0 e c hc N₃ ΘB₃).hom =
      (presentationPullbackChartIso (P0.ofIsoYoneda e c hc) Pb hA yU hY Tm₃ κ₃ Θ₃).hom)
    (μ : Tm₁.obj ⊗ Tm₂.obj ⟶ Tm₃.obj)
    (m : quasicoherentTensorObj B S hS Pb.U M₁ M₂ ⟶ M₃)
    (m'' : quasicoherentTensorObj B S hS (P0.ofIsoYoneda e c hc).U M''₁ M''₂ ⟶ M''₃)
    (mN : quasicoherentTensorObj B S hS W N₁ N₂ ⟶ N₃)
    (hμ : (modulePullback B S hS (presentationAtlas Pb)).map μ ≫ κ₃.hom =
      (modulePullbackTensorIso B S hS (presentationAtlas Pb) Tm₁.obj Tm₂.obj).hom ≫
        (κ₁.hom ⊗ₘ κ₂.hom) ≫ representedTensorChartMul B S hS m)
    (hbU : RepresentedC3TensorCompat B S hS yU M₁ M₂)
    (hm : (quasicoherentPullbackTensorIso B S hS yU M₁ M₂).inv ≫
        quasicoherentPullbackMap B S hS yU m ≫ Θ₃.hom =
      quasicoherentTensorHom B S hS (P0.ofIsoYoneda e c hc).U Θ₁.hom Θ₂.hom ≫ m'')
    (hbW : RepresentedC3TensorCompat B S hS c N₁ N₂)
    (hmN : (quasicoherentPullbackTensorIso B S hS c N₁ N₂).inv ≫
        quasicoherentPullbackMap B S hS c mN ≫ ΘB₃.hom =
      quasicoherentTensorHom B S hS P0.U ΘB₁.hom ΘB₂.hom ≫ m'') :
    (modulePullbackTensorIso B S hS hA Tm₁.obj Tm₂.obj).inv ≫
        (modulePullback B S hS hA).map μ ≫ e₃.hom =
      (e₁.hom ⊗ₘ e₂.hom) ≫ representedTensorChartMul B S hS mN :=
  modulePullbackTensorIso_inv_comp_map_comp_eq_of_heq
    (Z₂ := (⟨(representedAlgebraicSpace B S hS W).obj, (representedAlgebraicSpace B S hS
        W).property⟩ :
      AlgebraicSpaces B S hS)) (X₂ := (⟨XA.obj, XA.property⟩ : AlgebraicSpaces B S hS))
    (h₂ := hA) (T₁' := Tm₁.obj) (T₂' := Tm₂.obj) (T₃' := Tm₃.obj) (μ' := μ)
    (G₁' := ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N₁).obj)
    (G₂' := ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N₂).obj)
    (G₃' := ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N₃).obj)
    (e₁' := e₁.hom) (e₂' := e₂.hom) (e₃' := e₃.hom) (μG' := representedTensorChartMul B S hS mN)
    (modulePullbackTensorIso_inv_comp_map_comp_of_ofIsoYoneda_spec_aux P0 e c hc Pb hA yU hY κ₁ κ₂
        κ₃
      Θ₁ Θ₂ Θ₃ ΘB₁ ΘB₂ ΘB₃ e₁ e₂ e₃ he₁ he₂ he₃ μ m m'' mN hμ hbU hm hbW hmN)
    hA μ e₁.hom e₂.hom e₃.hom (representedTensorChartMul B S hS mN) rfl rfl
    HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl

/-- **Identifications of descended modules along a representable algebraic space carry units to
units**, in the situation of
`AlgebraicGeometry.Space.modulePullbackTensorIso_inv_comp_map_comp_of_ofIsoYoneda_spec`, through
Stacks 03LU. -/
theorem modulePullbackUnitIso_inv_comp_map_comp_of_ofIsoYoneda_spec
    {Tm : QuasicoherentSheaves.{u, u} B S hS XA.obj XA.property}
    {M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Pb.U).ringCatSheaf).FullSubcategory}
    (κ : (modulePullback B S hS (presentationAtlas Pb)).obj Tm.obj ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Pb.U).functor.obj M).obj)
    {M'' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj (P0.ofIsoYoneda e c hc).U).ringCatSheaf).FullSubcategory}
    (Θ : quasicoherentPullbackObj B S hS yU M ≅ M'')
    {N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf).FullSubcategory}
    (ΘB : quasicoherentPullbackObj B S hS c N ≅ M'')
    (e₀ : (modulePullback B S hS hA).obj Tm.obj ≅
      ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N).obj)
    (he₀ : (modulePullback B S hS (presentationAtlas (P0.ofIsoYoneda e c hc))).map e₀.hom ≫
        (ofIsoYonedaChartIso P0 e c hc N ΘB).hom =
      (presentationPullbackChartIso (P0.ofIsoYoneda e c hc) Pb hA yU hY Tm κ Θ).hom)
    (ν : SheafOfModules.unit (structureRingSheaf B S hS XA) ⟶ Tm.obj)
    (νU : quasicoherentUnitObj B S hS Pb.U ⟶ M)
    (ν'' : quasicoherentUnitObj B S hS (P0.ofIsoYoneda e c hc).U ⟶ M'')
    (νN : quasicoherentUnitObj B S hS W ⟶ N)
    (hν : (modulePullback B S hS (presentationAtlas Pb)).map ν ≫ κ.hom =
      (modulePullbackUnitIso B S hS (presentationAtlas Pb)).hom ≫
        representedUnitChartHom B S hS νU)
    (hbU : RepresentedC3UnitCompat B S hS yU)
    (hu : (quasicoherentPullbackUnitIso B S hS yU).inv ≫
        quasicoherentPullbackMap B S hS yU νU ≫ Θ.hom = ν'')
    (hbW : RepresentedC3UnitCompat B S hS c)
    (huN : (quasicoherentPullbackUnitIso B S hS c).inv ≫
        quasicoherentPullbackMap B S hS c νN ≫ ΘB.hom = ν'') :
    (modulePullbackUnitIso B S hS hA).inv ≫ (modulePullback B S hS hA).map ν ≫ e₀.hom =
      representedUnitChartHom B S hS νN := by
  have hl := modulePullback_map_representedUnitChartHom_comp_of_heq B S hS yU νU ν'' Θ.hom hbU hu
      (X := (presentationGroupoid (P0.ofIsoYoneda e c hc)).objects)
      (Y := (presentationGroupoid Pb).objects) (representedSpaceMap B S hS yU)
      ((modulePullbackRepresentedQuasicoherentIso B S hS yU M).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS (P0.ofIsoYoneda e c hc).U).functor.map
          Θ.hom).hom) (representedUnitChartHom B S hS νU) (representedUnitChartHom B S hS ν'')
      rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
  have hr := modulePullback_map_representedUnitChartHom_comp_of_heq B S hS c νN ν'' ΘB.hom hbW huN
      (presentationAtlas (P0.ofIsoYoneda e c hc)) (ofIsoYonedaChartIso P0 e c hc N ΘB).hom
      (representedUnitChartHom B S hS νN) (representedUnitChartHom B S hS ν'')
      (L := ((representedQuasicoherentSchemeEquivalence B S hS
        (P0.ofIsoYoneda e c hc).U).functor.obj M'').obj)
      rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
  have hcc := presentationPullbackChartIso_hom_eq_pullbackSquareHom_comp (P0.ofIsoYoneda e c hc)
      Pb hA
      yU hY Tm κ Θ
  have H := pullbackUnitIso_inv_comp_map_comp_of_chart (presentationAtlas (P0.ofIsoYoneda e c hc))
    (presentationAtlas Pb) hA (representedSpaceMap B S hS yU) hY ν κ.hom
    (representedUnitChartHom B S hS νU) hν
    ((modulePullbackRepresentedQuasicoherentIso B S hS yU M).hom ≫
      ((representedQuasicoherentSchemeEquivalence B S hS (P0.ofIsoYoneda e c hc).U).functor.map
        Θ.hom).hom)
    (representedUnitChartHom B S hS ν'') hl
    (ofIsoYonedaChartIso P0 e c hc N ΘB) (representedUnitChartHom B S hS νN) hr
    e₀.hom _ he₀ hcc
    (fun _ _ hφψ => @presentationAtlas_map_injective _ _ _ _ (P0.ofIsoYoneda e c hc) _ _
      (SheafOfModules.isQuasicoherentOnSite_unit _)
      ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N).property
      _ _ hφψ)
  exact modulePullbackUnitIso_inv_comp_map_comp_eq_of_heq
    (Z₂ := (⟨(representedAlgebraicSpace B S hS W).obj, (representedAlgebraicSpace B S hS
        W).property⟩ :
      AlgebraicSpaces B S hS)) (X₂ := (⟨XA.obj, XA.property⟩ : AlgebraicSpaces B S hS))
    (h₂ := hA) (T₂ := Tm.obj) (ν₂ := ν)
    (G₂ := ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N).obj) (e₂ := e₀.hom)
    (νG₂ := representedUnitChartHom B S hS νN) H hA ν e₀.hom (representedUnitChartHom B S hS νN)
        rfl rfl
    HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl

end OfIsoYonedaMul


namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})

/-! ### The base change to a scheme point, as graded algebras -/

section Point

variable (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1)

/-- **The base change identification of Stacks 084D is unital**: for a scheme point `f : T ⟶ X`,
the identification `(T ×_X P ⟶ P)^*𝒪_P(0) ≅ 𝒪(0)^a` carries the inverse image of the unit
`𝒪_P ⟶ 𝒪_P(0)`, read through Stacks 03LU, to the unit of the twists of Stacks 01NR on
`T ×_X P` (stated for `…RelativeProjSituation.fibreToSpaceTwistModuleIso` unfolded by
`…RelativeProjSituation.fibreToSpaceTwistModuleIso_eq`, the twist as the descended module it is
by definition and the unit as `…RelativeProjSituation.twistModuleUnit`). -/
theorem fibreToSpaceTwistModuleIso_unit :
    type_of% (modulePullbackUnitIso_inv_comp_map_comp_of_ofIsoYoneda_spec _ _ _ _ _ _ _ _ _ _ _ _
      (s.fibreToSpaceTwistModuleIso_spec Px T f 0) _
      (s.twistPieceUnit Px.U Px.toSpace)
      ((s.pullback (s.schemePointHom T f)).twistPieceUnit (Px.alongPoint f).U
        (Px.alongPoint f).toSpace)
      (s.twistPieceUnit T f) (s.twistAlgebraUnit_spec Px)
      (representedC3UnitCompat s.site s.base s.containsBase _)
      (quasicoherentPullbackUnitIso_inv_comp_map_comp_eq_of_heq
        (s.baseChangeTwistPieceComparison_unit (s.schemePointHom T f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) _
        (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
          (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)))
        rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl)
      (representedC3UnitCompat s.site s.base s.containsBase _)
      (quasicoherentPullbackUnitIso_inv_comp_map_comp_eq_of_heq
        (s.baseChangeTwistPieceComparison_unit (s.schemePointHom T f) (Px.alongPointToPoint f) rfl _
        (s.liesOverAlong_pointChartMap Px T f))
        rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl)) :=
  modulePullbackUnitIso_inv_comp_map_comp_of_ofIsoYoneda_spec _ _ _ _ _ _ _ _ _ _ _ _
      (s.fibreToSpaceTwistModuleIso_spec Px T f 0) _
      (s.twistPieceUnit Px.U Px.toSpace)
      ((s.pullback (s.schemePointHom T f)).twistPieceUnit (Px.alongPoint f).U
        (Px.alongPoint f).toSpace)
      (s.twistPieceUnit T f) (s.twistAlgebraUnit_spec Px)
      (representedC3UnitCompat s.site s.base s.containsBase _)
      (quasicoherentPullbackUnitIso_inv_comp_map_comp_eq_of_heq
        (s.baseChangeTwistPieceComparison_unit (s.schemePointHom T f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) _
        (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
          (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)))
        rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl)
      (representedC3UnitCompat s.site s.base s.containsBase _)
      (quasicoherentPullbackUnitIso_inv_comp_map_comp_eq_of_heq
        (s.baseChangeTwistPieceComparison_unit (s.schemePointHom T f) (Px.alongPointToPoint f) rfl _
        (s.liesOverAlong_pointChartMap Px T f))
        rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl)

end Point

end RelativeProjSituation

end AlgebraicGeometry.Space

end
