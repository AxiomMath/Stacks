module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartSource
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceRepresentedSpaceBridge

/-!
# The square of the source factor of the chart maps `χ_w` of `θ` of Stacks 0D2Z

For a pair `(ℒ, ψ)` on the small étale site of an algebraic space `X` over the algebraic space `Y`
of Situation 0849, the chart map `χ_w : w^*(r^*𝒪(d)) ⟶ w^*(ℒ^{⊗ d}|_{U(ψ)})` at a scheme point
`w : T ⟶ U(ψ)` (`…InvertibleTwistingRestriction.chartMap`) is the composite of the source
identification `w^*(r^*𝒪(d)) ≅ (c_w^*𝒪(d))^a` (`…InvertibleTwistingRestriction.chartSourceIso`),
the module attached to `θ` of Stacks 01O9 on `T`, and a target identification.  This file proves
**the square of the source factor** along a morphism `τ : T' ⟶ T` of test schemes, with
`w' = w ∘ τ` and a morphism `y : T' ×_Y Proj_Y(𝒜) ⟶ T ×_Y Proj_Y(𝒜)` lying over `τ`: `τ^*` of the
source identification at `w`, followed by `τ^*((c_w^*𝒪(d))^a) ≅ (τ^*c_w^*𝒪(d))^a` and the module
attached to the comparison `σ : τ^*c_w^*𝒪(d) ⟶ c_{w'}^*𝒪(d)` of the two pullbacks, is the
comparison of Stacks 03LU for `τ` and `w` followed by the source identification at `w'`.  It is
the first of the three squares of `AlgebraicGeometry.Space.pullbackTransportSquare_of_squares`.

## Main results

* `AlgebraicGeometry.Space.chartSourceShaped_square`: the square at variables, for any two
  identifications built as `…chartSourceIso` is, from compatible data.
* `…InvertibleTwistingRestriction.chartSource_square`: **the square of the source factor of the
  chart maps**, in the shape of the first hypothesis of
  `AlgebraicGeometry.Space.pullbackTransportSquare_of_squares`, with the comparison `σ` and the
  composite `β = (τ^*M^a ≅ (τ^*M)^a) ≫ σ^a` as variables with their values as equations.
* `AlgebraicGeometry.Space.pullbackTransportSquare_source_of_heq`: a square in the shape of the
  first hypothesis of `AlgebraicGeometry.Space.pullbackTransportSquare_of_squares`, read in a
  second spelling of the site.
* `…InvertibleTwistingRestriction.chartSource_square_shrink`: **the square of the source factor
  of the chart maps over the site of `s.shrink`**, in the spelling of
  `AlgebraicGeometry.Space.pullbackTransportSquare_of_squares` there.

## Implementation notes

The square is proved at variables (`AlgebraicGeometry.Space.chartSourceShaped_square`) by the
reduction of `RelativeProjInvertibleSpaceChartSource`: the readings of Stacks 03DX (2) on both
sides, the coherence of Stacks 03LU between them and the naturality of Stacks 084D.  At variables
every composite which the reduction compares is spelled identically on both sides, so the
comparisons are syntactic for the kernel.  Two spellings are pinned for that: the factorisation
equations are stated in the category `AlgebraicGeometry.AlgebraicSpaces` itself (written
`@CategoryStruct.comp (AlgebraicSpaces B S hS)`), as the coherence of Stacks 03LU states them,
rather than in the full subcategory it abbreviates; and the source identifications enter through
their value with the comparison `modulePullbackCompTransportIso` written out, with its type
ascribed, so that the five factors of the reading carry the objects of the statement rather than
the auxiliary proofs of the definition's body.  The reading of the base change identification at
`w'` is `AlgebraicGeometry.Space.modulePullback_map_attachedSource_target_reading_eq_spaces`, the
same statement as `…modulePullback_map_attachedSource_target_reading_eq` with its factorisation in
that spelling.

The family of chart maps, and with it `AlgebraicGeometry.Space.PointFamilyNatural`, lives over the
site of `s.shrink`, which is `s.site` by definition but not syntactically.  Two such spellings of
one morphism of modules are not compared cheaply: the unifier reads a projection (`Functor.map`,
`NatTrans.app`, `CategoryStruct.comp`) of two differently spelled functors by reducing the functors
themselves.  The square is therefore proved over `s.site` and then read over `s.shrink.site` by
`AlgebraicGeometry.Space.pullbackTransportSquare_source_of_heq`, whose hypotheses compare only the
leaves (spaces, morphisms of spaces, modules, the factors), each of which is the same term in both
readings; its conclusion is the first hypothesis of
`AlgebraicGeometry.Space.pullbackTransportSquare_of_squares` verbatim, so that
`…chartSource_square_shrink` is that hypothesis on the nose.

The source identifications at `w` and `w'` are then substituted, one per declaration
(`…chartSource_square_of_point`, `…chartSource_square_of_points`), by
`…InvertibleTwistingRestriction.chartSourceIso_eq_value`, their value with every represented
algebraic space in the spelling of `AlgebraicGeometry.Space.representedSpaceMap`: it matches the
hypothesis syntactically up to proofs, where `rfl` would unify the definition with its value at
about half of the per-declaration budget each time.  Every argument
of the instances is given as `(e : _)`: elaborated against the expected type, an argument of these
statements makes the elaborator unify an application whose implicit arguments are not yet known,
which normalises the section `c_w` as a morphism of schemes; elaborated alone and then compared,
the same argument is checked in a fraction of a second.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

namespace AlgebraicGeometry.Space

section Bridge

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Tt Tt' Ff Ff' : BigFppfOver B S hS} {P L : AlgebraicSpaces B S hS}

/-- `AlgebraicGeometry.Space.modulePullback_map_attachedSource_target_reading_eq` with the
factorisation `y ≫ b' = b'₁` stated in the category of algebraic spaces, the spelling in which the
coherence of Stacks 03LU (`AlgebraicGeometry.Space.modulePullback_sourceChain_eq`) states it. -/
theorem modulePullback_map_attachedSource_target_reading_eq_spaces (c₁ : Tt' ⟶ Ff')
    (y : Ff' ⟶ Ff)
    (b' : (⟨yoneda.obj Ff, isAlgebraicSpace_yoneda B S hS Ff⟩ : AlgebraicSpaces B S hS) ⟶ P)
    (b'₁ : (⟨yoneda.obj Ff', isAlgebraicSpace_yoneda B S hS Ff'⟩ : AlgebraicSpaces B S hS) ⟶ P)
    (hfy : @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _
      (representedSpaceMap B S hS y) b' = b'₁)
    (Tm : Modules.{u, u} B S hS P.1 P.2)
    {N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Ff).ringCatSheaf).FullSubcategory}
    {N' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Ff').ringCatSheaf).FullSubcategory}
    (E₀ : (modulePullback B S hS b').obj Tm ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Ff).functor.obj N).obj)
    (E₀' : (modulePullback B S hS b'₁).obj Tm ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Ff').functor.obj N').obj)
    (cmp : quasicoherentPullbackObj B S hS y N ≅ N')
    (hE : E₀' = eqToIso (congrArg
        (fun k : (⟨yoneda.obj Ff', isAlgebraicSpace_yoneda B S hS Ff'⟩ :
            AlgebraicSpaces B S hS) ⟶ P =>
          (modulePullback B S hS k).obj Tm) hfy.symm) ≪≫
      attachedModuleIsoPullback Tm b' y E₀ cmp)
    (tl : (modulePullback B S hS (representedSpaceMap B S hS (c₁ ≫ y))).obj
        ((modulePullback B S hS b').obj Tm) ⟶
      ((representedQuasicoherentSchemeEquivalence B S hS Tt').functor.obj
        (quasicoherentPullbackObj B S hS c₁ N')).obj)
    (htl : tl = attachedSourceReadingComp c₁ y b' Tm E₀ cmp) :
    type_of% (targetReading_chase (modulePullback B S hS (representedSpaceMap B S hS c₁)) _ _
      (pullbackTransport_eq_eqToHom Tm hfy.symm) _ _ _ _ _ _ hE
      (attachedModuleIsoPullback_hom (N := N) (N' := N') (y := y) (cmp := cmp)
        (Tmo := Tm) (hWc := b') (E₀ := E₀)) _ _ _ _ _ _ _ _ _
      (modulePullbackRepresentedQuasicoherentIso_naturality B S hS c₁ cmp.hom)
      (modulePullback_map_reading_comp Tm c₁ y b' E₀.hom) htl) :=
  targetReading_chase (modulePullback B S hS (representedSpaceMap B S hS c₁)) _ _
    (pullbackTransport_eq_eqToHom Tm hfy.symm) _ _ _ _ _ _ hE
    (attachedModuleIsoPullback_hom (N := N) (N' := N') (y := y) (cmp := cmp)
      (Tmo := Tm) (hWc := b') (E₀ := E₀)) _ _ _ _ _ _ _ _ _
    (modulePullbackRepresentedQuasicoherentIso_naturality B S hS c₁ cmp.hom)
    (modulePullback_map_reading_comp Tm c₁ y b' E₀.hom) htl

/-- The comparison `f^*g^*M ≅ (f ≫ g)^*M` of Stacks 03LU at a module, read as
`AlgebraicGeometry.Space.modulePullbackCompHom`, with its source spelled `f^*(g^*M)`. -/
theorem modulePullbackCompIso_app_hom_eq {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) (M : Modules.{u, u} B S hS Z.1 Z.2) :
    @Iso.hom _ _ ((modulePullback B S hS f).obj ((modulePullback B S hS g).obj M))
        ((modulePullback B S hS (f ≫ g)).obj M) ((modulePullbackCompIso B S hS f g).app M) =
      modulePullbackCompHom B S hS f g M :=
  Iso.app_hom _ _

/-- `AlgebraicGeometry.Space.modulePullbackCompHom` is the component of the comparison of
Stacks 03LU. -/
theorem modulePullbackCompHom_eq_hom_app {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) (M : Modules.{u, u} B S hS Z.1 Z.2) :
    modulePullbackCompHom B S hS f g M = (modulePullbackCompIso B S hS f g).hom.app M :=
  rfl

/-- The inverse comparison `(f ≫ g)^*M ≅ f^*g^*M` of Stacks 03LU at a module, read as
`AlgebraicGeometry.Space.modulePullbackCompInv`, with its target spelled `f^*(g^*M)`. -/
theorem modulePullbackCompIso_app_symm_hom_eq {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) (M : Modules.{u, u} B S hS Z.1 Z.2) :
    @Iso.hom _ _ ((modulePullback B S hS (f ≫ g)).obj M)
        ((modulePullback B S hS f).obj ((modulePullback B S hS g).obj M))
        ((modulePullbackCompIso B S hS f g).app M).symm =
      modulePullbackCompInv B S hS f g M :=
  (Iso.symm_hom _).trans (Iso.app_inv _ _)

end Bridge

section AbstractChases

variable {D : Type*} [Category D]

/-- The right-hand half of the square of the source factor, at variables, with the reading
`hΞ'` of the source factor at `w ∘ τ` given in the factors of `H`. -/
theorem attachedSourceRightRead_chase_factors {a m0 q0 q1 r1 r2 r3 s1 : D} {lhs : a ⟶ m0}
    {C0 : a ⟶ q0} {Tr : q0 ⟶ q1} {J1 : q1 ⟶ r1} {J2 : r1 ⟶ r2} {J3 : r2 ⟶ r3}
    {J4 : r3 ⟶ s1} {J5 : s1 ⟶ m0}
    (H : lhs = C0 ≫ Tr ≫ J1 ≫ J2 ≫ J3 ≫ J4 ≫ J5)
    (Ξ' : q1 ⟶ m0) (hΞ' : Ξ' = J1 ≫ J2 ≫ J3 ≫ J4 ≫ J5) :
    lhs = (C0 ≫ Tr) ≫ Ξ' := by
  rw [H, hΞ']
  simp only [Category.assoc]

/-- The left-hand half of the square of the source factor, at variables, with the reading `hΞ`
of the source factor at `w` given in the factors of `H`. -/
theorem attachedSourceSquareLeft_chase_factors {C : Type*} [Category C] {F : C ⥤ D}
    {p0 p1 p2 p3 p4 p5 : C} {g0 m0 : D}
    {K1 : p0 ⟶ p1} {K2 : p1 ⟶ p2} {K3 : p2 ⟶ p3} {K4 : p3 ⟶ p4} {K5 : p4 ⟶ p5}
    {S1 : F.obj p5 ⟶ g0} {S2 : g0 ⟶ m0} {R : F.obj p0 ⟶ m0}
    (H : F.map K1 ≫ F.map K2 ≫ F.map K3 ≫ F.map K4 ≫ F.map K5 ≫ S1 ≫ S2 = R)
    (Ξ : p0 ⟶ p5) (hΞ : Ξ = K1 ≫ K2 ≫ K3 ≫ K4 ≫ K5) (β : F.obj p5 ⟶ m0) (hβ : β = S1 ≫ S2) :
    F.map Ξ ≫ β = R := by
  rw [hΞ, hβ]
  simp only [Functor.map_comp, Category.assoc]
  exact H

/-- A five-factor reading `Ξ = a₁ ≫ ⋯ ≫ a₅` rewritten factor by factor. -/
theorem comp_five_eq_of_eq {x0 x1 x2 x3 x4 x5 : D} {Ξ : x0 ⟶ x5} {a1 b1 : x0 ⟶ x1}
    {a2 b2 : x1 ⟶ x2} {a3 b3 : x2 ⟶ x3} {a4 b4 : x3 ⟶ x4} {a5 b5 : x4 ⟶ x5}
    (hΞ : Ξ = a1 ≫ a2 ≫ a3 ≫ a4 ≫ a5) (h1 : a1 = b1) (h2 : a2 = b2)
    (h3 : a3 = b3) (h4 : a4 = b4) (h5 : a5 = b5) :
    Ξ = b1 ≫ b2 ≫ b3 ≫ b4 ≫ b5 := by
  rw [hΞ, h1, h2, h3, h4, h5]

end AbstractChases

section Bridge

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The square of the source factor of the chart maps, at variables.**  Let
`J : A^*(r^*𝒯) ≅ (c^*N)^a` and `J' : A₁^*(r^*𝒯) ≅ (c₁^*N')^a` be built as
`…InvertibleTwistingRestriction.chartSourceIso` is -- the comparisons of Stacks 03LU along the
factorisations `A ≫ r = c ≫ b'` and `A₁ ≫ r = c₁ ≫ b'₁`, the inverse images of identifications
`E₀ : b'^*𝒯 ≅ N^a`, `E₀' : b'₁^*𝒯 ≅ N'^a`, and Stacks 03DX (2) -- and let `τ ≫ A = A₁`,
`τ ≫ c = c₁ ≫ y`, `y ≫ b' = b'₁`, with `E₀'` the transfer of `E₀` along `y` and an isomorphism
`cmp : y^*N ≅ N'` (Stacks 084D).  Then `τ^*J`, followed by `β = (τ^*(c^*N)^a ≅ (τ^*c^*N)^a) ≫ σ^a`
for the comparison `σ : τ^*c^*N ⟶ c₁^*N'` of the two pullbacks, is the comparison of Stacks 03LU
for `τ` and `A` followed by `J'`. -/
theorem chartSourceShaped_square {Tt Ff : BigFppfOver B S hS} {L P : AlgebraicSpaces B S hS}
    {A : (⟨yoneda.obj Tt, isAlgebraicSpace_yoneda B S hS Tt⟩ : AlgebraicSpaces B S hS) ⟶ L}
    {r : L ⟶ P} {Tm : Modules.{u, u} B S hS P.1 P.2} {c : Tt ⟶ Ff}
    {N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Ff).ringCatSheaf).FullSubcategory}
    (J : (modulePullback B S hS A).obj ((modulePullback B S hS r).obj Tm) ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Tt).functor.obj
        (quasicoherentPullbackObj B S hS c N)).obj)
    {b' : (⟨yoneda.obj Ff, isAlgebraicSpace_yoneda B S hS Ff⟩ : AlgebraicSpaces B S hS) ⟶ P}
    {hab : @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ A r =
      @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ (representedSpaceMap B S hS c) b'}
    {E₀ : (modulePullback B S hS b').obj Tm ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Ff).functor.obj N).obj}
    (hJ : J = ((((modulePullbackCompIso B S hS A r).app Tm ≪≫
          eqToIso (congrArg (fun k => (modulePullback B S hS k).obj Tm) hab) ≪≫
          ((modulePullbackCompIso B S hS (representedSpaceMap B S hS c) b').app Tm).symm) :
        (modulePullback B S hS A).obj ((modulePullback B S hS r).obj Tm) ≅
          (modulePullback B S hS (representedSpaceMap B S hS c)).obj
            ((modulePullback B S hS b').obj Tm))) ≪≫
      (modulePullback B S hS (representedSpaceMap B S hS c)).mapIso E₀ ≪≫
        modulePullbackRepresentedQuasicoherentIso B S hS c N)
    {Tt' Ff' : BigFppfOver B S hS}
    {A₁ : (⟨yoneda.obj Tt', isAlgebraicSpace_yoneda B S hS Tt'⟩ : AlgebraicSpaces B S hS) ⟶ L}
    {c₁ : Tt' ⟶ Ff'}
    {N' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Ff').ringCatSheaf).FullSubcategory}
    (J' : (modulePullback B S hS A₁).obj ((modulePullback B S hS r).obj Tm) ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Tt').functor.obj
        (quasicoherentPullbackObj B S hS c₁ N')).obj)
    {b'₁ : (⟨yoneda.obj Ff', isAlgebraicSpace_yoneda B S hS Ff'⟩ : AlgebraicSpaces B S hS) ⟶ P}
    {hab₁ : @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ A₁ r =
      @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ (representedSpaceMap B S hS c₁) b'₁}
    {E₀' : (modulePullback B S hS b'₁).obj Tm ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Ff').functor.obj N').obj}
    (hJ' : J' = ((((modulePullbackCompIso B S hS A₁ r).app Tm ≪≫
          eqToIso (congrArg (fun k => (modulePullback B S hS k).obj Tm) hab₁) ≪≫
          ((modulePullbackCompIso B S hS (representedSpaceMap B S hS c₁) b'₁).app Tm).symm) :
        (modulePullback B S hS A₁).obj ((modulePullback B S hS r).obj Tm) ≅
          (modulePullback B S hS (representedSpaceMap B S hS c₁)).obj
            ((modulePullback B S hS b'₁).obj Tm))) ≪≫
      (modulePullback B S hS (representedSpaceMap B S hS c₁)).mapIso E₀' ≪≫
        modulePullbackRepresentedQuasicoherentIso B S hS c₁ N')
    (τ : Tt' ⟶ Tt)
    (h : @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ (representedSpaceMap B S hS τ) A =
      A₁)
    (y : Ff' ⟶ Ff) (hwc : τ ≫ c = c₁ ≫ y)
    (hfy : @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _
      (representedSpaceMap B S hS y) b' = b'₁)
    (cmp : quasicoherentPullbackObj B S hS y N ≅ N')
    (hE : E₀' = eqToIso (congrArg
        (fun k : (⟨yoneda.obj Ff', isAlgebraicSpace_yoneda B S hS Ff'⟩ :
            AlgebraicSpaces B S hS) ⟶ P =>
          (modulePullback B S hS k).obj Tm) hfy.symm) ≪≫
      attachedModuleIsoPullback Tm b' y E₀ cmp)
    (σ : quasicoherentPullbackObj B S hS τ (quasicoherentPullbackObj B S hS c N) ⟶
      quasicoherentPullbackObj B S hS c₁ N')
    (hσ : σ = (quasicoherentPullbackCompIso B S hS τ c N).hom ≫
      quasicoherentPullbackEqToHom B S hS hwc N ≫
        (quasicoherentPullbackCompIso B S hS c₁ y N).inv ≫
          quasicoherentPullbackMap B S hS c₁ cmp.hom)
    (β : (modulePullback B S hS (representedSpaceMap B S hS τ)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS Tt).functor.obj
          (quasicoherentPullbackObj B S hS c N)).obj ⟶
      ((representedQuasicoherentSchemeEquivalence B S hS Tt').functor.obj
        (quasicoherentPullbackObj B S hS c₁ N')).obj)
    (hβ : β = (modulePullbackRepresentedQuasicoherentIso B S hS τ
        (quasicoherentPullbackObj B S hS c N)).hom ≫
      ((representedQuasicoherentSchemeEquivalence B S hS Tt').functor.map σ).hom) :
    (modulePullback B S hS (representedSpaceMap B S hS τ)).map J.hom ≫ β =
      ((modulePullbackCompIso B S hS (representedSpaceMap B S hS τ) A).hom.app
          ((modulePullback B S hS r).obj Tm) ≫
        pullbackTransport ((modulePullback B S hS r).obj Tm) h) ≫ J'.hom := by
  have HL := modulePullback_map_attachedSource_reading_eq τ c c₁ y hwc b' Tm E₀ cmp σ hσ _ rfl
  have HC := modulePullback_sourceChain_eq (representedSpaceMap B S hS τ) A A₁ r
    (representedSpaceMap B S hS c) b' (representedSpaceMap B S hS c₁) b'₁
    (representedSpaceMap B S hS y) Tm h hab hab₁ hfy
    (algebraicSpacesComp_representedSpaceMap B S hS τ c)
    (congrArg (representedSpaceMap B S hS) hwc)
    (algebraicSpacesComp_representedSpaceMap B S hS c₁ y)
  have HS := attachedSourceSides_chase HL HC rfl
  have HR := modulePullback_map_attachedSource_target_reading_eq_spaces c₁ y b' b'₁ hfy Tm E₀ E₀'
    cmp hE _ rfl
  have HG := attachedSourceRightGlue_chase HS HR rfl
  have e1 := comp_five_eq_of_eq
    (comp_assoc_five_of_trans J'.hom (trans_trans_hom _ hJ') (trans_trans_hom _ rfl))
    (modulePullbackCompIso_app_hom_eq _ _ _) (eqToIso_hom_eq_pullbackTransport B S hS hab₁ Tm)
    (modulePullbackCompIso_app_symm_hom_eq _ _ _) (Functor.mapIso_hom _ _) rfl
  have HRR := attachedSourceRightRead_chase_factors HG J'.hom e1
  have e0 := comp_five_eq_of_eq
    (comp_assoc_five_of_trans J.hom (trans_trans_hom _ hJ) (trans_trans_hom _ rfl))
    (modulePullbackCompIso_app_hom_eq _ _ _) (eqToIso_hom_eq_pullbackTransport B S hS hab Tm)
    (modulePullbackCompIso_app_symm_hom_eq _ _ _) (Functor.mapIso_hom _ _) rfl
  rw [← modulePullbackCompHom_eq_hom_app]
  exact attachedSourceSquareLeft_chase_factors HRR J.hom e0 β hβ


/-- The comparison `g^*(M^a) ≅ (g^*M)^a` followed by the module map attached to `σ : g^*M ⟶ M'`,
read in a second spelling of the site: heterogeneously equal leaves give heterogeneously equal
composites. -/
theorem modulePullbackRepresentedQuasicoherentIso_hom_comp_map_heq {B₁ B₂ : BigFppfSite.{u}}
    (hB : B₁ = B₂) {S₁ S₂ : Scheme.{u}} (hSS : S₁ = S₂) {hS₁ : B₁.Contains S₁}
    {hS₂ : B₂.Contains S₂} {T₁ T₁' : BigFppfOver B₁ S₁ hS₁} {τ₁ : T₁' ⟶ T₁}
    {M₁ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B₁ S₁ hS₁).obj T₁).ringCatSheaf).FullSubcategory}
    {M₁' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B₁ S₁ hS₁).obj T₁').ringCatSheaf).FullSubcategory}
    {σ₁ : quasicoherentPullbackObj B₁ S₁ hS₁ τ₁ M₁ ⟶ M₁'}
    {T₂ T₂' : BigFppfOver B₂ S₂ hS₂} {τ₂ : T₂' ⟶ T₂}
    {M₂ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B₂ S₂ hS₂).obj T₂).ringCatSheaf).FullSubcategory}
    {M₂' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B₂ S₂ hS₂).obj T₂').ringCatSheaf).FullSubcategory}
    {σ₂ : quasicoherentPullbackObj B₂ S₂ hS₂ τ₂ M₂ ⟶ M₂'}
    (hT : HEq T₁ T₂) (hT' : HEq T₁' T₂') (hτ : HEq τ₁ τ₂) (hM : HEq M₁ M₂) (hM' : HEq M₁' M₂')
    (hσ : HEq σ₁ σ₂) :
    HEq ((modulePullbackRepresentedQuasicoherentIso B₁ S₁ hS₁ τ₁ M₁).hom ≫
          ((representedQuasicoherentSchemeEquivalence B₁ S₁ hS₁ T₁').functor.map σ₁).hom)
      ((modulePullbackRepresentedQuasicoherentIso B₂ S₂ hS₂ τ₂ M₂).hom ≫
          ((representedQuasicoherentSchemeEquivalence B₂ S₂ hS₂ T₂').functor.map σ₂).hom) := by
  subst hB hSS
  obtain rfl : hS₁ = hS₂ := rfl
  subst hT hT'
  subst hτ hM hM'
  subst hσ
  rfl

/-- **A square of a source factor, read in a second spelling of the site.**  Let
`τ^*s₁ ≫ β₁ = ((τ^*x₁^* ≅ (τ ≫ x₁)^*) ≫ transport) ≫ s₁'` be a square as
`AlgebraicGeometry.Space.chartSourceShaped_square` concludes it, over the site `B₁`, with
`β₁ = (τ^*(M^a) ≅ (τ^*M)^a) ≫ σ^a`.  Then the same square holds over a site `B₂ = B₁`, for data
heterogeneously equal to the data over `B₁`, in the shape of the first hypothesis of
`AlgebraicGeometry.Space.pullbackTransportSquare_of_squares` (the factorisation `f ≫ x = x'` taken
in the full subcategory). -/
theorem pullbackTransportSquare_source_of_heq {B₁ B₂ : BigFppfSite.{u}} (hB : B₁ = B₂)
    {S₁ S₂ : Scheme.{u}} (hSS : S₁ = S₂) {hS₁ : B₁.Contains S₁} {hS₂ : B₂.Contains S₂}
    {T₁ T₁' : BigFppfOver B₁ S₁ hS₁} {τ₁ : T₁' ⟶ T₁} {X₁ : AlgebraicSpaces B₁ S₁ hS₁}
    {x₁ : (⟨yoneda.obj T₁, isAlgebraicSpace_yoneda B₁ S₁ hS₁ T₁⟩ : AlgebraicSpaces B₁ S₁ hS₁) ⟶ X₁}
    {x₁' : (⟨yoneda.obj T₁', isAlgebraicSpace_yoneda B₁ S₁ hS₁ T₁'⟩ : AlgebraicSpaces B₁ S₁ hS₁) ⟶
      X₁}
    {h₁ : @CategoryStruct.comp (AlgebraicSpaces B₁ S₁ hS₁) _ _ _ _
      (representedSpaceMap B₁ S₁ hS₁ τ₁) x₁ = x₁'}
    {G₁ : Modules.{u, u} B₁ S₁ hS₁ X₁.1 X₁.2}
    {M₁ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B₁ S₁ hS₁).obj T₁).ringCatSheaf).FullSubcategory}
    {M₁' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B₁ S₁ hS₁).obj T₁').ringCatSheaf).FullSubcategory}
    {s₁ : (modulePullback B₁ S₁ hS₁ x₁).obj G₁ ⟶
      ((representedQuasicoherentSchemeEquivalence B₁ S₁ hS₁ T₁).functor.obj M₁).obj}
    {s₁' : (modulePullback B₁ S₁ hS₁ x₁').obj G₁ ⟶
      ((representedQuasicoherentSchemeEquivalence B₁ S₁ hS₁ T₁').functor.obj M₁').obj}
    {σ₁ : quasicoherentPullbackObj B₁ S₁ hS₁ τ₁ M₁ ⟶ M₁'}
    (H : (modulePullback B₁ S₁ hS₁ (representedSpaceMap B₁ S₁ hS₁ τ₁)).map s₁ ≫
        ((modulePullbackRepresentedQuasicoherentIso B₁ S₁ hS₁ τ₁ M₁).hom ≫
          ((representedQuasicoherentSchemeEquivalence B₁ S₁ hS₁ T₁').functor.map σ₁).hom) =
      ((modulePullbackCompIso B₁ S₁ hS₁ (representedSpaceMap B₁ S₁ hS₁ τ₁) x₁).hom.app G₁ ≫
        pullbackTransport G₁ h₁) ≫ s₁')
    {X₂ Y₂ Z₂ : AlgebraicSpaces B₂ S₂ hS₂} (f₂ : Z₂ ⟶ Y₂) (x₂ : Y₂ ⟶ X₂) (x₂' : Z₂ ⟶ X₂)
    (h₂ : f₂ ≫ x₂ = x₂') (G₂ : Modules.{u, u} B₂ S₂ hS₂ X₂.1 X₂.2)
    {A₂ : Modules.{u, u} B₂ S₂ hS₂ Y₂.1 Y₂.2} {A₂' : Modules.{u, u} B₂ S₂ hS₂ Z₂.1 Z₂.2}
    (s₂ : (modulePullback B₂ S₂ hS₂ x₂).obj G₂ ⟶ A₂)
    (s₂' : (modulePullback B₂ S₂ hS₂ x₂').obj G₂ ⟶ A₂')
    (β₂ : (modulePullback B₂ S₂ hS₂ f₂).obj A₂ ⟶ A₂')
    (hX : HEq X₁ X₂)
    (hY : HEq (⟨yoneda.obj T₁, isAlgebraicSpace_yoneda B₁ S₁ hS₁ T₁⟩ : AlgebraicSpaces B₁ S₁ hS₁)
      Y₂)
    (hZ : HEq (⟨yoneda.obj T₁', isAlgebraicSpace_yoneda B₁ S₁ hS₁ T₁'⟩ :
      AlgebraicSpaces B₁ S₁ hS₁) Z₂)
    (hf : HEq (representedSpaceMap B₁ S₁ hS₁ τ₁) f₂) (hx : HEq x₁ x₂) (hx' : HEq x₁' x₂')
    (hG : HEq G₁ G₂)
    (hA : HEq ((representedQuasicoherentSchemeEquivalence B₁ S₁ hS₁ T₁).functor.obj M₁).obj A₂)
    (hA' : HEq ((representedQuasicoherentSchemeEquivalence B₁ S₁ hS₁ T₁').functor.obj M₁').obj
      A₂')
    (hs : HEq s₁ s₂) (hs' : HEq s₁' s₂')
    (hβ : HEq ((modulePullbackRepresentedQuasicoherentIso B₁ S₁ hS₁ τ₁ M₁).hom ≫
          ((representedQuasicoherentSchemeEquivalence B₁ S₁ hS₁ T₁').functor.map σ₁).hom) β₂) :
    (modulePullback B₂ S₂ hS₂ f₂).map s₂ ≫ β₂ =
      ((modulePullbackCompIso B₂ S₂ hS₂ f₂ x₂).hom.app G₂ ≫ pullbackTransport G₂ h₂) ≫ s₂' := by
  subst hB hSS
  obtain rfl : hS₁ = hS₂ := rfl
  subst hX hY hZ
  subst hf hx hx' hG hA hA'
  subst hs hs' hβ
  -- the two factorisations are spelled differently; the transports agree by proof irrelevance
  have e : pullbackTransport G₁ h₂ = pullbackTransport G₁ h₁ := rfl
  rw [e]
  exact H

end Bridge

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

variable {s : RelativeProjSituation.{u, m}}
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} {f : X ⟶ s.shrink.space}
  {L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O)}
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  {ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L)}
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  {T T' : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase} (τ : T' ⟶ T)
  {w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj}
  {w' : yoneda.obj T' ⟶ (locusSpaceOfUnitalHom s f L ψ).obj} (hw : yoneda.map τ ≫ w = w')

/-- `AlgebraicGeometry.Space.chartSourceShaped_square` at the source identification
`…InvertibleTwistingRestriction.chartSourceIso` at `w`, read through its value. -/
theorem chartSource_square_of_point (d : ℤ) :
    type_of% (@AlgebraicGeometry.Space.chartSourceShaped_square s.site s.base s.containsBase
      _ _ _ _ _ _ _ _ _ (chartSourceIso Px w (locusOpen_locusPoint w) d) _
      (pointHom_comp_invertibleSpaceMorphism w) _ (chartSourceIso_eq_value Px w d)) :=
  @AlgebraicGeometry.Space.chartSourceShaped_square s.site s.base s.containsBase
    _ _ _ _ _ _ _ _ _ (chartSourceIso Px w (locusOpen_locusPoint w) d) _
    (pointHom_comp_invertibleSpaceMorphism w) _ (chartSourceIso_eq_value Px w d)

/-- `…InvertibleTwistingRestriction.chartSource_square_of_point` with the source identification
at `w'` read through its definition as well. -/
theorem chartSource_square_of_points (d : ℤ) :
    type_of% (chartSource_square_of_point Px (w := w) d
      (chartSourceIso Px w' (locusOpen_locusPoint w') d)
      (hab₁ := pointHom_comp_invertibleSpaceMorphism w') (chartSourceIso_eq_value Px w' d)) :=
  chartSource_square_of_point Px (w := w) d (chartSourceIso Px w' (locusOpen_locusPoint w') d)
    (hab₁ := pointHom_comp_invertibleSpaceMorphism w') (chartSourceIso_eq_value Px w' d)

include hw in
/-- **The square of the source factor of the chart maps along `τ : T' ⟶ T`**: for scheme points
`w` of `U(ψ)` at `T` and `w' = w ∘ τ` at `T'`, and a morphism
`y : T' ×_Y Proj_Y(𝒜) ⟶ T ×_Y Proj_Y(𝒜)` lying over `τ`, `τ^*` of the source identification
`w^*(r^*𝒪(d)) ≅ (c_w^*𝒪(d))^a` (`…InvertibleTwistingRestriction.chartSourceIso`), followed by
`β = (τ^*((c_w^*𝒪(d))^a) ≅ (τ^*c_w^*𝒪(d))^a) ≫ σ^a` for the comparison
`σ : τ^*c_w^*𝒪(d) ⟶ c_{w'}^*𝒪(d)` of the two pullbacks (through `c_w ∘ τ = y ∘ c_{w'}` and the
comparison of the twists of Stacks 084D), is the comparison of Stacks 03LU for `τ` and `w`, the
transport along `w ∘ τ = w'`, and the source identification at `w'`.

This is the first hypothesis of `AlgebraicGeometry.Space.pullbackTransportSquare_of_squares` for
the chart maps; `σ` and `β` are variables with their values as equations. -/
theorem chartSource_square (d : ℤ)
    (y : s.relativeProjPoints.fibre T' (locusPoint w' ≫ f.hom) ⟶
      s.relativeProjPoints.fibre T (locusPoint w ≫ f.hom))
    (hy : s.relativeProjPoints.LiesOver y τ)
    (hfy : representedSpaceMap s.site s.base s.containsBase y ≫
        s.fibreToSpaceHom T (locusPoint w ≫ f.hom) =
      s.fibreToSpaceHom T' (locusPoint w' ≫ f.hom))
    (σ : quasicoherentPullbackObj s.site s.base s.containsBase τ
        (quasicoherentPullbackObj s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
          (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d)) ⟶
      quasicoherentPullbackObj s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w') (locusOpen_locusPoint w'))
        (s.twistPieceQcoh T' (locusPoint w' ≫ f.hom) d))
    (hσ : σ = (quasicoherentPullbackCompIso s.site s.base s.containsBase τ
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
        (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d)).hom ≫
      quasicoherentPullbackEqToHom s.site s.base s.containsBase
        (comp_chartSection_locusPoint τ hw y hy) (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d) ≫
      (quasicoherentPullbackCompIso s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w') (locusOpen_locusPoint w')) y
        (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d)).inv ≫
      quasicoherentPullbackMap s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w') (locusOpen_locusPoint w'))
        (s.twistPieceComparison τ (map_comp_locusPoint_comp τ hw) y hy d).hom)
    (β : (modulePullback s.site s.base s.containsBase
        (representedSpaceMap s.site s.base s.containsBase τ)).obj
        ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase T).functor.obj
          (quasicoherentPullbackObj s.site s.base s.containsBase
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
            (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d))).obj ⟶
      ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase T').functor.obj
        (quasicoherentPullbackObj s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w') (locusOpen_locusPoint w'))
          (s.twistPieceQcoh T' (locusPoint w' ≫ f.hom) d))).obj)
    (hβ : β = (modulePullbackRepresentedQuasicoherentIso s.site s.base s.containsBase τ
        (quasicoherentPullbackObj s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
          (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d))).hom ≫
      ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase T').functor.map
        σ).hom) :
    type_of% (chartSource_square_of_points Px (w := w) (w' := w') d (τ : _)
      (pointHom_comp τ hw : _) y
      (comp_chartSection_locusPoint τ hw y hy : _) (hfy : _)
      (s.twistPieceComparison τ (map_comp_locusPoint_comp τ hw) y hy d : _)
      (s.fibreToSpaceTwistModuleIso_comp_of_eq Px τ (locusPoint w ≫ f.hom)
        (locusPoint w' ≫ f.hom) (map_comp_locusPoint_comp τ hw) y hy d hfy : _)
      (σ : _) (hσ : _) (β : _) (hβ : _)) :=
  chartSource_square_of_points Px (w := w) (w' := w') d (τ : _) (pointHom_comp τ hw : _) y
    (comp_chartSection_locusPoint τ hw y hy : _) (hfy : _)
    (s.twistPieceComparison τ (map_comp_locusPoint_comp τ hw) y hy d : _)
    (s.fibreToSpaceTwistModuleIso_comp_of_eq Px τ (locusPoint w ≫ f.hom)
      (locusPoint w' ≫ f.hom) (map_comp_locusPoint_comp τ hw) y hy d hfy : _)
    (σ : _) (hσ : _) (β : _) (hβ : _)

include hw in
/-- **The square of the source factor of the chart maps along `τ : T' ⟶ T`, over the site of
`s.shrink`**: `…InvertibleTwistingRestriction.chartSource_square`, with
`β = (τ^*((c_w^*𝒪(d))^a) ≅ (τ^*c_w^*𝒪(d))^a) ≫ σ^a`, read over `s.shrink.site`, where the chart
maps `…InvertibleTwistingRestriction.chartMap` and their compatibility
(`AlgebraicGeometry.Space.PointFamilyNatural`) live.

The statement is the first hypothesis of
`AlgebraicGeometry.Space.pullbackTransportSquare_of_squares` for `f = τ`, `x = w`, `x' = w'`,
`h = w ∘ τ = w'`, `G = r^*𝒪(d)` (`…thetaSourceOfUnitalHom`), `s, s'` the source identifications at
`w` and `w'` (`…chartSourceIso`), and `β` the comparison
`(modulePullbackRepresentedQuasicoherentIso τ _).hom` followed by the module map attached to `σ`
over `s.shrink.site` -- the `β` of
`AlgebraicGeometry.Space.modulePullback_map_functor_map_comp_eq_of_square` there. -/
theorem chartSource_square_shrink (d : ℤ)
    (y : s.relativeProjPoints.fibre T' (locusPoint w' ≫ f.hom) ⟶
      s.relativeProjPoints.fibre T (locusPoint w ≫ f.hom))
    (hy : s.relativeProjPoints.LiesOver y τ)
    (hfy : representedSpaceMap s.site s.base s.containsBase y ≫
        s.fibreToSpaceHom T (locusPoint w ≫ f.hom) =
      s.fibreToSpaceHom T' (locusPoint w' ≫ f.hom))
    (σ : quasicoherentPullbackObj s.site s.base s.containsBase τ
        (quasicoherentPullbackObj s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
          (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d)) ⟶
      quasicoherentPullbackObj s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w') (locusOpen_locusPoint w'))
        (s.twistPieceQcoh T' (locusPoint w' ≫ f.hom) d))
    (hσ : σ = (quasicoherentPullbackCompIso s.site s.base s.containsBase τ
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
        (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d)).hom ≫
      quasicoherentPullbackEqToHom s.site s.base s.containsBase
        (comp_chartSection_locusPoint τ hw y hy) (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d) ≫
      (quasicoherentPullbackCompIso s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w') (locusOpen_locusPoint w')) y
        (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d)).inv ≫
      quasicoherentPullbackMap s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w') (locusOpen_locusPoint w'))
        (s.twistPieceComparison τ (map_comp_locusPoint_comp τ hw) y hy d).hom) :
    type_of% (pullbackTransportSquare_source_of_heq s.shrink_site.symm s.shrink_base.symm
      (hS₂ := s.shrink.containsBase) (chartSource_square Px τ hw d y hy hfy σ hσ _ rfl : _)
      (representedSpaceMap s.shrink.site s.shrink.base s.shrink.containsBase τ)
      (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)
      (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w') (pointHom_comp τ hw)
      (thetaSourceOfUnitalHom s f L ψ Px d).obj
      (chartSourceIso Px w (locusOpen_locusPoint w) d).hom
      (chartSourceIso Px w' (locusOpen_locusPoint w') d).hom
      ((modulePullbackRepresentedQuasicoherentIso s.shrink.site s.shrink.base
          s.shrink.containsBase τ
          (quasicoherentPullbackObj s.site s.base s.containsBase
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
            (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d))).hom ≫
        ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
          s.shrink.containsBase T').functor.map σ).hom)
      HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
      (modulePullbackRepresentedQuasicoherentIso_hom_comp_map_heq s.shrink_site.symm
        s.shrink_base.symm HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl)) :=
  pullbackTransportSquare_source_of_heq s.shrink_site.symm s.shrink_base.symm
    (hS₂ := s.shrink.containsBase) (chartSource_square Px τ hw d y hy hfy σ hσ _ rfl : _)
    (representedSpaceMap s.shrink.site s.shrink.base s.shrink.containsBase τ)
    (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)
    (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w') (pointHom_comp τ hw)
    (thetaSourceOfUnitalHom s f L ψ Px d).obj
    (chartSourceIso Px w (locusOpen_locusPoint w) d).hom
    (chartSourceIso Px w' (locusOpen_locusPoint w') d).hom
    ((modulePullbackRepresentedQuasicoherentIso s.shrink.site s.shrink.base
        s.shrink.containsBase τ
        (quasicoherentPullbackObj s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
          (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d))).hom ≫
      ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
        s.shrink.containsBase T').functor.map σ).hom)
    HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
    (modulePullbackRepresentedQuasicoherentIso_hom_comp_map_heq s.shrink_site.symm
      s.shrink_base.symm HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl)

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction


end
