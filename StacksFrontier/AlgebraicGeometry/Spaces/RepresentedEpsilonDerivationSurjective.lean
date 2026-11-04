module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedEpsilonDerivationExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpChartPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleToposSupplement

/-!
# Stacks 0D0X: every Zariski derivation into `ε_*T` comes from an étale one

Let `φ : U ⟶ V` be a morphism of the big fppf site over `S`, `f₀ : X₀ ⟶ Y₀` the underlying
morphism of schemes, `f = h_φ : X ⟶ Y` the morphism of algebraic spaces it represents and
`ε : X_étale ⟶ X_{0,Zar}` the morphism of Stacks 08H7.  Let `T` be a sheaf of `𝒪_X`-modules and
`D₀` an `f₀^{-1}𝒪_{Y₀}`-derivation of `𝒪_{X₀}` with values in `ε_*T`.

The local extensions of `D₀` over the affine charts `A ⟶ ε(Z)`, `Z` an affine open
(`AlgebraicGeometry.Space.representedEpsilonLocalDerivation`), glue to a derivation of `𝒪_X`
(`Stacks.SheafOfModules.glueDerivationOfCover`).  It is an `f^{-1}𝒪_Y`-derivation: it kills every
chartwise pullback of a regular function of `Y`, since locally such a pullback comes from an
affine open `O` étale over an affine open `W` of `Y₀`, and a Leibniz map on `Γ(O)` killing the
image of the formally unramified `Γ(W) ⟶ Γ(O)` is zero; and the chartwise pullbacks test the
image of `f♯`, through sheaves of sets of the universe of the structure rings
(`Stacks.SheafOfModules.exists_typeSheafHom_app_eq_iff`,
`AlgebraicGeometry.Space.structureSharpInverseImageSet_comp_eq_iff_chartPullback`).  Its
restriction along `ε` is `D₀`.

So the restriction of derivations along `ε` is bijective for every `T`, and the adjunct of the
map induced on the cokernels of the differentials of the naive cotangent complexes is an
isomorphism.

## Main definitions

* `AlgebraicGeometry.Space.representedEpsilonGluedDerivation`: the glued derivation.

## Main results

* `AlgebraicGeometry.Space.representedEpsilonGlueValue_chartPullback`: the glued values kill the
  chartwise pullbacks.
* `AlgebraicGeometry.Space.representedEpsilonDerivationRestriction_surjective`: the restriction
  of derivations along `ε` is surjective.
* `AlgebraicGeometry.Space.isIso_representedEpsilonCokernelHom_adjunct`: the adjunct
  `ε^*(coker d₀) ⟶ coker d` is an isomorphism.

## References

* [Stacks Project, Tag 0D0X](https://stacks.math.columbia.edu/tag/0D0X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U V : BigFppfOver B S hS}
  (φ : U ⟶ V)

/-- **A Leibniz map vanishing on the image of a formally unramified ring map kills everything
pulled back along a further ring map.**  For `q : R ⟶ A` formally unramified, `k : A ⟶ B` and a
Leibniz map `δ : B ⟶ M`, if `δ ∘ k ∘ q = 0` then `δ ∘ k = 0`. -/
theorem leibnizHom_comp_eq_zero_of_formallyUnramified {R A Bb : CommRingCat.{u}} (q : R ⟶ A)
    (hq : q.hom.FormallyUnramified) (k : A ⟶ Bb) {M : Type*} [AddCommGroup M] [Module Bb M]
    (δ : Bb →+ M) (hmul : ∀ x y : Bb, δ (x * y) = x • δ y + y • δ x)
    (hvanish : ∀ r : R, δ (k (q r)) = 0) (a : A) : δ (k a) = 0 := by
  let : Module A M := Module.compHom M k.hom
  refine leibnizHom_eq_zero_of_formallyUnramified q hq (δ.comp k.hom.toAddMonoidHom)
    (fun x y => ?_) hvanish a
  show δ (k (x * y)) = k x • δ (k y) + k y • δ (k x)
  rw [map_mul]
  exact hmul _ _

/-- Global sections along two factorizations of one morphism of schemes agree. -/
theorem Γ_map_apply_of_comp_eq {P Q Q' R : Scheme.{u}} {a : P ⟶ Q} {c : Q ⟶ R} {k : P ⟶ Q'}
    {ι : Q' ⟶ R} (h : a ≫ c = k ≫ ι) (x : ToType (Scheme.Γ.obj (op R))) :
    Scheme.Γ.map a.op (Scheme.Γ.map c.op x) = Scheme.Γ.map k.op (Scheme.Γ.map ι.op x) := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, h, op_comp, Functor.map_comp,
    ConcreteCategory.comp_apply]

attribute [local instance] isContinuous_representedToZariskiRingedToposSiteHom_u

variable (T : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O))
  (D₀ : ((representedEpsilonModulePushforward B S hS U).obj T).val.Derivation'
    (representedZariskiSchemeHom B S hS φ).fSharpInverseImage.hom)

/-- Two sections of `T` agreeing over a covering sieve are equal. -/
theorem representedEpsilonSheaf_ext {A : SmallEtale B S hS (yoneda.obj U)}
    {R : Sieve A} (hR : R ∈ (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J A)
    (x y : ToType (T.val.presheaf.obj (op A)))
    (h : ∀ (Y : SmallEtale B S hS (yoneda.obj U)) (g : Y ⟶ A), R g →
      T.val.presheaf.map g.op x = T.val.presheaf.map g.op y) : x = y :=
  T.isSheaf.isSeparated A R hR x y h

/-- Restriction in the structure sheaf of `X = h_U` along a composite. -/
theorem representedStructureSheaf_map_comp_apply {Y₁ Y₂ Y₃ : SmallEtale B S hS (yoneda.obj U)}
    (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃)
    (x : ToType ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.obj
      (op Y₃))) :
    (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.map (f ≫ g).op x =
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.map f.op
        ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.map g.op x) := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- The local extension of `D₀` over an affine chart with a morphism to the chart of an
affine open, at the chosen such open. -/
def representedEpsilonGlueFamily (A : SmallEtale B S hS (yoneda.obj U))
    (hA : representedEpsilonAffineChart B S hS U A) :
    ToType ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.obj
      (op A)) →+ T.val.obj (op A) :=
  representedEpsilonLocalDerivation B S hS φ T D₀ hA.2.choose_spec.2.some hA.2.choose_spec.1 hA.1

/-- The local extension of `D₀` over an affine chart `A` does not depend on the chosen affine
open: it agrees with the local extension along any morphism `j : A ⟶ ε(Z)`, `Z` affine. -/
theorem representedEpsilonGlueFamily_eq {A : SmallEtale B S hS (yoneda.obj U)}
    (hA : representedEpsilonAffineChart B S hS U A)
    {Z : ((BigFppfOver.toScheme B S hS).obj U).Opens}
    (j : A ⟶ (representedEpsilonFunctor B S hS U).obj Z) (hZ : IsAffineOpen Z)
    (r : ToType ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.obj
      (op A))) :
    representedEpsilonGlueFamily B S hS φ T D₀ A hA r =
      representedEpsilonLocalDerivation B S hS φ T D₀ j hZ hA.1 r :=
  representedEpsilonLocalDerivation_eq B S hS φ T D₀ _ j _ hZ hA.1 r

/-- The local extensions of `D₀` over affine charts commute with restriction along a morphism
`m : A₂ ⟶ A₁` of affine charts. -/
theorem representedEpsilonGlueFamily_naturality {A₁ A₂ : SmallEtale B S hS (yoneda.obj U)}
    (h₂ : representedEpsilonAffineChart B S hS U A₂)
    (h₁ : representedEpsilonAffineChart B S hS U A₁) (m : A₂ ⟶ A₁)
    (r : ToType ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.obj
      (op A₁))) :
    representedEpsilonGlueFamily B S hS φ T D₀ A₂ h₂
        ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.map m.op r) =
      T.val.presheaf.map m.op (representedEpsilonGlueFamily B S hS φ T D₀ A₁ h₁ r) :=
  (representedEpsilonGlueFamily_eq B S hS φ T D₀ h₂ (m ≫ h₁.2.choose_spec.2.some)
    h₁.2.choose_spec.1 _).trans
    (representedEpsilonLocalDerivation_comp B S hS φ T D₀ m h₁.2.choose_spec.2.some
      (m ≫ h₁.2.choose_spec.2.some) h₁.2.choose_spec.1 h₁.2.choose_spec.1 h₁.1 h₂.1 le_rfl r)

/-- The glued values of the local extensions of `D₀`. -/
def representedEpsilonGlueValue (A : SmallEtale B S hS (yoneda.obj U))
    (r : ToType ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.obj
      (op A))) : T.val.obj (op A) :=
  Stacks.SheafOfModules.glueDerivationOfCoverValue (representedEpsilonAffineChart B S hS U)
    (generate_representedEpsilonAffineChart_mem B S hS U φ)
    (representedEpsilonGlueFamily B S hS φ T D₀)
    (fun h₂ h₁ m r => representedEpsilonGlueFamily_naturality B S hS φ T D₀ h₂ h₁ m r) A r

/-- The restriction of a glued value to an affine chart `Y` is the local extension of `D₀` over
`Y` applied to the restricted section. -/
theorem representedEpsilonGlueValue_map {A Y : SmallEtale B S hS (yoneda.obj U)}
    (hY : representedEpsilonAffineChart B S hS U Y) (f : Y ⟶ A)
    (r : ToType ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.obj
      (op A))) :
    T.val.presheaf.map f.op (representedEpsilonGlueValue B S hS φ T D₀ A r) =
      representedEpsilonGlueFamily B S hS φ T D₀ Y hY
        ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.map f.op r) :=
  Stacks.SheafOfModules.glueDerivationOfCoverValue_map _ _ _ _ hY f r

/-- The glued values commute with restriction along a morphism `f : A' ⟶ A`. -/
theorem representedEpsilonGlueValue_naturality {A A' : SmallEtale B S hS (yoneda.obj U)}
    (f : A' ⟶ A)
    (r : ToType ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.obj
      (op A))) :
    representedEpsilonGlueValue B S hS φ T D₀ A'
        ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.map f.op r) =
      T.val.presheaf.map f.op (representedEpsilonGlueValue B S hS φ T D₀ A r) :=
  Stacks.SheafOfModules.glueDerivationOfCoverValue_naturality _ _ _ _ f r

/-- The glued value of `0` is `0`. -/
theorem representedEpsilonGlueValue_zero (A : SmallEtale B S hS (yoneda.obj U)) :
    representedEpsilonGlueValue B S hS φ T D₀ A 0 = 0 :=
  Stacks.SheafOfModules.glueDerivationOfCoverValue_zero (T := T) _ _ _ _ A

/-- **The glued values over the chart of a Zariski open are the seed**: over `ε(Z)`, the glued
value of `x ∈ 𝒪_X(ε Z) = Γ(Z)` is `D₀ x`. -/
theorem representedEpsilonGlueValue_eq_seed (Z : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (x : ToType ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.obj
      (op ((representedEpsilonFunctor B S hS U).obj Z)))) :
    representedEpsilonGlueValue B S hS φ T D₀ ((representedEpsilonFunctor B S hS U).obj Z) x =
      representedEpsilonDerivationSeed B S hS φ T D₀ Z x := by
  refine representedEpsilonSheaf_ext B S hS T (generate_affineChart_le_mem B S hS φ (𝟙 _)) _ _ ?_
  rintro Y g ⟨Y', h, g', ⟨hY', Z₂, hZ₂, hle, ⟨j₂⟩⟩, rfl⟩
  have hw : g' = j₂ ≫ (representedEpsilonFunctor B S hS U).map (homOfLE hle) :=
    Subsingleton.elim _ _
  have hY : representedEpsilonAffineChart B S hS U Y' := ⟨hY', Z₂, hZ₂, ⟨j₂⟩⟩
  have hTT : ∀ (y : ToType (T.val.presheaf.obj
      (op ((representedEpsilonFunctor B S hS U).obj Z)))),
      T.val.presheaf.map j₂.op (T.val.presheaf.map
        ((representedEpsilonFunctor B S hS U).map (homOfLE hle)).op y) =
        T.val.presheaf.map g'.op y := by
    intro y
    rw [hw, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  have hOO : (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.map g'.op x =
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.map j₂.op
        ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.map
          ((representedEpsilonFunctor B S hS U).map (homOfLE hle)).op x) := by
    rw [hw]
    exact representedStructureSheaf_map_comp_apply B S hS _ _ x
  have key : T.val.presheaf.map g'.op
      (representedEpsilonGlueValue B S hS φ T D₀ ((representedEpsilonFunctor B S hS U).obj Z) x) =
      T.val.presheaf.map g'.op (representedEpsilonDerivationSeed B S hS φ T D₀ Z x) := by
    refine (representedEpsilonGlueValue_map B S hS φ T D₀ hY g' x).trans ?_
    refine (representedEpsilonGlueFamily_eq B S hS φ T D₀ hY j₂ hZ₂ _).trans ?_
    refine (congrArg (representedEpsilonLocalDerivation B S hS φ T D₀ j₂ hZ₂ hY') hOO).trans ?_
    refine (representedEpsilonLocalDerivation_map B S hS φ T D₀ j₂ hZ₂ hY' _).trans ?_
    refine (congrArg (T.val.presheaf.map j₂.op).hom
      (representedEpsilonDerivationSeed_map B S hS φ T D₀ hle x)).trans ?_
    exact hTT _
  rw [op_comp, Functor.map_comp]
  exact congrArg (T.val.presheaf.map h.op).hom key

/-- **The local extension kills the functions pulled back along the chart diagram of a Zariski
square**: for `Z ⊆ f₀⁻¹W`, the extension over an affine chart `A ⟶ ε(Z)` vanishes on the image of
`𝒪_Y(ε W) ⟶ 𝒪_X(ε Z) ⟶ 𝒪_X(A)`. -/
theorem representedEpsilonLocalDerivation_chartDiagram_eq_zero
    {A : SmallEtale B S hS (yoneda.obj U)} {Z : ((BigFppfOver.toScheme B S hS).obj U).Opens}
    {W : ((BigFppfOver.toScheme B S hS).obj V).Opens}
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (j : A ⟶ (representedEpsilonFunctor B S hS U).obj Z) (hZ : IsAffineOpen Z)
    (hA : IsAffine ((SmallEtale.toOver B S hS (yoneda.obj U) ⋙ BigFppfOver.toScheme B S hS).obj
      A))
    (r : ToType ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O.obj.obj
      (op ((representedEpsilonFunctor B S hS V).obj W)))) :
    representedEpsilonLocalDerivation B S hS φ T D₀ j hZ hA
      ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.map j.op
        (chartDiagramRingHom B S hS (representedSpaceMap B S hS φ)
          (representedEpsilonChartDiagram B S hS φ hZW) r)) = 0 := by
  have h0 : representedEpsilonDerivationSeed B S hS φ T D₀ Z
      (chartDiagramRingHom B S hS (representedSpaceMap B S hS φ)
        (representedEpsilonChartDiagram B S hS φ hZW) r) = 0 :=
    (congrArg (D₀.d (X := op Z)) (representedChartToZariski_comm B S hS φ hZW r)).trans
      (D₀.d_app _)
  refine (representedEpsilonLocalDerivation_map B S hS φ T D₀ j hZ hA _).trans ?_
  exact (congrArg (T.val.map j.op).hom h0).trans (map_zero _)

/-- The scheme morphism underlying a morphism of étale charts of `h_U` commutes with the
structure morphisms to `X₀`. -/
theorem toScheme_map_toOver_map_comp_yonedaEquiv {A₁ A₂ : SmallEtale B S hS (yoneda.obj U)}
    (h : A₁ ⟶ A₂) :
    (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS (yoneda.obj U)).map h) ≫
        (BigFppfOver.toScheme B S hS).map (yonedaEquiv A₂.1.hom) =
      (BigFppfOver.toScheme B S hS).map (yonedaEquiv A₁.1.hom) := by
  rw [← Functor.map_comp]
  congr 1
  apply yoneda.map_injective
  rw [Functor.map_comp, yoneda_map_yonedaEquiv, yoneda_map_yonedaEquiv]
  exact h.hom.w

/-- The vertical morphism of a diagram of charts over `h_φ` lies over `f₀`. -/
theorem toScheme_map_chartDiagram_g_comp_yonedaEquiv
    (d : ChartDiagram B S hS (representedAlgebraicSpace B S hS U).1
      (representedAlgebraicSpace B S hS V).1 (representedSpaceMap B S hS φ).hom) :
    (BigFppfOver.toScheme B S hS).map d.g ≫
        (BigFppfOver.toScheme B S hS).map (yonedaEquiv d.V.1.hom) =
      (BigFppfOver.toScheme B S hS).map (yonedaEquiv d.U.1.hom) ≫
        (BigFppfOver.toScheme B S hS).map φ := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply yoneda.map_injective
  rw [Functor.map_comp, Functor.map_comp, yoneda_map_yonedaEquiv, yoneda_map_yonedaEquiv]
  exact d.comm.symm

/-- An étale chart of `h_U` whose structure morphism to `X₀` lands in a Zariski open `Z` maps to
the chart `ε(Z)`, by the image-open adjunction. -/
theorem nonempty_hom_representedEpsilonFunctor_obj_of_range {A : SmallEtale B S hS (yoneda.obj U)}
    {Z : ((BigFppfOver.toScheme B S hS).obj U).Opens}
    (h : Set.range ((BigFppfOver.toScheme B S hS).map (yonedaEquiv A.1.hom)) ⊆ (Z : Set _)) :
    Nonempty (A ⟶ (representedEpsilonFunctor B S hS U).obj Z) :=
  ⟨(representedImageOpenEpsilonAdjunction B S hS U).homEquiv A Z (homOfLE h)⟩

/-- **The local extension kills the functions pulled back from an affine open over an affine
open of `Y₀`.**  Let `b : C ⟶ Y₀` be étale, `O ⊆ b⁻¹W` affine opens, `A ⟶ ε(Z)` an affine chart
with `Z ⊆ f₀⁻¹W` affine, and `k : A ⟶ O` lying over `f₀`.  Then the local extension `δ` over `A`
satisfies `δ(k^*(x|_O)) = 0` for every `x ∈ Γ(C)`. -/
theorem representedEpsilonLocalDerivation_pullback_eq_zero
    {A : SmallEtale B S hS (yoneda.obj U)} {Z : ((BigFppfOver.toScheme B S hS).obj U).Opens}
    {W : ((BigFppfOver.toScheme B S hS).obj V).Opens} {C : Scheme.{u}} (O : C.Opens)
    (hA : IsAffine ((SmallEtale.toOver B S hS (yoneda.obj U) ⋙ BigFppfOver.toScheme B S hS).obj
      A))
    (hZ : IsAffineOpen Z) (hW : IsAffineOpen W) (hO : IsAffineOpen O)
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (b : C ⟶ (BigFppfOver.toScheme B S hS).obj V)
    [Etale b] (hOW : O ≤ b ⁻¹ᵁ W) (j : A ⟶ (representedEpsilonFunctor B S hS U).obj Z)
    (k : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS _).obj A) ⟶ O.toScheme)
    (hk : k ≫ O.ι ≫ b = (BigFppfOver.toScheme B S hS).map (yonedaEquiv A.1.hom) ≫
      (BigFppfOver.toScheme B S hS).map φ)
    (x : Γ(C, ⊤)) :
    representedEpsilonLocalDerivation B S hS φ T D₀ j hZ hA
      (Scheme.Γ.map k.op (Scheme.Γ.map O.ι.op x)) = 0 := by
  have hrange : Set.range (O.ι ≫ b) ⊆ Set.range W.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hOW ((Scheme.Opens.range_ι O).le ⟨y, rfl⟩)
  let q : O.toScheme ⟶ W.toScheme := IsOpenImmersion.lift W.ι (O.ι ≫ b) hrange
  have hq : q ≫ W.ι = O.ι ≫ b := IsOpenImmersion.lift_fac _ _ _
  have : Etale (q ≫ W.ι) := by rw [hq]; infer_instance
  have : Etale q := Etale.of_comp q W.ι
  have : IsAffine W.toScheme := hW
  have : IsAffine O.toScheme := hO
  have hfu : (Scheme.Γ.map q.op).hom.FormallyUnramified := by
    rw [(Scheme.Γ_map_op _).trans (Scheme.Hom.appLE_eq_app _).symm]
    exact q.formallyUnramified_appLE (isAffineOpen_top _) (isAffineOpen_top _) le_rfl
  have hεW := toScheme_representedChartBase_representedOpenChart B S hS V W
  have hg := toScheme_map_chartDiagram_g_comp_yonedaEquiv B S hS φ
    (representedEpsilonChartDiagram B S hS φ hZW)
  have hj := toScheme_map_toOver_map_comp_yonedaEquiv B S hS j
  let dg : (BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS (yoneda.obj U)).obj ((representedEpsilonFunctor B S hS U).obj Z)) ⟶
      W.toScheme := (BigFppfOver.toScheme B S hS).map
        (representedEpsilonChartDiagram B S hS φ hZW).g
  have hkq : k ≫ q = (BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS (yoneda.obj U)).map j) ≫ dg := by
    refine (cancel_mono W.ι).1 ?_
    rw [Category.assoc, hq, hk, Category.assoc, ← hj, Category.assoc]
    refine congrArg (_ ≫ ·) ?_
    exact hg.symm.trans (congrArg (dg ≫ ·) hεW)
  refine leibnizHom_comp_eq_zero_of_formallyUnramified (Scheme.Γ.map q.op) hfu
    (show Scheme.Γ.obj (op O.toScheme) ⟶
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.obj (op A) from
      Scheme.Γ.map k.op) (M := ToType (T.val.obj (op A)))
    (representedEpsilonLocalDerivation B S hS φ T D₀ j hZ hA)
    (representedEpsilonLocalDerivation_mul B S hS φ T D₀ j hZ hA) (fun w => ?_) _
  have e : Scheme.Γ.map k.op (Scheme.Γ.map q.op w) =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS (yoneda.obj U)).map j)).op (Scheme.Γ.map dg.op w) := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hkq, op_comp,
      Functor.map_comp, ConcreteCategory.comp_apply]
  refine (congrArg (representedEpsilonLocalDerivation B S hS φ T D₀ j hZ hA) e).trans ?_
  exact representedEpsilonLocalDerivation_chartDiagram_eq_zero B S hS φ T D₀ hZW j hZ hA w

/-- **The glued values kill every chartwise pullback of a regular function from an étale chart
of `Y = h_V`.** -/
theorem representedEpsilonGlueValue_chartPullback (V' : SmallEtale B S hS (yoneda.obj V))
    (j : StructuredArrow (op (chartBaseChange B S hS (representedSpaceMap B S hS φ) V'))
      (comparisonFunctor B S hS (representedAlgebraicSpace B S hS U)).op)
    (g : (structureSetSheaf B S hS (representedAlgebraicSpace B S hS V)).obj.obj (op V')) :
    representedEpsilonGlueValue B S hS φ T D₀ j.right.unop
      (chartPullback B S hS (representedSpaceMap B S hS φ) V' j g) = 0 := by
  have hk : (BigFppfOver.toScheme B S hS).map
        (chartBaseChangeMap B S hS (representedSpaceMap B S hS φ) V' j) ≫
        (BigFppfOver.toScheme B S hS).map (yonedaEquiv V'.1.hom) =
      (BigFppfOver.toScheme B S hS).map (yonedaEquiv j.right.unop.1.hom) ≫
        (BigFppfOver.toScheme B S hS).map φ := by
    have hc := chartBaseChangeMap_comm B S hS (representedSpaceMap B S hS φ) j.right.unop V'
      j.hom.unop
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_comp, yoneda_map_yonedaEquiv, yoneda_map_yonedaEquiv]
    exact hc.symm
  refine representedEpsilonSheaf_ext B S hS T (R := Sieve.generate fun Y (h : Y ⟶ j.right.unop) =>
      IsAffine ((SmallEtale.toOver B S hS (yoneda.obj U) ⋙ BigFppfOver.toScheme B S hS).obj Y) ∧
      ∃ (Z₂ : ((BigFppfOver.toScheme B S hS).obj U).Opens)
        (W : ((BigFppfOver.toScheme B S hS).obj V).Opens)
        (O : ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS _).obj V')).Opens),
        IsAffineOpen Z₂ ∧ IsAffineOpen W ∧ IsAffineOpen O ∧
        Z₂ ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W ∧
        O ≤ (BigFppfOver.toScheme B S hS).map (yonedaEquiv V'.1.hom) ⁻¹ᵁ W ∧
        Nonempty (Y ⟶ (representedEpsilonFunctor B S hS U).obj Z₂) ∧
        ∃ k : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS _).obj Y) ⟶ O.toScheme,
          k ≫ O.ι = (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS _).map h) ≫
            (BigFppfOver.toScheme B S hS).map
              (chartBaseChangeMap B S hS (representedSpaceMap B S hS φ) V' j)) ?_ _ _ ?_
  · rw [SmallEtale.mem_topology_iff_exists_mem_range]
    intro x
    obtain ⟨_, ⟨W, hW, rfl⟩, hpW, -⟩ :=
      ((BigFppfOver.toScheme B S hS).obj V).isBasis_affineOpens.exists_subset_of_mem_open
        (show (BigFppfOver.toScheme B S hS).map (yonedaEquiv V'.1.hom)
          ((BigFppfOver.toScheme B S hS).map
            (chartBaseChangeMap B S hS (representedSpaceMap B S hS φ) V' j) x) ∈
            (⊤ : Set _) from trivial) isOpen_univ
    obtain ⟨_, ⟨O, hO, rfl⟩, hyO, hOle⟩ :=
      (Scheme.isBasis_affineOpens _).exists_subset_of_mem_open
        (show (BigFppfOver.toScheme B S hS).map
            (chartBaseChangeMap B S hS (representedSpaceMap B S hS φ) V' j) x ∈
          (BigFppfOver.toScheme B S hS).map (yonedaEquiv V'.1.hom) ⁻¹ᵁ W from hpW)
        ((BigFppfOver.toScheme B S hS).map (yonedaEquiv V'.1.hom) ⁻¹ᵁ W).isOpen
    have hx₀ : (BigFppfOver.toScheme B S hS).map φ
        ((BigFppfOver.toScheme B S hS).map (yonedaEquiv j.right.unop.1.hom) x) ∈ W := by
      rwa [← Scheme.Hom.comp_apply, ← hk, Scheme.Hom.comp_apply]
    obtain ⟨_, ⟨Z₂, hZ₂, rfl⟩, hxZ, hZle⟩ :=
      (Scheme.isBasis_affineOpens _).exists_subset_of_mem_open
        (show (BigFppfOver.toScheme B S hS).map (yonedaEquiv j.right.unop.1.hom) x ∈
          (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W from hx₀)
        ((BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W).isOpen
    obtain ⟨_, ⟨N, hN, rfl⟩, hxN, hNle⟩ :=
      (Scheme.isBasis_affineOpens _).exists_subset_of_mem_open
        (show x ∈ (BigFppfOver.toScheme B S hS).map
            (chartBaseChangeMap B S hS (representedSpaceMap B S hS φ) V' j) ⁻¹ᵁ O ⊓
            (BigFppfOver.toScheme B S hS).map (yonedaEquiv j.right.unop.1.hom) ⁻¹ᵁ Z₂ from
          ⟨hyO, hxZ⟩)
        (((BigFppfOver.toScheme B S hS).map
            (chartBaseChangeMap B S hS (representedSpaceMap B S hS φ) V' j) ⁻¹ᵁ O ⊓
            (BigFppfOver.toScheme B S hS).map (yonedaEquiv j.right.unop.1.hom) ⁻¹ᵁ Z₂).isOpen)
    have hι := toScheme_map_toOver_map_openChartInclusion B S hS _ j.right.unop N
    have hπ := toScheme_map_toOver_map_comp_yonedaEquiv B S hS
      (openChartInclusion B S hS _ j.right.unop N)
    refine ⟨_, openChartInclusion B S hS _ j.right.unop N,
      ⟨_, 𝟙 _, openChartInclusion B S hS _ j.right.unop N,
        ⟨isAffine_chartScheme_openChart B S hS _ j.right.unop ⟨N, hN⟩, Z₂, W, O, hZ₂, hW, hO,
          hZle, hOle,
          nonempty_hom_representedEpsilonFunctor_obj_of_range B S hS ?_,
          ((BigFppfOver.toScheme B S hS).map
            (chartBaseChangeMap B S hS (representedSpaceMap B S hS φ) V' j)).resLE O N
              (fun y hy => (hNle hy).1), ?_⟩, Category.id_comp _⟩, ?_⟩
    · rintro _ ⟨y, rfl⟩
      rw [← hπ]
      have hy : (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS _).map
          (openChartInclusion B S hS _ j.right.unop N)) y ∈ N := by
        rw [hι]
        exact (Scheme.Opens.range_ι N).le ⟨y, rfl⟩
      exact (hNle hy).2
    · exact (Scheme.Hom.resLE_comp_ι _ _).trans (congrArg (· ≫ _) hι.symm)
    · rw [hι]
      exact ⟨⟨x, hxN⟩, rfl⟩
  · rintro Y h ⟨Y', h', g', ⟨hY', Z₂, W, O, hZ₂, hW, hO, hZW, hOW, ⟨j₂⟩, k, hkc⟩, rfl⟩
    have hY : representedEpsilonAffineChart B S hS U Y' := ⟨hY', Z₂, hZ₂, ⟨j₂⟩⟩
    have : Etale ((BigFppfOver.toScheme B S hS).map (yonedaEquiv V'.1.hom)) :=
      etale_toScheme_representedChartBase B S hS V V'
    have hk' : k ≫ O.ι ≫ (BigFppfOver.toScheme B S hS).map (yonedaEquiv V'.1.hom) =
        (BigFppfOver.toScheme B S hS).map (yonedaEquiv Y'.1.hom) ≫
          (BigFppfOver.toScheme B S hS).map φ := by
      rw [← Category.assoc, hkc, Category.assoc, hk, ← Category.assoc,
        toScheme_map_toOver_map_comp_yonedaEquiv]
    have e : (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.map g'.op
        (chartPullback B S hS (representedSpaceMap B S hS φ) V' j g) =
        Scheme.Γ.map k.op (Scheme.Γ.map O.ι.op g) :=
      Γ_map_apply_of_comp_eq hkc.symm g
    have key : T.val.presheaf.map g'.op (representedEpsilonGlueValue B S hS φ T D₀ j.right.unop
        (chartPullback B S hS (representedSpaceMap B S hS φ) V' j g)) = 0 := by
      refine (representedEpsilonGlueValue_map B S hS φ T D₀ hY g' _).trans ?_
      refine (representedEpsilonGlueFamily_eq B S hS φ T D₀ hY j₂ hZ₂ _).trans ?_
      refine (congrArg (representedEpsilonLocalDerivation B S hS φ T D₀ j₂ hZ₂ hY') e).trans ?_
      exact representedEpsilonLocalDerivation_pullback_eq_zero B S hS φ T D₀ O hY' hZ₂ hW hO hZW
        _ hOW j₂ k hk' g
    rw [op_comp, Functor.map_comp]
    exact congrArg (T.val.presheaf.map h'.op).hom (key.trans (map_zero _).symm)

/-- **The glued values kill the image of `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X`.** -/
theorem representedEpsilonGlueValue_fSharpInverseImage
    (W : (SmallEtale B S hS (yoneda.obj U))ᵒᵖ)
    (a : ToType ((inverseImageStructureSheaf B S hS (representedSpaceMap B S hS φ)).obj.obj W)) :
    representedEpsilonGlueValue B S hS φ T D₀ W.unop
      ((structureSharpInverseImage B S hS (representedSpaceMap B S hS φ)).hom.app W a) = 0 := by
  obtain ⟨E, ε, ε', hε⟩ := Stacks.SheafOfModules.exists_typeSheafHom_app_eq_iff
    (J := (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J) (T := T)
    (structureSetSheaf B S hS (representedAlgebraicSpace B S hS U))
    (fun X => (0 : ToType ((smallEtaleRingedTopos B S hS
      (representedAlgebraicSpace B S hS U)).O.obj.obj X)))
    (fun f => map_zero ((smallEtaleRingedTopos B S hS
      (representedAlgebraicSpace B S hS U)).O.obj.map f).hom)
    (fun X r => representedEpsilonGlueValue B S hS φ T D₀ X.unop r)
    (fun f r => representedEpsilonGlueValue_naturality B S hS φ T D₀ f.unop r)
    (fun X => representedEpsilonGlueValue_zero B S hS φ T D₀ X.unop)
  have h := (structureSharpInverseImageSet_comp_eq_iff_chartPullback B S hS
    (representedSpaceMap B S hS φ) ε ε').2
    (fun V' j g => (hε _ _).2 (representedEpsilonGlueValue_chartPullback B S hS φ T D₀ V' j g))
  exact (hε W _).1 (CategoryTheory.Sheaf.congr_sections_comp
    (structureSharpInverseImageSet B S hS (representedSpaceMap B S hS φ)) h W a)

/-- **The étale extension of a Zariski derivation**: the local extensions of `D₀` over the
affine charts mapping to charts of affine opens glue to an `f♯`-derivation of `𝒪_X` with values
in `T`. -/
def representedEpsilonGluedDerivation :
    T.val.Derivation'
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).fSharpInverseImage.hom :=
  Stacks.SheafOfModules.glueDerivationOfCover (representedEpsilonAffineChart B S hS U)
    (generate_representedEpsilonAffineChart_mem B S hS U φ)
    (representedEpsilonGlueFamily B S hS φ T D₀)
    (fun h₂ h₁ m r => representedEpsilonGlueFamily_naturality B S hS φ T D₀ h₂ h₁ m r)
    (fun _ _ a b => representedEpsilonLocalDerivation_mul B S hS φ T D₀ _ _ _ a b)
    (ψ := (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).fSharpInverseImage.hom)
    (fun W a => representedEpsilonGlueValue_fSharpInverseImage B S hS φ T D₀ W a)

/-- **The restriction of derivations along `ε` is surjective**: the glued derivation restricts
to `D₀`. -/
theorem representedEpsilonDerivationRestriction_surjective :
    Function.Surjective (representedEpsilonDerivationRestriction B S hS φ T) := fun D₀ => by
  refine ⟨representedEpsilonGluedDerivation B S hS φ T D₀, ?_⟩
  ext Z t
  exact (representedEpsilonGlueValue_eq_seed B S hS φ T D₀ Z.unop _).trans
    (congrArg (D₀.d (X := Z))
      (topIso_hom_representedToZariskiRingedToposSiteHom_fSharp_app B S hS Z.unop t))

/-- **The adjunct `ε^*(coker d₀) ⟶ coker d` of the map induced by `β` on the cokernels of the
differentials is an isomorphism**. -/
theorem isIso_representedEpsilonCokernelHom_adjunct :
    IsIso (((representedEpsilonModuleAdjunction B S hS U).homEquiv _ _).symm
      (representedEpsilonCokernelHom B S hS φ)) :=
  (isIso_representedEpsilonCokernelHom_adjunct_iff B S hS φ).2 fun T =>
    ⟨representedEpsilonDerivationRestriction_injective B S hS φ T,
      representedEpsilonDerivationRestriction_surjective B S hS φ T⟩

end AlgebraicGeometry.Space

end
