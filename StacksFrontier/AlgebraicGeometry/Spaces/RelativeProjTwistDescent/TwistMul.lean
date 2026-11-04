module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ChartModuleTensorPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.Modules
public import StacksFrontier.AlgebraicGeometry.TwistTensor.RelativeLaurentComparison

/-!
# The comparisons of the twists of a relative Proj are multiplicative

In Situation 0849 the twists `𝒪(n)` of `P = Proj_X(𝒜)` are descended from the twists
`𝒪_{U ×_X P}(n)` on the scheme of a presentation `U ×_X P` of `P`, along the transitions
`AlgebraicGeometry.Space.RelativeProjSituation.twistTransition`, which are built from the
comparisons `AlgebraicGeometry.Space.RelativeProjSituation.twistPieceComparison` of the twists
along morphisms of base changes.  Each comparison is the degree-`n` piece of an isomorphism of
sheaves of graded algebras, so the comparisons are compatible with the multiplications
`𝒪(i) ⊗ 𝒪(j) ⟶ 𝒪(i + j)`, read through Stacks 01CD.  This file proves that compatibility and,
from it, descends the multiplications of the twists to `P` along the presentation (Stacks 084D),
given the compatibility of the tensor identification of Stacks 03DX (2) with inverse images along
the two projections of the presentation.

## Main definitions

* `AlgebraicGeometry.Space.pullbackGradedAlgebraIsoOfSquare`: for a commutative square
  `y ≫ ιX = ιY ≫ pc` of schemes and an isomorphism `pc^*G ≅ N` of sheaves of graded algebras,
  the isomorphism `y^*(ιX^*G) ≅ ιY^*N` of sheaves of graded algebras whose pieces are
  `AlgebraicGeometry.Space.pullbackIsoOfSquare`.
* `AlgebraicGeometry.Space.RelativeProjSituation.twistPieceMul`: the multiplication
  `𝒪(i) ⊗ 𝒪(j) ⟶ 𝒪(i + j)` of the twists on the scheme of a base change.
* `AlgebraicGeometry.Space.RelativeProjPoints.TransitionMulCompat`: the compatibility of a
  multiplication with scheme transitions on the presentation `P = P_U/P_R`, as a named
  proposition.
* `AlgebraicGeometry.Space.RelativeProjPoints.spacePresentationDescendedMul`: the descended
  multiplication on the presentation `P = P_U/P_R`, with its data spelled through the base
  changes.
* `AlgebraicGeometry.Space.RelativeProjSituation.twistModuleMul`: **the multiplication
  `𝒪_P(i) ⊗ 𝒪_P(j) ⟶ 𝒪_P(i + j)` of the descended twists**.

## Main results

* `AlgebraicGeometry.Space.mulSheaf_comp_tensorSheafMap_of_hom`: a homomorphism of sheaves of
  graded algebras on a scheme commutes with the multiplications as morphisms out of the tensor
  product sheaf.
* `AlgebraicGeometry.Space.pullbackIsoOfSquare_hom_mul`: the comparison along a square is
  compatible with the multiplications.
* `AlgebraicGeometry.Space.RelativeProjSituation.twistPieceComparison_mul`: the comparisons of
  the twists are compatible with the multiplications.
* `AlgebraicGeometry.Space.RelativeProjSituation.twistTransition_mul`: the transitions of the
  twists are compatible with the multiplications.
* `AlgebraicGeometry.Space.RelativeProjSituation.existsUnique_twistModuleMul`: **the
  multiplication `𝒪_P(i) ⊗ 𝒪_P(j) ⟶ 𝒪_P(i + j)` of the descended twists exists and is unique**,
  characterized by its inverse image along the atlas, and
  `AlgebraicGeometry.Space.RelativeProjSituation.twistModuleMul_spec`: the inverse image of
  `AlgebraicGeometry.Space.RelativeProjSituation.twistModuleMul` along the atlas.

## Implementation notes

A definition, unlike a theorem, has its nested proofs abstracted into auxiliary lemmas.  Inside
`AlgebraicGeometry.Space.RelativeProjSituation.twistModuleMul` this replaces the proof
`s.space.property` carried by the presentation in the data of the twists, while the type of the
compatibility of the transitions with the multiplications keeps it; compared through the deep
types of the presentation, the two spellings of that compatibility exhaust the kernel's budget.
The compatibility is therefore passed as the named proposition
`AlgebraicGeometry.Space.RelativeProjPoints.TransitionMulCompat`, which the kernel compares
argument by argument, as it does `AlgebraicGeometry.Space.RepresentedC3TensorCompat`.  For the
same reason `AlgebraicGeometry.Space.RelativeProjSituation.twistModuleMul_spec` spells the twists
as the descended modules they are by definition.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist
open Stacks.AlgebraicGeometry (Tag07ZGTwist.twistAlgebra GluedTwistAlgebra.twistDataOfGradedAlgebra)
open Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp
open Stacks.AlgebraicGeometry.RelativeProjTwists (SchemeGradedAlgebra)
open scoped TensorProduct

universe u m

namespace AlgebraicGeometry.Space

/-- **A homomorphism of sheaves of graded algebras on a scheme commutes with the
multiplications**, as morphisms out of the tensor product sheaf: the converse of
`Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp.map_mul_of_mulSheaf_comp_tensorSheafMap`. -/
theorem mulSheaf_comp_tensorSheafMap_of_hom {W : Scheme.{u}} {A B : SchemeGradedAlgebra W}
    (e : A ⟶ B) (i j : ℤ) :
    SheafOfModules.GradedAlgebra.mulSheaf A i j ≫ e.app (i + j) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
        ((e.app i, e.app j) : (_, _) ⟶ (_, _)) ≫
        SheafOfModules.GradedAlgebra.mulSheaf B i j := by
  refine PresheafOfModules.tensorSheaf_hom_ext
    (Osharp := ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩) fun U x y => ?_
  refine Eq.trans (congrArg (fun z => (e.app (i + j)).val.app U z)
    (SheafOfModules.GradedAlgebra.mulSheaf_unit A i j U x y)) ?_
  refine Eq.trans (e.map_mul i j U x y) ?_
  refine Eq.trans (SheafOfModules.GradedAlgebra.mulSheaf_unit B i j U _ _).symm ?_
  exact congrArg (fun z => (SheafOfModules.GradedAlgebra.mulSheaf B i j).val.app U z)
    (Stacks.RingedSpace.tensorSheaf_map_unit_tmul W.toRingedSpace (e.app i) (e.app j) U x y).symm

section PullbackSquare

variable {X' X Y' Y : Scheme.{u}} (ιX : X' ⟶ X) (ιY : Y' ⟶ Y) (y : Y' ⟶ X') (pc : Y ⟶ X)
  (e : y ≫ ιX = ιY ≫ pc) {G : SchemeGradedAlgebra X} {N : SchemeGradedAlgebra Y}
  (E : pbAlgS pc G ≅ N)

/-- **The comparison along a commutative square, as an isomorphism of sheaves of graded
algebras.**  For a square `y ≫ ιX = ιY ≫ pc` of schemes and an isomorphism `E : pc^*G ≅ N`, the
isomorphism `y^*(ιX^*G) ≅ ιY^*N`: the contraction of the pullbacks along the square, followed by
the pullback of `E` along `ιY`. -/
def pullbackGradedAlgebraIsoOfSquare : pbAlgS y (pbAlgS ιX G) ≅ pbAlgS ιY N :=
  pullbackGradedAlgebraCompIso G y ιX ≪≫ pullbackGradedAlgebraCongrIso G e ≪≫
    (pullbackGradedAlgebraCompIso G ιY pc).symm ≪≫
      Stacks.RingedSpace.pullbackGradedAlgebraMapIso ιY.toLRSHom.toShHom E

/-- The pieces of `AlgebraicGeometry.Space.pullbackGradedAlgebraIsoOfSquare` are the comparisons
`AlgebraicGeometry.Space.pullbackIsoOfSquare` of the pieces. -/
theorem pullbackGradedAlgebraIsoOfSquare_hom_app (n : ℤ) :
    (pullbackGradedAlgebraIsoOfSquare ιX ιY y pc e E).hom.app n =
      (pullbackIsoOfSquare ιX ιY y pc e (gradedPieceIso pc E n)).hom :=
  rfl

/-- **The comparison along a commutative square is compatible with the multiplications.**  For a
square `y ≫ ιX = ιY ≫ pc` of schemes and an isomorphism `E : pc^*G ≅ N` of sheaves of graded
algebras, the comparisons `y^*(ιX^*G_n) ≅ ιY^*N_n` carry the multiplication of `ιX^*G`, pulled
back along `y` and read through Stacks 01CD, to the multiplication of `ιY^*N`. -/
theorem pullbackIsoOfSquare_hom_mul (i j : ℤ) :
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso y
        ((Scheme.Modules.pullback ιX).obj (G.piece i))
        ((Scheme.Modules.pullback ιX).obj (G.piece j))).inv ≫
      (Scheme.Modules.pullback y).map
        (SheafOfModules.GradedAlgebra.mulSheaf (pbAlgS ιX G) i j) ≫
      (pullbackIsoOfSquare ιX ιY y pc e (gradedPieceIso pc E (i + j))).hom =
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨Y'.toRingedSpace.presheaf, Y'.toRingedSpace.IsSheaf⟩)).map
      (((pullbackIsoOfSquare ιX ιY y pc e (gradedPieceIso pc E i)).hom,
        (pullbackIsoOfSquare ιX ιY y pc e (gradedPieceIso pc E j)).hom) : (_, _) ⟶ (_, _)) ≫
      SheafOfModules.GradedAlgebra.mulSheaf (pbAlgS ιY N) i j := by
  have h1 := Stacks.RingedSpace.mulSheaf_pullbackGradedAlgebra y.toLRSHom.toShHom
    (pbAlgS ιX G) i j
  have h2 := mulSheaf_comp_tensorSheafMap_of_hom
    (pullbackGradedAlgebraIsoOfSquare ιX ιY y pc e E).hom i j
  refine Eq.trans ?_ h2
  rw [h1]
  rfl

/-- The comparison along a square, read as an isomorphism of sheaves of modules, has the same
underlying morphism. -/
theorem pullbackSheafIsoOfSquare_hom {M : X.Modules} {M' : Y.Modules}
    (T : (Scheme.Modules.pullback pc).obj M ≅ M') :
    (pullbackSheafIsoOfSquare ιX ιY y pc e T).hom = (pullbackIsoOfSquare ιX ιY y pc e T).hom :=
  rfl

/-- The tensor product of two morphisms in the two spellings of the tensor product sheaf of a
scheme: whiskered through the sheaf of rings of the Zariski ringed site, and through the
uncurried bifunctor. -/
theorem sheafTensor_whisker_eq_uncurry_map {W : Scheme.{u}} {A A' B B' : W.Modules}
    (a : A ⟶ A') (b : B ⟶ B') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        W.zariskiRingedSite.toRingedTopos.O).map a).app B ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        W.zariskiRingedSite.toRingedTopos.O).obj A').map b =
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
      ((a, b) : (_, _) ⟶ (_, _)) :=
  rfl

end PullbackSquare

/-- An equation `f ≫ g ≫ h = p ≫ q` transported along equations of its five morphisms, so that
an instance compares two spellings morphism by morphism. -/
private theorem comp_comp_eq_comp_of_eq {C : Type*} [Category C] {X₁ X₂ X₃ X₄ Y₁ : C}
    {f f' : X₁ ⟶ X₂} {g g' : X₂ ⟶ X₃} {h h' : X₃ ⟶ X₄} {p p' : X₁ ⟶ Y₁} {q q' : Y₁ ⟶ X₄}
    (H : f ≫ g ≫ h = p ≫ q) (hf : f' = f) (hg : g' = g) (hh : h' = h) (hp : p' = p)
    (hq : q' = q) : f' ≫ g' ≫ h' = p' ≫ q' := by
  subst hf hg hh hp hq
  exact H

/-- The tensor product of two whiskered composites is the composite of the whiskered tensor
products, for any bifunctor. -/
private theorem bifunctor_whisker_comp {C D : Type*} [Category C] [Category D] (F : C ⥤ C ⥤ D)
    {M M' M'' N N' N'' : C} (a : M ⟶ M') (a' : M' ⟶ M'') (b : N ⟶ N') (b' : N' ⟶ N'') :
    (F.map (a ≫ a')).app N ≫ (F.obj M'').map (b ≫ b') =
      ((F.map a).app N ≫ (F.obj M').map b) ≫ ((F.map a').app N' ≫ (F.obj M'').map b') := by
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [← (F.map a').naturality_assoc b]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) in
/-- **The tensor product of quasi-coherent modules is functorial in both factors.** -/
theorem quasicoherentTensorHom_comp (U : BigFppfOver B S hS)
    {M M' M'' N N' N'' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (a : M ⟶ M') (a' : M' ⟶ M'') (b : N ⟶ N') (b' : N' ⟶ N'') :
    quasicoherentTensorHom B S hS U (a ≫ a') (b ≫ b') =
      quasicoherentTensorHom B S hS U a b ≫ quasicoherentTensorHom B S hS U a' b' :=
  ObjectProperty.hom_ext _ (bifunctor_whisker_comp _ a.hom a'.hom b.hom b'.hom)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) in
/-- A tensor product of composites with inverses, followed by the tensor product of the
isomorphisms, is the tensor product of the first factors. -/
theorem quasicoherentTensorHom_comp_inv_comp (U : BigFppfOver B S hS)
    {M M' M'' N N' N'' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (τ : M ⟶ M') (σ : N ⟶ N') (a : M ⟶ M'') (c : M' ≅ M'') (b : N ⟶ N'') (d : N' ≅ N'')
    (hτ : τ = a ≫ c.inv) (hσ : σ = b ≫ d.inv) :
    quasicoherentTensorHom B S hS U τ σ ≫ quasicoherentTensorHom B S hS U c.hom d.hom =
      quasicoherentTensorHom B S hS U a b := by
  subst hτ hσ
  rw [← quasicoherentTensorHom_comp]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The abstract shape of
`AlgebraicGeometry.Space.RelativeProjSituation.twistTransition_mul`: a transition made of two
comparisons compatible with a multiplication is compatible with it. -/
private theorem transition_mul_of_comparisons {C : Type*} [Category C]
    {Pt Ps Qt Qs Kt Ks Rm Kr : C} (et : Qt ⟶ Pt) (mt : Pt ⟶ Kt) (es : Qs ⟶ Ps) (ms : Ps ⟶ Ks)
    (Tt : Kt ≅ Kr) (Ts : Ks ≅ Kr) (A : Qt ⟶ Qs) (B₁ : Qt ⟶ Rm) (B₂' : Qs ⟶ Rm) (mR : Rm ⟶ Kr)
    (ht : et ≫ mt ≫ Tt.hom = B₁ ≫ mR) (hs : es ≫ ms ≫ Ts.hom = B₂' ≫ mR)
    (hA : A ≫ B₂' = B₁) :
    et ≫ mt ≫ Tt.hom ≫ Ts.inv = A ≫ es ≫ ms := by
  have hs' : es ≫ ms = B₂' ≫ mR ≫ Ts.inv := by
    rw [← reassoc_of% hs, Iso.hom_inv_id, Category.comp_id]
  rw [hs', reassoc_of% hA, ← reassoc_of% ht]

namespace RelativeProjPoints

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

/-- The compatibility of a multiplication with scheme transitions on the presentation
`P = P_U/P_R`, from its form spelled through the base changes `U ×_X P`, `R ×_X P`. -/
theorem spacePresentation_mul_transition
    (h : (quasicoherentPullbackTensorIso B S hS (d.spaceTarget Px hP) M N).inv ≫
        quasicoherentPullbackMap B S hS (d.spaceTarget Px hP) m ≫ κ =
      quasicoherentTensorHom B S hS (d.fibre Px.R (relationPoint Px)) τ σ ≫
        (quasicoherentPullbackTensorIso B S hS (d.spaceSource Px hP) M N).inv ≫
        quasicoherentPullbackMap B S hS (d.spaceSource Px hP) m) :
    (quasicoherentPullbackTensorIso B S hS (d.spacePresentation Px hP).target M N).inv ≫
        quasicoherentPullbackMap B S hS (d.spacePresentation Px hP).target m ≫ κ =
      quasicoherentTensorHom B S hS (d.spacePresentation Px hP).R τ σ ≫
        (quasicoherentPullbackTensorIso B S hS (d.spacePresentation Px hP).source M N).inv ≫
        quasicoherentPullbackMap B S hS (d.spacePresentation Px hP).source m :=
  h

/-- **The compatibility of a multiplication with the scheme transitions of the presentation
`P = P_U/P_R`**, spelled through the base changes `U ×_X P`, `R ×_X P`: for
`m : M ⊗ N ⟶ K` on the scheme of `P_U` and transitions `τ`, `σ`, `κ` of `M`, `N`, `K` on the
scheme of `P_R`, the transition `κ` carries the pullback of `m` along the target projection, read
through Stacks 03EL, to the pullback of `m` along the source projection after `τ ⊗ σ`.

It is a named proposition so that the descended multiplication
`AlgebraicGeometry.Space.RelativeProjPoints.spacePresentationDescendedMul` can be instantiated
inside a definition: there the equation, written out, is compared with its instance through the
deep types of the presentation and the comparison exhausts the kernel's budget, while this name
is compared argument by argument. -/
def TransitionMulCompat : Prop :=
  (quasicoherentPullbackTensorIso B S hS (d.spaceTarget Px hP) M N).inv ≫
      quasicoherentPullbackMap B S hS (d.spaceTarget Px hP) m ≫ κ =
    quasicoherentTensorHom B S hS (d.fibre Px.R (relationPoint Px)) τ σ ≫
      (quasicoherentPullbackTensorIso B S hS (d.spaceSource Px hP) M N).inv ≫
      quasicoherentPullbackMap B S hS (d.spaceSource Px hP) m

/-- `AlgebraicGeometry.Space.RelativeProjPoints.TransitionMulCompat`, written out. -/
theorem transitionMulCompat_iff :
    d.TransitionMulCompat Px hP τ σ κ m ↔
      (quasicoherentPullbackTensorIso B S hS (d.spaceTarget Px hP) M N).inv ≫
          quasicoherentPullbackMap B S hS (d.spaceTarget Px hP) m ≫ κ =
        quasicoherentTensorHom B S hS (d.fibre Px.R (relationPoint Px)) τ σ ≫
          (quasicoherentPullbackTensorIso B S hS (d.spaceSource Px hP) M N).inv ≫
          quasicoherentPullbackMap B S hS (d.spaceSource Px hP) m :=
  Iff.rfl

section Descent

attribute [local instance] modulesMonoidalCategory

variable (hc : PresentationSchemeCocycle (d.spacePresentation Px hP) M τ)
  (hu : PresentationSchemeUnit (d.spacePresentation Px hP) M τ)
  (hc' : PresentationSchemeCocycle (d.spacePresentation Px hP) N σ)
  (hu' : PresentationSchemeUnit (d.spacePresentation Px hP) N σ)
  (hc'' : PresentationSchemeCocycle (d.spacePresentation Px hP) K κ)
  (hu'' : PresentationSchemeUnit (d.spacePresentation Px hP) K κ)
  (hbt : RepresentedC3TensorCompat B S hS (d.spaceTarget Px hP) M N)
  (hbs : RepresentedC3TensorCompat B S hS (d.spaceSource Px hP) M N)
  (hm : d.TransitionMulCompat Px hP τ σ κ m)

/-- `AlgebraicGeometry.Space.presentationDescendedMul` on the presentation `P = P_U/P_R`, with
its data spelled through the base changes `U ×_X P`, `R ×_X P`. -/
def spacePresentationDescendedMul :
    (presentationDescendedModule (d.spacePresentation Px hP) M τ hc hu).obj ⊗
        (presentationDescendedModule (d.spacePresentation Px hP) N σ hc' hu').obj ⟶
      (presentationDescendedModule (d.spacePresentation Px hP) K κ hc'' hu'').obj :=
  presentationDescendedMul (d.spacePresentation Px hP) τ hc hu σ hc' hu' κ hc'' hu'' m hbt hbs
    (d.spacePresentation_mul_transition Px hP τ σ κ m
      ((d.transitionMulCompat_iff Px hP τ σ κ m).1 hm))

/-- The inverse image along the atlas of
`AlgebraicGeometry.Space.RelativeProjPoints.spacePresentationDescendedMul` is the attached
multiplication. -/
theorem spacePresentationDescendedMul_spec :
    (modulePullback B S hS (presentationAtlas (d.spacePresentation Px hP))).map
        (d.spacePresentationDescendedMul Px hP τ σ κ m hc hu hc' hu' hc'' hu'' hbt hbs hm) ≫
        (presentationDescendedModuleChartIso (d.spacePresentation Px hP) K κ hc'' hu'').hom =
      (modulePullbackTensorIso B S hS (presentationAtlas (d.spacePresentation Px hP))
          (presentationDescendedModule (d.spacePresentation Px hP) M τ hc hu).obj
          (presentationDescendedModule (d.spacePresentation Px hP) N σ hc' hu').obj).hom ≫
        ((presentationDescendedModuleChartIso (d.spacePresentation Px hP) M τ hc hu).hom ⊗ₘ
          (presentationDescendedModuleChartIso (d.spacePresentation Px hP) N σ hc' hu').hom) ≫
        representedTensorChartMul B S hS m :=
  presentationDescendedMul_spec (d.spacePresentation Px hP) τ hc hu σ hc' hu' κ hc'' hu'' m hbt
    hbs (d.spacePresentation_mul_transition Px hP τ σ κ m hm)

include hbt hbs hm in
/-- **The descended multiplication on the presentation `P = P_U/P_R` is unique**: it is the only
morphism whose inverse image along the atlas is the attached multiplication. -/
theorem spacePresentationDescendedMul_existsUnique :
    ∃! ψ : (presentationDescendedModule (d.spacePresentation Px hP) M τ hc hu).obj ⊗
        (presentationDescendedModule (d.spacePresentation Px hP) N σ hc' hu').obj ⟶
        (presentationDescendedModule (d.spacePresentation Px hP) K κ hc'' hu'').obj,
      (modulePullback B S hS (presentationAtlas (d.spacePresentation Px hP))).map ψ ≫
          (presentationDescendedModuleChartIso (d.spacePresentation Px hP) K κ hc'' hu'').hom =
        (modulePullbackTensorIso B S hS (presentationAtlas (d.spacePresentation Px hP))
            (presentationDescendedModule (d.spacePresentation Px hP) M τ hc hu).obj
            (presentationDescendedModule (d.spacePresentation Px hP) N σ hc' hu').obj).hom ≫
          ((presentationDescendedModuleChartIso (d.spacePresentation Px hP) M τ hc hu).hom ⊗ₘ
            (presentationDescendedModuleChartIso (d.spacePresentation Px hP) N σ hc' hu').hom) ≫
          representedTensorChartMul B S hS m :=
  ⟨d.spacePresentationDescendedMul Px hP τ σ κ m hc hu hc' hu' hc'' hu'' hbt hbs hm,
    d.spacePresentationDescendedMul_spec Px hP τ σ κ m hc hu hc' hu' hc'' hu'' hbt hbs hm,
    fun ψ hψ => presentationDescendedMul_unique (d.spacePresentation Px hP) τ hc hu σ hc' hu' κ hc''
      hu'' m hbt hbs (d.spacePresentation_mul_transition Px hP τ σ κ m hm) ψ hψ⟩

end Descent

end RelativeProjPoints

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})

/-- **The multiplication of the twists on the scheme of a base change**: for an object `V` of the
site and `v : V ⟶ X`, the multiplication `𝒪(i) ⊗ 𝒪(j) ⟶ 𝒪(i + j)` of Tag 01NR's `⨁_n 𝒪(n)` on
`Proj_V(v^*𝒜)`, read on the scheme of `V ×_X P` through
`AlgebraicGeometry.Space.RelativeProjSituation.toRelativeProj`, as a morphism of quasi-coherent
modules. -/
def twistPieceMul (V : BigFppfOver s.site s.base s.containsBase)
    (v : yoneda.obj V ⟶ s.space.1) (i j : ℤ) :
    quasicoherentTensorObj s.site s.base s.containsBase (s.relativeProjPoints.fibre V v)
        (s.twistPieceQcoh V v i) (s.twistPieceQcoh V v j) ⟶
      s.twistPieceQcoh V v (i + j) :=
  ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf
    (pbAlgS (s.toRelativeProj V v) (Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra V v))) i j)

/-- `AlgebraicGeometry.Space.pullbackIsoOfSquare_hom_mul` at the comparison of the twists along
a morphism of base changes. -/
private theorem twistPieceComparison_mul_aux {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ s.space.1} (k : V ⟶ U)
    (hv : yoneda.map k ≫ u = v)
    (y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
    (hy : s.relativeProjPoints.LiesOver y k) (i j : ℤ) :
    type_of% (pullbackIsoOfSquare_hom_mul
      (X := (relativeProj (s.shrink.pointAlgebra U u)).scheme)
      (Y := (relativeProj (s.shrink.pointAlgebra V v)).scheme)
      (s.toRelativeProj U u) (s.toRelativeProj V v)
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map y) (s.map_comp_toRelativeProj y)
      (s.pointTwistComparison k u v hv ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
        (s.toScheme_map_eq_of_liesOver hv hy)) i j) :=
  pullbackIsoOfSquare_hom_mul
    (X := (relativeProj (s.shrink.pointAlgebra U u)).scheme)
    (Y := (relativeProj (s.shrink.pointAlgebra V v)).scheme)
    (s.toRelativeProj U u) (s.toRelativeProj V v)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map y) (s.map_comp_toRelativeProj y)
    (s.pointTwistComparison k u v hv ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
      (s.toScheme_map_eq_of_liesOver hv hy)) i j

/-- The underlying morphism of the comparison of the twists along a morphism lying over `k` is the
comparison along the square of `AlgebraicGeometry.Space.RelativeProjSituation.toRelativeProj`. -/
private theorem twistPieceComparison_hom_hom_eq {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ s.space.1} (k : V ⟶ U)
    (hv : yoneda.map k ≫ u = v)
    (y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
    (hy : s.relativeProjPoints.LiesOver y k) (n : ℤ) :
    (s.twistPieceComparison k hv y hy n).hom.hom =
      (pullbackIsoOfSquare (s.toRelativeProj U u) (s.toRelativeProj V v)
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
        (s.map_comp_toRelativeProj y)
        (gradedPieceIso (X := (relativeProj (s.shrink.pointAlgebra U u)).scheme)
          (Y := (relativeProj (s.shrink.pointAlgebra V v)).scheme)
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
          (s.pointTwistComparison k u v hv
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
            (s.toScheme_map_eq_of_liesOver hv hy)) n)).hom :=
  (s.twistPieceComparison_hom_hom k hv y hy n).trans (pullbackSheafIsoOfSquare_hom _ _ _ _ _ _)

/-- The tensor product of two comparisons of the twists, in the uncurried spelling. -/
private theorem quasicoherentTensorHom_twistPieceComparison_hom
    {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ s.space.1} (k : V ⟶ U)
    (hv : yoneda.map k ≫ u = v)
    (y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
    (hy : s.relativeProjPoints.LiesOver y k) (i j : ℤ) :
    (quasicoherentTensorHom s.site s.base s.containsBase (s.relativeProjPoints.fibre V v)
        (s.twistPieceComparison k hv y hy i).hom (s.twistPieceComparison k hv y hy j).hom).hom =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((BigFppfOver.toScheme s.site s.base s.containsBase).obj
              (s.relativeProjPoints.fibre V v)).toRingedSpace.presheaf,
            ((BigFppfOver.toScheme s.site s.base s.containsBase).obj
              (s.relativeProjPoints.fibre V v)).toRingedSpace.IsSheaf⟩)).map
        (((s.twistPieceComparison k hv y hy i).hom.hom,
          (s.twistPieceComparison k hv y hy j).hom.hom) : (_, _) ⟶ (_, _)) :=
  sheafTensor_whisker_eq_uncurry_map _ _

/-- **The comparisons of the twists are compatible with the multiplications.**  Along a morphism
`y : V ×_X P ⟶ U ×_X P` lying over `k : V ⟶ U`, the comparisons `y^*𝒪(n) ≅ 𝒪(n)` carry the
multiplication of the twists of `U ×_X P`, pulled back along `y` and read through Stacks 01CD, to
the multiplication of the twists of `V ×_X P`. -/
theorem twistPieceComparison_mul {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ s.space.1} (k : V ⟶ U)
    (hv : yoneda.map k ≫ u = v)
    (y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
    (hy : s.relativeProjPoints.LiesOver y k) (i j : ℤ) :
    (quasicoherentPullbackTensorIso s.site s.base s.containsBase y (s.twistPieceQcoh U u i)
        (s.twistPieceQcoh U u j)).inv ≫
      quasicoherentPullbackMap s.site s.base s.containsBase y (s.twistPieceMul U u i j) ≫
      (s.twistPieceComparison k hv y hy (i + j)).hom =
    quasicoherentTensorHom s.site s.base s.containsBase (s.relativeProjPoints.fibre V v)
        (s.twistPieceComparison k hv y hy i).hom (s.twistPieceComparison k hv y hy j).hom ≫
      s.twistPieceMul V v i j := by
  refine ObjectProperty.hom_ext _ ?_
  refine comp_comp_eq_comp_of_eq
    (C := SheafOfModules.{u} ((BigFppfOver.toScheme s.site s.base s.containsBase).obj
      (s.relativeProjPoints.fibre V v)).ringCatSheaf)
    (s.twistPieceComparison_mul_aux k hv y hy i j) ?_ ?_
    (s.twistPieceComparison_hom_hom_eq k hv y hy (i + j)) ?_ ?_
  · rfl
  · rfl
  · rw [s.quasicoherentTensorHom_twistPieceComparison_hom k hv y hy i j,
      s.twistPieceComparison_hom_hom_eq k hv y hy i, s.twistPieceComparison_hom_hom_eq k hv y hy j]
    rfl
  · rfl

section Presentation

attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor
  Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso

variable (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

/-- The tensor product of the transitions of the twists, contracted with the inverse of the
tensor product of the comparisons along the source. -/
private theorem quasicoherentTensorHom_twistTransition_comp (i j : ℤ) :
    quasicoherentTensorHom s.site s.base s.containsBase
        (s.relativeProjPoints.fibre Px.R (RelativeProjPoints.relationPoint Px))
        (s.twistTransition Px i) (s.twistTransition Px j) ≫
      quasicoherentTensorHom s.site s.base s.containsBase
        (s.relativeProjPoints.fibre Px.R (RelativeProjPoints.relationPoint Px))
        (s.twistPieceComparison (u := Px.toSpace) (v := RelativeProjPoints.relationPoint Px)
          Px.source (s.map_source_comp_toSpace Px)
          (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
          (s.relativeProjPoints.liesOver_spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
          i).hom
        (s.twistPieceComparison (u := Px.toSpace) (v := RelativeProjPoints.relationPoint Px)
          Px.source (s.map_source_comp_toSpace Px)
          (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
          (s.relativeProjPoints.liesOver_spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
          j).hom =
    quasicoherentTensorHom s.site s.base s.containsBase
        (s.relativeProjPoints.fibre Px.R (RelativeProjPoints.relationPoint Px))
        (s.twistPieceComparison (u := Px.toSpace) (v := RelativeProjPoints.relationPoint Px)
          Px.target rfl
          (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
          (s.relativeProjPoints.liesOver_spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
          i).hom
        (s.twistPieceComparison (u := Px.toSpace) (v := RelativeProjPoints.relationPoint Px)
          Px.target rfl
          (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
          (s.relativeProjPoints.liesOver_spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
          j).hom :=
  quasicoherentTensorHom_comp_inv_comp _ _ _ _ _ _ _ _ _ _ rfl rfl

/-- **The transitions of the twists are compatible with the multiplications**: the transition
`𝒪(i + j)` carries the multiplication of the twists, pulled back along the target projection and
read through Stacks 01CD, to the multiplication pulled back along the source projection, after
the tensor product of the transitions `𝒪(i)` and `𝒪(j)`. -/
theorem twistTransition_mul (i j : ℤ) :
    (quasicoherentPullbackTensorIso s.site s.base s.containsBase
        (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.twistPieceQcoh Px.U Px.toSpace i) (s.twistPieceQcoh Px.U Px.toSpace j)).inv ≫
      quasicoherentPullbackMap s.site s.base s.containsBase
        (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.twistPieceMul Px.U Px.toSpace i j) ≫ s.twistTransition Px (i + j) =
    quasicoherentTensorHom s.site s.base s.containsBase
        (s.relativeProjPoints.fibre Px.R (RelativeProjPoints.relationPoint Px))
        (s.twistTransition Px i) (s.twistTransition Px j) ≫
      (quasicoherentPullbackTensorIso s.site s.base s.containsBase
        (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.twistPieceQcoh Px.U Px.toSpace i) (s.twistPieceQcoh Px.U Px.toSpace j)).inv ≫
      quasicoherentPullbackMap s.site s.base s.containsBase
        (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.twistPieceMul Px.U Px.toSpace i j) :=
  transition_mul_of_comparisons _ _ _ _ _ _ _ _ _ _
    (s.twistPieceComparison_mul (u := Px.toSpace) (v := RelativeProjPoints.relationPoint Px)
      Px.target rfl (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.liesOver_spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor) i j)
    (s.twistPieceComparison_mul (u := Px.toSpace) (v := RelativeProjPoints.relationPoint Px)
      Px.source (s.map_source_comp_toSpace Px)
      (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.liesOver_spaceSource Px s.isAlgebraicSpace_relativeProjFunctor) i j)
    (s.quasicoherentTensorHom_twistTransition_comp Px i j)

/-- `AlgebraicGeometry.Space.RelativeProjSituation.twistTransition_mul` as the named proposition
`AlgebraicGeometry.Space.RelativeProjPoints.TransitionMulCompat`. -/
theorem transitionMulCompat_twistTransition (i j : ℤ) :
    s.relativeProjPoints.TransitionMulCompat Px s.isAlgebraicSpace_relativeProjFunctor
      (s.twistTransition Px i) (s.twistTransition Px j) (s.twistTransition Px (i + j))
      (s.twistPieceMul Px.U Px.toSpace i j) :=
  (s.relativeProjPoints.transitionMulCompat_iff Px s.isAlgebraicSpace_relativeProjFunctor
    (s.twistTransition Px i) (s.twistTransition Px j) (s.twistTransition Px (i + j))
    (s.twistPieceMul Px.U Px.toSpace i j)).2 (s.twistTransition_mul Px i j)

attribute [local instance] modulesMonoidalCategory

/-- **The multiplication of the twists of the relative Proj exists and is unique** (Stacks
084D): there is exactly one morphism `𝒪_P(i) ⊗ 𝒪_P(j) ⟶ 𝒪_P(i + j)` whose inverse image along the
atlas of the presentation `P = P_U/P_R` is the multiplication of the twists of Stacks 01NR on the
scheme of `P_U`, through Stacks 03EL, the chart identifications of the twists and the tensor
identification of Stacks 03DX (2).  Its hypothesis is the compatibility of that tensor
identification with inverse images along morphisms of the site. -/
theorem existsUnique_twistModuleMul
    (hb : ∀ {V U : BigFppfOver s.site s.base s.containsBase} (g : V ⟶ U)
      (M N : (SheafOfModules.isQuasicoherent
        ((BigFppfOver.toScheme s.site s.base s.containsBase).obj U).ringCatSheaf).FullSubcategory),
      RepresentedC3TensorCompat s.site s.base s.containsBase g M N) (i j : ℤ) :
    type_of% (s.relativeProjPoints.spacePresentationDescendedMul_existsUnique Px
      s.isAlgebraicSpace_relativeProjFunctor
      (s.twistTransition Px i) (s.twistTransition Px j) (s.twistTransition Px (i + j))
      (s.twistPieceMul Px.U Px.toSpace i j)
      (s.presentationSchemeCocycle_twistTransition Px i)
      (s.presentationSchemeUnit_twistTransition Px i)
      (s.presentationSchemeCocycle_twistTransition Px j)
      (s.presentationSchemeUnit_twistTransition Px j)
      (s.presentationSchemeCocycle_twistTransition Px (i + j))
      (s.presentationSchemeUnit_twistTransition Px (i + j))
      (hb _ _ _) (hb _ _ _) (s.transitionMulCompat_twistTransition Px i j)) :=
  s.relativeProjPoints.spacePresentationDescendedMul_existsUnique Px
      s.isAlgebraicSpace_relativeProjFunctor
      (s.twistTransition Px i) (s.twistTransition Px j) (s.twistTransition Px (i + j))
      (s.twistPieceMul Px.U Px.toSpace i j)
      (s.presentationSchemeCocycle_twistTransition Px i)
      (s.presentationSchemeUnit_twistTransition Px i)
      (s.presentationSchemeCocycle_twistTransition Px j)
      (s.presentationSchemeUnit_twistTransition Px j)
      (s.presentationSchemeCocycle_twistTransition Px (i + j))
      (s.presentationSchemeUnit_twistTransition Px (i + j))
      (hb _ _ _) (hb _ _ _) (s.transitionMulCompat_twistTransition Px i j)

/-- **The multiplication of the twists of the relative Proj** (Stacks 084D):
`𝒪_P(i) ⊗ 𝒪_P(j) ⟶ 𝒪_P(i + j)`, the descent along the presentation `P = P_U/P_R` of the
multiplication of the twists of Stacks 01NR on the scheme of `P_U`
(`AlgebraicGeometry.Space.RelativeProjPoints.spacePresentationDescendedMul`).  Its hypothesis is
the compatibility of the tensor identification of Stacks 03DX (2) with inverse images along
morphisms of the site. -/
def twistModuleMul
    (hb : ∀ {V U : BigFppfOver s.site s.base s.containsBase} (g : V ⟶ U)
      (M N : (SheafOfModules.isQuasicoherent
        ((BigFppfOver.toScheme s.site s.base s.containsBase).obj U).ringCatSheaf).FullSubcategory),
      RepresentedC3TensorCompat s.site s.base s.containsBase g M N) (i j : ℤ) :
    (s.twistModule Px i).obj ⊗ (s.twistModule Px j).obj ⟶ (s.twistModule Px (i + j)).obj :=
  s.relativeProjPoints.spacePresentationDescendedMul Px s.isAlgebraicSpace_relativeProjFunctor
    (s.twistTransition Px i) (s.twistTransition Px j) (s.twistTransition Px (i + j))
    (s.twistPieceMul Px.U Px.toSpace i j)
    (s.presentationSchemeCocycle_twistTransition Px i)
    (s.presentationSchemeUnit_twistTransition Px i)
    (s.presentationSchemeCocycle_twistTransition Px j)
    (s.presentationSchemeUnit_twistTransition Px j)
    (s.presentationSchemeCocycle_twistTransition Px (i + j))
    (s.presentationSchemeUnit_twistTransition Px (i + j))
    (hb _ _ _) (hb _ _ _) (s.transitionMulCompat_twistTransition Px i j)

/-- **The inverse image along the atlas of the multiplication of the twists is the
multiplication of the twists of Stacks 01NR on the scheme of `P_U`**, through Stacks 03EL, the
chart identifications of the twists and the tensor identification of Stacks 03DX (2).  The twists
are spelled as the descended modules they are by definition. -/
theorem twistModuleMul_spec
    (hb : ∀ {V U : BigFppfOver s.site s.base s.containsBase} (g : V ⟶ U)
      (M N : (SheafOfModules.isQuasicoherent
        ((BigFppfOver.toScheme s.site s.base s.containsBase).obj U).ringCatSheaf).FullSubcategory),
      RepresentedC3TensorCompat s.site s.base s.containsBase g M N) (i j : ℤ) :
    (modulePullback s.site s.base s.containsBase (presentationAtlas
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor))).map
        (s.twistModuleMul Px hb i j) ≫
        (presentationDescendedModuleChartIso
          (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
          (s.twistPieceQcoh Px.U Px.toSpace (i + j)) (s.twistTransition Px (i + j))
          (s.presentationSchemeCocycle_twistTransition Px (i + j))
          (s.presentationSchemeUnit_twistTransition Px (i + j))).hom =
      (modulePullbackTensorIso s.site s.base s.containsBase (presentationAtlas
          (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor))
          (presentationDescendedModule
            (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
            (s.twistPieceQcoh Px.U Px.toSpace i) (s.twistTransition Px i)
            (s.presentationSchemeCocycle_twistTransition Px i)
            (s.presentationSchemeUnit_twistTransition Px i)).obj
          (presentationDescendedModule
            (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
            (s.twistPieceQcoh Px.U Px.toSpace j) (s.twistTransition Px j)
            (s.presentationSchemeCocycle_twistTransition Px j)
            (s.presentationSchemeUnit_twistTransition Px j)).obj).hom ≫
        ((presentationDescendedModuleChartIso
            (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
            (s.twistPieceQcoh Px.U Px.toSpace i) (s.twistTransition Px i)
            (s.presentationSchemeCocycle_twistTransition Px i)
            (s.presentationSchemeUnit_twistTransition Px i)).hom ⊗ₘ
          (presentationDescendedModuleChartIso
            (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
            (s.twistPieceQcoh Px.U Px.toSpace j) (s.twistTransition Px j)
            (s.presentationSchemeCocycle_twistTransition Px j)
            (s.presentationSchemeUnit_twistTransition Px j)).hom) ≫
        representedTensorChartMul s.site s.base s.containsBase
          (s.twistPieceMul Px.U Px.toSpace i j) :=
  s.relativeProjPoints.spacePresentationDescendedMul_spec Px s.isAlgebraicSpace_relativeProjFunctor
    (s.twistTransition Px i) (s.twistTransition Px j) (s.twistTransition Px (i + j))
    (s.twistPieceMul Px.U Px.toSpace i j)
    (s.presentationSchemeCocycle_twistTransition Px i)
    (s.presentationSchemeUnit_twistTransition Px i)
    (s.presentationSchemeCocycle_twistTransition Px j)
    (s.presentationSchemeUnit_twistTransition Px j)
    (s.presentationSchemeCocycle_twistTransition Px (i + j))
    (s.presentationSchemeUnit_twistTransition Px (i + j))
    (hb _ _ _) (hb _ _ _) (s.transitionMulCompat_twistTransition Px i j)

end Presentation

end RelativeProjSituation

end AlgebraicGeometry.Space

end
