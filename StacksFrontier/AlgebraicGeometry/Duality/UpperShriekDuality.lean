module

public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.SheafHomRestrictionCurry
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.SheafHomRestrictionNaturality
public import StacksFrontier.AlgebraicGeometry.Duality.SeparatedFiniteTypeProper
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageDuality
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Basic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional

/-!
# The upper shriek of a dual

In Situation [Stacks, Tag 0F42] let `f : X ⟶ Y` be a morphism of `FTS_S`, let `K` be a dualizing
complex on `Y` and write `D_Y = R𝓗om(-, K)`, `D_X = R𝓗om(-, f^!K)`. Then for every
compactification `j` of `X` over `Y` there is an isomorphism

`f^! M ≅ D_X(Lf^* D_Y(M))`

natural in `M ∈ D^+_Coh(𝒪_Y)` ([Stacks, Tag 0AU2]).

On the compactification `f̄ : X̄ ⟶ Y` this is
`Stacks.Duality.TwistedInverseImageDuality.dualityIso`, `a(M) ≅ R𝓗om(Lf̄^* D_Y(M), a(K))`; it is
restricted along the open immersion `X ⟶ X̄`, through which the derived internal Hom commutes
([Stacks, Tag 08DL], by the canonical map
`Stacks.Duality.TwistedInverseImageDuality.pullSheafHomMap`), and
`L(j^*) ∘ Lf̄^* = Lf^*`.

## Main definitions

* `Stacks.Duality.UpperShriekDuality.upperShriekStd`: `f^!` on `D^+_Coh(𝒪_Y)`, read at the
  standard model of the derived categories.
* `Stacks.Duality.UpperShriekDuality.upperShriekDualityIso`: **[Stacks, Tag 0AU2]**.

## Implementation notes

`f^!` is defined at the locally small model of `D(𝒪)`, and the derived internal Hom and
the derived pullback at the standard model. The two models have the same objects, and the
comparison `StacksDraft.DerivedModel.schemeModulesComparison` is the identity on objects; `f^!M`
and `f^!K` are read at the standard model through it.

## References

* [Stacks Project, Tag 0AU2](https://stacks.math.columbia.edu/tag/0AU2)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Duality.TwistedInverseImageDuality

universe u

namespace Stacks.Duality.UpperShriekDuality

/-! ### Derived pullback at the two models and along composites -/

section Pullback

variable {A B : Scheme.{u}} (g : A ⟶ B)

/-- `Lg^*` at the two models. -/
def pullModelIso :
    pull g ⋙ (comparison A).functor ≅ (comparison B).functor ⋙ Stacks.Duality.derivedPullback g :=
  StacksDraft.DerivedModel.derivedPullbackModelIso g.toLRSHom.toShHom

/-- `Lg^*` at the locally small model, read at the standard model. -/
def pullModelConj :
    Stacks.Duality.derivedPullback g ⋙ (comparison A).inverse ≅ (comparison B).inverse ⋙ pull g :=
  Functor.isoWhiskerRight
      (ProjectionFormulaLocallySmall.conjugateIso (comparison B) (comparison A)
        (pullModelIso g)).symm
      (comparison A).inverse ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (comparison A).unitIso.symm) ≪≫
    Functor.isoWhiskerLeft _ (Functor.rightUnitor _)

/-- A comparison `F ⋙ E₂ ≅ E₁ ⋙ F'` read as `F' ⋙ E₂⁻¹ ≅ E₁⁻¹ ⋙ F`, through `E₂` and its counit. -/
theorem conj_inv_app_comp_counit {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁]
    [Category D₂] (E₁ : C₁ ≌ D₁) (E₂ : C₂ ≌ D₂) {F : C₁ ⥤ C₂} {F' : D₁ ⥤ D₂}
    (e : F ⋙ E₂.functor ≅ E₁.functor ⋙ F') (φ : F' ⋙ E₂.inverse ≅ E₁.inverse ⋙ F)
    (hφ : φ = Functor.isoWhiskerRight
      (ProjectionFormulaLocallySmall.conjugateIso E₁ E₂ e).symm E₂.inverse ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
      Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ E₂.unitIso.symm) ≪≫
      Functor.isoWhiskerLeft _ (Functor.rightUnitor _)) (Q : D₁) :
    E₂.functor.map (φ.inv.app Q) ≫ E₂.counit.app (F'.obj Q) =
      e.hom.app (E₁.inverse.obj Q) ≫ F'.map (E₁.counit.app Q) := by
  subst hφ
  simp [ProjectionFormulaLocallySmall.conjugateIso]

/-- `pullModelConj` through the comparison of the models: `Lg^*` of the counit after the comparison
of `Lg^*` at the two models. -/
theorem pullModelConj_inv_app_comp_counit {A₀ B₀ : Scheme.{u}} (g : A₀ ⟶ B₀)
    (Q : DerivedCategory B₀.Modules) :
    (comparison A₀).functor.map ((pullModelConj g).inv.app Q) ≫
        (comparison A₀).counit.app ((Stacks.Duality.derivedPullback g).obj Q) =
      (pullModelIso g).hom.app ((comparison B₀).inverse.obj Q) ≫
        (Stacks.Duality.derivedPullback g).map ((comparison B₀).counit.app Q) :=
  conj_inv_app_comp_counit _ _ _ _ rfl Q

end Pullback

section CompositeModel

open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)
open StacksDraft.DerivedModel (derivedPullbackModelIso derivedPullbackCongr)
open Stacks.Injectives (hasDerivedCategory_of_isGrothendieckAbelian grothendieckModelEquiv)

/-- Solving the model-compatibility squares of a composite and of a transport. -/
theorem comp_model_chase {C : Type*} [Category C] {P Q R A B S T : C} (c : P ⟶ Q) (d : Q ⟶ R)
    (i : Q ⟶ S) (Ik : T ≅ R) (J₂ : A ≅ P) (J₁ : B ≅ A) (Gs : B ⟶ S) (Gt : S ⟶ T) (Gst : B ⟶ T)
    (hA : c ≫ i = J₂.inv ≫ J₁.inv ≫ Gs) (hB : d ≫ Ik.inv = i ≫ Gt) (hG : Gst = Gs ≫ Gt) :
    Gst ≫ Ik.hom = J₁.hom ≫ J₂.hom ≫ c ≫ d := by
  have h : Gs = J₁.hom ≫ J₂.hom ≫ c ≫ i := by
    rw [hA]; simp
  rw [hG, h]
  simp only [Category.assoc]
  rw [← reassoc_of% hB, Iso.inv_hom_id, Category.comp_id]

/-- The composition isomorphism of derived pullback followed by a transport, for ringed spaces,
at the two models. -/
theorem map_compCongr_hom_app_comp_derivedPullbackModelIso_hom_app {X Y Z : RingedSpace.{u, u}}
    (f₁ : X ⟶ Y) (f₂ : Y ⟶ Z) (k : X ⟶ Z) (e : f₁ ≫ f₂ = k)
    (K : @DerivedCategory _ _ _ (HasDerivedCategory.standard
      (SheafOfModules.{u} (structureSheafRing Z)))) :
    (grothendieckModelEquiv _).functor.map
        ((@derivedPullbackCompIsoCanonical X Y Z f₁ f₂ (HasDerivedCategory.standard _)
          (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) ≪≫
          @derivedPullbackCongr X Z (HasDerivedCategory.standard _)
            (HasDerivedCategory.standard _) _ _ e).hom.app K) ≫
      (derivedPullbackModelIso k).hom.app K =
    (derivedPullbackModelIso f₁).hom.app
        ((@Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback _ _ f₂
          (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) inferInstance).obj K) ≫
      (@Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback _ _ f₁
          (hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
          (hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance).map
        ((derivedPullbackModelIso f₂).hom.app K) ≫
      (@derivedPullbackCompIsoCanonical X Y Z f₁ f₂
          (hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
          (hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
          (hasDerivedCategory_of_isGrothendieckAbelian.{u} _) ≪≫
        @derivedPullbackCongr X Z (hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
          (hasDerivedCategory_of_isGrothendieckAbelian.{u} _) _ _ e).hom.app
        ((grothendieckModelEquiv _).functor.obj K) :=
  comp_model_chase _ _ _ ((derivedPullbackModelIso k).app K)
    ((@Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback _ _ f₁
          (hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance).mapIso
        ((derivedPullbackModelIso f₂).app K))
    ((derivedPullbackModelIso f₁).app _) _ _ _
    (StacksDraft.DerivedModel.derivedPullbackCompIsoCanonical_comp_derivedPullbackModelIso f₁ f₂ K)
    (StacksDraft.DerivedModel.derivedPullbackCongr_hom_app_comp_derivedPullbackModelIso_inv_app
      e K) ((grothendieckModelEquiv _).functor.map_comp _ _)

end CompositeModel

section Composite

attribute [local instance 10000] HasDerivedCategory.standard

variable {A B C : Scheme.{u}} (g : A ⟶ B) (h : B ⟶ C) (k : A ⟶ C) (w : g ≫ h = k)

/-- `Lg^* ∘ Lh^* = Lk^*` for `k = g ≫ h`, at the standard model. -/
def pullCompIso : pull h ⋙ pull g ≅ pull k :=
  Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g.toLRSHom.toShHom
      h.toLRSHom.toShHom ≪≫
    StacksDraft.DerivedModel.derivedPullbackCongr (by
      rw [← w, Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom])

/-- **The composition isomorphism of derived pullback at the two models**: `Lg^* Lh^* ≅ Lk^*` at
the standard model, read through the comparisons of the models, is the one of the locally small
model followed by the transport along `g ≫ h = k`. -/
theorem pullCompIso_hom_app_comp_pullModelIso_hom {A₀ B₀ C₀ : Scheme.{u}} (h : A₀ ⟶ B₀)
    (g : C₀ ⟶ A₀) (k : C₀ ⟶ B₀) (w : g ≫ h = k)
    (K : Std B₀) :
    (comparison C₀).functor.map ((pullCompIso g h k w).hom.app K) ≫ (pullModelIso k).hom.app K =
      (pullModelIso g).hom.app ((pull h).obj K) ≫
        (Stacks.Duality.derivedPullback g).map ((pullModelIso h).hom.app K) ≫
        (Stacks.Duality.derivedPullbackCompIso g h).hom.app ((comparison B₀).functor.obj K) ≫
        eqToHom (congrArg (fun t : C₀ ⟶ B₀ =>
          (Stacks.Duality.derivedPullback t).obj ((comparison B₀).functor.obj K)) w) := by
  subst w
  exact map_compCongr_hom_app_comp_derivedPullbackModelIso_hom_app g.toLRSHom.toShHom
    h.toLRSHom.toShHom _ rfl K

end Composite

/-! ### Restriction of the derived internal Hom along an open immersion, at `Lj^*` -/

section OpenImmersion

attribute [local instance 10000] HasDerivedCategory.standard

variable {A B : Scheme.{u}} (g : A ⟶ B) [IsOpenImmersion g]

/-- [Stacks, Tag 08DL] for an open immersion `g`, with restriction written as `Lg^*`: the
canonical map `Lg^* R𝓗om(P, L) ⟶ R𝓗om(Lg^*P, Lg^*L)` of [Stacks, Tag 08I3], the transpose of
`Lg^*` of the evaluation morphism (`TwistedInverseImageDuality.pullSheafHomMap`), invertible by
`TwistedInverseImageDuality.isIso_pullSheafHomMap`. It is used
rather than `Stacks.SheafOfModules.derivedSheafHomOpenImmersionIso`, the isomorphism built from
the restriction of internal Hom complexes, because it is compatible with the tensor–internal-Hom
bijection by construction (`TwistedInverseImageDuality.curry_pull_map_comp_pullSheafHomMap`);
the two isomorphisms are not compared. -/
def pullSheafHomIso (L : Std B) :
    (sheafHom B).flip.obj L ⋙ pull g ≅ (pull g).op ⋙ (sheafHom A).flip.obj ((pull g).obj L) :=
  NatIso.ofComponents
    (fun P => haveI := isIso_pullSheafHomMap g P.unop L; asIso (pullSheafHomMap g P.unop L))
    (fun l => pullSheafHomMap_naturality g l.unop L)

/-- The component of `pullSheafHomIso g L` at `P` is the canonical map
`pullSheafHomMap g P.unop L`. -/
@[simp]
theorem pullSheafHomIso_hom_app (L : Std B) (P : (Std B)ᵒᵖ) :
    (pullSheafHomIso g L).hom.app P = pullSheafHomMap g P.unop L :=
  rfl

end OpenImmersion

/-! ### The duality formula for `f^!` -/

section UpperShriek

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  (j : CompactificationOf (Over.mk f.left))

/-- `f^!` on `D^+_Coh(𝒪_Y)`, read at the standard model of the derived categories through the
comparison of models, which is the identity on objects. -/
abbrev upperShriekStd : (plusCoh Y.left).FullSubcategory ⥤ Std X.left :=
  ObjectProperty.lift (Coherator.quasiCoherentProp Y.left)
      ((plusCoh Y.left).ι ⋙ (comparison Y.left).functor) (fun M => plusCoh_le_qcoh _ M.property) ⋙
    upperShriek f j ⋙ ObjectProperty.ι _ ⋙ (comparison X.left).inverse

variable {K : Std Y.left} (hK : IsDualizing K)

/-- A dualizing complex on `Y`, as an object of `D_QCoh(𝒪_Y)` at the locally small model. -/
abbrev dualizingQCoh : quasiCoherentDerivedCategory Y.left :=
  ⟨(comparison Y.left).functor.obj K, qcoh_of_isDualizingComplex hK⟩

/-- `f^!K`, read at the standard model. -/
abbrev upperShriekDualizing : Std X.left :=
  (comparison X.left).inverse.obj ((upperShriek f j).obj (dualizingQCoh hK)).obj

/-- `f^!` on `D^+_Coh` is `ā` followed by `Lj^*`, at the standard model. -/
def upperShriekStdIso :
    upperShriekStd f j ≅ ObjectProperty.ιOfLE plusCoh_le_qcoh ⋙ rightAdjointStd j.toBase ⋙
      pull j.immersion :=
  Functor.isoWhiskerLeft (ObjectProperty.lift (Coherator.quasiCoherentProp Y.left)
      ((plusCoh Y.left).ι ⋙ (comparison Y.left).functor) (fun M => plusCoh_le_qcoh _ M.property) ⋙
        twistedInverseImage j.toBase
            (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase) ⋙
          ObjectProperty.ι _) (pullModelConj j.immersion)

/-- **Stacks Project, Tag 0AU2.** In Situation [Stacks, Tag 0F42] — `S` Noetherian — let
`f : X ⟶ Y` be a morphism of schemes separated and of finite type over `S`, let `j` be a
compactification of `X` over `Y`, and let `K` be a dualizing complex on `Y`. Set
`D_Y(M) = R𝓗om(M, K)` and `D_X(E) = R𝓗om(E, f^!K)`. Then there is a canonical isomorphism

`f^!M ≅ D_X(Lf^* D_Y(M))`,

natural in `M ∈ D^+_Coh(𝒪_Y)`. -/
@[stacks 0AU2]
def upperShriekDualityIso :
    upperShriekStd f j ≅
      (plusCoh Y.left).ι ⋙ ((sheafHom Y.left).flip.obj K).rightOp ⋙ (pull f.left).op ⋙
        (sheafHom X.left).flip.obj (upperShriekDualizing f j hK) :=
  upperShriekStdIso f j ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (dualityIso j.toBase hK) (pull j.immersion) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (pullSheafHomIso j.immersion _) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (NatIso.op (pullCompIso j.immersion j.toBase f.left
          (immersion_comp_toBase f j))).symm _ ≪≫
        Functor.isoWhiskerLeft _ ((sheafHom X.left).flip.mapIso
          ((pullModelConj j.immersion).app _).symm)))

end UpperShriek

end Stacks.Duality.UpperShriekDuality

end
