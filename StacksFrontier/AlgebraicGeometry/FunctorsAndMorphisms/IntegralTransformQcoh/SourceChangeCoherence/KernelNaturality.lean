module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkMateComp
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.SourceChangeComp
import all StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Equivalence

/-!
# Naturality in the kernel of the source-change isomorphism of an integral transform

Let `R` be a commutative ring, let `X` be an affine scheme over `R`, let `f : X' ⟶ X` be a
morphism of schemes over `R` whose underlying morphism of schemes is affine and let `Y` be a
scheme over `R`.  For a quasi-coherent kernel `K` on `X ×_R Y` the integral transform of `K`
precomposed with the direct image along `f` is the integral transform of the inverse image of
`K` on `X' ×_R Y`.  This file proves that this identification is natural in the kernel.

## Main results

* `AlgebraicGeometry.quasicoherentIntegralTransformSourceChangeIso_naturality`: the
  source-change isomorphism of Tag 0FZF is natural in the kernel.
* `AlgebraicGeometry.projectionFormulaSourceNatTrans_naturality`: the projection-formula
  morphism of Tag 0FZE is natural in the module on the target of the morphism, as a
  commutative square of natural transformations.
* `AlgebraicGeometry.tensorLeftIsoTensorRightScheme_naturality`: the symmetry identifying
  tensoring on the left and on the right by a module is natural in that module.
* `AlgebraicGeometry.projectionFormulaSourceIsoOfFunctor_hom`: the projection-formula
  isomorphism of functors of Tag 0FZE is the projection-formula morphism whiskered by the
  functor along which it is restricted.
* `AlgebraicGeometry.tensorLeftIsoTensorRightScheme_naturality_inv`: the symmetry of the tensor
  product with both symmetries inverted.

## References

* [Stacks Project, Tag 0FZF](https://stacks.math.columbia.edu/tag/0FZF)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.IntegralTransformQcoh
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ProjectionFormula
open Stacks.SheafOfModules.TensorStalkRingedSpace
open scoped CategoryTheory.Prod

universe u

namespace AlgebraicGeometry

attribute [local implicit_reducible] TopCat.Sheaf
  AlgebraicGeometry.Scheme.Modules CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf structureSheafRing
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
  AlgebraicGeometry.Scheme.Modules.instCategory AlgebraicGeometry.Scheme.Modules.Hom

/-! ### Pasting of commutative squares -/

/-- A functor carries a commutative square to a commutative square. -/
private theorem map_square {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B A' B' : C} (a : A ⟶ B) (b : B ⟶ B') (c : A ⟶ A') (d : A' ⟶ B')
    (h : a ≫ b = c ≫ d) : F.map a ≫ F.map b = F.map c ≫ F.map d := by
  rw [← F.map_comp, ← F.map_comp, h]

/-- A commutative square whose two vertical edges are isomorphisms may be transposed to their
inverses. -/
theorem square_inv {E : Type*} [Category E] {A B A' B' : E} (e : A ≅ A') (d : B ≅ B')
    (x : A ⟶ B) (y : A' ⟶ B') (h : x ≫ d.hom = e.hom ≫ y) : y ≫ d.inv = e.inv ≫ x := by
  have hx : x = e.hom ≫ y ≫ d.inv := by
    rw [← Category.assoc, ← h, Category.assoc, d.hom_inv_id, Category.comp_id]
  rw [hx, Iso.inv_hom_id_assoc]

/-- A factorisation through two isomorphisms may be rewritten along equalities of those
isomorphisms. -/
private theorem subst_iso {E : Type*} [Category E] {A B A' B' : E} (e₁ e₂ : A ≅ A')
    (d₁ d₂ : B ≅ B') (h1 : e₁ = e₂) (h2 : d₁ = d₂) (Φ : A' ⟶ B') (α : A ⟶ B)
    (h : α = e₁.hom ≫ Φ ≫ d₁.inv) : α = e₂.hom ≫ Φ ≫ d₂.inv := by
  subst h1 h2
  exact h

/-- Five commutative squares pasted horizontally. -/
private theorem sq5 {E : Type*} [Category E] {A0 A1 A2 A3 A4 A5 B0 B1 B2 B3 B4 B5 : E}
    (x0 : A0 ⟶ B0) (x1 : A1 ⟶ B1) (x2 : A2 ⟶ B2) (x3 : A3 ⟶ B3) (x4 : A4 ⟶ B4) (x5 : A5 ⟶ B5)
    {a : A0 ⟶ A1} {b : A1 ⟶ A2} {c : A2 ⟶ A3} {d : A3 ⟶ A4} {e : A4 ⟶ A5}
    {a' : B0 ⟶ B1} {b' : B1 ⟶ B2} {c' : B2 ⟶ B3} {d' : B3 ⟶ B4} {e' : B4 ⟶ B5}
    (ha : x0 ≫ a' = a ≫ x1) (hb : x1 ≫ b' = b ≫ x2) (hc : x2 ≫ c' = c ≫ x3)
    (hd : x3 ≫ d' = d ≫ x4) (he : x4 ≫ e' = e ≫ x5) :
    x0 ≫ a' ≫ b' ≫ c' ≫ d' ≫ e' = (a ≫ b ≫ c ≫ d ≫ e) ≫ x5 := by
  rw [← Category.assoc x0 a', ha, Category.assoc, ← Category.assoc x1 b', hb,
    Category.assoc, ← Category.assoc x2 c', hc, Category.assoc,
    ← Category.assoc x3 d', hd, Category.assoc, he]
  simp only [Category.assoc]

/-- A commutative square conjugated by two isomorphisms on each side. -/
private theorem paste {E : Type*} [Category E] {A B A' B' C₁ C₂ C₁' C₂' : E}
    (u : A ≅ A') (v : B ≅ B') (w : C₁ ≅ C₁') (z : C₂ ≅ C₂')
    (Φ : A' ⟶ B') (Ψ : C₁' ⟶ C₂') (gK : A' ⟶ C₁') (gL : B' ⟶ C₂')
    (α : A ⟶ B) (β : C₁ ⟶ C₂)
    (hα : α = u.hom ≫ Φ ≫ v.inv) (hβ : β = w.hom ≫ Ψ ≫ z.inv)
    (h : Φ ≫ gL = gK ≫ Ψ) :
    α ≫ v.hom ≫ gL ≫ z.inv = (u.hom ≫ gK ≫ w.inv) ≫ β := by
  subst hα hβ
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc Φ gL, h, Category.assoc]

/-- A commutative square of natural transformations stays commutative after whiskering on both
sides. -/
private theorem whisker_square {C D D' E : Type*} [Category C] [Category D] [Category D']
    [Category E] (G : C ⥤ D) (H : D' ⥤ E) {F1 F2 F3 F4 : D ⥤ D'}
    (x : F1 ⟶ F2) (y : F2 ⟶ F4) (u : F1 ⟶ F3) (v : F3 ⟶ F4) (h : x ≫ y = u ≫ v) :
    Functor.whiskerLeft G (Functor.whiskerRight x H) ≫
        Functor.whiskerLeft G (Functor.whiskerRight y H) =
      Functor.whiskerLeft G (Functor.whiskerRight u H) ≫
        Functor.whiskerLeft G (Functor.whiskerRight v H) := by
  rw [← Functor.whiskerLeft_comp, ← Functor.whiskerLeft_comp, ← Functor.whiskerRight_comp,
    ← Functor.whiskerRight_comp, h]

/-- The exchange law for whiskering, with the right-hand whiskering of an isomorphism. -/
private theorem whisker_exchange_iso_left {C D E : Type*} [Category C] [Category D]
    [Category E] {F G : C ⥤ D} (e : F ≅ G) {H I : D ⥤ E} (β : H ⟶ I) :
    Functor.whiskerLeft F β ≫ (Functor.isoWhiskerRight e I).hom =
      (Functor.isoWhiskerRight e H).hom ≫ Functor.whiskerLeft G β :=
  Functor.whiskerLeft_comp_whiskerRight e.hom β

/-- The exchange law for whiskering, with the left-hand whiskering of an isomorphism and the
right-hand whiskering performed in two steps. -/
private theorem whisker_exchange_iso_right {C D D' E E' : Type*} [Category C] [Category D]
    [Category D'] [Category E] [Category E'] (G : C ⥤ D) {F1 F2 : D ⥤ D'} (α : F1 ⟶ F2)
    (H : D' ⥤ E) (H' : E ⥤ E') (J : D' ⥤ E') (η : H ⋙ H' ≅ J) :
    Functor.whiskerLeft G (Functor.whiskerRight (Functor.whiskerRight α H) H') ≫
        (Functor.isoWhiskerLeft (G ⋙ F2) η).hom =
      (Functor.isoWhiskerLeft (G ⋙ F1) η).hom ≫
        Functor.whiskerLeft G (Functor.whiskerRight α J) :=
  (Functor.whiskerLeft_comp_whiskerRight (Functor.whiskerLeft G α) η.hom).symm

/-- A commutative square one pair of whose edges are whiskerings of isomorphisms. -/
private theorem whisker_iso_square {C D D' E : Type*} [Category C] [Category D] [Category D']
    [Category E] (G : C ⥤ D) (H : D' ⥤ E) {F1 F2 F3 F4 : D ⥤ D'}
    (eK : F1 ≅ F3) (eL : F2 ≅ F4) (x : F1 ⟶ F2) (y : F3 ⟶ F4)
    (h : x ≫ eL.hom = eK.hom ≫ y) :
    Functor.whiskerLeft G (Functor.whiskerRight x H) ≫
        (Functor.isoWhiskerRight (Functor.isoWhiskerLeft G eL) H).hom =
      (Functor.isoWhiskerRight (Functor.isoWhiskerLeft G eK) H).hom ≫
        Functor.whiskerLeft G (Functor.whiskerRight y H) :=
  whisker_square G H x eL.hom eK.hom y h

/-- `AlgebraicGeometry.whisker_iso_square` with the right-hand whiskering performed in two
steps. -/
private theorem whisker_iso_square₂ {C D D' E E' : Type*} [Category C] [Category D]
    [Category D'] [Category E] [Category E'] (G : C ⥤ D) (H : D' ⥤ E) (H' : E ⥤ E')
    {F1 F2 F3 F4 : D ⥤ D'} (eK : F1 ≅ F3) (eL : F2 ≅ F4) (x : F1 ⟶ F2) (y : F3 ⟶ F4)
    (h : x ≫ eL.hom = eK.hom ≫ y) :
    Functor.whiskerLeft G (Functor.whiskerRight (Functor.whiskerRight x H) H') ≫
        (Functor.isoWhiskerRight (Functor.isoWhiskerLeft G eL) (H ⋙ H')).hom =
      (Functor.isoWhiskerRight (Functor.isoWhiskerLeft G eK) (H ⋙ H')).hom ≫
        Functor.whiskerLeft G (Functor.whiskerRight (Functor.whiskerRight y H) H') :=
  whisker_square G (H ⋙ H') x eL.hom eK.hom y h

/-- Three natural transformations whiskered on the left compose as they do before
whiskering. -/
theorem whiskerLeft_comp₃ {C D E : Type*} [Category C] [Category D] [Category E]
    (P : C ⥤ D) {F G H I : D ⥤ E} (x : F ⟶ G) (y : G ⟶ H) (z : H ⟶ I) :
    Functor.whiskerLeft P (x ≫ y ≫ z) =
      Functor.whiskerLeft P x ≫ Functor.whiskerLeft P y ≫ Functor.whiskerLeft P z := by
  simp

/-- A morphism in the source of a fully faithful functor commutes with isomorphisms that are
preimages under that functor as soon as their images do. -/
private theorem preimage_naturality {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    (FF : F.FullyFaithful) {A B A' B' : C} (a : A ⟶ A') (b : B ⟶ B')
    (e : F.obj A ≅ F.obj B) (e' : F.obj A' ≅ F.obj B')
    (h : F.map a ≫ e'.hom = e.hom ≫ F.map b) :
    a ≫ (FF.preimageIso e').hom = (FF.preimageIso e).hom ≫ b := by
  apply FF.map_injective
  rwa [F.map_comp, F.map_comp, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.preimageIso_hom, FF.map_preimage, FF.map_preimage]

/-! ### Naturality of the symmetry of the tensor product -/

/-- **The symmetry of the tensor product of modules on a scheme is natural in the fixed
factor.**  Tensoring on the left by a morphism `ψ` and then exchanging the two factors is
exchanging the two factors and then tensoring on the right by `ψ`. -/
theorem tensorLeftIsoTensorRightScheme_naturality (P : Scheme.{u}) {K L : P.Modules}
    (ψ : K ⟶ L) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (P).toRingedSpace.sheaf).map ψ ≫
        ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight (P).presheaf
          (P).ringCatSheaf.2 (L))).hom =
      ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight (P).presheaf
          (P).ringCatSheaf.2 (K))).hom ≫
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (P.toRingedSpace).sheaf).flip.map ψ :=
  NatTrans.ext (funext fun moduleSheaf =>
    (Stacks.SheafOfModules.TensorRaised.tensorRightRaisedIso
      P.toRingedSpace.sheaf moduleSheaf).hom.naturality ψ)

/-- `AlgebraicGeometry.tensorLeftIsoTensorRightScheme_naturality` with the two symmetries
inverted: tensoring on the right by `ψ` and then exchanging the two factors back is exchanging
the two factors back and then tensoring on the left by `ψ`. -/
theorem tensorLeftIsoTensorRightScheme_naturality_inv (P : Scheme.{u}) {K L : P.Modules}
    (ψ : K ⟶ L) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (P.toRingedSpace).sheaf).flip.map ψ ≫
        ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight (P).presheaf
          (P).ringCatSheaf.2 (L))).inv =
      ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight (P).presheaf
          (P).ringCatSheaf.2 (K))).inv ≫
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (P).toRingedSpace.sheaf).map ψ :=
  square_inv _ _ _ _ (tensorLeftIsoTensorRightScheme_naturality P ψ)

/-! ### Naturality of the projection formula in the module on the target -/

/-- Naturality of the projection-formula morphism in the module on the target, in the form in
which the two tensorings by that morphism are values of the canonical bifunctor map. -/
theorem projectionFormulaMap_naturality_target {T S : Scheme.{u}} (h : T ⟶ S)
    (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
    {H H' : S.Modules} (k : H ⟶ H') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (S.toRingedSpace).sheaf).flip.map k).app ((Scheme.Modules.pushforward h).obj G) ≫
        projectionFormulaMap h G H' =
      projectionFormulaMap h G H ≫ (Scheme.Modules.pushforward h).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (T.toRingedSpace).sheaf).flip.map ((Scheme.Modules.pullback h).map k)).app G) := by
  have hid := (modulePushforward h.toLRSHom.toShHom).map_id G
  have hnat := projectionFormulaMap_natural h (𝟙 G) k
  rw [hid] at hnat
  let sourceTensor := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    S.toRingedSpace.sheaf
  let targetTensor := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    T.toRingedSpace.sheaf
  let directImage := Scheme.Modules.pushforward h
  let inverseImage := Scheme.Modules.pullback h
  have sourceIdentity :=
    (congrArg (fun transformation : sourceTensor.obj (directImage.obj G) ⟶
        sourceTensor.obj (directImage.obj G) =>
      transformation.app H ≫ (sourceTensor.obj (directImage.obj G)).map k)
      (sourceTensor.map_id (directImage.obj G))).trans (Category.id_comp _)
  have targetIdentity :=
    (congrArg (fun transformation : targetTensor.obj G ⟶ targetTensor.obj G =>
      transformation.app (inverseImage.obj H) ≫ (targetTensor.obj G).map (inverseImage.map k))
      (targetTensor.map_id G)).trans (Category.id_comp _)
  have naturality :
      ((sourceTensor.map (𝟙 (directImage.obj G))).app H ≫
        (sourceTensor.obj (directImage.obj G)).map k) ≫ projectionFormulaMap h G H' =
      projectionFormulaMap h G H ≫ directImage.map
        ((targetTensor.map (𝟙 G)).app (inverseImage.obj H) ≫
          (targetTensor.obj G).map (inverseImage.map k)) := hnat
  exact (congrArg (fun component => component ≫ projectionFormulaMap h G H')
    sourceIdentity).symm.trans (naturality.trans
      (congrArg (fun component => projectionFormulaMap h G H ≫ directImage.map component)
        targetIdentity))

/-- **The projection-formula morphism of Tag 0FZE is natural in the module on the target**, as
a commutative square of the natural transformations in the module on the source. -/
theorem projectionFormulaSourceNatTrans_naturality {T S : Scheme.{u}} (h : T ⟶ S)
    {H H' : S.Modules} (k : H ⟶ H') :
    Functor.whiskerLeft (Scheme.Modules.pushforward h)
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (S.toRingedSpace).sheaf).flip.map k) ≫
        projectionFormulaSourceNatTrans h H' =
      projectionFormulaSourceNatTrans h H ≫
        Functor.whiskerRight
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              (T.toRingedSpace).sheaf).flip.map ((Scheme.Modules.pullback h).map k))
          (Scheme.Modules.pushforward h) :=
  NatTrans.ext (funext fun G => projectionFormulaMap_naturality_target h G k)

/-- The projection-formula isomorphism of functors of Tag 0FZE is the projection-formula
morphism whiskered by the functor along which it is restricted. -/
theorem projectionFormulaSourceIsoOfFunctor_hom {C : Type*} [Category C] {T S : Scheme.{u}}
    (h : T ⟶ S) [IsAffineHom h] (H : S.Modules) (hH : H.IsQuasicoherent) (F : C ⥤ T.Modules)
    (hF : ∀ A, (F.obj A).IsQuasicoherent) :
    (projectionFormulaSourceIsoOfFunctor h H hH F hF).hom =
      Functor.whiskerLeft F (projectionFormulaSourceNatTrans h H) :=
  rfl

/-- `AlgebraicGeometry.projectionFormulaSourceNatTrans_naturality` whiskered on both sides. -/
private theorem projectionFormulaSourceIsoOfFunctor_whisker_square {C : Type*} [Category C]
    {E : Type*} [Category E] {T S : Scheme.{u}} (h : T ⟶ S) [IsAffineHom h]
    {H H' : S.Modules} (k : H ⟶ H') (hH : H.IsQuasicoherent) (hH' : H'.IsQuasicoherent)
    (F : C ⥤ T.Modules) (hF : ∀ A, (F.obj A).IsQuasicoherent) (W : S.Modules ⥤ E) :
    Functor.whiskerLeft (F ⋙ Scheme.Modules.pushforward h)
          (Functor.whiskerRight ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              (S.toRingedSpace).sheaf).flip.map k) W) ≫
        (Functor.isoWhiskerRight
          (projectionFormulaSourceIsoOfFunctor h H' hH' F hF) W).hom =
      (Functor.isoWhiskerRight (projectionFormulaSourceIsoOfFunctor h H hH F hF) W).hom ≫
        Functor.whiskerLeft F (Functor.whiskerRight (Functor.whiskerRight
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              (T.toRingedSpace).sheaf).flip.map ((Scheme.Modules.pullback h).map k))
          (Scheme.Modules.pushforward h)) W) :=
  whisker_square F W _ _ _ _ (projectionFormulaSourceNatTrans_naturality h k)

/-! ### Naturality of the formula of Tag 0FZB in the kernel -/

/-- The pullback--tensor--pushforward formula applied to a morphism of kernels is tensoring on
the left by that morphism, after taking inverse images along the first projection and before
taking direct images along the second. -/
theorem formulaFunctor_map (R : Type u) [CommRing R] (Z Y : Over (Spec (.of R)))
    [CompactSpace Z.left] [QuasiSeparatedSpace Z.left]
    {K L : (pullback Z.hom Y.hom).Modules} (ψ : K ⟶ L) :
    (formulaFunctor R Z Y).map ψ =
      Functor.whiskerLeft ((SheafOfModules.isQuasicoherent Z.left.ringCatSheaf).ι ⋙
          Scheme.Modules.pullback (pullback.fst Z.hom Y.hom))
        (Functor.whiskerRight ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ((pullback Z.hom Y.hom)).toRingedSpace.sheaf).map ψ)
          (Scheme.Modules.pushforward (pullback.snd Z.hom Y.hom))) :=
  rfl

section SourceChange

variable (R : Type u) [CommRing R] (X X' Y : Over (Spec (.of R))) [IsAffine X.left]
  (f : X' ⟶ X) [IsAffineHom f.left]
  (K L : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) (φ : K ⟶ L)

omit [IsAffine X.left] in
/-- Affine change of source for the pullback--tensor--pushforward formula of Tag 0FZB is
natural in the kernel, with the tensorings by the morphism of kernels written out. -/
private theorem integralTransformFormulaSourceChangeIsoHom_naturality :
    Functor.whiskerLeft ((SheafOfModules.isQuasicoherent X'.left.ringCatSheaf).ι ⋙
          Scheme.Modules.pushforward f.left ⋙
          Scheme.Modules.pullback (pullback.fst X.hom Y.hom))
        (Functor.whiskerRight ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ((pullback X.hom Y.hom)).toRingedSpace.sheaf).map φ.hom)
          (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom))) ≫
        (integralTransformFormulaSourceChangeIso R X X' Y f L).hom =
      (integralTransformFormulaSourceChangeIso R X X' Y f K).hom ≫
        Functor.whiskerLeft ((SheafOfModules.isQuasicoherent X'.left.ringCatSheaf).ι ⋙
            Scheme.Modules.pullback (pullback.fst X'.hom Y.hom))
          (Functor.whiskerRight ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ((pullback X'.hom Y.hom)).toRingedSpace.sheaf).map
              ((Scheme.Modules.pullback (sourceChangeMap R X X' Y f)).map φ.hom))
            (Scheme.Modules.pushforward (pullback.snd X'.hom Y.hom))) := by
  refine sq5 _
    (Functor.whiskerLeft ((SheafOfModules.isQuasicoherent X'.left.ringCatSheaf).ι ⋙
        Scheme.Modules.pullback (pullback.fst X'.hom Y.hom) ⋙
        Scheme.Modules.pushforward (sourceChangeMap R X X' Y f))
      (Functor.whiskerRight ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ((pullback X.hom Y.hom)).toRingedSpace.sheaf).map φ.hom)
        (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom))))
    (Functor.whiskerLeft (((SheafOfModules.isQuasicoherent X'.left.ringCatSheaf).ι ⋙
          Scheme.Modules.pullback (pullback.fst X'.hom Y.hom)) ⋙
        Scheme.Modules.pushforward (sourceChangeMap R X X' Y f))
      (Functor.whiskerRight ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ((pullback X.hom Y.hom).toRingedSpace).sheaf).flip.map φ.hom)
        (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom))))
    (Functor.whiskerLeft ((SheafOfModules.isQuasicoherent X'.left.ringCatSheaf).ι ⋙
        Scheme.Modules.pullback (pullback.fst X'.hom Y.hom))
      (Functor.whiskerRight (Functor.whiskerRight
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ((pullback X'.hom Y.hom).toRingedSpace).sheaf).flip.map
            ((Scheme.Modules.pullback (sourceChangeMap R X X' Y f)).map φ.hom))
          (Scheme.Modules.pushforward (sourceChangeMap R X X' Y f)))
        (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom))))
    (Functor.whiskerLeft ((SheafOfModules.isQuasicoherent X'.left.ringCatSheaf).ι ⋙
        Scheme.Modules.pullback (pullback.fst X'.hom Y.hom))
      (Functor.whiskerRight (Functor.whiskerRight
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ((pullback X'.hom Y.hom)).toRingedSpace.sheaf).map
            ((Scheme.Modules.pullback (sourceChangeMap R X X' Y f)).map φ.hom))
          (Scheme.Modules.pushforward (sourceChangeMap R X X' Y f)))
        (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom))))
    _ ?_ ?_ ?_ ?_ ?_
  · exact whisker_exchange_iso_left _ _
  · refine whisker_iso_square _ _ _ _ _ _ ?_
    exact tensorLeftIsoTensorRightScheme_naturality (pullback X.hom Y.hom) φ.hom
  · exact projectionFormulaSourceIsoOfFunctor_whisker_square _ _ _ _ _ _ _
  · refine whisker_iso_square₂ _ _ _ _ _ _ _ ?_
    exact square_inv _ _ _ _
      (tensorLeftIsoTensorRightScheme_naturality (pullback X'.hom Y.hom)
        ((Scheme.Modules.pullback (sourceChangeMap R X X' Y f)).map φ.hom))
  · exact whisker_exchange_iso_right _ _ _ _ _ _

omit [IsAffine X.left] in
/-- Affine change of source for the pullback--tensor--pushforward formula of Tag 0FZB is
natural in the kernel.  Only quasi-compactness and quasi-separatedness of the two sources are
used. -/
theorem integralTransformFormulaSourceChangeIso_naturality
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [CompactSpace X'.left] [QuasiSeparatedSpace X'.left] :
    Functor.whiskerLeft (quasicoherentPushforward f.left)
          ((formulaFunctor R X Y).map φ.hom) ≫
        (integralTransformFormulaSourceChangeIso R X X' Y f L).hom =
      (integralTransformFormulaSourceChangeIso R X X' Y f K).hom ≫
        (formulaFunctor R X' Y).map
          ((Scheme.Modules.pullback (sourceChangeMap R X X' Y f)).map φ.hom) :=
  integralTransformFormulaSourceChangeIsoHom_naturality R X X' Y f K L φ

/-- The image under the inclusion of quasi-coherent modules of the integral transform of a
morphism of kernels is the pullback--tensor--pushforward formula applied to that morphism. -/
theorem whiskerRight_integralTransformQcohFunctor_map (Z : Over (Spec (.of R)))
    [CompactSpace Z.left] [QuasiSeparatedSpace Z.left]
    (A B : Scheme.QuasicoherentModules (pullback Z.hom Y.hom)) (ψ : A ⟶ B) :
    Functor.whiskerRight ((integralTransformQcohFunctor R Z Y).map ψ)
        (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).ι =
      (quasicoherentIntegralTransformData R Z Y A).comparison.hom ≫
        (formulaFunctor R Z Y).map ψ.hom ≫
        (quasicoherentIntegralTransformData R Z Y B).comparison.inv :=
  subst_iso (comparisonData R Z Y A) _ (comparisonData R Z Y B) _
    (Iso.trans_refl _) (Iso.trans_refl _) _ _
    (((SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).fullyFaithfulι.whiskeringRight
      (Scheme.QuasicoherentModules Z.left)).map_preimage _)

/-- The source-change isomorphism, written as a preimage under the inclusion of quasi-coherent
modules, is natural in the kernel.  The section variables are rebound so as not to require `X`
to be affine. -/
private theorem preimageIso_sourceChange_naturality_aux (X : Over (Spec (.of R)))
    (f : X' ⟶ X) [IsAffineHom f.left] (K L : Scheme.QuasicoherentModules (pullback X.hom Y.hom))
    (φ : K ⟶ L) [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [CompactSpace X'.left] [QuasiSeparatedSpace X'.left] :
    Functor.whiskerLeft (quasicoherentPushforward f.left)
          ((integralTransformQcohFunctor R X Y).map φ) ≫
        (((SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).fullyFaithfulι.whiskeringRight
          (Scheme.QuasicoherentModules X'.left)).preimageIso
          (X := quasicoherentPushforward f.left ⋙ quasicoherentIntegralTransform R X Y L)
          (Y := quasicoherentIntegralTransform R X' Y (sourceChangeKernel R X X' Y f L))
          (Functor.isoWhiskerLeft (quasicoherentPushforward f.left)
              (quasicoherentIntegralTransformData R X Y L).comparison ≪≫
            integralTransformFormulaSourceChangeIso R X X' Y f L ≪≫
            (quasicoherentIntegralTransformData R X' Y
              (sourceChangeKernel R X X' Y f L)).comparison.symm)).hom =
      (((SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).fullyFaithfulι.whiskeringRight
          (Scheme.QuasicoherentModules X'.left)).preimageIso
          (X := quasicoherentPushforward f.left ⋙ quasicoherentIntegralTransform R X Y K)
          (Y := quasicoherentIntegralTransform R X' Y (sourceChangeKernel R X X' Y f K))
          (Functor.isoWhiskerLeft (quasicoherentPushforward f.left)
              (quasicoherentIntegralTransformData R X Y K).comparison ≪≫
            integralTransformFormulaSourceChangeIso R X X' Y f K ≪≫
            (quasicoherentIntegralTransformData R X' Y
              (sourceChangeKernel R X X' Y f K)).comparison.symm)).hom ≫
        (integralTransformQcohFunctor R X' Y).map
          ((quasicoherentPullback (sourceChangeMap R X X' Y f)).map φ) := by
  refine preimage_naturality
    ((SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).fullyFaithfulι.whiskeringRight
      (Scheme.QuasicoherentModules X'.left))
    (Functor.whiskerLeft (quasicoherentPushforward f.left)
      ((integralTransformQcohFunctor R X Y).map φ))
    ((integralTransformQcohFunctor R X' Y).map
      ((quasicoherentPullback (sourceChangeMap R X X' Y f)).map φ))
    (Functor.isoWhiskerLeft (quasicoherentPushforward f.left)
        (quasicoherentIntegralTransformData R X Y K).comparison ≪≫
      integralTransformFormulaSourceChangeIso R X X' Y f K ≪≫
      (quasicoherentIntegralTransformData R X' Y
        (sourceChangeKernel R X X' Y f K)).comparison.symm)
    (Functor.isoWhiskerLeft (quasicoherentPushforward f.left)
        (quasicoherentIntegralTransformData R X Y L).comparison ≪≫
      integralTransformFormulaSourceChangeIso R X X' Y f L ≪≫
      (quasicoherentIntegralTransformData R X' Y
        (sourceChangeKernel R X X' Y f L)).comparison.symm) ?_
  refine paste _ _ _ _ _ _ _ _ _ _ ?_ ?_
    (integralTransformFormulaSourceChangeIso_naturality R X X' Y f K L φ)
  · exact (congrArg (Functor.whiskerLeft (quasicoherentPushforward f.left))
      (whiskerRight_integralTransformQcohFunctor_map R Y X K L φ)).trans
      (whiskerLeft_comp₃ _ _ _ _)
  · exact whiskerRight_integralTransformQcohFunctor_map R Y X' _ _ _

/-- **The source-change isomorphism of Tag 0FZF is natural in the kernel.**  For a morphism
`φ : K ⟶ L` of quasi-coherent modules on `X ×_R Y`, the square formed by the two source-change
isomorphisms, the direct image along `f` of the integral transform of `φ` and the integral
transform of the inverse image of `φ` commutes. -/
theorem quasicoherentIntegralTransformSourceChangeIso_naturality :
    let : IsAffine X'.left := isAffine_of_isAffineHom f.left
    Functor.whiskerLeft (quasicoherentPushforward f.left)
          ((integralTransformQcohFunctor R X Y).map φ) ≫
        (quasicoherentIntegralTransformSourceChangeIso R X X' Y f L).hom =
      (quasicoherentIntegralTransformSourceChangeIso R X X' Y f K).hom ≫
        (integralTransformQcohFunctor R X' Y).map
          ((quasicoherentPullback (sourceChangeMap R X X' Y f)).map φ) := by
  let : IsAffine X'.left := isAffine_of_isAffineHom f.left
  exact preimageIso_sourceChange_naturality_aux R X' Y X f K L φ

omit [IsAffine X.left] in
/-- **The source-change isomorphism of Tag 0FZF is natural in the kernel, for a quasi-compact
and quasi-separated source.**  The isomorphisms are written out as the preimages, under the
inclusion of the quasi-coherent modules, of the source change of the pullback--tensor--pushforward
formula conjugated by the comparisons. -/
theorem preimageIso_sourceChange_naturality
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [CompactSpace X'.left] [QuasiSeparatedSpace X'.left] :
    Functor.whiskerLeft (quasicoherentPushforward f.left)
          ((integralTransformQcohFunctor R X Y).map φ) ≫
        (((SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).fullyFaithfulι.whiskeringRight
          (Scheme.QuasicoherentModules X'.left)).preimageIso
          (X := quasicoherentPushforward f.left ⋙ quasicoherentIntegralTransform R X Y L)
          (Y := quasicoherentIntegralTransform R X' Y (sourceChangeKernel R X X' Y f L))
          (Functor.isoWhiskerLeft (quasicoherentPushforward f.left)
              (quasicoherentIntegralTransformData R X Y L).comparison ≪≫
            integralTransformFormulaSourceChangeIso R X X' Y f L ≪≫
            (quasicoherentIntegralTransformData R X' Y
              (sourceChangeKernel R X X' Y f L)).comparison.symm)).hom =
      (((SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).fullyFaithfulι.whiskeringRight
          (Scheme.QuasicoherentModules X'.left)).preimageIso
          (X := quasicoherentPushforward f.left ⋙ quasicoherentIntegralTransform R X Y K)
          (Y := quasicoherentIntegralTransform R X' Y (sourceChangeKernel R X X' Y f K))
          (Functor.isoWhiskerLeft (quasicoherentPushforward f.left)
              (quasicoherentIntegralTransformData R X Y K).comparison ≪≫
            integralTransformFormulaSourceChangeIso R X X' Y f K ≪≫
            (quasicoherentIntegralTransformData R X' Y
              (sourceChangeKernel R X X' Y f K)).comparison.symm)).hom ≫
        (integralTransformQcohFunctor R X' Y).map
          ((quasicoherentPullback (sourceChangeMap R X X' Y f)).map φ) :=
  preimageIso_sourceChange_naturality_aux R X' Y X f K L φ

end SourceChange

end AlgebraicGeometry

end
