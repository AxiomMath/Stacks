module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.FibreSolution
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageCompAssoc
public import StacksFrontier.Deformation.ToposThickening.SolutionTransportExtension

/-!
# The solution of a flat deformation, read on `i⁻¹𝒪_{X'}`

Let `D = (f' : X' ⟶ Y', i : X ⟶ X')` be a flat deformation of `f : X ⟶ Y` over the first order
thickening `Y ⊂ Y'`. Its solution of the extension problem of [Stacks Project, Tag 0D17]
(`AlgebraicGeometry.Space.FlatThickeningDeformation.Deformation.solutionOnSource`) is built on the
closed fibre `X'_0 = f'⁻¹(Y)` and restricted along `X ≅ X'_0`. This file reads it on the sheaf
of rings `i⁻¹𝒪_{X'}` of the source's proof: the middle term is identified with `i⁻¹𝒪_{X'}`, the
reduction becomes `i^♯ : i⁻¹𝒪_{X'} ⟶ 𝒪_X`, and the map from the thickened base becomes the
inverse image along `i` of `f'^♯`, read through `f⁻¹t⁻¹𝒪_{Y'} ≅ (f ≫ t)⁻¹𝒪_{Y'} = (i ≫ f')⁻¹𝒪_{Y'}`
(Stacks 03G8).

## Main definitions
* `...Deformation.ambientSolution`: the solution with middle term `i⁻¹𝒪_{X'}`.

## Main results
* `...Deformation.ambientSolution_reduction`, `...Deformation.ambientSolution_baseMap`: its
  reduction and its map from the thickened base.
* `...Deformation.isomorphic_ambientSolution`: it is isomorphic to `solutionOnSource`.

## References
* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Deformation.ToposThickening.RingedToposExtensionProblem
open Stacks.Sheaves.ToposPullback (inverseImageCommRingRestrictionIso
  inverseImageCommRingRestrictionIso_naturality)

universe u

namespace AlgebraicGeometry.Space.FlatThickeningDeformation

open _root_.Deformation.ToposThickening.RingedToposExtensionProblem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y' : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS Y'.1}
  (hZ : IsFirstOrderThickening B S hS Y' Z.1) {X : AlgebraicSpaces B S hS}

/-- A composite with `eqToHom`s, computed from its two pieces. -/
theorem eqToHom_comp_chain {𝒞 : Type*} [Category 𝒞] {A₁ A₂ R T O : 𝒞} (e₁ : A₁ = A₂)
    (α : A₂ ⟶ R) (c₁ : R = T) (c₂ : T = R) (r : R ⟶ O) (s' : A₂ ⟶ O) (s : A₁ ⟶ O)
    (h : α ≫ r = s') (h' : eqToHom e₁ ≫ s' = s) :
    ((eqToHom e₁ ≫ α) ≫ eqToHom c₁) ≫ eqToHom c₂ ≫ r = s := by
  subst h h' c₁; simp

/-- The categorical shape of the comparison of the two maps from the thickened base. -/
theorem baseMap_coherence_aux {𝒞 𝒞' : Type*} [Category 𝒞] [Category 𝒞'] (F R : 𝒞' ⥤ 𝒞)
    {T₀ A₁ A₂ P₀ N₀ : 𝒞} {T' U' V' P' N' : 𝒞'}
    (a : T₀ ⟶ F.obj T') (νT : F.obj T' ≅ R.obj T') (νN : F.obj N' ≅ R.obj N')
    (uI : T' ≅ U') (e' : U' ⟶ V') (v : V' ⟶ P') (s : P' ⟶ N')
    (xI : T₀ ≅ A₁) (e₀ : A₁ ⟶ A₂) (y : A₂ ⟶ P₀) (s₀ : P₀ ⟶ N₀)
    (b : F.obj N' ⟶ N₀) (bPI : F.obj P' ≅ P₀) (z₁ : A₁ ⟶ F.obj U') (z₂ : A₂ ⟶ F.obj V')
    (hν : F.map ((uI.hom ≫ e') ≫ v ≫ s) ≫ νN.hom = νT.hom ≫ R.map ((uI.hom ≫ e') ≫ v ≫ s))
    (H1 : xI.inv ≫ a = z₁ ≫ F.map uI.inv) (H2 : y ≫ bPI.inv = z₂ ≫ F.map v)
    (H3 : F.map s ≫ b = bPI.hom ≫ s₀) (H4 : z₁ ≫ F.map e' = e₀ ≫ z₂) :
    (a ≫ νT.hom) ≫ R.map ((uI.hom ≫ e') ≫ v ≫ s) ≫ (νN.inv ≫ b) = xI.hom ≫ e₀ ≫ y ≫ s₀ := by
  have ha : a = xI.hom ≫ z₁ ≫ F.map uI.inv := by rw [← H1, Iso.hom_inv_id_assoc]
  have hz : z₂ ≫ F.map v = y ≫ bPI.inv := H2.symm
  have hν' : νT.hom ≫ R.map ((uI.hom ≫ e') ≫ v ≫ s) ≫ νN.inv ≫ b =
      F.map ((uI.hom ≫ e') ≫ v ≫ s) ≫ b := by
    rw [← Category.assoc, ← hν, Category.assoc, Iso.hom_inv_id_assoc]
  rw [Category.assoc, hν', ha]
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc uI.inv uI.hom, Iso.inv_hom_id, F.map_id, Category.id_comp]
  rw [reassoc_of% H4, H3, reassoc_of% hz, Iso.inv_hom_id_assoc]

/-- Assembling a composite with `eqToHom`s from a factorization. -/
theorem eqToHom_assemble {𝒞 : Type*} [Category 𝒞] {A₀ A M₁ M₂ N₀ N₁ Q : 𝒞} (b : A₀ = A)
    (M : A ⟶ M₁) (c : M₂ = M₁) (N : M₁ ⟶ N₀) (e : N₀ = N₁) (M' : A ⟶ Q) (M'' : Q ⟶ M₁)
    (K : A ⟶ N₀) (h : M = M' ≫ M'') (h' : M' ≫ M'' ≫ N = K) :
    (eqToHom b ≫ M ≫ eqToHom c.symm) ≫ (eqToHom c ≫ N ≫ eqToHom e) =
      eqToHom b ≫ K ≫ eqToHom e := by
  subst h h' c; simp

/-- Conjugating a morphism by `eqToHom`s of self-equalities leaves it unchanged. -/
theorem eqToHom_conj_self {𝒞 : Type*} [Category 𝒞] {A₁ A₂ : 𝒞} (b : A₁ = A₁) (e : A₂ = A₂)
    (k : A₁ ⟶ A₂) : eqToHom b ≫ k ≫ eqToHom e = k := by
  simp

/-! ### Solutions along an equality of morphisms -/

section Cast

variable {f₁ f₂ : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)} (h : f₁ = f₂)
  (P : (problem f₁ hZ).CompatibleFirstOrderThickening)

/-- Transporting a solution along an equality `f₁ = f₂` does not change its middle term. -/
theorem cast_extension :
    (h ▸ P : (problem f₂ hZ).CompatibleFirstOrderThickening).extension = P.extension := by
  subst h; rfl

/-- The reduction of a solution transported along `f₁ = f₂` is the original reduction, read
through the equality of middle terms. -/
theorem cast_reduction :
    (h ▸ P : (problem f₂ hZ).CompatibleFirstOrderThickening).reduction =
      eqToHom (cast_extension hZ h P) ≫ P.reduction := by
  subst h; exact (Category.id_comp _).symm

/-- The map from the thickened base of a solution transported along `f₁ = f₂` is the original
one, conjugated by the equalities of its source and of the middle terms. -/
theorem cast_baseMap :
    (h ▸ P : (problem f₂ hZ).CompatibleFirstOrderThickening).baseMap =
      eqToHom (by subst h; rfl) ≫ P.baseMap ≫ eqToHom (cast_extension hZ h P).symm := by
  subst h; exact ((Category.id_comp _).trans (Category.comp_id _)).symm

end Cast

section RingIso

variable {X₀ W : AlgebraicSpaces B S hS} (ρ : X ≅ X₀) (g : X₀ ⟶ W)

/-- `fibreRingIso` followed by the restriction of `g^♯` is `(ρ ≫ g)^♯`. -/
theorem fibreRingIso_hom_comp_structureSharp :
    (fibreRingIso ρ g (smallEtaleRingedTopos B S hS W).O).hom ≫
        (fibreRingRes ρ).map (structureSharpInverseImage B S hS g) ≫ (fibreStructureIso ρ).inv =
      structureSharpInverseImage B S hS (ρ.hom ≫ g) :=
  (Category.assoc _ _ _).symm.trans ((Iso.comp_inv_eq _).2
    (etaleRestrictionRingComparison B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ) g).comm.symm)

end RingIso

section BaseCoherence

variable {X' X₀ W : AlgebraicSpaces B S hS} (incl : X₀ ⟶ X') (g : X' ⟶ Y') (e₀ : X₀ ⟶ W)
  (t : W ⟶ Y') (hsq : incl ≫ g = e₀ ≫ t) (ρ : X ≅ X₀)

omit hZ in
/-- Equal morphisms of spaces have equal inverse images of a sheaf of rings. -/
theorem inverseImage_congr {W₁ W₂ : AlgebraicSpaces B S hS} {p q : W₁ ⟶ W₂} (h : p = q)
    (A : Sheaf (SmallEtale.topology B S hS W₂.1) CommRingCat.{u}) :
    (smallEtaleInverseImageRing B S hS p).obj A = (smallEtaleInverseImageRing B S hS q).obj A := by
  rw [h]

omit hZ in
/-- Equal morphisms of spaces, precomposed with a common `r`, have equal inverse images of a
sheaf of rings. -/
theorem inverseImage_congr_comp {V W₁ W₂ : AlgebraicSpaces B S hS} (r : V ⟶ W₁)
    {p q : W₁ ⟶ W₂} (h : p = q) (A : Sheaf (SmallEtale.topology B S hS W₂.1) CommRingCat.{u}) :
    (smallEtaleInverseImageRing B S hS (r ≫ p)).obj A =
      (smallEtaleInverseImageRing B S hS (r ≫ q)).obj A := by
  rw [h]

omit hZ in
/-- The comparison `r⁻¹p⁻¹ ≅ (r ≫ p)⁻¹` commutes with the `eqToHom`s induced by an equality
`p = q`. -/
theorem compInverseImageRingIso_inv_app_eqToHom {V W₁ W₂ : AlgebraicSpaces B S hS}
    (r : V ⟶ W₁) {p q : W₁ ⟶ W₂} (hpq : p = q) (A : Sheaf (SmallEtale.topology B S hS W₂.1)
        CommRingCat.{u}) :
    (smallEtaleRingedToposHom_compInverseImageRingIso B S hS r p).inv.app A ≫
        (smallEtaleInverseImageRing B S hS r).map
          (eqToHom (inverseImage_congr hpq A)) =
      eqToHom (inverseImage_congr_comp r hpq A) ≫
        (smallEtaleRingedToposHom_compInverseImageRingIso B S hS r q).inv.app A := by
  subst hpq
  simp only [eqToHom_refl, Category.id_comp]
  exact (congrArg (_ ≫ ·) ((smallEtaleInverseImageRing B S hS r).map_id _)).trans
    (Category.comp_id _)

/-- The shape of the comparison of the two maps from the thickened base, on the sheaves of
the closed fibre: every composite morphism of spaces is a variable. -/
theorem fibreRingIso_squareBaseIso_coherence :
    ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS ρ.hom e₀).inv.app
        ((smallEtaleInverseImageRing B S hS t).obj (smallEtaleRingedTopos B S hS Y').O) ≫
        (inverseImageCommRingRestrictionIso (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS X₀.1)
      (smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ))
      (smallEtaleRingedToposHom B S hS ρ.hom).toToposHom
      (smallToposMorphismTypeU_inverseImageIso B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ))
      ((smallEtaleInverseImageRing B S hS e₀).obj ((smallEtaleInverseImageRing B S hS t).obj
          (smallEtaleRingedTopos B S hS Y').O))).hom) ≫
      (fibreRingRes ρ).map ((((smallEtaleRingedToposHom_compInverseImageRingIso B S hS e₀ t).app
          (smallEtaleRingedTopos B S hS Y').O).hom ≫
          eqToHom (inverseImage_congr hsq.symm (smallEtaleRingedTopos B S hS Y').O)) ≫
        (smallEtaleRingedToposHom_compInverseImageRingIso B S hS incl g).inv.app
            (smallEtaleRingedTopos B S hS Y').O ≫
          (smallEtaleInverseImageRing B S hS incl).map
            (smallEtaleRingedToposHom B S hS g).fSharpInverseImage) ≫
      ((inverseImageCommRingRestrictionIso (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS X₀.1)
      (smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ))
      (smallEtaleRingedToposHom B S hS ρ.hom).toToposHom
      (smallToposMorphismTypeU_inverseImageIso B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ))
      ((smallEtaleInverseImageRing B S hS incl).obj (smallEtaleRingedTopos B S hS X').O)).inv ≫
        (smallEtaleRingedToposHom_compInverseImageRingIso B S hS ρ.hom incl).hom.app
            (smallEtaleRingedTopos B S hS X').O) =
    ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS (ρ.hom ≫ e₀) t).app
        (smallEtaleRingedTopos B S hS Y').O).hom ≫
      eqToHom (inverseImage_congr_comp ρ.hom hsq.symm (smallEtaleRingedTopos B S hS Y').O) ≫
      (smallEtaleRingedToposHom_compInverseImageRingIso B S hS (ρ.hom ≫ incl) g).inv.app
          (smallEtaleRingedTopos B S hS Y').O ≫
        (smallEtaleInverseImageRing B S hS (ρ.hom ≫ incl)).map
          (smallEtaleRingedToposHom B S hS g).fSharpInverseImage := by
  refine baseMap_coherence_aux (smallEtaleInverseImageRing B S hS ρ.hom) (fibreRingRes ρ)
    (T' := (smallEtaleInverseImageRing B S hS e₀).obj
      ((smallEtaleInverseImageRing B S hS t).obj (smallEtaleRingedTopos B S hS Y').O))
    (U' := (smallEtaleInverseImageRing B S hS (e₀ ≫ t)).obj (smallEtaleRingedTopos B S hS Y').O)
    (V' := (smallEtaleInverseImageRing B S hS (incl ≫ g)).obj (smallEtaleRingedTopos B S hS Y').O)
    (P' := (smallEtaleInverseImageRing B S hS incl).obj
      ((smallEtaleInverseImageRing B S hS g).obj (smallEtaleRingedTopos B S hS Y').O))
    (N' := (smallEtaleInverseImageRing B S hS incl).obj (smallEtaleRingedTopos B S hS X').O)
    _ _ _ _ _ _ _ _ _ _ _ _
    ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS ρ.hom incl).app
      ((smallEtaleInverseImageRing B S hS g).obj (smallEtaleRingedTopos B S hS Y').O))
    ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS ρ.hom (e₀ ≫ t)).inv.app
        (smallEtaleRingedTopos B S hS Y').O)
    ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS ρ.hom (incl ≫ g)).inv.app
        (smallEtaleRingedTopos B S hS Y').O) ?_ ?_ ?_ ?_ ?_
  · exact inverseImageCommRingRestrictionIso_naturality (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS X₀.1)
      (smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ))
      (smallEtaleRingedToposHom B S hS ρ.hom).toToposHom
      (smallToposMorphismTypeU_inverseImageIso B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)) _
  · exact smallEtaleRingedToposHom_compInverseImageRingIso_inv_assoc B S hS ρ.hom e₀ t
      (smallEtaleRingedTopos B S hS Y').O
  · exact smallEtaleRingedToposHom_compInverseImageRingIso_inv_assoc B S hS ρ.hom incl g
      (smallEtaleRingedTopos B S hS Y').O
  · exact (smallEtaleRingedToposHom_compInverseImageRingIso B S hS ρ.hom incl).hom.naturality
      (smallEtaleRingedToposHom B S hS g).fSharpInverseImage
  · exact compInverseImageRingIso_inv_app_eqToHom ρ.hom hsq.symm _

/-- The composite giving the map from the thickened base, read through the inverse images along
`f ≫ t = i ≫ g`, is unchanged, up to the `eqToHom`s `b` and `e`, by replacing `f` and `i` by
equal morphisms. -/
theorem baseMap_transport {f₁ f₂ : X ⟶ W} (hf : f₁ = f₂) {i₁ i₂ : X ⟶ X'} (hi : i₁ = i₂)
    (hw₁ : f₁ ≫ t = i₁ ≫ g) (hw₂ : f₂ ≫ t = i₂ ≫ g)
    (b : (smallEtaleInverseImageRing B S hS f₂).obj
        ((smallEtaleInverseImageRing B S hS t).obj (smallEtaleRingedTopos B S hS Y').O) =
      (smallEtaleInverseImageRing B S hS f₁).obj ((smallEtaleInverseImageRing B S hS t).obj
          (smallEtaleRingedTopos B S hS Y').O))
    (e : (smallEtaleInverseImageRing B S hS i₁).obj (smallEtaleRingedTopos B S hS X').O =
      (smallEtaleInverseImageRing B S hS i₂).obj (smallEtaleRingedTopos B S hS X').O) :
    eqToHom b ≫ ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS f₁ t).hom.app
        (smallEtaleRingedTopos B S hS Y').O ≫ eqToHom (inverseImage_congr hw₁
            (smallEtaleRingedTopos B S hS Y').O) ≫
        (smallEtaleRingedToposHom_compInverseImageRingIso B S hS i₁ g).inv.app
            (smallEtaleRingedTopos B S hS Y').O ≫
          (smallEtaleInverseImageRing B S hS i₁).map
            (smallEtaleRingedToposHom B S hS g).fSharpInverseImage) ≫ eqToHom e =
      (smallEtaleRingedToposHom_compInverseImageRingIso B S hS f₂ t).hom.app (smallEtaleRingedTopos
          B S hS Y').O ≫ eqToHom (inverseImage_congr hw₂ (smallEtaleRingedTopos B S hS Y').O) ≫
        (smallEtaleRingedToposHom_compInverseImageRingIso B S hS i₂ g).inv.app
            (smallEtaleRingedTopos B S hS Y').O ≫
          (smallEtaleInverseImageRing B S hS i₂).map
            (smallEtaleRingedToposHom B S hS g).fSharpInverseImage := by
  subst hf hi
  exact eqToHom_conj_self b e _

end BaseCoherence

section FibreSolution

variable {X₀ : AlgebraicSpaces B S hS} (ρ : X ≅ X₀)
  (g : X₀ ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
  (P : (problem g hZ).CompatibleFirstOrderThickening)

/-- The middle term of `fibreSolution` is the restriction along `ρ` of the original middle term. -/
theorem fibreSolution_extension :
    (fibreSolution hZ ρ g P).extension = (fibreRingRes ρ).obj P.extension :=
  rfl

/-- The reduction of `fibreSolution` is the restriction along `ρ` of the original reduction,
followed by `fibreStructureIso`. -/
theorem fibreSolution_reduction :
    (fibreSolution hZ ρ g P).reduction =
      (fibreRingRes ρ).map P.reduction ≫ (fibreStructureIso ρ).inv :=
  rfl

/-- The map from the thickened base of `fibreSolution` is `fibreRingIso` followed by the
restriction along `ρ` of the original map. -/
theorem fibreSolution_baseMap :
    (fibreSolution hZ ρ g P).baseMap =
      (fibreRingIso ρ g (baseExtension hZ).extension).hom ≫ (fibreRingRes ρ).map P.baseMap := by
  refine (rfl : _ = (fibreRingIso ρ g (baseExtension hZ).extension).hom ≫ 𝟙 _ ≫
    (fibreRingRes ρ).map (𝟙 _ ≫ P.baseMap)).trans ?_
  exact congrArg (_ ≫ ·) ((Category.id_comp _).trans (congrArg _ (Category.id_comp _)))

end FibreSolution

namespace Deformation

variable {f : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)} (D : Deformation f)

/-- The map from the thickened base to `i⁻¹𝒪_{X'}`: the inverse image along `i` of `f'^♯`,
read through `f⁻¹t⁻¹𝒪_{Y'} ≅ (f ≫ t)⁻¹𝒪_{Y'} = (i ≫ f')⁻¹𝒪_{Y'} ≅ i⁻¹f'⁻¹𝒪_{Y'}` (Stacks 03G8). -/
def ambientBaseMap :
    (inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj
        (baseExtension hZ).extension ⟶ inverseImageStructureSheaf B S hS D.i :=
  (smallEtaleRingedToposHom_compInverseImageRingIso B S hS f (subspaceInclusion B S hS Y'
      Z)).hom.app (smallEtaleRingedTopos B S hS Y').O ≫
    eqToHom (inverseImage_congr D.isPullback.w.symm (smallEtaleRingedTopos B S hS Y').O) ≫
    (smallEtaleRingedToposHom_compInverseImageRingIso B S hS D.i D.f').inv.app
        (smallEtaleRingedTopos B S hS Y').O ≫
    (smallEtaleInverseImageRing B S hS D.i).map (smallEtaleRingedToposHom B S hS
        D.f').fSharpInverseImage

/-- The identification of the middle term of `solutionOnSource` with `i⁻¹𝒪_{X'}`. -/
def ambientExtensionIso :
    (D.solutionOnSource hZ).extension ≅ inverseImageStructureSheaf B S hS D.i :=
  eqToIso (cast_extension hZ D.fibreIso_hom_reduction
      (fibreSolution hZ D.fibreIso D.reduction (D.solution hZ))) ≪≫
    (fibreRingIso D.fibreIso (subspaceInclusion B S hS D.X' D.subspace)
      (smallEtaleRingedTopos B S hS D.X').O).symm ≪≫
    eqToIso (congrArg (inverseImageStructureSheaf B S hS) D.fibreIso_hom_inclusion)

/-- The inverse of `ambientExtensionIso`, as a composite of its three pieces. -/
theorem ambientExtensionIso_inv :
    (D.ambientExtensionIso hZ).inv =
      (eqToHom (congrArg (inverseImageStructureSheaf B S hS) D.fibreIso_hom_inclusion.symm) ≫
        (fibreRingIso D.fibreIso (subspaceInclusion B S hS D.X' D.subspace)
          (smallEtaleRingedTopos B S hS D.X').O).hom) ≫
        eqToHom (cast_extension hZ D.fibreIso_hom_reduction
          (fibreSolution hZ D.fibreIso D.reduction (D.solution hZ))).symm :=
  rfl

/-- **The solution of a flat deformation on `i⁻¹𝒪_{X'}`.** -/
def ambientSolution : (problem f hZ).CompatibleFirstOrderThickening :=
  (D.solutionOnSource hZ).transportExtension (D.ambientExtensionIso hZ)

/-- The solution on `i⁻¹𝒪_{X'}` is isomorphic to `solutionOnSource`. -/
theorem isomorphic_ambientSolution :
    CompatibleFirstOrderThickening.Isomorphic.{u, u + 1, u, u, u + 1, u}
      (D.solutionOnSource hZ) (D.ambientSolution hZ) :=
  (D.solutionOnSource hZ).isomorphic_transportExtension _

/-- The middle term of `ambientSolution` is `i⁻¹𝒪_{X'}`. -/
theorem ambientSolution_extension :
    (D.ambientSolution hZ).extension = inverseImageStructureSheaf B S hS D.i :=
  rfl

/-- The reduction of the solution on the closed fibre is the structure map of the inclusion of
the closed fibre `X'_0 ⟶ X'`. -/
theorem solution_reduction :
    (D.solution hZ).reduction =
      structureSharpInverseImage B S hS (subspaceInclusion B S hS D.X' D.subspace) :=
  rfl

/-- The map from the thickened base of the solution on the closed fibre: the inverse of
`squareBaseIso` followed by the inverse-image structure map of `X'_0 ⟶ X'` over `f'`. -/
theorem solution_baseMap :
    (D.solution hZ).baseMap =
      (squareBaseIso hZ D.subspace D.f' D.reduction D.reduction_comm).inv ≫
        inverseImageStructureSheafMap B S hS (subspaceInclusion B S hS D.X' D.subspace) D.f' :=
  rfl

/-- The forward map of `ambientExtensionIso`, as a composite of its three pieces. -/
theorem ambientExtensionIso_hom :
    (D.ambientExtensionIso hZ).hom =
      eqToHom (cast_extension hZ D.fibreIso_hom_reduction
          (fibreSolution hZ D.fibreIso D.reduction (D.solution hZ))) ≫
        (fibreRingIso D.fibreIso (subspaceInclusion B S hS D.X' D.subspace)
          (smallEtaleRingedTopos B S hS D.X').O).inv ≫
        eqToHom (congrArg (inverseImageStructureSheaf B S hS) D.fibreIso_hom_inclusion) :=
  rfl

/-- The reduction of the solution on `i⁻¹𝒪_{X'}` is `i^♯`. -/
theorem ambientSolution_reduction :
    (D.ambientSolution hZ).reduction = structureSharpInverseImage B S hS D.i := by
  have h1 : (D.ambientSolution hZ).reduction =
      (D.ambientExtensionIso hZ).inv ≫ (D.solutionOnSource hZ).reduction := rfl
  have h2 := cast_reduction hZ D.fibreIso_hom_reduction
    (fibreSolution hZ D.fibreIso D.reduction (D.solution hZ))
  have h3 := fibreSolution_reduction hZ D.fibreIso D.reduction (D.solution hZ)
  rw [h1]
  refine (congrArg _ h2).trans ?_
  rw [ambientExtensionIso_inv]
  exact eqToHom_comp_chain _ _ _ _ _ _ _
    (h3 ▸ fibreRingIso_hom_comp_structureSharp D.fibreIso _)
    (structureSharpInverseImage_eqToHom B S hS D.fibreIso_hom_inclusion.symm)

/-- The map from the thickened base of the solution on `i⁻¹𝒪_{X'}` is `ambientBaseMap`. -/
theorem ambientSolution_baseMap : (D.ambientSolution hZ).baseMap = D.ambientBaseMap hZ := by
  have h1 : (D.ambientSolution hZ).baseMap =
      (D.solutionOnSource hZ).baseMap ≫ (D.ambientExtensionIso hZ).hom := rfl
  have h2 := cast_baseMap hZ D.fibreIso_hom_reduction
    (fibreSolution hZ D.fibreIso D.reduction (D.solution hZ))
  rw [h1, ambientExtensionIso_hom]
  refine (congrArg (· ≫ _) h2).trans ?_
  refine (eqToHom_assemble _ _ _ _ _ _ _ _
    (fibreSolution_baseMap hZ D.fibreIso D.reduction (D.solution hZ))
    (fibreRingIso_squareBaseIso_coherence (subspaceInclusion B S hS D.X' D.subspace) D.f'
      D.reduction (subspaceInclusion B S hS Y' Z) D.reduction_comm D.fibreIso)).trans ?_
  exact baseMap_transport D.f' (subspaceInclusion B S hS Y' Z) D.fibreIso_hom_reduction
    D.fibreIso_hom_inclusion
    (by rw [Category.assoc, Category.assoc, D.reduction_comm]) D.isPullback.w.symm _ _

end Deformation

end AlgebraicGeometry.Space.FlatThickeningDeformation

end
