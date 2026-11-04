module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexPullAction
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDuality
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectOpenLocality

/-!
# Restricting a relative dualizing complex along an open immersion

Let `f : X ⟶ S` be flat and locally of finite presentation, `W` a diagonal open of `f` and
`(K, ξ)` a relative dualizing complex for `f` relative to `W` (Stacks 0E2T). Let `j : Y ⟶ X` be
an open immersion and `W_Y ⊆ Y ×_S Y` the restricted diagonal open, with `j_W : W_Y ⟶ W`. Then
`Lj^*K` together with the restriction of `ξ`,

`Δ_{Y*}𝒪_Y ≅ Lj_W^*(Δ_*𝒪_X) ⟶ Lj_W^*(L pr₁^*K|_W) ≅ L pr₁^*(Lj^*K)|_{W_Y}`,

is a relative dualizing complex for `j ≫ f`. This is the remark "trivially the restriction of a
relative dualizing complex to an open is a relative dualizing complex" in the proof of
Stacks 0E2X.

The first condition is the locality of relative perfectness. The second follows from the
compatibility of `R𝓗om` with restriction to opens (Stacks 08DL) once the identification
`Lj_W^*(Δ_*𝒪_X) ≅ Δ_{Y*}𝒪_Y` is compatible with the derived multiplications, which is the input
`hmul` of this file.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.restrictProjIso`:
  `Lj_W^*(L pr₁^*K|_W) ≅ L pr₁^*(Lj^*K)|_{W_Y}`.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.restrictXiOf`: the restriction of `ξ` along an
  identification of the two diagonal objects.

## Main results

* `AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex.restrict_of`: the restriction is a
  relative dualizing complex.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.restrictXiOf_comp`: restriction of `ξ` is natural
  in `K`.

## References

* [Stacks Project, Definition 48.28.1 (Tag 0E2T)](https://stacks.math.columbia.edu/tag/0E2T)
* [Stacks Project, Lemma 48.28.6 (Tag 0E2X)](https://stacks.math.columbia.edu/tag/0E2X)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite StrictlyPerfect
open Stacks.Duality.TwistedInverseImageDuality
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] DiagonalOpen.isOpenImmersion

namespace DiagonalOpen

variable {X S : Scheme.{u}} {f : X ⟶ S} (D : DiagonalOpen f) {Y : Scheme.{u}} (j : Y ⟶ X)
  [IsOpenImmersion j]

/-- `W_Y ⟶ W` is an open immersion, read with source the diagonal open of `j ≫ f`. -/
instance isOpenImmersion_restrictInclusion' :
    @IsOpenImmersion (D.restrict j).W D.W (D.restrictInclusion j) :=
  D.isOpenImmersion_restrictInclusion j

/-- **`Lg^*(L pr₁^*K|_W) ≅ L pr₁'^*(Lj^*K)|_{W'}`** for an open immersion `g : W' ⟶ W` of
diagonal opens lying over `j : X' ⟶ X`, i.e. with `g ≫ pr₁|_W = pr₁|_{W'} ≫ j`. -/
def projPullIso {X' S' : Scheme.{u}} {f' : X' ⟶ S'} (D' : DiagonalOpen f') (j' : X' ⟶ X)
    (g : D'.W ⟶ D.W) (hproj : g ≫ D.proj = D'.proj ≫ j') (K : Std X) :
    (pull g).obj ((pull D.proj).obj K) ≅ (pull D'.proj).obj ((pull j').obj K) :=
  (Stacks.Duality.UpperShriekDuality.pullCompIso g D.proj _ hproj).app K ≪≫
    ((Stacks.Duality.UpperShriekDuality.pullCompIso D'.proj j' _ rfl).app K).symm

/-- **`Lj_W^*(L pr₁^*K|_W) ≅ L pr₁^*(Lj^*K)|_{W_Y}`**, from the composition formula for derived
pullback and the equality `j_W ≫ pr₁|_W = pr₁|_{W_Y} ≫ j`. -/
def restrictProjIso (K : Std X) :
    (pull (D.restrictInclusion j)).obj ((pull D.proj).obj K) ≅
      (pull (D.restrict j).proj).obj ((pull j).obj K) :=
  (Stacks.Duality.UpperShriekDuality.pullCompIso (D.restrictInclusion j) D.proj _
      (D.restrictInclusion_proj j)).app K ≪≫
    ((Stacks.Duality.UpperShriekDuality.pullCompIso (D.restrict j).proj j _ rfl).app K).symm

/-- **The restriction of `ξ`** along an identification `eΔ` of `Lj_W^*(Δ_*𝒪_X)` with
`Δ_{Y*}𝒪_Y`. -/
def restrictXiOf (eΔ : (pull (D.restrictInclusion j)).obj D.diagonalObject ≅
      (D.restrict j).diagonalObject)
    (K : Std X) (ξ : (D.diagonalObject : Std D.W) ⟶ (pull D.proj).obj K) :
    ((D.restrict j).diagonalObject : Std (D.restrict j).W) ⟶
      (pull (D.restrict j).proj).obj ((pull j).obj K) :=
  eΔ.inv ≫ (pull (D.restrictInclusion j)).map ξ ≫ (D.restrictProjIso j K).hom

end DiagonalOpen

variable {X S : Scheme.{u}} {f : X ⟶ S} [Flat f] [LocallyOfFinitePresentation f]
  {D : DiagonalOpen f} {K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
  {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K}

/-- **Transport of a relative dualizing complex along an open immersion of diagonal opens.**
Let `j : X' ⟶ X` be an open immersion with `j ≫ f = f'`, and `g : W' ⟶ W` an open immersion
from a diagonal open of `f'` with `g ≫ pr₁|_W = pr₁|_{W'} ≫ j`. Given an identification
`eΔ : Lg^*(Δ_*𝒪_X) ≅ Δ'_*𝒪_{X'}` compatible with the derived multiplications, `Lj^*K` together
with `eΔ⁻¹ ≫ Lg^*ξ ≫ eP` is a relative dualizing complex for `f'` relative to `W'`. -/
theorem IsRelativeDualizingComplex.transport_of
    (hK : IsRelativeDualizingComplex f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) D K ξ)
    {X' : Scheme.{u}} {f' : X' ⟶ S} [Flat f'] [LocallyOfFinitePresentation f']
    (D' : DiagonalOpen f') (j : X' ⟶ X) [IsOpenImmersion j] (hf : j ≫ f = f')
    (g : D'.W ⟶ D.W) [IsOpenImmersion g] (hproj : g ≫ D.proj = D'.proj ≫ j)
    (eΔ : (pull g).obj D.diagonalObject ≅ D'.diagonalObject)
    (hmul : D'.diagonalMul ≫ eΔ.inv =
      ((tensor D'.W).map eΔ.inv).app D'.diagonalObject ≫
        ((tensor D'.W).obj ((pull g).obj D.diagonalObject)).map eΔ.inv ≫
          (pullTensorIso g D.diagonalObject D.diagonalObject).inv ≫ (pull g).map D.diagonalMul) :
    IsRelativeDualizingComplex f'
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f'.base)) D'
      ((derivedPullback j.toLRSHom.toShHom).obj K)
      (eΔ.inv ≫ (pull g).map ξ ≫ (D.projPullIso D' j g hproj K).hom) := by
  subst hf
  constructor
  · have h₀ := hK.isPerfectRelativeTo
    have h₁ := isPerfectRelativeTo_comp_openImmersion f j K h₀
    exact h₁
  · have h₂ := DiagonalOpen.isIso_diagonalAction_transport D K D'
      ((derivedPullback j.toLRSHom.toShHom).obj K) g ξ eΔ (D.projPullIso D' j g hproj K) hmul
      hK.isIso_diagonalAction
    exact h₂

/-- **The restriction of a relative dualizing complex along an open immersion is a relative
dualizing complex**, given an identification `eΔ` of `Lj_W^*(Δ_*𝒪_X)` with `Δ_{Y*}𝒪_Y`
compatible with the derived multiplications. Relative perfectness is read at the canonical
families of certificates. -/
theorem IsRelativeDualizingComplex.restrict_of
    (hK : IsRelativeDualizingComplex f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) D K ξ)
    {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (eΔ : (pull (D.restrictInclusion j)).obj D.diagonalObject ≅ (D.restrict j).diagonalObject)
    (hmul : (D.restrict j).diagonalMul ≫ eΔ.inv =
      ((tensor (D.restrict j).W).map eΔ.inv).app (D.restrict j).diagonalObject ≫
        ((tensor (D.restrict j).W).obj
          ((pull (D.restrictInclusion j)).obj D.diagonalObject)).map eΔ.inv ≫
          (pullTensorIso (D.restrictInclusion j) D.diagonalObject D.diagonalObject).inv ≫
            (pull (D.restrictInclusion j)).map D.diagonalMul) :
    IsRelativeDualizingComplex (j ≫ f)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace (j ≫ f).base)) (D.restrict j)
      ((derivedPullback j.toLRSHom.toShHom).obj K) (D.restrictXiOf j eΔ K ξ) :=
  transport_of hK (D.restrict j) j rfl (D.restrictInclusion j) (D.restrictInclusion_proj j) eΔ hmul

namespace DiagonalOpen

variable (D) {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
  (eΔ : (pull (D.restrictInclusion j)).obj D.diagonalObject ≅ (D.restrict j).diagonalObject)

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- `Lj_W^*(L pr₁^*K|_W) ≅ L pr₁^*(Lj^*K)|_{W_Y}` is natural in `K`. -/
theorem restrictProjIso_hom_naturality {K L : Std X} (φ : K ⟶ L) :
    (pull (D.restrictInclusion j)).map ((pull D.proj).map φ) ≫ (D.restrictProjIso j L).hom =
      (D.restrictProjIso j K).hom ≫ (pull (D.restrict j).proj).map ((pull j).map φ) := by
  have h₁ := (Stacks.Duality.UpperShriekDuality.pullCompIso (D.restrictInclusion j) D.proj _
    (D.restrictInclusion_proj j)).hom.naturality φ
  have h₂ := (Stacks.Duality.UpperShriekDuality.pullCompIso (D.restrict j).proj j _
    rfl).inv.naturality φ
  dsimp only [Functor.comp_map] at h₁ h₂
  simp only [restrictProjIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  rw [reassoc_of% h₁, h₂]
  exact (Category.assoc _ _ _).symm

omit [IsOpenImmersion j] in
private theorem assoc₄ {C : Type*} [Category C] {A B P Q R : C} (a : A ⟶ B) (b : B ⟶ P)
    (c : P ⟶ Q) (d : Q ⟶ R) : a ≫ b ≫ c ≫ d = (a ≫ b ≫ c) ≫ d := by
  simp

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- **Restriction of `ξ` is natural in `K`**: restricting `ξ` followed by `L pr₁^*φ` is
restricting `ξ` and then applying `L pr₁^*(Lj^*φ)`. -/
theorem restrictXiOf_comp {K L : Std X}
    (ξ : (D.diagonalObject : Std D.W) ⟶ (pull D.proj).obj K) (φ : K ⟶ L) :
    D.restrictXiOf j eΔ L (ξ ≫ (pull D.proj).map φ) =
      D.restrictXiOf j eΔ K ξ ≫ (pull (D.restrict j).proj).map ((pull j).map φ) := by
  have hn := restrictProjIso_hom_naturality D j φ
  unfold restrictXiOf
  calc eΔ.inv ≫ (pull (D.restrictInclusion j)).map (ξ ≫ (pull D.proj).map φ) ≫
          (D.restrictProjIso j L).hom
      = eΔ.inv ≫ ((pull (D.restrictInclusion j)).map ξ ≫
          (pull (D.restrictInclusion j)).map ((pull D.proj).map φ)) ≫
            (D.restrictProjIso j L).hom := by
        congr 2
        exact Functor.map_comp _ _ _
    _ = _ := by
        simp only [Category.assoc]
        rw [hn]
        exact assoc₄ _ _ _ _

end DiagonalOpen

end AlgebraicGeometry.Scheme.Hom

end
