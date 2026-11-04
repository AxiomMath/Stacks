module

public import StacksFrontier.AlgebraicGeometry.QcohAlgebraFPColimit.SymQuotientIndex
public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraSheafUniversal

/-!
# Joint surjectivity of the system of quotients on sections over an affine open

The directed system of `Sym(ℱᵢ)/ℐ` of [Stacks, Tag 05JS] maps to `𝒜`, and this file proves the
first of the two sectionwise conditions the colimit criterion imposes on it: over an affine open
of `X`, every section of `𝒜` already comes from a member of the system. The member used is
`Sym(ℱᵢ)/0 = Sym(ℱᵢ)` for a stage `i` whose module hits the section.

## Main results

* `Stacks.SymQuotientSystem.quotIncl_comp_coconeApp`: the surjection `Sym(ℱᵢ) ⟶ Sym(ℱᵢ)/ℐ`
  followed by the cocone component is the extension `Sym(ℱᵢ) ⟶ 𝒜` of `φᵢ`, read through the
  comparison isomorphism `(𝐕(ℱᵢ) ⟶ X)_* 𝒪 ≅ Sym(ℱᵢ)`.
* `Stacks.SymQuotientSystem.exists_section_of_section`: **joint surjectivity on sections over an
  affine open**, from joint surjectivity of the system of modules on sections.

## Implementation notes

The section of `Sym(ℱᵢ)` realising a prescribed section of `𝒜` is the degree-one image of a
section of `ℱᵢ`, and that it maps to the prescribed section is
`Stacks.SymAlgSheaf.algebraLift_ungradedIncl_gen`. What this file adds is
the passage from `Sym(ℱᵢ)` to the member `Sym(ℱᵢ)/0` of the system: the surjection
`Sym(ℱᵢ) ⟶ Sym(ℱᵢ)/ℐ` is the direct image of the closed immersion `𝐙(ℐ) ⟶ 𝐕(ℱᵢ)`, and
`quotIncl_comp_coconeApp` identifies its composite with the cocone component.

All the identities are proved as equations between morphisms of algebra sheaves and only then
evaluated on a section, by `congrArg`; evaluating first and rewriting afterwards would put a
composite of pushed-forward structure sheaves under a `rewrite` motive, which makes the kernel
unfold the glueing that builds the relative spectrum.

**No `@[stacks]` attribute.** This is one of the two sectionwise conditions on the system of
[Stacks, Tag 05JS], not the assertion of the tag.

## References

* [Stacks Project, Tag 05JS](https://stacks.math.columbia.edu/tag/05JS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AffineAlgebraEquivalence Stacks.AlgebraicGeometry.FiniteTypeDominating
open Stacks.SymQuotientAlgebra

universe u

namespace Stacks.SymQuotientSystem

variable {X : Scheme.{u}}

/-- Sections of a composite of morphisms of algebra sheaves over an open: the composite of the
maps on sections. -/
theorem comp_right_app {A B C : X.QuasicoherentAlgebra} (f : A ⟶ B) (g : B ⟶ C) (U : X.Opens)
    (z : A.right.obj.obj (op U)) :
    ((f ≫ g).right.hom.app (op U)).hom z =
      (g.right.hom.app (op U)).hom ((f.right.hom.app (op U)).hom z) :=
  rfl

variable (𝒜 : X.QuasicoherentAlgebra) [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent 𝒜]
  {I : Type u} [PartialOrder I] {D : I ⥤ SheafOfModules.{u} X.ringCatSheaf}
  [∀ i, (D.obj i).IsQuasicoherent]
  (φ : D ⟶ (Functor.const I).obj
    (Scheme.QuasicoherentAlgebra.underlyingModule 𝒜 : SheafOfModules.{u} X.ringCatSheaf))

/-- **The surjection `Sym(ℱᵢ) ⟶ Sym(ℱᵢ)/ℐ` followed by the cocone component is the extension
`Sym(ℱᵢ) ⟶ 𝒜` of `φᵢ`**, read through the comparison isomorphism
`(𝐕(ℱᵢ) ⟶ X)_* 𝒪 ≅ Sym(ℱᵢ)`. -/
theorem quotIncl_comp_coconeApp (a : Index (proj 𝒜 φ)) :
    pushforwardAlgebraMap (quotIncl (D.obj a.idx) a.ideal) ≫
        coconeApp (proj 𝒜 φ) 𝒜 (relativeSpecOverIso 𝒜) a =
      (Scheme.Modules.vectorBundlePushforwardIso X (F := D.obj a.idx)).hom ≫
        symLift 𝒜 φ a.idx := by
  have := Scheme.Modules.isAffineHom_vectorBundleOver X (F := D.obj a.idx)
  have h : coconeApp (proj 𝒜 φ) 𝒜 (relativeSpecOverIso 𝒜) a =
      quotientAlgebraLift (D.obj a.idx) a.ideal (proj 𝒜 φ a.idx) a.le_ker ≫
        (relativeSpecOverIso 𝒜).hom := rfl
  rw [h, ← Category.assoc, quotIncl_comp_quotientAlgebraLift, pushforwardAlgebraMap_proj]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The same identity with the comparison isomorphism moved to the other side: the cocone
component, precomposed with the comparison and the surjection, is the extension of `φᵢ`. -/
theorem pushforwardIso_inv_comp_coconeApp (a : Index (proj 𝒜 φ)) :
    (Scheme.Modules.vectorBundlePushforwardIso X (F := D.obj a.idx)).inv ≫
        pushforwardAlgebraMap (quotIncl (D.obj a.idx) a.ideal) ≫
          coconeApp (proj 𝒜 φ) 𝒜 (relativeSpecOverIso 𝒜) a =
      symLift 𝒜 φ a.idx :=
  by rw [quotIncl_comp_coconeApp, Iso.inv_hom_id_assoc]

/-- **Joint surjectivity of the system on sections over an affine open.** If the system of
modules is jointly surjective on sections over `U`, then so is the system of quotients: the
section of `𝒜` is hit by the member `Sym(ℱᵢ)/0` at a stage `i` whose module hits it. -/
theorem exists_section_of_section (U : X.Opens)
    (x : 𝒜.right.obj.obj (op U)) (i : I)
    (t : (D.obj i).val.obj (op U))
    (ht : ((symLift 𝒜 φ i).right.hom.app (op U)).hom
      ((Scheme.Modules.symmetricAlgebra X (D.obj i)).ungradedIncl 1
        ((Scheme.Modules.symmetricAlgebraGen X (D.obj i)).val.app (op U) t)) = x) :
    ∃ (a : Index (proj 𝒜 φ)) (y : ((system (proj 𝒜 φ)).obj a).right.obj.obj (op U)),
      ((cocone (proj 𝒜 φ) 𝒜 (relativeSpecOverIso 𝒜)
        (fun _ _ h => proj_comp 𝒜 φ h)).app a).right.hom.app (op U) y = x := by
  refine ⟨⟨i, ⊥, Stacks.FiniteTypeIdealSheaf.isFiniteType_bot, bot_le⟩, ?_, ?_⟩
  · exact ((pushforwardAlgebraMap (quotIncl (D.obj i) ⊥)).right.hom.app (op U)).hom
      (((Scheme.Modules.vectorBundlePushforwardIso X (F := D.obj i)).inv.right.hom.app
        (op U)).hom ((Scheme.Modules.symmetricAlgebra X (D.obj i)).ungradedIncl 1
          ((Scheme.Modules.symmetricAlgebraGen X (D.obj i)).val.app (op U) t)))
  · refine Eq.trans ?_ ht
    exact congrArg
      (fun k : (Scheme.Modules.symmetricAlgebraSheaf X (D.obj i) : X.QuasicoherentAlgebra) ⟶ 𝒜 =>
        (k.right.hom.app (op U)).hom
          ((Scheme.Modules.symmetricAlgebra X (D.obj i)).ungradedIncl 1
            ((Scheme.Modules.symmetricAlgebraGen X (D.obj i)).val.app (op U) t)))
      (pushforwardIso_inv_comp_coconeApp 𝒜 φ
        ⟨i, ⊥, Stacks.FiniteTypeIdealSheaf.isFiniteType_bot, bot_le⟩)

end Stacks.SymQuotientSystem

end
