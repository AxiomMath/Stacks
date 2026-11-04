module

public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Functoriality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Scheme
public import StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.Hom
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.PullbackSections

/-!
# The degree-one generator of the symmetric algebra is natural

For a morphism `g : ℰ₁ ⟶ ℰ₂` of modules on a scheme, the homomorphism
`Stacks.SymGraded.schemeSymAlgebraHom g : Sym(ℰ₁) ⟶ Sym(ℰ₂)` it induces is compatible with the
degree-one generators `ℰ ⟶ Sym(ℰ)₁`: in degree one,

  `ι_{ℰ₁} ≫ Sym(g)₁ = g ≫ ι_{ℰ₂}`.

## Main results

* `Stacks.Chow.GenuineChern.symmetricAlgebraGen_comp_schemeSymAlgebraHom`: the identity of
  morphisms.
* `Stacks.Chow.GenuineChern.schemeSymAlgebraHom_symmetricAlgebraGen_apply`: the same on the
  sections over an open.
* `Stacks.Chow.GenuineChern.sectionHom_of_symmetricAlgebraGen`: the same on the graded rings of
  sections.
* `Stacks.Chow.GenuineChern.homEquiv_pullbackId_comp_apply`: the adjoint of `g` along the
  identity of `X` is `g`, on sections.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Chow.GenuineChern

variable {X : Scheme.{u}} {E₁ E₂ : X.Modules} (g : E₁ ⟶ E₂)

/-- The generator of `Sym(ℰ)` is the sheafified sectionwise generator
`Stacks.SymGraded.siteGen`, precomposed with the identification of the sheafification of `ℰ`
with `ℰ`. -/
theorem symmetricAlgebraGen_eq (E : X.Modules) :
    Scheme.Modules.symmetricAlgebraGen X E =
      (Scheme.Modules.sheafificationIso X E).inv ≫
        (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
          (Stacks.SymGraded.siteGen E.val) :=
  rfl

/-- An isomorphism of modules undoes itself on sections. -/
theorem iso_inv_hom_val_app {A B : X.Modules} (e : A ≅ B) (U : (Opens X.carrier)ᵒᵖ)
    (y : A.val.obj U) : e.inv.val.app U (e.hom.val.app U y) = y :=
  congrArg (fun θ : A ⟶ A ↦ θ.val.app U y) e.hom_inv_id

/-- The identification of the sheafification of a sheaf with the sheaf is natural, on
sections. -/
theorem sheafificationIso_inv_naturality_apply (U : X.Opens) (x : Γ(E₁, U)) :
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map g.val).val.app (op U)
        ((Scheme.Modules.sheafificationIso X E₁).inv.val.app (op U) x) =
      (Scheme.Modules.sheafificationIso X E₂).inv.val.app (op U) (g.val.app (op U) x) :=
  congrArg (fun θ ↦ θ.val.app (op U) x)
    ((asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit).inv.naturality g).symm

/-- **The naturality of the generator on sections**: `Sym(g)₁(ι(x)) = ι(g(x))` for a section `x`
of `ℰ₁` over any open. -/
theorem schemeSymAlgebraHom_symmetricAlgebraGen_apply (U : X.Opens) (x : Γ(E₁, U)) :
    ((Stacks.SymGraded.schemeSymAlgebraHom g).app 1).val.app (op U)
        ((Scheme.Modules.symmetricAlgebraGen X E₁).val.app (op U) x) =
      (Scheme.Modules.symmetricAlgebraGen X E₂).val.app (op U) (g.val.app (op U) x) := by
  have hpre : Stacks.SymGraded.siteGen E₁.val ≫ Stacks.SymGraded.siteGradedPieceMap g.val 1 =
      g.val ≫ Stacks.SymGraded.siteGen E₂.val := by
    ext ⟨W⟩ m
    exact Subtype.ext (SymmetricAlgebra.mapₛₗ_ι (R := Γ(X, W)) (S := Γ(X, W)) (M := Γ(E₁, W))
      (N := Γ(E₂, W)) (RingHom.id _) (g.val.app (op W)).hom m)
  have hS : ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (Stacks.SymGraded.siteGen E₁.val) ≫
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (Stacks.SymGraded.siteGradedPieceMap g.val 1)) =
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map g.val ≫
        (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
          (Stacks.SymGraded.siteGen E₂.val) :=
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map_comp _ _).symm.trans
      ((congrArg (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map hpre).trans
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map_comp _ _))
  show ((Stacks.SymGraded.schemeSymAlgebraHom g).app 1).val.app (op U)
      (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (Stacks.SymGraded.siteGen E₁.val)).val.app (op U)
          ((Scheme.Modules.sheafificationIso X E₁).inv.val.app (op U) x)) =
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (Stacks.SymGraded.siteGen E₂.val)).val.app (op U)
      ((Scheme.Modules.sheafificationIso X E₂).inv.val.app (op U) (g.val.app (op U) x))
  rw [← sheafificationIso_inv_naturality_apply]
  exact congrArg (fun θ ↦ θ.val.app (op U)
    ((Scheme.Modules.sheafificationIso X E₁).inv.val.app (op U) x)) hS

/-- **The degree-one generator of the symmetric algebra is natural**: `ι_{ℰ₁} ≫ Sym(g)₁ =
g ≫ ι_{ℰ₂}`. -/
theorem symmetricAlgebraGen_comp_schemeSymAlgebraHom :
    Scheme.Modules.symmetricAlgebraGen X E₁ ≫ (Stacks.SymGraded.schemeSymAlgebraHom g).app 1 =
      g ≫ Scheme.Modules.symmetricAlgebraGen X E₂ := by
  ext U x
  exact schemeSymAlgebraHom_symmetricAlgebraGen_apply g U.unop x

/-- **The naturality of the generator on the graded rings of sections**: the graded ring
homomorphism `Γ(U, Sym ℰ₁) ⟶ Γ(U, Sym ℰ₂)` induced by `g` sends the degree-one element `ι(x)` to
`ι(g(x))`. -/
theorem sectionHom_of_symmetricAlgebraGen
    (hqc₁ : Stacks.SymGraded.IsQuasicoherentPieces E₁)
    (hqc₂ : Stacks.SymGraded.IsQuasicoherentPieces E₂) (U : X.Opens) (x : Γ(E₁, U)) :
    (Stacks.SymGraded.schemeSheafGradedAlgebraHom g hqc₁ hqc₂).sectionHom U
        (DirectSum.of ((Stacks.SymGraded.schemeSheafGradedAlgebra E₁ hqc₁).sectionPieces U) 1
          ((Scheme.Modules.symmetricAlgebraGen X E₁).val.app (op U) x)) =
      DirectSum.of ((Stacks.SymGraded.schemeSheafGradedAlgebra E₂ hqc₂).sectionPieces U) 1
        ((Scheme.Modules.symmetricAlgebraGen X E₂).val.app (op U) (g.val.app (op U) x)) :=
  (Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.sectionHom_of
    (Stacks.SymGraded.schemeSheafGradedAlgebraHom g hqc₁ hqc₂) U _).trans
    (congrArg (DirectSum.of _ 1) (schemeSymAlgebraHom_symmetricAlgebraGen_apply g U x))

/-- The morphism `ℰ₁ ⟶ ℰ₂` adjoint, along the identity of `X`, to `(𝟙 X)^*ℰ₁ ≅ ℰ₁ ⟶ ℰ₂` is `g`, on
sections. -/
theorem homEquiv_pullbackId_comp_apply (U : X.Opens) (x : Γ(E₁, U)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv E₁ E₂
        ((Scheme.Modules.pullbackId X).hom.app E₁ ≫ g)).val.app (op U) x =
      g.val.app (op U) x := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    AlgebraicGeometry.pullbackId_unit E₁]
  rfl

end Stacks.Chow.GenuineChern

end
