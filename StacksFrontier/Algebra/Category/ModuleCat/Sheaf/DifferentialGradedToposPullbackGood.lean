module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposDirectImageComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposPullbackUniversal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposTriangle
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposComp

/-!
# The pullback of a good differential graded module is good

Let `f : (Sh(C'), O') ⟶ (Sh(C), O)` be a morphism of ringed topoi, `A` a sheaf of differential
graded `O`-algebras, `B` a sheaf of differential graded `O'`-algebras and `ψ : A ⟶ f_*B` a unital
homomorphism. **Every pullback of a good right differential graded `A`-module along `(f, B, ψ)` is
a good right differential graded `B`-module**, which is the goodness half of part (2) of
[Stacks, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI).

## Main definitions

* `Stacks.Sheaves.RingedToposModules.RingedToposHom.comp`: the composite of two morphisms of
  ringed topoi, with its structure map in inverse-image form
  `(ψ ∘ φ)⁻¹O_Z = φ⁻¹ψ⁻¹O_Z ⟶ φ⁻¹O_Y ⟶ O_X`.
* `CategoryTheory.Functor.CorepresentableBy.ofComp` and `ofCompSymm`: if `T` corepresents
  `Hom(P, G₂ -)` and `H ≅ G₁ ⋙ G₂`, then the objects corepresenting `Hom(T, G₁ -)` are those
  corepresenting `Hom(P, H -)`.

## Main results

* `Stacks.Sheaves.RingedToposModules.RingedToposHom.fSharpSetComp_comp`: the structure map of the
  composite is the composite structure map on underlying sheaves of sets.
* `SheafOfModules.isGoodToposBaseChange_of_toposCorepresentableBy`: every pullback of a good module
  along a base change is good.
* `SheafOfModules.isGoodToposBaseChange_toposPullbackModule`: `f^*P` is good when `P` is.

## References

* [Stacks Project, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe w v₁ u₁ v₂ u₂ v₃ u₃

namespace Stacks.Sheaves.RingedToposModules.RingedToposHom

variable {X : AlgebraicGeometry.RingedTopos.{v₁, u₁, w}}
  {Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, w}} {Z : AlgebraicGeometry.RingedTopos.{v₃, u₃, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [Z.J.HasSheafCompose (forget RingCat.{w})]

/-- **The composite of two morphisms of ringed topoi**, `(ψ ∘ φ, (ψ ∘ φ)♯)`: the underlying
morphisms of topoi compose, and the structure map in inverse-image form is
`(ψ ∘ φ)⁻¹O_Z = φ⁻¹ψ⁻¹O_Z ⟶ φ⁻¹O_Y ⟶ O_X`. -/
def comp (ψ : RingedToposHom Y Z) (φ : RingedToposHom X Y) : RingedToposHom X Z :=
  ofFSharpInverseImage (ψ.toToposHom.comp φ.toToposHom)
    ((pullbackRingSheafCompIso X.J Y.J φ.toToposHom.inverseImage ψ.toToposHom.inverseImage
        (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).inv ≫
      pullbackRingSheafMap X.J φ.toToposHom.inverseImage ψ.fSharpInverseImage ≫
        φ.fSharpInverseImage)

variable [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Z.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]

omit [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Z.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})] in
/-- The structure map of the composite is the composite structure map, on underlying sheaves of
sets: `ψ♯` followed by `ψ_*φ♯`. -/
theorem fSharpSetComp_comp (ψ : RingedToposHom Y Z) (φ : RingedToposHom X Y) :
    fSharpSetComp φ ψ ≫ (Iso.refl (φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward)).hom.app
        (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = fSharpSet (comp ψ φ) := by
  let u : ψ.toToposHom.inverseImage.obj
        (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ⟶
      Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) :=
    (sheafCompose Y.J (CategoryTheory.forget RingCat.{w})).map ψ.fSharpInverseImage
  let v : φ.toToposHom.inverseImage.obj
        (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⟶
      Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
    (sheafCompose X.J (CategoryTheory.forget RingCat.{w})).map φ.fSharpInverseImage
  have key : (sheafCompose X.J (CategoryTheory.forget RingCat.{w})).map
      (comp ψ φ).fSharpInverseImage = φ.toToposHom.inverseImage.map u ≫ v :=
    Sheaf.hom_ext_sections fun _ _ ↦ rfl
  have h₁ : fSharpSet (comp ψ φ) = (ψ.toToposHom.adj.comp φ.toToposHom.adj).homEquiv _ _
      (φ.toToposHom.inverseImage.map u ≫ v) :=
    (comp ψ φ).fSharp_adjunct.trans (congrArg _ key)
  have h₂ : fSharpSet ψ = ψ.toToposHom.adj.homEquiv _ _ u := ψ.fSharp_adjunct
  have h₃ : fSharpSet φ = φ.toToposHom.adj.homEquiv _ _ v := φ.fSharp_adjunct
  rw [Iso.refl_hom, NatTrans.id_app, Category.comp_id, fSharpSetComp_eq, h₁, h₂, h₃,
    Adjunction.comp_homEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]

end Stacks.Sheaves.RingedToposModules.RingedToposHom

namespace CategoryTheory.Functor.CorepresentableBy

universe c₁ d₁ c₂ d₂ c₃ d₃

variable {C₁ : Type c₁} [Category.{d₁} C₁] {C₂ : Type c₂} [Category.{d₂} C₂]
  {C₃ : Type c₃} [Category.{d₃} C₃] {G₁ : C₁ ⥤ C₂} {G₂ : C₂ ⥤ C₃} {H : C₁ ⥤ C₃}
  {P : C₃} {T : C₂}

/-- **A pullback of a pullback is a pullback along the composite.** If `T` corepresents
`Y ↦ Hom(P, G₂ Y)` and `H ≅ G₁ ⋙ G₂`, then an object corepresenting `Y ↦ Hom(T, G₁ Y)`
corepresents `Y ↦ Hom(P, H Y)`. -/
def ofComp (eT : (G₂ ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T)
    (α : H ≅ G₁ ⋙ G₂) {T' : C₁} (e : (G₁ ⋙ coyoneda.obj (Opposite.op T)).CorepresentableBy T') :
    (H ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T' where
  homEquiv {Y} := e.homEquiv.trans (eT.homEquiv.trans
    { toFun := fun x ↦ x ≫ α.inv.app Y
      invFun := fun x ↦ x ≫ α.hom.app Y
      left_inv := fun x ↦ by simp
      right_inv := fun x ↦ by simp })
  homEquiv_comp {Y Y'} l k := by
    change eT.homEquiv (e.homEquiv (k ≫ l)) ≫ α.inv.app Y' =
      (eT.homEquiv (e.homEquiv k) ≫ α.inv.app Y) ≫ H.map l
    have h₁ : e.homEquiv (k ≫ l) = e.homEquiv k ≫ G₁.map l := e.homEquiv_comp l k
    have h₂ : eT.homEquiv (e.homEquiv k ≫ G₁.map l) =
        eT.homEquiv (e.homEquiv k) ≫ G₂.map (G₁.map l) := eT.homEquiv_comp _ _
    rw [h₁, h₂, Category.assoc, Category.assoc, ← α.inv.naturality l, Functor.comp_map]

/-- **A pullback along the composite is a pullback of a pullback.** If `T` corepresents
`Y ↦ Hom(P, G₂ Y)` and `H ≅ G₁ ⋙ G₂`, then an object corepresenting `Y ↦ Hom(P, H Y)`
corepresents `Y ↦ Hom(T, G₁ Y)`. -/
def ofCompSymm (eT : (G₂ ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T)
    (α : H ≅ G₁ ⋙ G₂) {T' : C₁} (e : (H ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T') :
    (G₁ ⋙ coyoneda.obj (Opposite.op T)).CorepresentableBy T' where
  homEquiv {Y} := e.homEquiv.trans
    ((show (P ⟶ H.obj Y) ≃ (P ⟶ G₂.obj (G₁.obj Y)) from
      { toFun := fun x ↦ x ≫ α.hom.app Y
        invFun := fun x ↦ x ≫ α.inv.app Y
        left_inv := fun x ↦ by simp
        right_inv := fun x ↦ by simp }).trans eT.homEquiv.symm)
  homEquiv_comp {Y Y'} l k := by
    change eT.homEquiv.symm (e.homEquiv (k ≫ l) ≫ α.hom.app Y') =
      eT.homEquiv.symm (e.homEquiv k ≫ α.hom.app Y) ≫ G₁.map l
    have h₁ : e.homEquiv (k ≫ l) = e.homEquiv k ≫ H.map l := e.homEquiv_comp l k
    have h₂ : eT.homEquiv.symm (e.homEquiv k ≫ α.hom.app Y) ≫ G₁.map l =
        eT.homEquiv.symm ((e.homEquiv k ≫ α.hom.app Y) ≫ G₂.map (G₁.map l)) :=
      eT.homEquiv_symm_comp _ _
    rw [h₁, h₂, Category.assoc, Category.assoc, α.hom.naturality l, Functor.comp_map]

end CategoryTheory.Functor.CorepresentableBy

namespace SheafOfModules

open DifferentialGradedModule

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable {Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, w}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [HasSheafify Y.J (Type w)]
  {X : AlgebraicGeometry.RingedTopos.{v₁, u₁, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify X.J AddCommGrpCat.{w}]
  [HasSheafify X.J (Type w)]
  (f : RingedToposHom X Y)
  {A : DifferentialGradedAlgebra.{w, w} (toRingCat Y.J Y.O)}
  {B : DifferentialGradedAlgebra.{w, w} (toRingCat X.J X.O)}
  (ψ : A ⟶ toposPushforwardAlgebra (toposDirectImageModules f) B) (hψ : ψ.IsUnital)

omit [HasSheafify Y.J (Type w)] in
/-- **The pullback of a good module is good, across universes.** Every pullback `T` of a right
differential graded module `P` along a base change `(f, B, ψ)` is good at the base changes of
universe level `(v₃, u₃)`, as soon as `P` is good at those of level `(v₁, u₁)` (the level of `f`)
and at those of level `(v₃, u₃)`. -/
theorem isGoodToposBaseChange_of_toposCorepresentableBy_of_univ
    {P : DifferentialGradedModule.{w, w, w} A} (hP₁ : IsGoodToposBaseChange.{w, v₁, u₁} P)
    (hP₃ : IsGoodToposBaseChange.{w, v₃, u₃} P) {T : DifferentialGradedModule.{w, w, w} B}
    (eT : (toposPushforward (toposDirectImageModules f) ψ hψ ⋙
      coyoneda.obj (Opposite.op P)).CorepresentableBy T) :
    IsGoodToposBaseChange.{w, v₃, u₃} T := by
  obtain ⟨h₁, h₂⟩ := (hP₁.baseChange f B ψ hψ).2 T eT
  refine ⟨h₁, h₂, ?_⟩
  intro X' _ _ _ _ _ _ g B' ψ' hψ'
  let τ := Iso.refl (g.toToposHom.pushforward ⋙ f.toToposHom.pushforward)
  have hτ := RingedToposHom.fSharpSetComp_comp f g
  let α := toposPushforwardCompIsoOfComparison g f (RingedToposHom.comp f g) τ hτ B' hψ' hψ
  obtain ⟨⟨T', ⟨e'⟩⟩, hT'⟩ := hP₃.baseChange (RingedToposHom.comp f g) B'
    (toposPushforwardCompAlgebraHom g f (RingedToposHom.comp f g) τ hτ B' ψ' ψ)
    (isUnital_toposPushforwardCompAlgebraHom g f (RingedToposHom.comp f g) τ hτ B' ψ' ψ hψ' hψ)
  exact ⟨⟨T', ⟨Functor.CorepresentableBy.ofCompSymm eT α e'⟩⟩,
    fun T'' e'' => hT' T'' (Functor.CorepresentableBy.ofComp eT α e'')⟩

omit [HasSheafify Y.J (Type w)] in
/-- **The goodness half of Tag 0FSI (2).** Let `f : (Sh(C'), O') ⟶ (Sh(C), O)` be a morphism of
ringed topoi, `B` a sheaf of differential graded `O'`-algebras and `ψ : A ⟶ f_*B` a unital
homomorphism. Every pullback `T` of a good right differential graded `A`-module `P` along
`(f, B, ψ)` — every object corepresenting `Q ↦ Hom_A(P, f_{*,ψ}Q)` — is a good right
differential graded `B`-module. -/
theorem isGoodToposBaseChange_of_toposCorepresentableBy
    {P : DifferentialGradedModule.{w, w, w} A} (hP : IsGoodToposBaseChange.{w, v₁, u₁} P)
    {T : DifferentialGradedModule.{w, w, w} B}
    (eT : (toposPushforward (toposDirectImageModules f) ψ hψ ⋙
      coyoneda.obj (Opposite.op P)).CorepresentableBy T) :
    IsGoodToposBaseChange.{w, v₁, u₁} T :=
  isGoodToposBaseChange_of_toposCorepresentableBy_of_univ f ψ hψ hP hP eT

omit [HasSheafify Y.J (Type w)] in
/-- **The pullback `f^*P` of a good right differential graded module is good**, as a right
differential graded `f^*A`-module. -/
theorem isGoodToposBaseChange_toposPullbackModule
    {P : DifferentialGradedModule.{w, w, w} A} (hP : IsGoodToposBaseChange.{w, v₁, u₁} P) :
    IsGoodToposBaseChange.{w, v₁, u₁} (toposPullbackModule f P) :=
  isGoodToposBaseChange_of_toposCorepresentableBy f _ (isUnital_toposPullbackUnit f A) hP
    (toposPullbackCorepresentableBy f P)

end SheafOfModules
