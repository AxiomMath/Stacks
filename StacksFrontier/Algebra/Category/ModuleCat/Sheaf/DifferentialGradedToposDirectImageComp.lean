module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeDifferentialGradedModuleToposPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardCompMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPushPullHomogeneous
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposBaseChangeExtension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback

/-!
# Direct images of differential graded modules along a composite

Let `φ : X ⟶ Y`, `ψ : Y ⟶ Z` and `χ : X ⟶ Z` be morphisms of ringed topoi, `χ` playing the role
of the composite through a comparison `τ` of the geometric direct images compatible with the
structure maps, let `A`, `B`, `C` be sheaves of differential graded algebras on `X`, `Y`, `Z`, and
let `φa : B ⟶ φ_*A` and `ψa : C ⟶ ψ_*B` be unital homomorphisms. This file builds the composite
structure homomorphism

`χa : C --ψa--> ψ_*B --ψ_*φa--> ψ_*φ_*A ≅ χ_*A`

(`toposPushforwardCompAlgebraHom`), proves it unital, and proves that the direct image of right
differential graded modules along `χ`, restricting scalars along `χa`, is the composite of the
direct images along `φ` and `ψ` (`toposPushforwardCompIsoOfComparison`), degreewise the
comparison of direct images of sheaves of modules. For the literal composite `g ∘ f` of two
morphisms of ringed topoi in the sense of Stacks 01D3, where the comparison of geometric direct
images is the identity, these are `toposCompAlgebraHom` and `toposPushforwardRingedCompIso`.

## Main definitions

* `toposPushforwardAlgebraCompHom`, `toposPushforwardAlgebraCompIso`: the comparison
  `ψ_*φ_*A ≅ χ_*A` of sheaves of differential graded algebras.
* `toposPushforwardCompAlgebraHom`: the composite structure homomorphism `χa`.
* `toposPushforwardCompIsoOfComparison`: `χ_{*,χa} ≅ φ_{*,φa} ⋙ ψ_{*,ψa}`.
* `toposCompAlgebraHom`, `toposPushforwardRingedCompIso`: the same for the literal composite
  `g ∘ f`.

## Main results

* `isUnital_toposPushforwardCompAlgebraHom` and `isUnital_toposCompAlgebraHom`: the composite
  structure homomorphism is unital.
* `toposPushforwardCompAlgebraHom_f`, `toposCompAlgebraHom_f`: the composite structure
  homomorphism in degree `n`.
* `toposPushforwardCompIsoOfComparison_inv_app_f`, `toposPushforwardCompIsoOfComparison_hom_app_f`
  and their counterparts for `toposPushforwardRingedCompIso`: the isomorphism of direct images in
  degree `n` is the comparison of direct images of the degree-`n` piece.

## Implementation notes

The direct image of sheaves of modules carries its lax monoidal structure
`SheafOfModules.toposDirectImageModules_laxMonoidal` at the `CategoryTheory.Sheaf.toRingCat`
spelling, while the monoidality of the comparison is proved at the
`Stacks.SheafOfModules.Tensor.ringSheaf` spelling. The two lax structures are the same term, but
unifying their tensorators directly exceeds the recursion limit; the monoidality transfers instead
as the `Prop`-valued `CategoryTheory.NatTrans.IsMonoidal`
(`isMonoidal_toposDirectImageCompIso_hom`), from which the two equations at the `toRingCat`
spelling are its fields.

## References

* [Stacks Project, Tag 0FRG](https://stacks.math.columbia.edu/tag/0FRG)
* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CategoryTheory.Sheaf
open AlgebraicGeometry Stacks.Sheaves.RingedToposModules

universe w v₁ u₁ v₂ u₂ v₃ u₃

namespace SheafOfModules.DifferentialGradedModule

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

section AlgebraIso

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- A homomorphism of sheaves of differential graded algebras which is an isomorphism in every
degree is an isomorphism of sheaves of differential graded algebras. -/
def algebraIsoOfDegreewiseIso {A B : DifferentialGradedAlgebra.{w, w} R} (h : A ⟶ B)
    (hiso : ∀ p : ℤ, IsIso (h.toHomologicalComplex.f p)) : A ≅ B where
  hom := h
  inv :=
    { toHomologicalComplex :=
        { f := fun p ↦ inv (h.toHomologicalComplex.f p)
          comm' := fun p q hpq ↦ by
            rw [IsIso.inv_comp_eq, ← Category.assoc, h.toHomologicalComplex.comm' p q hpq,
              Category.assoc, IsIso.hom_inv_id, Category.comp_id] }
      map_mul := fun p q U x y ↦ by
        change homSections (inv (h.toHomologicalComplex.f (p + q))) U ((B.mul p q).app U x y) =
          (A.mul p q).app U (homSections (inv (h.toHomologicalComplex.f p)) U x)
            (homSections (inv (h.toHomologicalComplex.f q)) U y)
        have hinv : ∀ (r : ℤ) (z : (B.complex.X r).val.obj U),
            homSections (h.toHomologicalComplex.f r) U
              (homSections (inv (h.toHomologicalComplex.f r)) U z) = z := fun r z ↦ by
          rw [← homSections_comp, homSections_congr (IsIso.inv_hom_id _) U z, homSections_id]
        have hcancel : ∀ (r : ℤ) (z : (A.complex.X r).val.obj U),
            homSections (inv (h.toHomologicalComplex.f r)) U
              (homSections (h.toHomologicalComplex.f r) U z) = z := fun r z ↦ by
          rw [← homSections_comp, homSections_congr (IsIso.hom_inv_id _) U z, homSections_id]
        have key := h.map_mul p q U (homSections (inv (h.toHomologicalComplex.f p)) U x)
          (homSections (inv (h.toHomologicalComplex.f q)) U y)
        change homSections (h.toHomologicalComplex.f (p + q)) U _ =
          (B.mul p q).app U (homSections (h.toHomologicalComplex.f p) U _)
            (homSections (h.toHomologicalComplex.f q) U _) at key
        rw [hinv p x, hinv q y] at key
        exact (congrArg (fun z ↦ homSections (inv (h.toHomologicalComplex.f (p + q))) U z)
          key.symm).trans (hcancel _ _) }
  hom_inv_id := DifferentialGradedAlgebra.Hom.ext fun p ↦ by simp
  inv_hom_id := DifferentialGradedAlgebra.Hom.ext fun p ↦ by simp

/-- The forward morphism of `algebraIsoOfDegreewiseIso h hiso` is `h`. -/
@[simp]
theorem algebraIsoOfDegreewiseIso_hom {A B : DifferentialGradedAlgebra.{w, w} R} (h : A ⟶ B)
    (hiso : ∀ p : ℤ, IsIso (h.toHomologicalComplex.f p)) :
    (algebraIsoOfDegreewiseIso h hiso).hom = h :=
  rfl

end AlgebraIso

section Unital

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Psharp : Sheaf K CommRingCat.{w}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- A composite of unital homomorphisms of sheaves of differential graded algebras is unital. -/
theorem isUnital_comp {A B E : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)}
    {f : A ⟶ B} {g : B ⟶ E} (hf : f.IsUnital) (hg : g.IsUnital) : (f ≫ g).IsUnital :=
  fun U ↦ (congrArg ((g.toHomologicalComplex.f 0).val.app U) (hf U)).trans (hg U)

variable (F : SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w} (toRingCat K Psharp))
  [F.LaxMonoidal] [F.Additive]
  (hO : Presheaf.IsSheaf J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))
  (hP : Presheaf.IsSheaf K
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Psharp.obj))

/-- The unit morphism of the transport of a sheaf of differential graded algebras along a lax
monoidal functor is the unit of the functor followed by the image of the unit morphism. -/
theorem oneHom_toGradedAlgebra_transport
    (A : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)) :
    GradedAlgebra.oneHom (DifferentialGradedAlgebra.transport F hO hP A).toGradedAlgebra =
      Functor.LaxMonoidal.ε F ≫ F.map (GradedAlgebra.oneHom A.toGradedAlgebra) :=
  GradedAlgebra.oneHom_transport F A.toGradedAlgebra hO hP

/-- **The morphism-level action of a direct image of differential graded modules**: the action
of `f_{*,ρ}Q` in degrees `n` and `i` is `ρ` in the second factor followed by the image under the
lax monoidal functor of the action of `Q`. -/
theorem smulSheaf_toposPushforward {A : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)}
    {B : DifferentialGradedAlgebra.{w, w} (toRingCat K Psharp)}
    (ρ : B ⟶ toposPushforwardAlgebra F A) (hρ : ρ.IsUnital)
    (Q : DifferentialGradedModule.{w, w, w} A) (n i : ℤ) :
    smulSheaf ((toposPushforward F ρ hρ).obj Q) n i =
      F.obj (Q.complex.X n) ◁ ρ.toHomologicalComplex.f i ≫
        Stacks.MonoidalGraded.mapMul F (X := Q.complex.X n) (Y := A.complex.X i)
          (Z := Q.complex.X (n + i)) (smulSheaf Q n i) := by
  refine (smulSheaf_restrictScalarsObj
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Psharp) ρ hρ
      (transport F Q (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Osharp)
        (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Psharp)) n i).trans ?_
  rw [smulSheaf_transport, MonoidalCategory.id_tensorHom]
  rfl

/-- The multiplication of the direct image of a differential graded algebra is the image of its
multiplication. -/
private theorem mulSheaf_toposPushforwardAlgebra
    (A : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)) (n m : ℤ) :
    GradedAlgebra.mulSheaf (toposPushforwardAlgebra F A).toGradedAlgebra n m =
      Stacks.MonoidalGraded.mapMul F (GradedAlgebra.mulSheaf A.toGradedAlgebra n m) :=
  GradedAlgebra.mulSheaf_transport F A.toGradedAlgebra
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Osharp)
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Psharp) n m

/-- The unit morphism of the direct image of a differential graded algebra is the unit of the
functor followed by the image of its unit morphism. -/
private theorem oneHom_toposPushforwardAlgebra
    (A : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)) :
    GradedAlgebra.oneHom (toposPushforwardAlgebra F A).toGradedAlgebra =
      Functor.LaxMonoidal.ε F ≫ F.map (GradedAlgebra.oneHom A.toGradedAlgebra) :=
  oneHom_toGradedAlgebra_transport F
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Osharp)
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Psharp) A

end Unital

section Composition

variable {X : RingedTopos.{v₁, u₁, w}} {Y : RingedTopos.{v₂, u₂, w}}
  {Z : RingedTopos.{v₃, u₃, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify X.J AddCommGrpCat.{w}]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [Z.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Z.J AddCommGrpCat.{w}]
  (φ : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  (ψ : Stacks.Sheaves.RingedToposModules.RingedToposHom Y Z)
  (χ : Stacks.Sheaves.RingedToposModules.RingedToposHom X Z)
  (τ : φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward ≅ χ.toToposHom.pushforward)
  (hτ : fSharpSetComp φ ψ ≫
    τ.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = fSharpSet χ)

/-- **The comparison `ψ_*φ_* ≅ χ_*` of direct images of sheaves of modules**, at the
`CategoryTheory.Sheaf.toRingCat` spelling of the structure sheaves which the differential
graded transport is typed at: `Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso`. -/
abbrev toposDirectImageCompIso :
    toposDirectImageModules φ ⋙ toposDirectImageModules ψ ≅ toposDirectImageModules χ :=
  pushforwardModulesCompIso φ ψ χ τ hτ

/-- **The comparison of direct images along a composite is a monoidal natural transformation**
at the `toRingCat` spelling of the structure sheaves:
`Stacks.Sheaves.RingedToposModules.isMonoidal_pushforwardModulesCompIso_hom`. -/
instance isMonoidal_toposDirectImageCompIso_hom :
    NatTrans.IsMonoidal (toposDirectImageCompIso φ ψ χ τ hτ).hom :=
  isMonoidal_pushforwardModulesCompIso_hom φ ψ χ τ hτ

/-- The comparison of direct images along a composite is compatible with the tensorators, at
the `toRingCat` spelling: `Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso_μ`. -/
theorem toposDirectImageCompIso_μ (M N : SheafOfModules.{w} (toRingCat X.J X.O)) :
    Functor.LaxMonoidal.μ (toposDirectImageModules ψ) ((toposDirectImageModules φ).obj M)
          ((toposDirectImageModules φ).obj N) ≫
        (toposDirectImageModules ψ).map (Functor.LaxMonoidal.μ (toposDirectImageModules φ) M N) ≫
          (toposDirectImageCompIso φ ψ χ τ hτ).hom.app (M ⊗ N) =
      ((toposDirectImageCompIso φ ψ χ τ hτ).hom.app M ⊗ₘ
          (toposDirectImageCompIso φ ψ χ τ hτ).hom.app N) ≫
        Functor.LaxMonoidal.μ (toposDirectImageModules χ) M N :=
  (Category.assoc _ _ _).symm.trans
    (NatTrans.IsMonoidal.tensor (τ := (toposDirectImageCompIso φ ψ χ τ hτ).hom) M N)

/-- The comparison of direct images along a composite is compatible with the units, at the
`toRingCat` spelling: `Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso_ε`. -/
theorem toposDirectImageCompIso_ε :
    Functor.LaxMonoidal.ε (toposDirectImageModules ψ) ≫
        (toposDirectImageModules ψ).map (Functor.LaxMonoidal.ε (toposDirectImageModules φ)) ≫
          (toposDirectImageCompIso φ ψ χ τ hτ).hom.app
            (𝟙_ (SheafOfModules.{w} (toRingCat X.J X.O))) =
      Functor.LaxMonoidal.ε (toposDirectImageModules χ) :=
  (Category.assoc _ _ _).symm.trans
    (NatTrans.IsMonoidal.unit (τ := (toposDirectImageCompIso φ ψ χ τ hτ).hom))

/-- The image of a multiplication under the composite direct image, followed by the comparison,
is the tensor product of the comparisons followed by the image under the direct image along
`χ`. -/
theorem mapMul_mapMul_comp_toposDirectImageCompIso
    {P Q R : SheafOfModules.{w} (toRingCat X.J X.O)} (m : P ⊗ Q ⟶ R) :
    Stacks.MonoidalGraded.mapMul (toposDirectImageModules ψ)
        (Stacks.MonoidalGraded.mapMul (toposDirectImageModules φ) m) ≫
        (toposDirectImageCompIso φ ψ χ τ hτ).hom.app R =
      ((toposDirectImageCompIso φ ψ χ τ hτ).hom.app P ⊗ₘ
          (toposDirectImageCompIso φ ψ χ τ hτ).hom.app Q) ≫
        Stacks.MonoidalGraded.mapMul (toposDirectImageModules χ) m := by
  have hn := (toposDirectImageCompIso φ ψ χ τ hτ).hom.naturality m
  simp only [Functor.comp_map] at hn
  simp only [Stacks.MonoidalGraded.mapMul, Functor.map_comp, Category.assoc, hn]
  rw [reassoc_of% (toposDirectImageCompIso_μ φ ψ χ τ hτ P Q)]

/-- The image of a unit under the composite direct image, followed by the comparison, is its
image under the direct image along `χ`. -/
theorem mapOne_mapOne_comp_toposDirectImageCompIso {P : SheafOfModules.{w} (toRingCat X.J X.O)}
    (o : 𝟙_ (SheafOfModules.{w} (toRingCat X.J X.O)) ⟶ P) :
    (Functor.LaxMonoidal.ε (toposDirectImageModules ψ) ≫ (toposDirectImageModules ψ).map
        (Functor.LaxMonoidal.ε (toposDirectImageModules φ) ≫ (toposDirectImageModules φ).map o)) ≫
        (toposDirectImageCompIso φ ψ χ τ hτ).hom.app P =
      Functor.LaxMonoidal.ε (toposDirectImageModules χ) ≫ (toposDirectImageModules χ).map o := by
  have hn := (toposDirectImageCompIso φ ψ χ τ hτ).hom.naturality o
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc, hn]
  rw [reassoc_of% (toposDirectImageCompIso_ε φ ψ χ τ hτ)]

/-- **The action of an iterated direct image, followed by the comparison**: an action
`s : P ⊗ Q ⟶ R` restricted along `b` and transported along `φ_*`, then restricted along `a` and
transported along `ψ_*`, followed by the comparison, is the comparison in the first factor
followed by the action transported along `χ_*` and restricted along `a`, `ψ_*b` and the
comparison. -/
theorem whiskerLeft_comp_mapMul_comp_toposDirectImageCompIso
    {P Q R : SheafOfModules.{w} (toRingCat X.J X.O)} {Bi : SheafOfModules.{w} (toRingCat Y.J Y.O)}
    {Ci : SheafOfModules.{w} (toRingCat Z.J Z.O)} (s : P ⊗ Q ⟶ R)
    (b : Bi ⟶ (toposDirectImageModules φ).obj Q) (a : Ci ⟶ (toposDirectImageModules ψ).obj Bi) :
    ((toposDirectImageModules ψ).obj ((toposDirectImageModules φ).obj P) ◁ a ≫
        Stacks.MonoidalGraded.mapMul (toposDirectImageModules ψ)
          ((toposDirectImageModules φ).obj P ◁ b ≫
            Stacks.MonoidalGraded.mapMul (toposDirectImageModules φ) s)) ≫
        (toposDirectImageCompIso φ ψ χ τ hτ).hom.app R =
      ((toposDirectImageCompIso φ ψ χ τ hτ).hom.app P ⊗ₘ 𝟙 Ci) ≫
        (toposDirectImageModules χ).obj P ◁ (a ≫ (toposDirectImageModules ψ).map b ≫
          (toposDirectImageCompIso φ ψ χ τ hτ).hom.app Q) ≫
          Stacks.MonoidalGraded.mapMul (toposDirectImageModules χ) s := by
  have h := mapMul_mapMul_comp_toposDirectImageCompIso φ ψ χ τ hτ s
  simp only [Stacks.MonoidalGraded.mapMul, Functor.map_comp, Category.assoc] at h ⊢
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc, h]
  simp only [← Category.assoc]
  congr 2
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc, tensorHom_def, Category.id_comp,
    MonoidalCategory.whiskerLeft_id]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  refine (whisker_exchange_assoc ((toposDirectImageCompIso φ ψ χ τ hτ).hom.app P)
    (a ≫ (toposDirectImageModules ψ).map b) _).trans ?_
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]

variable (A : DifferentialGradedAlgebra.{w, w} (toRingCat X.J X.O))

/-- The multiplication of `ψ_*φ_*A`, followed by the comparison, is the tensor product of the
comparisons followed by the multiplication of `χ_*A`, as morphisms out of the tensor product. -/
theorem mulSheaf_toposPushforwardAlgebra_comp (n m : ℤ) :
    GradedAlgebra.mulSheaf (toposPushforwardAlgebra (toposDirectImageModules ψ)
          (toposPushforwardAlgebra (toposDirectImageModules φ) A)).toGradedAlgebra n m ≫
        (toposDirectImageCompIso φ ψ χ τ hτ).hom.app (A.complex.X (n + m)) =
      ((toposDirectImageCompIso φ ψ χ τ hτ).hom.app (A.complex.X n) ⊗ₘ
          (toposDirectImageCompIso φ ψ χ τ hτ).hom.app (A.complex.X m)) ≫
        GradedAlgebra.mulSheaf
          (toposPushforwardAlgebra (toposDirectImageModules χ) A).toGradedAlgebra n m := by
  have h1 : GradedAlgebra.mulSheaf (toposPushforwardAlgebra (toposDirectImageModules ψ)
        (toposPushforwardAlgebra (toposDirectImageModules φ) A)).toGradedAlgebra n m =
      Stacks.MonoidalGraded.mapMul (toposDirectImageModules ψ)
        (Stacks.MonoidalGraded.mapMul (toposDirectImageModules φ)
          (GradedAlgebra.mulSheaf A.toGradedAlgebra n m)) :=
    (mulSheaf_toposPushforwardAlgebra _ _ n m).trans
      (congrArg (Stacks.MonoidalGraded.mapMul (toposDirectImageModules ψ))
        (mulSheaf_toposPushforwardAlgebra _ A n m))
  rw [h1, mulSheaf_toposPushforwardAlgebra (toposDirectImageModules χ) A n m]
  exact mapMul_mapMul_comp_toposDirectImageCompIso φ ψ χ τ hτ _

/-- **The comparison of sheaves of differential graded algebras `ψ_*φ_*A ⟶ χ_*A`**: in degree `n`
it is the comparison `ψ_*φ_*A^n ≅ χ_*A^n` of direct images of sheaves of modules. -/
def toposPushforwardAlgebraCompHom :
    toposPushforwardAlgebra (toposDirectImageModules ψ)
        (toposPushforwardAlgebra (toposDirectImageModules φ) A) ⟶
      toposPushforwardAlgebra (toposDirectImageModules χ) A where
  toHomologicalComplex :=
    { f := fun n ↦ (toposDirectImageCompIso φ ψ χ τ hτ).hom.app (A.complex.X n)
      comm' := fun i j _ ↦ ((toposDirectImageCompIso φ ψ χ τ hτ).hom.naturality
        (A.complex.d i j)).symm }
  map_mul n m := (GradedAlgebra.mulSheaf_comp_eq_iff
      (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Z.O)
      (toposPushforwardAlgebra (toposDirectImageModules ψ)
        (toposPushforwardAlgebra (toposDirectImageModules φ) A)).toGradedAlgebra
      (toposPushforwardAlgebra (toposDirectImageModules χ) A).toGradedAlgebra
      (fun n ↦ (toposDirectImageCompIso φ ψ χ τ hτ).hom.app (A.complex.X n)) n m).mp
    (mulSheaf_toposPushforwardAlgebra_comp φ ψ χ τ hτ A n m)

/-- The comparison of sheaves of differential graded algebras is, in degree `n`, the comparison of
direct images of the degree-`n` piece. -/
@[simp]
theorem toposPushforwardAlgebraCompHom_f (n : ℤ) :
    (toposPushforwardAlgebraCompHom φ ψ χ τ hτ A).toHomologicalComplex.f n =
      (toposDirectImageCompIso φ ψ χ τ hτ).hom.app (A.complex.X n) :=
  rfl

/-- **The comparison `ψ_*φ_*A ≅ χ_*A` of sheaves of differential graded algebras**: the
comparison homomorphism, which is an isomorphism in every degree. -/
def toposPushforwardAlgebraCompIso :
    toposPushforwardAlgebra (toposDirectImageModules ψ)
        (toposPushforwardAlgebra (toposDirectImageModules φ) A) ≅
      toposPushforwardAlgebra (toposDirectImageModules χ) A :=
  algebraIsoOfDegreewiseIso (toposPushforwardAlgebraCompHom φ ψ χ τ hτ A)
    (fun p ↦ ((toposDirectImageCompIso φ ψ χ τ hτ).app (A.complex.X p)).isIso_hom)

/-- The forward morphism of `toposPushforwardAlgebraCompIso` is
`toposPushforwardAlgebraCompHom`. -/
@[simp]
theorem toposPushforwardAlgebraCompIso_hom :
    (toposPushforwardAlgebraCompIso φ ψ χ τ hτ A).hom =
      toposPushforwardAlgebraCompHom φ ψ χ τ hτ A :=
  rfl

/-- **The comparison of sheaves of differential graded algebras is unital.** -/
theorem isUnital_toposPushforwardAlgebraCompHom :
    (toposPushforwardAlgebraCompHom φ ψ χ τ hτ A).IsUnital := by
  refine DifferentialGradedAlgebra.Hom.isUnital_of_oneHom_comp _ ?_
  have h1 : GradedAlgebra.oneHom (toposPushforwardAlgebra (toposDirectImageModules ψ)
        (toposPushforwardAlgebra (toposDirectImageModules φ) A)).toGradedAlgebra =
      Functor.LaxMonoidal.ε (toposDirectImageModules ψ) ≫ (toposDirectImageModules ψ).map
        (Functor.LaxMonoidal.ε (toposDirectImageModules φ) ≫
          (toposDirectImageModules φ).map (GradedAlgebra.oneHom A.toGradedAlgebra)) :=
    (oneHom_toposPushforwardAlgebra _ _).trans
      (congrArg (fun g ↦ Functor.LaxMonoidal.ε (toposDirectImageModules ψ) ≫
          (toposDirectImageModules ψ).map g) (oneHom_toposPushforwardAlgebra _ A))
  rw [h1, oneHom_toposPushforwardAlgebra (toposDirectImageModules χ) A]
  exact mapOne_mapOne_comp_toposDirectImageCompIso φ ψ χ τ hτ _

variable {B : DifferentialGradedAlgebra.{w, w} (toRingCat Y.J Y.O)}
  {C : DifferentialGradedAlgebra.{w, w} (toRingCat Z.J Z.O)}
  (φa : B ⟶ toposPushforwardAlgebra (toposDirectImageModules φ) A)
  (ψa : C ⟶ toposPushforwardAlgebra (toposDirectImageModules ψ) B)

/-- **The composite of two homomorphisms into direct images of sheaves of differential graded
algebras**: `ψa : C ⟶ ψ_*B`, followed by the direct image along `ψ` of `φa : B ⟶ φ_*A`,
followed by the comparison `ψ_*φ_*A ⟶ χ_*A`. -/
def toposPushforwardCompAlgebraHom : C ⟶ toposPushforwardAlgebra (toposDirectImageModules χ) A :=
  ψa ≫ DifferentialGradedAlgebra.transportHom (toposDirectImageModules ψ)
      (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Y.O)
      (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Z.O) φa ≫
    toposPushforwardAlgebraCompHom φ ψ χ τ hτ A

/-- The composite homomorphism in degree `n`: `ψa`, then `ψ_*` of `φa`, then the comparison of
direct images of the degree-`n` piece. -/
theorem toposPushforwardCompAlgebraHom_f (n : ℤ) :
    (toposPushforwardCompAlgebraHom φ ψ χ τ hτ A φa ψa).toHomologicalComplex.f n =
      ψa.toHomologicalComplex.f n ≫
        (toposDirectImageModules ψ).map (φa.toHomologicalComplex.f n) ≫
          (toposDirectImageCompIso φ ψ χ τ hτ).hom.app (A.complex.X n) :=
  rfl

/-- **The composite homomorphism is unital** when the two factors are. -/
theorem isUnital_toposPushforwardCompAlgebraHom (hφa : φa.IsUnital) (hψa : ψa.IsUnital) :
    (toposPushforwardCompAlgebraHom φ ψ χ τ hτ A φa ψa).IsUnital :=
  isUnital_comp hψa (isUnital_comp (DifferentialGradedAlgebra.isUnital_transportHom _ _ _ φa hφa)
    (isUnital_toposPushforwardAlgebraCompHom φ ψ χ τ hτ A))

variable {φa ψa} (hφa : φa.IsUnital) (hψa : ψa.IsUnital)

/-- The action of the iterated direct image `ψ_{*,ψa} φ_{*,φa} Q`, followed by the comparison, is
the comparison in the first factor followed by the action of the direct image `χ_{*,χa} Q` along
the composite homomorphism. -/
theorem smulSheaf_toposPushforward_comp (Q : DifferentialGradedModule.{w, w, w} A) (n i : ℤ) :
    smulSheaf ((toposPushforward (toposDirectImageModules ψ) ψa hψa).obj
          ((toposPushforward (toposDirectImageModules φ) φa hφa).obj Q)) n i ≫
        (toposDirectImageCompIso φ ψ χ τ hτ).hom.app (Q.complex.X (n + i)) =
      ((toposDirectImageCompIso φ ψ χ τ hτ).hom.app (Q.complex.X n) ⊗ₘ 𝟙 (C.complex.X i)) ≫
        smulSheaf ((toposPushforward (toposDirectImageModules χ)
          (toposPushforwardCompAlgebraHom φ ψ χ τ hτ A φa ψa)
          (isUnital_toposPushforwardCompAlgebraHom φ ψ χ τ hτ A φa ψa hφa hψa)).obj Q) n i := by
  rw [smulSheaf_toposPushforward (toposDirectImageModules ψ) ψa hψa
      ((toposPushforward (toposDirectImageModules φ) φa hφa).obj Q),
    smulSheaf_toposPushforward (toposDirectImageModules φ) φa hφa Q,
    smulSheaf_toposPushforward (toposDirectImageModules χ)
      (toposPushforwardCompAlgebraHom φ ψ χ τ hτ A φa ψa)
      (isUnital_toposPushforwardCompAlgebraHom φ ψ χ τ hτ A φa ψa hφa hψa) Q]
  have key := whiskerLeft_comp_mapMul_comp_toposDirectImageCompIso φ ψ χ τ hτ
    (P := Q.complex.X n) (Q := A.complex.X i) (R := Q.complex.X (n + i)) (smulSheaf Q n i)
    (φa.toHomologicalComplex.f i) (ψa.toHomologicalComplex.f i)
  rw [toposPushforwardCompAlgebraHom_f]
  dsimp only [toposPushforward_obj_complex_X]
  exact key

/-- The comparison of the iterated direct image `ψ_{*,ψa} φ_{*,φa} Q` with the direct image
`χ_{*,χa} Q` along the composite homomorphism, for a single module: in degree `n` it is the
comparison of direct images of `Q^n`. -/
def toposPushforwardCompHomApp (Q : DifferentialGradedModule.{w, w, w} A) :
    (toposPushforward (toposDirectImageModules ψ) ψa hψa).obj
        ((toposPushforward (toposDirectImageModules φ) φa hφa).obj Q) ⟶
      (toposPushforward (toposDirectImageModules χ)
        (toposPushforwardCompAlgebraHom φ ψ χ τ hτ A φa ψa)
        (isUnital_toposPushforwardCompAlgebraHom φ ψ χ τ hτ A φa ψa hφa hψa)).obj Q where
  toHomologicalComplex :=
    { f := fun n ↦ (toposDirectImageCompIso φ ψ χ τ hτ).hom.app (Q.complex.X n)
      comm' := fun i j _ ↦ ((toposDirectImageCompIso φ ψ χ τ hτ).hom.naturality
        (Q.complex.d i j)).symm }
  map_mul n i := (smulSheaf_comp_eq_iff
      ((toposPushforward (toposDirectImageModules ψ) ψa hψa).obj
        ((toposPushforward (toposDirectImageModules φ) φa hφa).obj Q))
      (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Z.O)
      ((toposPushforward (toposDirectImageModules χ)
        (toposPushforwardCompAlgebraHom φ ψ χ τ hτ A φa ψa)
        (isUnital_toposPushforwardCompAlgebraHom φ ψ χ τ hτ A φa ψa hφa hψa)).obj Q)
      (fun n ↦ (toposDirectImageCompIso φ ψ χ τ hτ).hom.app (Q.complex.X n)) n i).mp
    (smulSheaf_toposPushforward_comp φ ψ χ τ hτ A hφa hψa Q n i)

/-- In degree `n`, the comparison `toposPushforwardCompHomApp` at `Q` is the comparison of
direct images of the degree-`n` piece of `Q`. -/
@[simp]
theorem toposPushforwardCompHomApp_f (Q : DifferentialGradedModule.{w, w, w} A) (n : ℤ) :
    (toposPushforwardCompHomApp φ ψ χ τ hτ A hφa hψa Q).toHomologicalComplex.f n =
      (toposDirectImageCompIso φ ψ χ τ hτ).hom.app (Q.complex.X n) :=
  rfl

/-- **The direct image of right differential graded modules along a composite.** For morphisms of
ringed topoi `φ : X ⟶ Y`, `ψ : Y ⟶ Z` and `χ : X ⟶ Z` related by the comparison `τ` of their
geometric direct images, and unital homomorphisms `φa : B ⟶ φ_*A`, `ψa : C ⟶ ψ_*B`, the direct
image along `χ` restricting scalars along the composite homomorphism
`toposPushforwardCompAlgebraHom` is the composite of the two direct images. In degree `n` the
isomorphism is the comparison of direct images of sheaves of modules of the degree-`n` piece
(`toposPushforwardCompIsoOfComparison_inv_app_f`). -/
def toposPushforwardCompIsoOfComparison :
    toposPushforward (toposDirectImageModules χ)
        (toposPushforwardCompAlgebraHom φ ψ χ τ hτ A φa ψa)
        (isUnital_toposPushforwardCompAlgebraHom φ ψ χ τ hτ A φa ψa hφa hψa) ≅
      toposPushforward (toposDirectImageModules φ) φa hφa ⋙
        toposPushforward (toposDirectImageModules ψ) ψa hψa :=
  (NatIso.ofComponents (fun Q ↦ isoOfDegreewiseIso
      (toposPushforwardCompHomApp φ ψ χ τ hτ A hφa hψa Q)
      (fun p ↦ ((toposDirectImageCompIso φ ψ χ τ hτ).app (Q.complex.X p)).isIso_hom))
    (fun {Q Q'} (g : Q ⟶ Q') ↦ Hom.ext fun n ↦
      (toposDirectImageCompIso φ ψ χ τ hτ).hom.naturality (g.toHomologicalComplex.f n))).symm

/-- The inverse of the isomorphism of direct images is, in degree `n`, the comparison of direct
images of sheaves of modules of the degree-`n` piece. -/
@[simp]
theorem toposPushforwardCompIsoOfComparison_inv_app_f (Q : DifferentialGradedModule.{w, w, w} A)
    (n : ℤ) :
    ((toposPushforwardCompIsoOfComparison φ ψ χ τ hτ A hφa hψa).inv.app Q).toHomologicalComplex.f
        n = (toposDirectImageCompIso φ ψ χ τ hτ).hom.app (Q.complex.X n) :=
  rfl

/-- The isomorphism of direct images is, in degree `n`, the inverse comparison of direct images
of sheaves of modules of the degree-`n` piece. -/
@[simp]
theorem toposPushforwardCompIsoOfComparison_hom_app_f (Q : DifferentialGradedModule.{w, w, w} A)
    (n : ℤ) :
    ((toposPushforwardCompIsoOfComparison φ ψ χ τ hτ A hφa hψa).hom.app Q).toHomologicalComplex.f
        n = (toposDirectImageCompIso φ ψ χ τ hτ).inv.app (Q.complex.X n) := by
  have h := congrArg (fun g ↦ g.toHomologicalComplex.f n)
    ((toposPushforwardCompIsoOfComparison φ ψ χ τ hτ A hφa hψa).hom_inv_id_app Q)
  simp only [comp_f, id_f, toposPushforwardCompIsoOfComparison_inv_app_f] at h
  refine (cancel_mono ((toposDirectImageCompIso φ ψ χ τ hτ).hom.app (Q.complex.X n))).1 ?_
  exact h.trans ((toposDirectImageCompIso φ ψ χ τ hτ).inv_hom_id_app _).symm

end Composition

/-! ### The literal composite of two morphisms of ringed topoi -/

section LiteralComposite

variable {X : RingedTopos.{v₁, u₁, w}} {Y : RingedTopos.{v₂, u₂, w}}
  {Z : RingedTopos.{v₃, u₃, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify X.J AddCommGrpCat.{w}]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [Z.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Z.J AddCommGrpCat.{w}]
  (f : AlgebraicGeometry.RingedToposHom X Y) (g : AlgebraicGeometry.RingedToposHom Y Z)

/-- The geometric direct image along the composite `g ∘ f` of two morphisms of ringed topoi is
the composite of the geometric direct images on the nose (`CategoryTheory.MorphismOfTopoi.comp`);
this is that identification, as the comparison of Stacks 01D3. -/
abbrev compToposPushforwardIso :
    f.toModulesHom.toToposHom.pushforward ⋙ g.toModulesHom.toToposHom.pushforward ≅
      (g.comp f).toModulesHom.toToposHom.pushforward :=
  Iso.refl _

omit [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify X.J AddCommGrpCat.{w}]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [Z.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Z.J AddCommGrpCat.{w}] in
/-- The identification of the geometric direct images carries the composite structure map to the
structure map of `g ∘ f`: on underlying sheaves of sets the structure map of a composite is
`g♯` followed by `g_*` of `f♯` (`AlgebraicGeometry.RingedToposHom.comp_fSharpRing_underlying`). -/
theorem fSharpSetComp_comp_compToposPushforwardIso :
    fSharpSetComp f.toModulesHom g.toModulesHom ≫
        (compToposPushforwardIso f g).hom.app
          (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) =
      fSharpSet (g.comp f).toModulesHom :=
  (Category.comp_id _).trans (AlgebraicGeometry.RingedToposHom.comp_fSharpRing_underlying g f).symm

/-- **The comparison `(g ∘ f)_* ≅ g_* ∘ f_*` of direct images of sheaves of modules along the
composite of two morphisms of ringed topoi**, at the `toRingCat` spelling. It is the identity on
underlying sheaves of sets. -/
abbrev toposDirectImageModulesCompIso :
    toposDirectImageModules f.toModulesHom ⋙ toposDirectImageModules g.toModulesHom ≅
      toposDirectImageModules (g.comp f).toModulesHom :=
  toposDirectImageCompIso f.toModulesHom g.toModulesHom (g.comp f).toModulesHom
    (compToposPushforwardIso f g) (fSharpSetComp_comp_compToposPushforwardIso f g)

/-- **The comparison of direct images along the composite of two morphisms of ringed topoi is
monoidal.** -/
instance isMonoidal_toposDirectImageModulesCompIso_hom :
    NatTrans.IsMonoidal (toposDirectImageModulesCompIso f g).hom :=
  isMonoidal_toposDirectImageCompIso_hom _ _ _ _ _

variable (A : DifferentialGradedAlgebra.{w, w} (toRingCat X.J X.O))
  {B : DifferentialGradedAlgebra.{w, w} (toRingCat Y.J Y.O)}
  {C : DifferentialGradedAlgebra.{w, w} (toRingCat Z.J Z.O)}
  (φa : B ⟶ toposPushforwardAlgebra (toposDirectImageModules f.toModulesHom) A)
  (ψa : C ⟶ toposPushforwardAlgebra (toposDirectImageModules g.toModulesHom) B)

/-- **The composite structure homomorphism along `g ∘ f`**: `ψa : C ⟶ g_*B`, then `g_*φa`, then
the comparison `g_*f_*A ⟶ (g ∘ f)_*A`. -/
def toposCompAlgebraHom :
    C ⟶ toposPushforwardAlgebra (toposDirectImageModules (g.comp f).toModulesHom) A :=
  toposPushforwardCompAlgebraHom f.toModulesHom g.toModulesHom (g.comp f).toModulesHom
    (compToposPushforwardIso f g) (fSharpSetComp_comp_compToposPushforwardIso f g) A φa ψa

/-- The composite structure homomorphism in degree `n`. -/
theorem toposCompAlgebraHom_f (n : ℤ) :
    (toposCompAlgebraHom f g A φa ψa).toHomologicalComplex.f n =
      ψa.toHomologicalComplex.f n ≫
        (toposDirectImageModules g.toModulesHom).map (φa.toHomologicalComplex.f n) ≫
          (toposDirectImageModulesCompIso f g).hom.app (A.complex.X n) :=
  rfl

omit [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify X.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Z.J AddCommGrpCat.{w}] in
/-- The comparison in the composite structure homomorphism is the identity on underlying sheaves
of sets. -/
theorem moduleSheafFunctor_map_toposDirectImageModulesCompIso_hom_app
    (M : SheafOfModules.{w} (toRingCat X.J X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
        ((toposDirectImageModulesCompIso f g).hom.app M) =
      𝟙 ((g.comp f).toModulesHom.toToposHom.pushforward.obj
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)) :=
  moduleSheafFunctor_map_pushforwardModulesCompIso_hom_app _ _ _ _ _ M

variable {φa ψa}

/-- The composite structure homomorphism is unital. -/
theorem isUnital_toposCompAlgebraHom (hφa : φa.IsUnital) (hψa : ψa.IsUnital) :
    (toposCompAlgebraHom f g A φa ψa).IsUnital :=
  isUnital_toposPushforwardCompAlgebraHom _ _ _ _ _ A φa ψa hφa hψa

/-- **The direct image of right differential graded modules along the composite `g ∘ f` of two
morphisms of ringed topoi is the composite of the direct images**, the scalars along `g ∘ f`
being restricted along the composite structure homomorphism `toposCompAlgebraHom`. In degree `n`
it is the comparison of direct images of sheaves of modules of the degree-`n` piece, which is the
identity on underlying sheaves of sets. -/
def toposPushforwardRingedCompIso (hφa : φa.IsUnital) (hψa : ψa.IsUnital) :
    toposPushforward (toposDirectImageModules (g.comp f).toModulesHom)
        (toposCompAlgebraHom f g A φa ψa) (isUnital_toposCompAlgebraHom f g A hφa hψa) ≅
      toposPushforward (toposDirectImageModules f.toModulesHom) φa hφa ⋙
        toposPushforward (toposDirectImageModules g.toModulesHom) ψa hψa :=
  toposPushforwardCompIsoOfComparison _ _ _ _ _ A hφa hψa

/-- The inverse of the isomorphism of direct images along `g ∘ f` in degree `n`. -/
theorem toposPushforwardRingedCompIso_inv_app_f (hφa : φa.IsUnital) (hψa : ψa.IsUnital)
    (Q : DifferentialGradedModule.{w, w, w} A) (n : ℤ) :
    ((toposPushforwardRingedCompIso f g A hφa hψa).inv.app Q).toHomologicalComplex.f n =
      (toposDirectImageModulesCompIso f g).hom.app (Q.complex.X n) :=
  rfl

/-- The isomorphism of direct images along `g ∘ f` in degree `n`. -/
theorem toposPushforwardRingedCompIso_hom_app_f (hφa : φa.IsUnital) (hψa : ψa.IsUnital)
    (Q : DifferentialGradedModule.{w, w, w} A) (n : ℤ) :
    ((toposPushforwardRingedCompIso f g A hφa hψa).hom.app Q).toHomologicalComplex.f n =
      (toposDirectImageModulesCompIso f g).inv.app (Q.complex.X n) :=
  toposPushforwardCompIsoOfComparison_hom_app_f _ _ _ _ _ A hφa hψa Q n

end LiteralComposite

end SheafOfModules.DifferentialGradedModule
