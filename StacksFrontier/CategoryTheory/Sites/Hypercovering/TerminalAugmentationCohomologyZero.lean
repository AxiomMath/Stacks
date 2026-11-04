module

public import StacksFrontier.CategoryTheory.Sites.FormalCoproductTerminalAugmentation
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.ObjectCohomologyZeroNatural

/-!
# The canonical augmentation of the Čech complex of a hypercovering is a kernel in degree zero

Let `C` be a site with fibre products, let `X` be an object of `C` and let `K` be a hypercovering
of `X` in the sense of [Stacks, Tag 01G9].  The complex of sections
`SectionsOver.sectionsComplex J K F` of an abelian sheaf `F` on `K` carries the canonical
augmentation `Stacks.CategoryTheory.FormalCoproductAugmentation.terminalAugZero` out of `F(X)`,
whose component on the factor indexed by `i` is the restriction of `F` along the structure map
`K₀(i) ⟶ X`.

**This file proves that the augmentation exhibits `F(X)` as the kernel of the first differential**,
for an *arbitrary* abelian sheaf `F` — no injectivity is needed.  That is the degree-zero half of
[Stacks, Tag 01GV] in canonical-map form, in the shape
`IsIso (CategoryTheory.Limits.kernel.lift _ _ _)` that the resolution criterion
`CochainComplex.quasiIso_mkHomFromSingle_zero` consumes.

The content already in the library is
`CategoryTheory.SimplicialObject.Augmented.isIso_kernelLift_freeAbelianSheafAugZero`, the same
statement for the Hom complex `Hom(s(**Z**_{F(K)}^♯), F)` out of the complex of free abelian
sheaves.  What is added here is the identification of the two augmentations: the canonical
augmentation of the complex of sections corresponds, under [Stacks, Tag 01GX]
(`SectionsOver.sectionsComplexIsoHomFreeAbelianSheafComplex`) and under the Yoneda identification
`evaluationIsoFreeAbelianSheafSections` of `F(X)` with `Hom(**Z**_X^♯, F)`, to the degree-zero
augmentation `freeAbelianSheafEpsZero` of the Hom complex.

## Main results

* `Stacks.KernelLift.isIso_kernelLift_of_iso`:  the property of a `kernel.lift` being an
  isomorphism transports along a commuting ladder of isomorphisms.
* `Stacks.CategoryTheory.FormalCoproductAugmentation.terminalAug_eq_comp_of_isTerminal`:  the
  canonical augmentation computed at two different terminal objects differs by the restriction
  along the unique isomorphism between them.
* `Stacks.CategoryTheory.Hypercovering.terminalAugZero_comp_sectionsDegreeIso_zero`:  **the
  identification of the two augmentations**, in degree zero.
* `Stacks.CategoryTheory.Hypercovering.isIso_kernelLift_terminalAugZero`:  **the degree-zero half
  of [Stacks, Tag 01GV] in kernel-lift form**, at an arbitrary abelian sheaf and an arbitrary
  terminal object of `Over X`.

## Implementation notes

The identification is proved on elements, exactly as `SectionsOver.sectionsEquiv_naturality` is:
the degreewise comparison `SectionsOver.sectionsDegreeIso` is an `Equiv.trans` of three
bijections, so it is not `simp`-normal and the only access to it is through `sectionsEquiv_π`,
which computes the `i`-th component of a section of the Hom complex as a value of
`uliftYonedaEquiv`.

Two spelling decisions are forced.  First, `sectionsEquiv_pi_comp_freeAbelian_map` is stated for a
*variable* presheaf `P` in place of `uliftYoneda.obj X` and for a variable morphism into it.  The
morphism actually used is `associatedPresheafAugmentationOver.app K₀`, whose target is written
`((Functor.const _).obj (uliftYoneda.obj X)).obj K₀`; a goal containing that spelling is not
type-correct at `implicit` transparency once the composite with a section of `**Z**_X^♯` is formed,
and every `rw` over it — in particular `Adjunction.homEquiv_naturality_left` — is refused.
Generalising the target removes the `Functor.const` from the statement, and the morphism is then
supplied to the general lemma, where only a definitional check is asked for.

Second, for the same reason none of `CategoryTheory.ConcreteCategory.comp_apply`,
`terminalAugZero_comp_π` or `Pi.π` is used through `rw`: the two sides of the identification are
typed at the `sectionsComplex`/`freeAbelianSheafHomCx` spellings on one side and at the product
spelling on the other, and `rw` builds a motive that mixes them.  They are applied as *terms*
through `Eq.trans` and `congrArg`, which only ever ask for a definitional equality.

## References

* [Stacks Project, Tag 01GV](https://stacks.math.columbia.edu/tag/01GV)
* [Stacks Project, Tag 01GX](https://stacks.math.columbia.edu/tag/01GX)
* [Stacks Project, Tag 09VV](https://stacks.math.columbia.edu/tag/09VV)
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open CategoryTheory.SimplicialObject.Augmented

namespace Stacks.KernelLift

/-- **The property of a `kernel.lift` being an isomorphism transports along a commuting ladder of
isomorphisms.**  Given two pairs `(k, g)` and `(k', g')` of composable-to-zero morphisms and
isomorphisms `p`, `q`, `r` making the two squares commute, the comparison `kernel.lift g k w` is
an isomorphism as soon as `kernel.lift g' k' w'` is.

The two comparisons differ by `CategoryTheory.Limits.kernel.map q r`, which is an isomorphism
because `q` and `r` are. -/
theorem isIso_kernelLift_of_iso {V : Type*} [Category V] [HasZeroMorphisms V]
    {W Y Z W' Y' Z' : V} (k : W ⟶ Y) (g : Y ⟶ Z) [HasKernel g] (w : k ≫ g = 0)
    (k' : W' ⟶ Y') (g' : Y' ⟶ Z') [HasKernel g'] (w' : k' ≫ g' = 0)
    (p : W ≅ W') (q : Y ≅ Y') (r : Z ≅ Z')
    (hk : k ≫ q.hom = p.hom ≫ k') (hg : g ≫ r.hom = q.hom ≫ g')
    (h : IsIso (kernel.lift g' k' w')) : IsIso (kernel.lift g k w) := by
  have hmap : IsIso (kernel.map g g' q.hom r.hom hg) := by
    rw [← kernel.mapIso_hom (f := g) g' q r hg]
    infer_instance
  have h2 : IsIso (kernel.lift g k w ≫ kernel.map g g' q.hom r.hom hg) := by
    rw [kernel.lift_map k g w k' g' w' p.hom q.hom r.hom hk hg]
    infer_instance
  exact IsIso.of_isIso_comp_right (kernel.lift g k w) (kernel.map g g' q.hom r.hom hg)

end Stacks.KernelLift

namespace Stacks.CategoryTheory.FormalCoproductAugmentation

variable {C : Type u} [Category.{v} C] {A : Type*} [Category A]
  [HasProducts.{w} A] [Preadditive A]
  (E : SimplicialObject (Limits.FormalCoproduct.{w} C))

/-- **The canonical augmentation computed at two different terminal objects differs by the
restriction along the unique isomorphism between them.**  Only terminality is used:  the unique
morphism to `T` is the unique morphism to `T'` followed by that isomorphism. -/
theorem terminalAug_eq_comp_of_isTerminal (P : Cᵒᵖ ⥤ A) (n : ℕ) {T T' : C}
    (hT : IsTerminal T) (hT' : IsTerminal T') :
    terminalAug E hT P n =
      P.map (hT.uniqueUpToIso hT').inv.op ≫ terminalAug E hT' P n := by
  refine Limits.Pi.hom_ext _ _ (fun j ↦ ?_)
  rw [terminalAug_comp_π, Category.assoc, terminalAug_comp_π, ← P.map_comp, ← op_comp]
  exact congrArg (fun m ↦ P.map (Quiver.Hom.op m))
    (hT.hom_ext (hT.from ((E.obj (op ⦋n⦌)).obj j))
      (hT'.from ((E.obj (op ⦋n⦌)).obj j) ≫ (hT.uniqueUpToIso hT').inv))

/-- `terminalAug_eq_comp_of_isTerminal` in degree zero, with the targets written as the
degree-zero term of the complex. -/
theorem terminalAugZero_eq_comp_of_isTerminal (P : Cᵒᵖ ⥤ A) {T T' : C}
    (hT : IsTerminal T) (hT' : IsTerminal T') :
    terminalAugZero E hT P =
      P.map (hT.uniqueUpToIso hT').inv.op ≫ terminalAugZero E hT' P :=
  terminalAug_eq_comp_of_isTerminal E P 0 hT hT'

end Stacks.CategoryTheory.FormalCoproductAugmentation

namespace Stacks.CategoryTheory.Hypercovering

open Stacks.CategoryTheory.FormalCoproductAugmentation

variable {C : Type u} [Category.{v} C]

/-! ### The two augmentations on elements -/

/-- The degree-zero augmentation of the Hom complex acts on a section of `**Z**_{A_right}^♯` by
precomposition with the degree-zero augmentation of the complex of free abelian sheaves. -/
theorem freeAbelianSheafEpsZero_apply (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v w}]
    (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type (max u v w)))
    (F : Sheaf J AddCommGrpCat.{max u v w})
    (uu : (freeAbelianSheafSections J A).obj F) :
    ConcreteCategory.hom (freeAbelianSheafEpsZero J A F) uu =
      freeAbelianSheafAugZero J A ≫ uu := rfl

/-- **The degree-zero augmentation of the Hom complex of the hypercovering `K`**, with its target
written as the degree-zero term of `SectionsOver.homFreeAbelianSheafComplex`.

The ascribed result type is load-bearing, not cosmetic.  `freeAbelianSheafEpsZero` has its target
spelled `((freeAbelianSheafHomCx J A).obj F).X 0`, which is definitionally but not syntactically
the degree-zero term of `SectionsOver.homFreeAbelianSheafComplex`, the spelling
`SectionsOver.sectionsDegreeIso` lands in.  A composite mixing the two is type-correct only at
default transparency, so every `rw` over it is refused;  this `def` fixes one of the two
spellings once. -/
noncomputable def homFreeAbelianSheafEpsZero (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v w}] {X : C}
    (K : SimplicialObject (Limits.FormalCoproduct.{w} (Over X)))
    (F : Sheaf J AddCommGrpCat.{max u v w}) :
    (freeAbelianSheafSections J (associatedAugmentedSimplicialPresheafOver.{w} K)).obj F ⟶
      (SectionsOver.homFreeAbelianSheafComplex J K F).X 0 :=
  freeAbelianSheafEpsZero J (associatedAugmentedSimplicialPresheafOver.{w} K) F

/-- The degree-zero augmentation of the Hom complex is a cycle. -/
theorem homFreeAbelianSheafEpsZero_comp_d (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v w}] {X : C}
    (K : SimplicialObject (Limits.FormalCoproduct.{w} (Over X)))
    (F : Sheaf J AddCommGrpCat.{max u v w}) :
    homFreeAbelianSheafEpsZero J K F ≫
      (SectionsOver.homFreeAbelianSheafComplex J K F).d 0 1 = 0 :=
  freeAbelianSheafEpsZero_comp_d J (associatedAugmentedSimplicialPresheafOver.{w} K) F 1 (by simp)

/-- `freeAbelianSheafEpsZero_apply` for the augmented simplicial presheaf of a simplicial formal
coproduct, with the degree-zero augmentation of the complex of free abelian sheaves written out as
the free abelian sheaf functor applied to `associatedPresheafAugmentationOver`.

The target of that augmentation is ascribed, so that the result is typed at
`SectionsOver.freeAbelianSheaf J K₀ ⟶ F`, the spelling `SectionsOver.sectionsEquiv` asks for. -/
theorem freeAbelianSheafEpsZero_apply_eq_comp (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v w}] {X : C}
    (K : SimplicialObject (Limits.FormalCoproduct.{w} (Over X)))
    (F : Sheaf J AddCommGrpCat.{max u v w})
    (uu : (freeAbelianSheafSections J (associatedAugmentedSimplicialPresheafOver.{w} K)).obj F) :
    (ConcreteCategory.hom (homFreeAbelianSheafEpsZero J K F) uu :
          SectionsOver.freeAbelianSheaf J (K.obj (op ⦋0⦌)) ⟶ F) =
      (presheafToSheaf J AddCommGrpCat.{max u v w}).map
          (((Functor.whiskeringRight Cᵒᵖ (Type (max u v w)) AddCommGrpCat.{max u v w}).obj
            AddCommGrpCat.free).map
            ((associatedPresheafAugmentationOver (X := X)).app (K.obj (op ⦋0⦌)) :
              (associatedPresheafFunctorOver.{w} (X := X)).obj (K.obj (op ⦋0⦌)) ⟶
                uliftYoneda.{max u w}.obj X)) ≫ uu := rfl

/-- **The `i`-th component of a section of the Hom complex obtained by precomposition with the
free abelian sheaf of a morphism of presheaves.**  Both adjunctions defining `**Z**^♯` are natural
in their left variable, so the precomposition becomes a precomposition of the morphism itself.

The target presheaf `P` of the morphism is a variable:  at the value `uliftYoneda.obj X` actually
used, the morphism supplied is `associatedPresheafAugmentationOver.app K₀`, whose own target is
spelled through `Functor.const`, and a goal carrying that spelling is not type-correct at
`implicit` transparency. -/
theorem sectionsEquiv_pi_comp_freeAbelian_map (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v w}] {X : C}
    (T : Limits.FormalCoproduct.{w} (Over X)) (F : Sheaf J AddCommGrpCat.{max u v w})
    (P : Cᵒᵖ ⥤ Type (max u v w))
    (a : (associatedPresheafFunctorOver.{w} (X := X)).obj T ⟶ P)
    (uu : (presheafToSheaf J AddCommGrpCat.{max u v w}).obj
      (((Functor.whiskeringRight Cᵒᵖ (Type (max u v w)) AddCommGrpCat.{max u v w}).obj
        AddCommGrpCat.free).obj P) ⟶ F)
    (i : T.I) :
    ConcreteCategory.hom (Pi.π (fun j ↦ F.obj.obj (op ((T.obj j).left))) i)
        ((SectionsOver.sectionsEquiv J T F).toFun
          ((presheafToSheaf J AddCommGrpCat.{max u v w}).map
            (((Functor.whiskeringRight Cᵒᵖ (Type (max u v w)) AddCommGrpCat.{max u v w}).obj
              AddCommGrpCat.free).map a) ≫ uu)) =
      uliftYonedaEquiv.{max u w}
        (SectionsOver.formalEvalι T i ≫ a ≫
          (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _
            ((sheafificationAdjunction J AddCommGrpCat.{max u v w}).homEquiv _ _ uu)) := by
  rw [SectionsOver.sectionsEquiv_π,
    (sheafificationAdjunction J AddCommGrpCat.{max u v w}).homEquiv_naturality_left,
    (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv_naturality_left]

/-- **The Yoneda identification of `F(X)` with the morphisms out of `**Z**_X^♯` is inverse to
reading a morphism off its value on the identity.**  This is `Equiv.apply_symm_apply` for the
composite bijection out of which `evaluationIsoFreeAbelianSheafSections` is built. -/
theorem uliftYonedaEquiv_evaluationIsoFreeAbelianSheafSections (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v w}] {X : C}
    (K : SimplicialObject (Limits.FormalCoproduct.{w} (Over X)))
    (F : Sheaf J AddCommGrpCat.{max u v w}) (z : F.obj.obj (op X)) :
    uliftYonedaEquiv.{max u w}
      ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _
        ((sheafificationAdjunction J AddCommGrpCat.{max u v w}).homEquiv _ _
          (ConcreteCategory.hom
            ((evaluationIsoFreeAbelianSheafSections.{w} J K).hom.app F) z))) = z :=
  (((sheafificationAdjunction J AddCommGrpCat.{max u v w}).homAddEquiv
    (uliftYoneda.{max u w}.obj X ⋙ AddCommGrpCat.free.{max u v w}) F).trans
    (freeEvaluationHomAddEquiv F.obj)).apply_symm_apply z

/-- The `i`-th component of the canonical augmentation of the complex of sections is the
restriction of `F` along the structure map of the `i`-th member of `K₀`:  the unique morphism from
an object of `Over X` to `Over.mk (𝟙 X)` is its own structure map. -/
theorem terminalAugZero_comp_π (J : GrothendieckTopology C) {X : C}
    (K : SimplicialObject (Limits.FormalCoproduct.{w} (Over X)))
    (F : Sheaf J AddCommGrpCat.{max u v w}) (i : (K.obj (op ⦋0⦌)).I) :
    terminalAugZero K (Over.mkIdTerminal (X := X))
          (((Functor.whiskeringLeft (Over X)ᵒᵖ Cᵒᵖ AddCommGrpCat.{max u v w}).obj
            (Over.forget X).op).obj ((sheafToPresheaf J AddCommGrpCat.{max u v w}).obj F)) ≫
        Pi.π (fun j ↦ F.obj.obj (op ((K.obj (op ⦋0⦌)).obj j).left)) i =
      F.obj.map ((K.obj (op ⦋0⦌)).obj i).hom.op :=
  Eq.trans (terminalAug_comp_π K (Over.mkIdTerminal (X := X))
      (((Functor.whiskeringLeft (Over X)ᵒᵖ Cᵒᵖ AddCommGrpCat.{max u v w}).obj
        (Over.forget X).op).obj ((sheafToPresheaf J AddCommGrpCat.{max u v w}).obj F)) 0 i)
    (congrArg (fun m ↦ F.obj.map (Quiver.Hom.op m))
      (Over.mkIdTerminal_from_left ((K.obj (op ⦋0⦌)).obj i)))

/-- The `i`-th component of the canonical augmentation of the complex of sections, read through
the degreewise comparison of [Stacks, Tag 01GX]. -/
theorem sectionsEquiv_pi_sectionsDegreeIso_terminalAugZero (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v w}] {X : C}
    (K : SimplicialObject (Limits.FormalCoproduct.{w} (Over X)))
    (F : Sheaf J AddCommGrpCat.{max u v w}) (z : F.obj.obj (op X)) (i : (K.obj (op ⦋0⦌)).I) :
    ConcreteCategory.hom (Pi.π (fun j ↦ F.obj.obj (op ((K.obj (op ⦋0⦌)).obj j).left)) i)
        ((SectionsOver.sectionsEquiv J (K.obj (op ⦋0⦌)) F).toFun
          (ConcreteCategory.hom (SectionsOver.sectionsDegreeIso J K F 0).hom
            (ConcreteCategory.hom
              (terminalAugZero K (Over.mkIdTerminal (X := X))
                (((Functor.whiskeringLeft (Over X)ᵒᵖ Cᵒᵖ AddCommGrpCat.{max u v w}).obj
                  (Over.forget X).op).obj
                  ((sheafToPresheaf J AddCommGrpCat.{max u v w}).obj F))) z))) =
      ConcreteCategory.hom (F.obj.map ((K.obj (op ⦋0⦌)).obj i).hom.op) z := by
  refine Eq.trans (congrArg _ (SectionsOver.sectionsEquiv_sectionsDegreeIso J K F 0 _)) ?_
  exact Eq.trans (ConcreteCategory.comp_apply _ _ z).symm
    (congrArg (fun m : F.obj.obj (op X) ⟶ F.obj.obj (op ((K.obj (op ⦋0⦌)).obj i).left) ↦
      ConcreteCategory.hom m z) (terminalAugZero_comp_π J K F i))

/-- The `i`-th component of the degree-zero augmentation of the Hom complex, evaluated on the
section corresponding to `z ∈ F(X)`:  the same restriction of `F` along the structure map of the
`i`-th member of `K₀`. -/
theorem sectionsEquiv_pi_freeAbelianSheafEpsZero (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v w}] {X : C}
    (K : SimplicialObject (Limits.FormalCoproduct.{w} (Over X)))
    (F : Sheaf J AddCommGrpCat.{max u v w}) (z : F.obj.obj (op X)) (i : (K.obj (op ⦋0⦌)).I) :
    ConcreteCategory.hom (Pi.π (fun j ↦ F.obj.obj (op ((K.obj (op ⦋0⦌)).obj j).left)) i)
        ((SectionsOver.sectionsEquiv J (K.obj (op ⦋0⦌)) F).toFun
          (ConcreteCategory.hom (homFreeAbelianSheafEpsZero J K F)
            (ConcreteCategory.hom
              ((evaluationIsoFreeAbelianSheafSections.{w} J K).hom.app F) z))) =
      ConcreteCategory.hom (F.obj.map ((K.obj (op ⦋0⦌)).obj i).hom.op) z := by
  refine Eq.trans (sectionsEquiv_pi_comp_freeAbelian_map J (K.obj (op ⦋0⦌)) F
    (uliftYoneda.{max u w}.obj X)
    ((associatedPresheafAugmentationOver (X := X)).app (K.obj (op ⦋0⦌)))
    (ConcreteCategory.hom ((evaluationIsoFreeAbelianSheafSections.{w} J K).hom.app F) z) i) ?_
  rw [← Category.assoc, formalEvalι_comp_associatedPresheafAugmentationOver]
  have hnat := uliftYonedaEquiv_naturality
    (F := (sheafToPresheaf J AddCommGrpCat.{max u v w}).obj F ⋙ forget AddCommGrpCat)
    ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _
      ((sheafificationAdjunction J AddCommGrpCat.{max u v w}).homEquiv _ _
        (ConcreteCategory.hom ((evaluationIsoFreeAbelianSheafSections.{w} J K).hom.app F) z)))
    ((K.obj (op ⦋0⦌)).obj i).hom.op
  rw [uliftYonedaEquiv_evaluationIsoFreeAbelianSheafSections] at hnat
  exact hnat.symm

/-! ### The identification of the two augmentations -/

/-- **The canonical augmentation of the complex of sections is the degree-zero augmentation of the
Hom complex**, read through the degreewise comparison of [Stacks, Tag 01GX] and through the Yoneda
identification of `F(X)` with the morphisms out of `**Z**_X^♯`.

This is the comparison that turns
`CategoryTheory.SimplicialObject.Augmented.isIso_kernelLift_freeAbelianSheafAugZero` into a
statement about the canonical augmentation of the Čech complex of [Stacks, Tag 01GX]. -/
theorem terminalAugZero_comp_sectionsDegreeIso_zero (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v w}] {X : C}
    (K : SimplicialObject (Limits.FormalCoproduct.{w} (Over X)))
    (F : Sheaf J AddCommGrpCat.{max u v w}) :
    terminalAugZero K (Over.mkIdTerminal (X := X))
          (((Functor.whiskeringLeft (Over X)ᵒᵖ Cᵒᵖ AddCommGrpCat.{max u v w}).obj
            (Over.forget X).op).obj ((sheafToPresheaf J AddCommGrpCat.{max u v w}).obj F)) ≫
        (SectionsOver.sectionsDegreeIso J K F 0).hom =
      (evaluationIsoFreeAbelianSheafSections.{w} J K).hom.app F ≫
        homFreeAbelianSheafEpsZero J K F := by
  refine ConcreteCategory.hom_ext _ _ (fun z ↦ ?_)
  refine Eq.trans (ConcreteCategory.comp_apply _ _ z)
    (Eq.trans ?_ (ConcreteCategory.comp_apply _ _ z).symm)
  apply (SectionsOver.sectionsEquiv J (K.obj (op ⦋0⦌)) F).injective
  apply (Concrete.productEquiv
    (fun i ↦ F.obj.obj (op ((K.obj (op ⦋0⦌)).obj i).left))).injective
  funext i
  simp only [Concrete.productEquiv_apply_apply]
  exact (sectionsEquiv_pi_sectionsDegreeIso_terminalAugZero J K F z i).trans
    (sectionsEquiv_pi_freeAbelianSheafEpsZero J K F z i).symm

/-! ### The degree-zero half of Tag 01GV in kernel-lift form -/

variable [HasPullbacks C]

/-- **The degree-zero augmentation of the Hom complex of a hypercovering exhibits the sections of
`F` over `X` as the kernel of the first differential.**  This is
`CategoryTheory.SimplicialObject.Augmented.isIso_kernelLift_freeAbelianSheafAugZero`, whose two
local-surjectivity hypotheses are conditions (1) and (2) of a hypercovering, read at the
`SectionsOver.homFreeAbelianSheafComplex` spelling of the complex.

The passage between the two spellings is made by `Stacks.KernelLift.isIso_kernelLift_of_iso` at
identity isomorphisms rather than by a single definitional check:  the two `kernel.lift`s are
definitionally equal, but checking that directly means comparing two `kernel` objects and their
`HasKernel` instances at once, which exhausts the kernel's heartbeats.  Split into the four
component equalities — the two objects, the differential and the augmentation — each check is
immediate. -/
theorem isIso_kernelLift_homFreeAbelianSheafEpsZero (J : Pretopology C) {X : C}
    (K : SimplicialObject (Limits.FormalCoproduct.{w} (Over X))) (hK : IsHypercovering J K)
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :
    IsIso (kernel.lift ((SectionsOver.homFreeAbelianSheafComplex J.toGrothendieck K F).d 0 1)
      (homFreeAbelianSheafEpsZero J.toGrothendieck K F)
      (homFreeAbelianSheafEpsZero_comp_d J.toGrothendieck K F)) := by
  refine Stacks.KernelLift.isIso_kernelLift_of_iso _ _ _
    ((preadditiveYoneda.obj F).map
      (freeAbelianSheafAugZero J.toGrothendieck
        (associatedAugmentedSimplicialPresheafOver.{w} K)).op)
    ((preadditiveYoneda.obj F).map
      (((SimplicialObject.freeAbelianSheafComplexFunctor J.toGrothendieck).obj
        (associatedAugmentedSimplicialPresheafOver.{w} K).left).d 1 0).op)
    (by rw [← Functor.map_comp, ← op_comp, d_comp_freeAbelianSheafAugZero, op_zero,
      Functor.map_zero])
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · exact Eq.trans (Category.comp_id _) (Category.id_comp _).symm
  · exact Eq.trans (Category.comp_id _) (Category.id_comp _).symm
  · convert isIso_kernelLift_freeAbelianSheafAugZero J.toGrothendieck
      (associatedAugmentedSimplicialPresheafOver.{w} K)
      (isLocallySurjective_of_isHypercovering.{w} J K hK).1
      (isLocallySurjective_of_isHypercovering.{w} J K hK).2.1 F using 2

/-- **[Stacks, Tag 01GV] in degree zero, in canonical-map form.**  For a hypercovering `K` of an
object `X` of a site and an **arbitrary** abelian sheaf `F`, the canonical augmentation
`F(X) ⟶ ∏_{i ∈ K₀} F(K₀(i))` of the Čech complex of `K` exhibits `F(X)` as the kernel of the first
differential.

No injectivity of `F` is assumed:  the input
`CategoryTheory.SimplicialObject.Augmented.isIso_kernelLift_freeAbelianSheafAugZero` needs only
conditions (1) and (2) of a hypercovering, which
`Stacks.CategoryTheory.Hypercovering.isLocallySurjective_of_isHypercovering` supplies.

The terminal object of `Over X` at which the augmentation is formed is arbitrary; the proof
transports it to `Over.mk (𝟙 X)` by `terminalAugZero_eq_comp_of_isTerminal`. -/
@[stacks 01GV "degree zero, as a kernel of the first differential of the Čech complex"]
theorem isIso_kernelLift_terminalAugZero (J : Pretopology C) {X : C}
    (K : SimplicialObject (Limits.FormalCoproduct.{w} (Over X)))
    (hK : IsHypercovering J K) {T : Over X} (hT : IsTerminal T)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :
    IsIso (kernel.lift ((SectionsOver.sectionsComplex J.toGrothendieck K F).d 0 1)
      (terminalAugZero K hT
        (((Functor.whiskeringLeft (Over X)ᵒᵖ Cᵒᵖ AddCommGrpCat.{max u v w}).obj
          (Over.forget X).op).obj
          ((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{max u v w}).obj F)))
      (terminalAugZero_comp_d K hT
        (((Functor.whiskeringLeft (Over X)ᵒᵖ Cᵒᵖ AddCommGrpCat.{max u v w}).obj
          (Over.forget X).op).obj
          ((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{max u v w}).obj F)))) := by
  have : HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w} :=
    hasSheafify_addCommGrpCat.{w} J.toGrothendieck
  refine Stacks.KernelLift.isIso_kernelLift_of_iso _ _ _
    (homFreeAbelianSheafEpsZero J.toGrothendieck K F)
    ((SectionsOver.homFreeAbelianSheafComplex J.toGrothendieck K F).d 0 1)
    (homFreeAbelianSheafEpsZero_comp_d J.toGrothendieck K F)
    (asIso
      ((((Functor.whiskeringLeft (Over X)ᵒᵖ Cᵒᵖ AddCommGrpCat.{max u v w}).obj
            (Over.forget X).op).obj
          ((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{max u v w}).obj F)).map
        (hT.uniqueUpToIso (Over.mkIdTerminal (X := X))).inv.op ≫
        (evaluationIsoFreeAbelianSheafSections.{w} J.toGrothendieck K).hom.app F))
    (SectionsOver.sectionsDegreeIso J.toGrothendieck K F 0)
    (SectionsOver.sectionsDegreeIso J.toGrothendieck K F 1) ?_ ?_ ?_
  · rw [asIso_hom,
      terminalAugZero_eq_comp_of_isTerminal K
        (((Functor.whiskeringLeft (Over X)ᵒᵖ Cᵒᵖ AddCommGrpCat.{max u v w}).obj
          (Over.forget X).op).obj
          ((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{max u v w}).obj F))
        hT (Over.mkIdTerminal (X := X)), Category.assoc,
      terminalAugZero_comp_sectionsDegreeIso_zero, Category.assoc]
  · exact ((SectionsOver.sectionsComplexIsoHomFreeAbelianSheafComplex
      J.toGrothendieck K F).hom.comm 0 1).symm
  · exact isIso_kernelLift_homFreeAbelianSheafEpsZero J K hK F

end Stacks.CategoryTheory.Hypercovering

end
