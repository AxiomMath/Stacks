module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorLower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorMate
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafWorldBridge

/-!
# The multiplication of a pullback of a sheaf of graded algebras, through Tag 03EL

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and `B` a sheaf of
graded `O_D`-algebras. The pullback `f^*B` of
`Stacks.Sheaves.GradedAlgebraPullback.toposPullbackGradedAlgebra` has the module pullbacks
`f^*B_i` as homogeneous pieces, and its multiplication is built from the inverse image of the
multiplication of `B` followed by extension of scalars. This file proves that the multiplication

`f^*B_i ⊗_{O_C} f^*B_j ⟶ f^*B_{i+j}`

is the pullback `f^*(μ_{ij})` of the multiplication `μ_{ij} : B_i ⊗_{O_D} B_j ⟶ B_{i+j}`, read
through the comparison `f^*(B_i ⊗ B_j) ≅ f^*B_i ⊗ f^*B_j` of **Tag 03EL**
(`Stacks.SheafOfModules.pullbackTensorIso`). Without it the multiplication of a pullback is
described only on the canonical local sections of
`Stacks.Sheaves.GradedAlgebraPullback.pullbackGeneratorSection`, and nothing relates it to the
monoidal structure of the pullback of modules — which is what a degreewise comparison built from
Tag 03EL (for instance the comparison of integral tensor powers of an invertible module) needs to
be multiplicative.

## Main results

* `Stacks.Sheaves.GradedAlgebraPullback.map_mulSheafHom_eq_prodComparison_comp`: the
  multiplication of a transported graded algebra, read on underlying sheaves of sets, is the
  transport of the original one after the product comparison.
* `Stacks.Sheaves.GradedAlgebraPullback.bottomPairing_comp_mulSheaf`: **the pairing identity
  upstairs** — the bottom of the chain of Tag 03EL followed by the multiplication of `f^*B` is the
  multiplication of the inverse image followed by the unit of extension of scalars.
* `Stacks.Sheaves.GradedAlgebraPullback.pullbackTensorIso_hom_app_comp_mulSheaf`: **the
  multiplication of `f^*B` is `f^*(μ)` read through Tag 03EL.**

## Implementation notes

The proof is the one of `Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp_rightUnitor`, with
the right scalar action replaced by the multiplication: the identity is transposed along the
adjunction of Stacks 03D7 to the target topos, reduced to pure tensors of local sections, and
there both sides are the pair of sections pushed through the unit of `f⁻¹ ⊣ f_*` and through the
direct image of a morphism upstairs; the two morphisms upstairs agree on pairs of local sections
by `Stacks.SheafOfModules.pairingApp_pullbackTensorBottom` and by the value of the multiplication
of an extension of scalars on pure tensors
(`Stacks.Sheaves.GradedAlgebraExtendScalars.extendScalarsGradedAlgebra_mul_unit`).

**No `@[stacks]` attribute.** Tag 03EL is carried by `Stacks.SheafOfModules.pullbackTensorIso` and
Tag 0FQX by `Stacks.Sheaves.GradedAlgebraPullback.gradedAlgebraPullbackSpecification`; the identity
below is a compatibility between the two, not a further result of the source.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf MonoidalCategory
open AlgebraicGeometry TensorProduct
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.PresheafOfModules.ChangeOfRings
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.GradedAlgebraInverseImage Stacks.Sheaves.GradedAlgebraExtendScalars
open Stacks.SheafOfModules

namespace Stacks.Sheaves.GradedAlgebraPullback

universe w v u v' u' w'

/-! ### The transported multiplication on underlying sheaves of sets -/

section Transport

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (Φ : Sheaf K (Type w') ⥤ Sheaf J (Type w)) [PreservesFiniteProducts Φ]
  {O : Sheaf K RingCat.{w'}} (A : SheafOfModules.GradedAlgebra.{w', w'} O)

/-- **The multiplication of a transported graded algebra is the transport of the multiplication**,
read on underlying sheaves of sets, once the product comparison of the transporting functor is
inserted. -/
theorem map_mulSheafHom_eq_prodComparison_comp (i j : ℤ) :
    Φ.map (mulSheafHom A i j) =
      prodComparison Φ (pieceSheaf A i) (pieceSheaf A j) ≫
        mulSheafHom (transportGradedAlgebra J Φ A) i j := by
  refine hom_ext_sections (fun X p ↦ ?_)
  change (Φ ⋙ sectionsFunctor J X).map (mulSheafHom A i j) p =
    (sectionsFunctor J X).map (mulSheafHom (transportGradedAlgebra J Φ A) i j)
      ((sectionsFunctor J X).map (prodComparison Φ (pieceSheaf A i) (pieceSheaf A j)) p)
  rw [CategoryTheory.Functor.map_prodComparison_apply]
  refine Eq.trans ?_ (sections_mulSheafHom (transportGradedAlgebra J Φ A) i j X _ _).symm
  exact (congrArg ((transportSections J Φ X).map (mulSheafHom A i j))
    (Functor.prodObjMk_map_fst_map_snd (P := transportSections J Φ X) p)).symm

end Transport

/-! ### The multiplication of a pullback, through Tag 03EL -/

section Pullback

variable {X Y : RingedTopos.{v, u, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  (B : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The inverse image of the multiplication of `B` is the multiplication of the inverse image,
after the product comparison of the inverse image. -/
theorem inverseImage_map_mulSheafHom (i j : ℤ) :
    f.toToposHom.inverseImage.map (mulSheafHom B i j) =
      prodComparison f.toToposHom.inverseImage (pieceSheaf B i) (pieceSheaf B j) ≫
        mulSheafHom (inverseImageGradedAlgebra f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B) i j := by
  have : PreservesFiniteLimits f.toToposHom.inverseImage := f.toToposHom.preservesFiniteLimits
  exact map_mulSheafHom_eq_prodComparison_comp X.J f.toToposHom.inverseImage B i j

/-- **The unit of extension of scalars is multiplicative** on the inverse image of `B`: the unit
of Stacks 03CZ carries a product `xs` of homogeneous local sections of `f⁻¹B` to the product of
the images in `f^*B`, because extension of scalars multiplies pure tensors componentwise and
`1 · 1 = 1`. -/
theorem extendScalarsUnit_mul (i j : ℤ) (V : X.Cᵒᵖ)
    (u : ((inverseImageGradedAlgebra f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).piece i).val.obj V)
    (v : ((inverseImageGradedAlgebra f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).piece j).val.obj V) :
    ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
        ((inverseImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj (B.piece (i + j)))).val.app V
        (((inverseImageGradedAlgebra f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).mul i j).app V u v) =
      ((toposPullbackGradedAlgebra f B).mul i j).app V
        (((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
              (inverseImageRingSheaf f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
            ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj (B.piece i))).val.app V u)
        (((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
              (inverseImageRingSheaf f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
            ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj (B.piece j))).val.app V v) := by
  let := ((fSharpCommRing f).app V).hom.toAlgebra
  have hmul := extendScalarsGradedAlgebra_mul_unit (fSharpCommRing f) X.J
    (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
    (inverseImageGradedAlgebra f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B) i j V
    (1 : X.O.obj.obj V) (1 : X.O.obj.obj V) u v
  have hforget := congrArg (fun φ => PresheafOfModules.Hom.app φ V
      (((inverseImageGradedAlgebra f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).mul i j).app V u v))
    (forget_map_extendRestrictScalarsAdjunction_unit_app X.J (fSharpCommRing f)
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
      ((inverseImageModules f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj (B.piece (i + j))))
  refine Eq.trans hforget ?_
  refine Eq.trans ?_ hmul.symm
  refine Eq.trans ?_ (congrArg
    (fun r => PresheafOfModules.Hom.app
      (PresheafOfModules.sheafifyUnit (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
        ((changeOfRings (fSharpCommRing f)).obj
          ((inverseImageGradedAlgebra f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).piece (i + j)).val)) V
      (r ⊗ₜ[(inverseImageStructureCommRing f).obj V]
        (((inverseImageGradedAlgebra f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).mul i j).app V u v)))
    (one_mul (1 : X.O.obj.obj V)).symm)
  exact congrArg
    (fun t => PresheafOfModules.Hom.app
      (PresheafOfModules.sheafifyUnit (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
        ((changeOfRings (fSharpCommRing f)).obj
          ((inverseImageModules f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj (B.piece (i + j))).val)) V t)
    (changeOfRingsAdjunction_unit_app_apply (fSharpCommRing f)
      ((inverseImageModules f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj (B.piece (i + j))).val V _)

/-- The multiplication of `f^*B` as a morphism out of the tensor product sheaf, on the
sheafification-unit image of a pure tensor, at the spelling of the chain of Tag 03EL. -/
theorem mulSheaf_toposPullback_val_app_unit_tmul (i j : ℤ) (V : X.Cᵒᵖ)
    (a : ((extendScalarsFSharp f).obj ((inverseImageModules f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj (B.piece i))).val.obj V)
    (b : ((extendScalarsFSharp f).obj ((inverseImageModules f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj (B.piece j))).val.obj V) :
    (SheafOfModules.GradedAlgebra.mulSheaf (toposPullbackGradedAlgebra f B) i j).val.app V
        (((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf X.J X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)
            (𝟙 _)).unit.app
          (((extendScalarsFSharp f).obj ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj (B.piece i))).val ⊗
            ((extendScalarsFSharp f).obj ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj (B.piece j))).val)).app V
          (a ⊗ₜ[(ringPresheaf X.O.obj).obj V] b)) =
      ((toposPullbackGradedAlgebra f B).mul i j).app V a b :=
  SheafOfModules.GradedAlgebra.mulSheaf_unit (toposPullbackGradedAlgebra f B) i j V a b

/-- **The pairing identity upstairs.** The pairing at the bottom of the chain of Tag 03EL,
followed by the multiplication of the pullback `f^*B`, is the multiplication of the inverse
image `f⁻¹B` followed by the unit of extension of scalars of Stacks 03CZ.

On a pair of local sections `x`, `s` of the inverse images, the bottom of the chain gives the pure
tensor `η(x) ⊗ η(s)`, the multiplication of `f^*B` on it is `η(x) · η(s)`, and that is `η(xs)` by
`extendScalarsUnit_mul`. -/
theorem bottomPairing_comp_mulSheaf (i j : ℤ) :
    ((pullbackTensorStep4 f (B.piece i) (B.piece j)
            (pullbackTensorTarget f (B.piece i) (B.piece j))).symm
          (pullbackTensorBottomHom f (B.piece i) (B.piece j))).1 ≫
        (Sheaf.moduleSheafFunctor
            (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
          ((SheafOfModules.restrictScalars f.fSharpInverseImage).map
            (SheafOfModules.GradedAlgebra.mulSheaf (toposPullbackGradedAlgebra f B) i j)) =
      mulSheafHom (inverseImageGradedAlgebra f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B) i j ≫
        extendScalarsUnitSheafHom f (B.piece (i + j)) := by
  refine pairing_ext
    (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    fun V x s ↦ ?_
  have hL : pairingApp
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (((pullbackTensorStep4 f (B.piece i) (B.piece j)
            (pullbackTensorTarget f (B.piece i) (B.piece j))).symm
          (pullbackTensorBottomHom f (B.piece i) (B.piece j))).1 ≫
        (Sheaf.moduleSheafFunctor
            (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
          ((SheafOfModules.restrictScalars f.fSharpInverseImage).map
            (SheafOfModules.GradedAlgebra.mulSheaf (toposPullbackGradedAlgebra f B) i j)))
        V x s =
      ((toposPullbackGradedAlgebra f B).mul i j).app V
        (((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
              (inverseImageRingSheaf f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
            ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj (B.piece i))).val.app V x)
        (((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
              (inverseImageRingSheaf f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
            ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj (B.piece j))).val.app V s) := by
    rw [pairingApp_comp, pairingApp_pullbackTensorBottom f (B.piece i) (B.piece j) V x s]
    exact mulSheaf_toposPullback_val_app_unit_tmul f B i j V _ _
  have hR : pairingApp
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (mulSheafHom (inverseImageGradedAlgebra f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B) i j ≫
          (Sheaf.moduleSheafFunctor
              (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
            ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
                (inverseImageRingSheaf f.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
              ((inverseImageModules f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj (B.piece (i + j))))) V x s =
      ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
            (inverseImageRingSheaf f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
          ((inverseImageModules f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj (B.piece (i + j)))).val.app V
        (((inverseImageGradedAlgebra f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).mul i j).app V x s) :=
    (pairingApp_comp (mulSheafHom (inverseImageGradedAlgebra f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B) i j)
      ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
            (inverseImageRingSheaf f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
          ((inverseImageModules f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj (B.piece (i + j)))) V x s).trans
      ((congrArg ((Sheaf.sectionsFunctor X.J V).map
        ((Sheaf.moduleSheafFunctor
            (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
          ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
            (inverseImageRingSheaf f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
          ((inverseImageModules f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj (B.piece (i + j))))))
        (sections_mulSheafHom (inverseImageGradedAlgebra f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B) i j V x s)).trans
      (sectionsFunctor_map_moduleSheafFunctor_map'
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
            (inverseImageRingSheaf f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
          ((inverseImageModules f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj (B.piece (i + j)))) V
        ((((inverseImageGradedAlgebra f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B)).mul i j).app V x s)))
  exact hL.trans ((extendScalarsUnit_mul f B i j V x s).symm.trans hR.symm)

/-- The pairing identity with the product comparison of the inverse image in front: the
morphism upstairs that the chain of Tag 03EL produces from the multiplication of `f^*B` is the
inverse image of the multiplication of `B` followed by the unit of extension of scalars. -/
theorem prodComparison_comp_bottomPairing_comp_mulSheaf (i j : ℤ) :
    prodComparison f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (B.piece i))
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (B.piece j)) ≫
        ((pullbackTensorStep4 f (B.piece i) (B.piece j)
            (pullbackTensorTarget f (B.piece i) (B.piece j))).symm
          (pullbackTensorBottomHom f (B.piece i) (B.piece j))).1 ≫
        (Sheaf.moduleSheafFunctor
            (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
          ((SheafOfModules.restrictScalars f.fSharpInverseImage).map
            (SheafOfModules.GradedAlgebra.mulSheaf (toposPullbackGradedAlgebra f B) i j)) =
      f.toToposHom.inverseImage.map (mulSheafHom B i j) ≫
        extendScalarsUnitSheafHom f (B.piece (i + j)) := by
  refine (congrArg (fun m ↦ prodComparison f.toToposHom.inverseImage
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (B.piece i))
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (B.piece j)) ≫ m)
    (bottomPairing_comp_mulSheaf f B i j)).trans ((Category.assoc _ _ _).symm.trans ?_)
  exact congrArg (fun m ↦ m ≫ extendScalarsUnitSheafHom f (B.piece (i + j)))
    (inverseImage_map_mulSheafHom f B i j).symm

/-- The adjoint transpose of the identity, on underlying sheaves of sets: the unit of `f⁻¹ ⊣ f_*`
followed by the direct image of the morphism upstairs is the multiplication of `B` followed by the
unit of Stacks 03D7. -/
theorem adjUnit_comp_pushforward_mulSheaf (i j : ℤ) :
    f.toToposHom.adj.unit.app
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (B.piece i) ⨯
            Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (B.piece j)) ≫
        f.toToposHom.pushforward.map
          (prodComparison f.toToposHom.inverseImage
              (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (B.piece i))
              (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (B.piece j)) ≫
            ((pullbackTensorStep4 f (B.piece i) (B.piece j)
                (pullbackTensorTarget f (B.piece i) (B.piece j))).symm
              (pullbackTensorBottomHom f (B.piece i) (B.piece j))).1 ≫
            (Sheaf.moduleSheafFunctor
                (inverseImageRingSheaf f.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
              ((SheafOfModules.restrictScalars f.fSharpInverseImage).map
                (SheafOfModules.GradedAlgebra.mulSheaf (toposPullbackGradedAlgebra f B) i j))) =
      mulSheafHom B i j ≫
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          ((pullbackAdjPushforwardModules f).unit.app (B.piece (i + j))) := by
  refine (congrArg (fun m ↦ f.toToposHom.adj.unit.app
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (B.piece i) ⨯
        Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (B.piece j)) ≫
      f.toToposHom.pushforward.map m)
    (prodComparison_comp_bottomPairing_comp_mulSheaf f B i j)).trans ?_
  refine (congrArg (fun m ↦ f.toToposHom.adj.unit.app
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (B.piece i) ⨯
        Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (B.piece j)) ≫ m)
    (f.toToposHom.pushforward.map_comp _ _)).trans ((Category.assoc _ _ _).symm.trans ?_)
  refine (congrArg (fun m ↦ m ≫ f.toToposHom.pushforward.map
      (extendScalarsUnitSheafHom f (B.piece (i + j))))
    (f.toToposHom.adj.unit.naturality (mulSheafHom B i j)).symm).trans
    ((Category.assoc _ _ _).trans ?_)
  exact congrArg (fun m ↦ mulSheafHom B i j ≫ m)
    (moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit_app f (B.piece (i + j))).symm

variable [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The multiplication of a pullback of a sheaf of graded algebras is the pullback of the
multiplication, read through the comparison of Tag 03EL**: for all degrees `i` and `j`,

`c ≫ μ^{f^*B}_{ij} = f^*(μ^B_{ij}) : f^*(B_i ⊗_{O_D} B_j) ⟶ f^*B_{i+j}`,

where `c : f^*(B_i ⊗ B_j) ⟶ f^*B_i ⊗ f^*B_j` is the comparison of Tag 03EL. -/
theorem pullbackTensorIso_hom_app_comp_mulSheaf (i j : ℤ) :
    (pullbackTensorIso f).hom.app (B.piece i, B.piece j) ≫
        SheafOfModules.GradedAlgebra.mulSheaf (toposPullbackGradedAlgebra f B) i j =
      (f.pullbackModules).map (SheafOfModules.GradedAlgebra.mulSheaf B i j) := by
  apply (pullbackTensorStep1 f (B.piece i) (B.piece j)
    ((f.pullbackModules).obj (B.piece (i + j)))).injective
  refine Eq.trans (pullbackTensorStep1_pullbackTensorIso_hom_app_comp f (B.piece i) (B.piece j)
    ((f.pullbackModules).obj (B.piece (i + j)))
    (SheafOfModules.GradedAlgebra.mulSheaf (toposPullbackGradedAlgebra f B) i j)) ?_
  refine Eq.trans ?_ (congrArg (pullbackTensorStep1 f (B.piece i) (B.piece j)
      ((f.pullbackModules).obj (B.piece (i + j))))
    (Category.comp_id ((f.pullbackModules).map (SheafOfModules.GradedAlgebra.mulSheaf B i j))))
  refine Eq.trans ?_ ((pullbackAdjPushforwardModules f).homEquiv_naturality_left
    (SheafOfModules.GradedAlgebra.mulSheaf B i j)
    (𝟙 ((f.pullbackModules).obj (B.piece (i + j))))).symm
  refine Eq.trans ?_ (congrArg (fun m ↦ SheafOfModules.GradedAlgebra.mulSheaf B i j ≫ m)
    ((pullbackAdjPushforwardModules f).homEquiv_id (B.piece (i + j)))).symm
  refine tensorSheaf_hom_ext fun U a r ↦ ?_
  refine Eq.trans (pullbackTensorStep2to6_symm_val_app_unit_tmul f (B.piece i) (B.piece j)
    ((f.pullbackModules).obj (B.piece (i + j)))
    (SheafOfModules.GradedAlgebra.mulSheaf (toposPullbackGradedAlgebra f B) i j) U a r) ?_
  refine Eq.trans ((Sheaf.sectionsFunctor Y.J U).map_comp_apply _ _ _).symm ?_
  refine Eq.trans (congrArg (fun m ↦ (Sheaf.sectionsFunctor Y.J U).map m
      (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w} Y.J U)
        (A := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (B.piece i))
        (B := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (B.piece j)) a r))
    (adjUnit_comp_pushforward_mulSheaf f B i j)) ?_
  refine Eq.trans ((Sheaf.sectionsFunctor Y.J U).map_comp_apply _ _ _) ?_
  refine Eq.trans (congrArg ((Sheaf.sectionsFunctor Y.J U).map
      ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((pullbackAdjPushforwardModules f).unit.app (B.piece (i + j)))))
    (sections_mulSheafHom B i j U a r)) ?_
  refine Eq.trans ?_ (CategoryTheory.comp_apply _ _ _).symm
  exact congrArg (((pullbackAdjPushforwardModules f).unit.app (B.piece (i + j))).val.app U)
    (SheafOfModules.GradedAlgebra.mulSheaf_unit B i j U a r).symm

end Pullback

end Stacks.Sheaves.GradedAlgebraPullback

end
