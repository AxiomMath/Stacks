module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantRingBridgeAction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafCompletionIdealAction
import StacksCore.Tactic.StacksAttribute

/-!
# The completed constant sheaf modulo the product of the constant ideal sheaf with it

Let `(C, J)` be a site, let `R` be a Noetherian commutative ring, let `I` be an ideal of `R` and
let `Osharp` be a sheaf of commutative rings presented by the constant presheaf of rings with
value `R` through `a`. Tag 093M identifies the quotient of the completed constant sheaf
`R̲^∧ = lim (R/Iⁿ)̲` by the product `I̲ · R̲^∧` of the constant sheaf of ideals `I̲` with it with
the constant sheaf `(R/I)̲`. This file proves that identification.

The product `I̲ · R̲^∧` is the image of the multiplication `I̲ ⊗_{Osharp} R̲^∧ ⟶ R̲^∧` of
`Stacks.ConstantSheaf.constantTensorAction`, so the quotient is the cokernel of that
multiplication. The source sandwiches the three ideal multiples

`I R̲^∧ ⊂ I̲ · R̲^∧ ⊂ I̲^∧`

and concludes from `I R̲^∧ = I̲^∧`, which is
`Stacks.ConstantSheaf.epi_completedConstantIdealSheafLift`, that all three agree, hence that
the three quotients agree. The two inclusions are what this file supplies, each in the form
that the comparison of cokernels needs.

The right-hand inclusion says that the canonical map `R̲^∧ ⟶ (R/I)̲`, whose kernel is `I̲^∧`,
kills the multiplication; it is `constantTensorAction_comp_eq_zero` applied to that map, whose
hypothesis holds because `a (m)` annihilates the bridge of a sheaf that `m` annihilates.

The left-hand inclusion says that a map out of `R̲^∧` over `Osharp` killing the multiplication
is killed by every element of `I`. Its proof needs no sections of the sheafification beyond the
images of the unit: a map out of the bridge of `R̲^∧` is determined by its restriction along the
sheafification unit, and on a unit image the value of the multiplication is pinned down by
`constantTensorAction_unit_tmul` together with the value formula
`constantToRingAsModule_app_toSheafify` of the ideal map on a constant section. The passage from
the elements of `I` to the single map `∐_{f ∈ I} R̲^∧ ⟶ R̲^∧` is the preservation of coproducts
by the bridge, which `sheafOfModulesOfConstantRingFunctor_map_comp_eq_zero_iff` reads off its
adjunction.

## Main definitions

* `Stacks.ConstantSheaf.isColimitCokernelCoforkConstantTensorAction`: the cofork exhibiting
  `(R/I)̲` as `R̲^∧/I̲ · R̲^∧`, and
  `Stacks.ConstantSheaf.completedConstantSheaf_quotientByConstantIdealSmul`: the resulting
  isomorphism out of the cokernel of the multiplication.

## Main results

* `Stacks.ConstantSheaf.smul_sheafOfModulesOfConstantRing_eq_zero`: a scalar `r` acting as zero
  on a sheaf of `R`-modules makes `a (r)` act as zero on its bridge over `Osharp`.
* `Stacks.ConstantSheaf.constantTensorAction_comp_completedConstantSheafResidueMap`:
  **Stacks 093M**, `I̲ · R̲^∧ ⊂ I̲^∧`, in the form that the canonical map to `(R/I)̲` kills the
  multiplication.
* `Stacks.ConstantSheaf.idealSmulMap_comp_of_constantTensorAction_comp_eq_zero`:
  **Stacks 093M**, `I R̲^∧ ⊂ I̲ · R̲^∧`, in the form that a map killing the multiplication is
  killed by the elements of `I`.
* `Stacks.ConstantSheaf.isColimitCokernelCoforkConstantTensorAction`: **Stacks 093M**, the
  identification `R̲^∧/I̲ · R̲^∧ = (R/I)̲`: the canonical map `R̲^∧ ⟶ (R/I)̲`, read over
  `Osharp`, is a cokernel of the multiplication `I̲ ⊗_{Osharp} R̲^∧ ⟶ R̲^∧`.
* `Stacks.ConstantSheaf.completedConstantSheaf_quotientByConstantIdealSmul_hom_comp`: the same
  identification as an isomorphism out of the cokernel, carrying the cokernel projection to the
  canonical map.

## References

* [Stacks Project, Tag 093M](https://stacks.math.columbia.edu/tag/093M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open AlgebraicGeometry.SheafOfModules (associatedRingMap moduleSheafificationUnit unitTypes)

universe u v w

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {R : Type w} [CommRing R] [HasWeakSheafify J (ModuleCat.{w} R)]
  {Osharp : Sheaf J CommRingCat.{w}} (a : constantRingPresheaf C R ⟶ Osharp.obj)
  [Presheaf.IsLocallyInjective J (associatedRingMap J a)]
  [Presheaf.IsLocallySurjective J (associatedRingMap J a)]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasWeakSheafify J (ModuleCat R)] in
/-- A scalar `r` of `R` which acts as zero on a sheaf of `R`-modules `G` makes the section
`a (r)` of the structure sheaf act as zero on the bridge of `G` over `Osharp`.

The sections of the bridge are only locally images of sections of `G`, so the statement is
proved after restricting to a covering sieve on which the given section is such an image; there
it is the `R`-linearity of the sheafification unit, whose target carries the restriction of
scalars along `a`, so that `r` acts on it as `a (r)`. -/
theorem smul_sheafOfModulesOfConstantRing_eq_zero (G : Sheaf J (ModuleCat.{w} R)) (r : R)
    (hr : r • 𝟙 G = 0) (U : Cᵒᵖ)
    (y : (sheafOfModulesOfConstantRing J (associatedRingMap J a) G).val.obj U) :
    ((associatedRingMap J a).app U).hom r • y = 0 := by
  apply (sheafOfModulesOfConstantRing J (associatedRingMap J a) G).isSheaf.isSeparated _ _
    (Presheaf.imageSieve_mem (A := Type w) (FA := TypeCat.Fun) (CA := fun X ↦ X) (U := U) J
      (unitTypes J a (ofConstantRingPresheaf G.obj)) y)
  rintro V h ⟨x, hxv⟩
  change (ofConstantRingPresheaf G.obj).obj (op V) at x
  change (moduleSheafificationUnit J a (ofConstantRingPresheaf G.obj)).app (op V) x =
    (sheafOfModulesOfConstantRing J (associatedRingMap J a) G).val.map h.op y at hxv
  have hrx : r • x = (0 : (ofConstantRingPresheaf G.obj).obj (op V)) :=
    congrArg (fun k : G ⟶ G => (k.hom.app (op V)).hom x) hr
  have hzero := ((map_smul
      ((moduleSheafificationUnit J a (ofConstantRingPresheaf G.obj)).app (op V)).hom r x).symm.trans
      (congrArg ((moduleSheafificationUnit J a (ofConstantRingPresheaf G.obj)).app (op V)).hom
        hrx)).trans
      (map_zero
        ((moduleSheafificationUnit J a (ofConstantRingPresheaf G.obj)).app (op V)).hom)
  have hnat : ((Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.map h.op).hom
        (((associatedRingMap J a).app U).hom r) =
      ((associatedRingMap J a).app (op V)).hom r :=
    (congrArg (fun k : (constantRingPresheaf C R ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U ⟶
        (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj (op V) => k.hom r)
      ((associatedRingMap J a).naturality h.op)).symm
  show (sheafOfModulesOfConstantRing J (associatedRingMap J a) G).val.map h.op
      (((associatedRingMap J a).app U).hom r • y) =
    (sheafOfModulesOfConstantRing J (associatedRingMap J a) G).val.map h.op 0
  rw [map_zero, PresheafOfModules.map_smul, ← hxv, hnat]
  exact hzero

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasWeakSheafify J (ModuleCat R)] in
/-- The bridge adjunction carries the zero morphism to the zero morphism: restricting the
scalars of a zero map of sheaves of `Osharp`-modules along `a` gives zero. -/
theorem sheafOfModulesOfConstantRingAdjunction_homEquiv_zero (X : Sheaf J (ModuleCat.{w} R))
    (Z : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)) :
    (sheafOfModulesOfConstantRingAdjunction J (associatedRingMap J a)).homEquiv X Z 0 = 0 := by
  rw [Adjunction.homEquiv_unit,
    show (moduleSheafOfConstantRing J (associatedRingMap J a)).map (0 : _ ⟶ Z) = 0 from rfl,
    comp_zero]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasWeakSheafify J (ModuleCat R)] in
/-- A map of sheaves of `R`-modules becomes zero after the bridge and composition with a map of
`Osharp`-modules exactly when it is zero after composition with the adjoint of that map. This is
the transposition of a vanishing condition across the bridge adjunction, and it is what lets a
condition on a coproduct of sheaves of `R`-modules be checked componentwise. -/
theorem sheafOfModulesOfConstantRingFunctor_map_comp_eq_zero_iff
    {X Y : Sheaf J (ModuleCat.{w} R)} (φ : X ⟶ Y)
    {Z : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
    (g : (sheafOfModulesOfConstantRingFunctor J (associatedRingMap J a)).obj Y ⟶ Z) :
    (sheafOfModulesOfConstantRingFunctor J (associatedRingMap J a)).map φ ≫ g = 0 ↔
      φ ≫ (sheafOfModulesOfConstantRingAdjunction J (associatedRingMap J a)).homEquiv Y Z g =
        0 := by
  rw [← Adjunction.homEquiv_naturality_left,
    ← sheafOfModulesOfConstantRingAdjunction_homEquiv_zero J a X Z, Equiv.apply_eq_iff_eq]

/-- A map out of `F` over the structure sheaf which kills the multiplication
`M̲ ⊗_{Osharp} F ⟶ F` kills the constant multiple `a (φ m) · y` of every section `y` of `F`
coming from the sheafification unit. This is the value formula
`constantTensorAction_unit_tmul` for the multiplication, evaluated on the pure tensor of the
unit image of the constant section `m` with the unit image of `y`, where the ideal map takes the
value `a (φ m)` by `constantToRingAsModule_app_toSheafify`. -/
theorem smul_unit_eq_zero_of_constantTensorAction_comp_eq_zero {M : ModuleCat.{w} R}
    (φ : M ⟶ ModuleCat.of R R) (F : Sheaf J (ModuleCat.{w} R))
    {Z : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
    (g : sheafOfModulesOfConstantRing J (associatedRingMap J a) F ⟶ Z)
    (hg : constantTensorAction J a φ F ≫ g = 0) (m : M) (U : Cᵒᵖ)
    (s : (ofConstantRingPresheaf F.obj).obj U) :
    (g.val.app U) (φ.hom m •
      (moduleSheafificationUnit J a (ofConstantRingPresheaf F.obj)).app U s) = 0 := by
  refine Eq.trans (congrArg (fun z => (g.val.app U) z) ?_)
    (congrArg (fun k : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp))).obj
        (sheafOfModulesOfConstantRing J (associatedRingMap J a)
            ((constantSheaf J (ModuleCat.{w} R)).obj M),
          sheafOfModulesOfConstantRing J (associatedRingMap J a) F) ⟶ Z =>
      (k.val.app U).hom
        (((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
            (PresheafOfModules.tensorObj
              (sheafOfModulesOfConstantRing J (associatedRingMap J a)
                ((constantSheaf J (ModuleCat.{w} R)).obj M)).val
              (sheafOfModulesOfConstantRing J (associatedRingMap J a) F).val)).app U
          ((moduleSheafificationUnit J a
              (ofConstantRingPresheaf ((constantSheaf J (ModuleCat.{w} R)).obj M).obj)).app U
            (((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).app U).hom m) ⊗ₜ
            (moduleSheafificationUnit J a (ofConstantRingPresheaf F.obj)).app U s))) hg)
  refine Eq.trans ?_ (constantTensorAction_unit_tmul J a φ F U
    (((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).app U).hom m) s).symm
  exact congrArg (fun rr => restrictScalarsActionFun J a
    (sheafOfModulesOfConstantRing J (associatedRingMap J a) F).val U rr
    ((moduleSheafificationUnit J a (ofConstantRingPresheaf F.obj)).app U s))
    (constantToRingAsModule_app_toSheafify J (associatedRingMap J a) φ U m).symm

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasWeakSheafify J (ModuleCat R)] in
/-- A map out of the bridge of `F` which kills the constant multiple `a (r) · y` of every section
`y` coming from the sheafification unit is killed by multiplication by `r` on `F`.

Only the unit images are needed: a map out of the bridge, which is a sheafification, is
determined by its restriction along the sheafification unit, and there multiplication by `r` on
`F` becomes multiplication by `a (r)` because the unit is a map to the restriction of scalars
along `a`. -/
theorem sheafOfModulesOfConstantRingMap_smul_id_comp_eq_zero (F : Sheaf J (ModuleCat.{w} R))
    (r : R) {Z : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
    (g : sheafOfModulesOfConstantRing J (associatedRingMap J a) F ⟶ Z)
    (h : ∀ (U : Cᵒᵖ) (s : (ofConstantRingPresheaf F.obj).obj U),
      (g.val.app U) (r •
        (moduleSheafificationUnit J a (ofConstantRingPresheaf F.obj)).app U s) = 0) :
    sheafOfModulesOfConstantRingMap J (associatedRingMap J a) (r • 𝟙 F) ≫ g = 0 := by
  refine (PresheafOfModules.sheafificationHomEquiv (associatedRingMap J a)).injective
    (PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext (LinearMap.ext fun s => ?_))
  show (g.val.app W) ((sheafOfModulesOfConstantRingMap J (associatedRingMap J a)
      (r • 𝟙 F)).val.app W
      ((moduleSheafificationUnit J a (ofConstantRingPresheaf F.obj)).app W s)) = 0
  refine Eq.trans (congrArg (fun z => (g.val.app W) z) ?_) (h W s)
  refine Eq.trans ?_ (map_smul
    ((moduleSheafificationUnit J a (ofConstantRingPresheaf F.obj)).app W).hom r s)
  exact (congrArg (fun k => (PresheafOfModules.Hom.app k W).hom s)
    ((PresheafOfModules.sheafificationAdjunction (associatedRingMap J a)).unit.naturality
      ((constantRingPresheafOfModules C R).map
        ((sheafToPresheaf J (ModuleCat.{w} R)).map (r • 𝟙 F))))).symm

section Ideal

variable (I : Ideal R)

section Right

variable [J.WEqualsLocallyBijective (ModuleCat.{w} R)]

/-- **Stacks 093M**, the inclusion `I̲ · R̲^∧ ⊂ I̲^∧`: the canonical map `R̲^∧ ⟶ (R/I)̲`, read
over `Osharp`, kills the multiplication `I̲ ⊗_{Osharp} R̲^∧ ⟶ R̲^∧`. Since `I̲^∧` is the kernel
of that canonical map, this says that the product of the constant sheaf of ideals with the
completed constant sheaf is contained in the completed constant ideal sheaf.

The multiplication is killed by any map annihilating every constant multiple, and the residue
map is such a map: an element of `I` acts as zero on `(R/I)̲`, hence `a (m)` acts as zero on its
bridge. -/
@[stacks 093M "I̲ Λ̂ ⊂ Î"]
theorem constantTensorAction_comp_completedConstantSheafResidueMap :
    constantTensorAction J a (ModuleCat.ofHom I.subtype) (completedConstantSheaf J I) ≫
        sheafOfModulesOfConstantRingMap J (associatedRingMap J a)
          (completedConstantSheafResidueMap J I) = 0 := by
  refine constantTensorAction_comp_eq_zero J a (ModuleCat.ofHom I.subtype)
    (completedConstantSheaf J I) _ fun m U y => ?_
  refine (map_smul
    ((sheafOfModulesOfConstantRingMap J (associatedRingMap J a)
      (completedConstantSheafResidueMap J I)).val.app U).hom
    ((associatedRingMap J a).app U ((ModuleCat.ofHom I.subtype).hom m)) y).trans ?_
  exact smul_sheafOfModulesOfConstantRing_eq_zero J a
    ((constantSheaf J (ModuleCat.{w} R)).obj (ModuleCat.of R (R ⧸ I))) (m : R)
    (smul_id_constantSheaf_eq_zero J (ModuleCat.of R (R ⧸ I)) (m : R) (by
      intro z
      induction z using Submodule.Quotient.induction_on with
      | _ b =>
        exact (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mul_mem_right b I m.2))) U _

end Right

variable [HasSheafify J (ModuleCat.{w} R)]

/-- **Stacks 093M**, the inclusion `I F ⊂ I̲ · F`: a map out of `F` over `Osharp` which kills the
multiplication `I̲ ⊗_{Osharp} F ⟶ F` also kills the map `∐_{f ∈ I} F ⟶ F` of multiplication by
the elements of `I`, whose image is `I F`.

Multiplying by a single element of `I` is tested on the images of the sheafification unit, where
the multiplication's value is known; the passage from the elements of `I` to the single map out
of the coproduct is the preservation of coproducts by the bridge, read off its adjunction. -/
@[stacks 093M "I Λ̂ ⊂ I̲ Λ̂"]
theorem idealSmulMap_comp_of_constantTensorAction_comp_eq_zero (F : Sheaf J (ModuleCat.{w} R))
    {Z : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
    (g : (sheafOfModulesOfConstantRingFunctor J (associatedRingMap J a)).obj F ⟶ Z)
    (hg : constantTensorAction J a (ModuleCat.ofHom I.subtype) F ≫ g = 0) :
    (sheafOfModulesOfConstantRingFunctor J (associatedRingMap J a)).map
        (idealSmulMap J I F) ≫ g = 0 := by
  rw [sheafOfModulesOfConstantRingFunctor_map_comp_eq_zero_iff]
  refine Sigma.hom_ext _ _ fun j => ?_
  rw [comp_zero, ← Category.assoc, sigma_ι_comp_idealSmulMap,
    ← sheafOfModulesOfConstantRingFunctor_map_comp_eq_zero_iff]
  exact sheafOfModulesOfConstantRingMap_smul_id_comp_eq_zero J a F (j : R) g fun U s =>
    smul_unit_eq_zero_of_constantTensorAction_comp_eq_zero J a (ModuleCat.ofHom I.subtype) F g
      hg j U s

section Quotient

variable [IsNoetherianRing R] [HasWeakSheafify J (Type w)]
  [J.PreservesSheafification (forget (ModuleCat.{w} R))]
  [J.HasSheafCompose (forget (ModuleCat.{w} R))]
  [J.WEqualsLocallyBijective (ModuleCat.{w} R)]

/-- The canonical map `R̲^∧ ⟶ (R/I)̲` is an epimorphism: it is the cokernel projection of the
ideal multiplication read through `completedConstantSheaf_quotientByIdealSmul`. -/
instance epi_completedConstantSheafResidueMap :
    Epi (completedConstantSheafResidueMap J I) := by
  rw [← completedConstantSheaf_quotientByIdealSmul_hom_comp J I]
  infer_instance

/-- The canonical map `R̲^∧ ⟶ (R/I)̲` is a cokernel of the map `∐_{f ∈ I} R̲^∧ ⟶ R̲^∧` of
multiplication by the elements of `I`. This is the identification `R̲^∧/I R̲^∧ = (R/I)̲` of
`completedConstantSheaf_quotientByIdealSmul`, read as a universal property. -/
noncomputable def isColimitCokernelCoforkCompletedConstantSheafResidueMap :
    IsColimit (CokernelCofork.ofπ (completedConstantSheafResidueMap J I)
      (idealSmulMap_comp_completedConstantSheafResidueMap J I)) :=
  IsColimit.ofIsoColimit (cokernelIsCokernel (idealSmulMap J I (completedConstantSheaf J I)))
    (Cofork.ext (completedConstantSheaf_quotientByIdealSmul J I)
      (completedConstantSheaf_quotientByIdealSmul_hom_comp J I))

/-- The cofork on `∐_{f ∈ I} R̲^∧ ⟶ R̲^∧` obtained from a map out of the bridge of `R̲^∧` killing
the multiplication `I̲ ⊗_{Osharp} R̲^∧ ⟶ R̲^∧`, by transposing it across the bridge
adjunction. -/
noncomputable def constantIdealQuotientCofork
    {W : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
    (k : (sheafOfModulesOfConstantRingFunctor J (associatedRingMap J a)).obj
      (completedConstantSheaf J I) ⟶ W)
    (hk : constantTensorAction J a (ModuleCat.ofHom I.subtype) (completedConstantSheaf J I) ≫
      k = 0) :
    CokernelCofork (idealSmulMap J I (completedConstantSheaf J I)) :=
  CokernelCofork.ofπ
    ((sheafOfModulesOfConstantRingAdjunction J (associatedRingMap J a)).homEquiv
      (completedConstantSheaf J I) W k)
    ((sheafOfModulesOfConstantRingFunctor_map_comp_eq_zero_iff J a
      (idealSmulMap J I (completedConstantSheaf J I)) k).mp
      (idealSmulMap_comp_of_constantTensorAction_comp_eq_zero J a I
        (completedConstantSheaf J I) k hk))

omit [J.WEqualsLocallyBijective (ModuleCat.{w} R)] in
/-- The factorisation of `constantIdealQuotientCofork` through the canonical map
`R̲^∧ ⟶ (R/I)̲`. -/
theorem completedConstantSheafResidueMap_comp_desc_constantIdealQuotientCofork
    {W : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
    (k : (sheafOfModulesOfConstantRingFunctor J (associatedRingMap J a)).obj
      (completedConstantSheaf J I) ⟶ W)
    (hk : constantTensorAction J a (ModuleCat.ofHom I.subtype) (completedConstantSheaf J I) ≫
      k = 0) :
    completedConstantSheafResidueMap J I ≫
        (isColimitCokernelCoforkCompletedConstantSheafResidueMap J I).desc
          (constantIdealQuotientCofork J a I k hk) =
      (sheafOfModulesOfConstantRingAdjunction J (associatedRingMap J a)).homEquiv
        (completedConstantSheaf J I) W k :=
  Cofork.IsColimit.π_desc (isColimitCokernelCoforkCompletedConstantSheafResidueMap J I)

/-- **Stacks 093M**, the identification `R̲^∧/I̲ · R̲^∧ = (R/I)̲`: the canonical map
`R̲^∧ ⟶ (R/I)̲`, read as a map of sheaves of modules over `Osharp`, is a cokernel of the
multiplication `I̲ ⊗_{Osharp} R̲^∧ ⟶ R̲^∧` by the constant sheaf of ideals `I̲`.

A map out of the bridge of `R̲^∧` which kills the multiplication kills the multiplications by
the elements of `I` as well, so its transpose across the bridge adjunction factors through
`(R/I)̲` by the identification `R̲^∧/I R̲^∧ = (R/I)̲`; transposing back gives the
factorisation, which is unique because the canonical map is an epimorphism. -/
@[stacks 093M "Λ̂/I̲ Λ̂ = (Λ/I)̲"]
noncomputable def isColimitCokernelCoforkConstantTensorAction :
    IsColimit (CokernelCofork.ofπ
      ((sheafOfModulesOfConstantRingFunctor J (associatedRingMap J a)).map
        (completedConstantSheafResidueMap J I))
      (constantTensorAction_comp_completedConstantSheafResidueMap J a I)) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun {W} k hk =>
      ((sheafOfModulesOfConstantRingAdjunction J (associatedRingMap J a)).homEquiv
        ((constantSheaf J (ModuleCat.{w} R)).obj (ModuleCat.of R (R ⧸ I))) W).symm
        ((isColimitCokernelCoforkCompletedConstantSheafResidueMap J I).desc
          (constantIdealQuotientCofork J a I k hk)))
    (fun {W} k hk =>
      Eq.trans
        (Eq.trans
          (((sheafOfModulesOfConstantRingAdjunction J
              (associatedRingMap J a)).homEquiv_naturality_left_symm
              (completedConstantSheafResidueMap J I)
              ((isColimitCokernelCoforkCompletedConstantSheafResidueMap J I).desc
                (constantIdealQuotientCofork J a I k hk))).symm)
          (congrArg
            ((sheafOfModulesOfConstantRingAdjunction J (associatedRingMap J a)).homEquiv
              (completedConstantSheaf J I) W).symm
            (completedConstantSheafResidueMap_comp_desc_constantIdealQuotientCofork J a I k hk)))
        (((sheafOfModulesOfConstantRingAdjunction J (associatedRingMap J a)).homEquiv
          (completedConstantSheaf J I) W).symm_apply_apply k))
    (fun {W} k hk m hm => by
      refine ((sheafOfModulesOfConstantRingAdjunction J (associatedRingMap J a)).homEquiv
        ((constantSheaf J (ModuleCat.{w} R)).obj (ModuleCat.of R (R ⧸ I))) W).injective ?_
      refine Eq.trans ?_ (((sheafOfModulesOfConstantRingAdjunction J
        (associatedRingMap J a)).homEquiv
          ((constantSheaf J (ModuleCat.{w} R)).obj (ModuleCat.of R (R ⧸ I))) W).apply_symm_apply
        ((isColimitCokernelCoforkCompletedConstantSheafResidueMap J I).desc
          (constantIdealQuotientCofork J a I k hk))).symm
      refine Cofork.IsColimit.hom_ext
        (isColimitCokernelCoforkCompletedConstantSheafResidueMap J I) ?_
      refine Eq.trans ?_
        (completedConstantSheafResidueMap_comp_desc_constantIdealQuotientCofork J a I k hk).symm
      refine Eq.trans ?_ (congrArg
        ((sheafOfModulesOfConstantRingAdjunction J (associatedRingMap J a)).homEquiv
          (completedConstantSheaf J I) W) hm)
      exact ((sheafOfModulesOfConstantRingAdjunction J
        (associatedRingMap J a)).homEquiv_naturality_left
        (completedConstantSheafResidueMap J I) m).symm)

/-- **Stacks 093M.** The canonical isomorphism `R̲^∧/I̲ · R̲^∧ ≅ (R/I)̲` from the quotient of the
completed constant sheaf by the product of the constant sheaf of ideals with it to the constant
sheaf of the quotient ring, as sheaves of modules over `Osharp`. -/
@[stacks 093M "Λ̂/I̲ Λ̂ = (Λ/I)̲"]
noncomputable def completedConstantSheaf_quotientByConstantIdealSmul :
    cokernel (constantTensorAction J a (ModuleCat.ofHom I.subtype)
        (completedConstantSheaf J I)) ≅
      (sheafOfModulesOfConstantRingFunctor J (associatedRingMap J a)).obj
        ((constantSheaf J (ModuleCat.{w} R)).obj (ModuleCat.of R (R ⧸ I))) :=
  IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (constantTensorAction J a (ModuleCat.ofHom I.subtype)
      (completedConstantSheaf J I)))
    (isColimitCokernelCoforkConstantTensorAction J a I)

/-- **Stacks 093M.** The isomorphism `R̲^∧/I̲ · R̲^∧ ≅ (R/I)̲` intertwines the cokernel
projection with the canonical map `R̲^∧ ⟶ (R/I)̲`, so it is the identification of Tag 093M and
not a bare existence statement. -/
@[stacks 093M "Λ̂/I̲ Λ̂ = (Λ/I)̲"]
theorem completedConstantSheaf_quotientByConstantIdealSmul_hom_comp :
    cokernel.π (constantTensorAction J a (ModuleCat.ofHom I.subtype)
          (completedConstantSheaf J I)) ≫
        (completedConstantSheaf_quotientByConstantIdealSmul J a I).hom =
      (sheafOfModulesOfConstantRingFunctor J (associatedRingMap J a)).map
        (completedConstantSheafResidueMap J I) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel (constantTensorAction J a (ModuleCat.ofHom I.subtype)
      (completedConstantSheaf J I)))
    (isColimitCokernelCoforkConstantTensorAction J a I) WalkingParallelPair.one

end Quotient

end Ideal

end Stacks.ConstantSheaf

end
