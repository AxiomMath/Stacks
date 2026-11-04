module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.StackReduction
public import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
public import Mathlib.CategoryTheory.Sites.Descent.Precoverage
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.DescentData

/-!
# The pseudofunctor of quasi-coherent modules, and the reduction of fpqc descent to coverings

For a pseudofunctor `F` to `Cat` and a property `P` of objects of its fibres closed under the
pullback functors, descent data for the sub-pseudofunctor cut out by `P` are the descent data for
`F` whose components satisfy `P`.  Applied to `Stacks.Descent.qcohPseudofunctor`, the
pseudofunctor of quasi-coherent modules, this states fpqc descent for quasi-coherent modules
(Stacks 023T) in terms of Mathlib's descent API, and reduces it to the fpqc covering families.

## Main definitions

* `Stacks.Descent.descentDataProperty`: the property of a descent datum for `F` that all its
  components satisfy `P`.
* `Stacks.Descent.fullsubcategoryDescentDataEquivalence`: the equivalence between descent data
  for the sub-pseudofunctor cut out by `P` and descent data for `F` whose components satisfy `P`.

## Main results

* `Stacks.Descent.qcohPseudofunctor_obj`: the fibre of `Stacks.Descent.qcohPseudofunctor` over
  `S` is the full subcategory of quasi-coherent `𝒪_S`-modules.
* `Stacks.Descent.isStack_qcohPseudofunctor_of_isStackFor`: if the pseudofunctor of
  quasi-coherent modules is a stack for every presieve of
  `AlgebraicGeometry.Scheme.fpqcPrecoverage`, it is a stack for the fpqc topology.
* `Stacks.Descent.isEquivalence_toDescentData_fpqc`,
  `Stacks.Descent.isEquivalence_toDescentData_comp_descentDataEquivalence`,
  `Stacks.Descent.nonempty_fullyFaithful_toDescentData_fpqc` and
  `Stacks.Descent.essImage_toDescentData_fpqc`: if the pseudofunctor of quasi-coherent modules
  is a stack for the fpqc topology, then pullback along an fpqc covering family is an
  equivalence onto quasi-coherent descent data; in particular it is fully faithful and every
  descent datum is effective.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 023S](https://stacks.math.columbia.edu/tag/023S)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Bicategory Opposite
open CategoryTheory.Pseudofunctor CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe t v' u' v u

namespace Stacks.Descent

open AlgebraicGeometry

section General

variable {C : Type u} [Category.{v} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
  (P : F.ObjectProperty) [P.IsClosedUnderMapObj]
  {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- The inclusion of a sub-pseudofunctor commutes with
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom`. -/
theorem hom_pullHom' ⦃X₁ X₂ : C⦄ ⦃M₁ : P.fullsubcategory.obj (.mk (op X₁))⦄
    ⦃M₂ : P.fullsubcategory.obj (.mk (op X₂))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (P.fullsubcategory.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (P.fullsubcategory.map f₂.op.toLoc).toFunctor.obj M₂)
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    (pullHom (F := P.fullsubcategory) φ g gf₁ gf₂ hgf₁ hgf₂).hom =
      pullHom (F := F) φ.hom g gf₁ gf₂ hgf₁ hgf₂ :=
  rfl

/-- The property of a descent datum for `F` that all its components satisfy `P`. -/
def descentDataProperty : CategoryTheory.ObjectProperty (F.DescentData f) :=
  fun D ↦ ∀ i, P.prop (.mk (op (X i))) (D.obj i)

/-- A descent datum for the sub-pseudofunctor cut out by `P`, read as a descent datum for `F`
whose components satisfy `P`.  The data are unchanged; only the ambient category is. -/
def descentDataToFullSubcategory (D : P.fullsubcategory.DescentData f) :
    (descentDataProperty P f).FullSubcategory where
  obj :=
    { obj i := (D.obj i).obj
      hom _ q _ _ f₁ f₂ hf₁ hf₂ := (D.hom q f₁ f₂ hf₁ hf₂).hom
      pullHom_hom _ _ g q q' hq _ _ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
        (hom_pullHom' P (D.hom q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁ hgf₂).symm.trans
          (congrArg CategoryTheory.InducedCategory.Hom.hom
            (D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂))
      hom_self _ q _ g hg := congrArg CategoryTheory.InducedCategory.Hom.hom (D.hom_self q g hg)
      hom_comp _ q _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
        congrArg CategoryTheory.InducedCategory.Hom.hom (D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃) }
  property i := (D.obj i).property

/-- The compatibility morphisms of `Stacks.Descent.descentDataOfFullSubcategory`: the morphisms
of the fibres of the sub-pseudofunctor whose underlying morphisms are those of `D`. -/
def descentDataOfFullSubcategoryHom (D : (descentDataProperty P f).FullSubcategory)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (P.fullsubcategory.map f₁.op.toLoc).toFunctor.obj ⟨D.obj.obj i₁, D.property i₁⟩ ⟶
      (P.fullsubcategory.map f₂.op.toLoc).toFunctor.obj ⟨D.obj.obj i₂, D.property i₂⟩ :=
  ⟨D.obj.hom q f₁ f₂ hf₁ hf₂⟩

/-- A descent datum for `F` whose components satisfy `P`, read as a descent datum for the
sub-pseudofunctor cut out by `P`.  This is inverse to
`Stacks.Descent.descentDataToFullSubcategory`. -/
def descentDataOfFullSubcategory (D : (descentDataProperty P f).FullSubcategory) :
    P.fullsubcategory.DescentData f where
  obj i := (⟨D.obj.obj i, D.property i⟩ : P.Obj (.mk (op (X i))))
  hom _ q _ _ f₁ f₂ hf₁ hf₂ := descentDataOfFullSubcategoryHom P f D q f₁ f₂ hf₁ hf₂
  pullHom_hom _ _ g q q' hq _ _ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
    CategoryTheory.InducedCategory.hom_ext <|
      (hom_pullHom' P (descentDataOfFullSubcategoryHom P f D q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂).trans
      (D.obj.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂)
  hom_self _ q _ g hg := CategoryTheory.InducedCategory.hom_ext (D.obj.hom_self q g hg)
  hom_comp _ q _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
    CategoryTheory.InducedCategory.hom_ext (D.obj.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃)

/-- Descent data for the sub-pseudofunctor cut out by a property `P` of objects, read as descent
data for the ambient pseudofunctor whose components satisfy `P`. -/
def descentDataToFullSubcategoryFunctor :
    P.fullsubcategory.DescentData f ⥤ (descentDataProperty P f).FullSubcategory where
  obj D := descentDataToFullSubcategory P f D
  map φ :=
    ⟨{ hom i := (φ.hom i).hom
       comm _ q _ _ f₁ f₂ hf₁ hf₂ :=
         congrArg CategoryTheory.InducedCategory.Hom.hom (φ.comm q f₁ f₂ hf₁ hf₂) }⟩

/-- Descent data for the ambient pseudofunctor whose components satisfy `P`, read as descent data
for the sub-pseudofunctor cut out by `P`. -/
def descentDataOfFullSubcategoryFunctor :
    (descentDataProperty P f).FullSubcategory ⥤ P.fullsubcategory.DescentData f where
  obj D := descentDataOfFullSubcategory P f D
  map {D₁ D₂} φ :=
    { hom i := show (descentDataOfFullSubcategory P f D₁).obj i ⟶
          (descentDataOfFullSubcategory P f D₂).obj i from ⟨φ.hom.hom i⟩
      comm _ q _ _ f₁ f₂ hf₁ hf₂ :=
        CategoryTheory.InducedCategory.hom_ext (φ.hom.comm q f₁ f₂ hf₁ hf₂) }

/-- Descent data for the sub-pseudofunctor cut out by a property `P` of objects are the descent
data for the ambient pseudofunctor all of whose components satisfy `P`.  Both functors are the
identity on the underlying data, so every component of the unit and of the counit is an
identity. -/
def fullsubcategoryDescentDataEquivalence :
    P.fullsubcategory.DescentData f ≌ (descentDataProperty P f).FullSubcategory where
  functor := descentDataToFullSubcategoryFunctor P f
  inverse := descentDataOfFullSubcategoryFunctor P f
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
    fun _ ↦ (Category.comp_id _).trans (Category.id_comp _).symm
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
    fun _ ↦ (Category.comp_id _).trans (Category.id_comp _).symm
  functor_unitIso_comp _ := (Category.comp_id _).trans (CategoryTheory.Functor.map_id _ _)

end General

section Qcoh

/-- The fibre of `Stacks.Descent.qcohPseudofunctor` over a scheme `S` is the full
subcategory of quasi-coherent objects of `S.Modules`. -/
theorem qcohPseudofunctor_obj (S : Scheme.{u}) :
    qcohPseudofunctor.obj (.mk (op S)) =
      Cat.of (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory :=
  rfl

variable {I : Type v} {S : Scheme.{u}} {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)

end Qcoh

section Fpqc

/-- **Fpqc descent of quasi-coherent modules reduces to the fpqc covering families.**  If descent
is effective and morphisms descend for every presieve belonging to
`AlgebraicGeometry.Scheme.fpqcPrecoverage`, then the pseudofunctor of quasi-coherent modules is a
stack for the whole fpqc topology. -/
theorem isStack_qcohPseudofunctor_of_isStackFor
    (h : ∀ (T : Scheme.{u}) (R : Presieve T), R ∈ Scheme.fpqcPrecoverage.{u}.coverings T →
      qcohPseudofunctor.IsStackFor R) :
    qcohPseudofunctor.{u}.IsStack Scheme.fpqcTopology.{u} :=
  Pseudofunctor.IsStack.of_precoverage h

variable {I : Type v} {S : Scheme.{u}} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S}

/-- **Stacks 023T.**  Granted that the pseudofunctor of quasi-coherent modules is a stack for the
fpqc topology, pulling a quasi-coherent module on `S` back along an fpqc covering family
`f i : X i ⟶ S` is an equivalence onto the descent data for that family.  By
`Stacks.Descent.qcohPseudofunctor_obj` the source of this functor is the category of
quasi-coherent modules on `S`, and by `Stacks.Descent.descentDataEquivalence` its target is
`AlgebraicGeometry.QuasicoherentDescentData f`. -/
theorem isEquivalence_toDescentData_fpqc
    [qcohPseudofunctor.{u}.IsStack Scheme.fpqcTopology.{u}]
    (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} S) :
    (qcohPseudofunctor.toDescentData f).IsEquivalence :=
  qcohPseudofunctor.isEquivalence_toDescentData f
    (Precoverage.generate_mem_toGrothendieck hf)

/-- **Stacks 023T, with target `AlgebraicGeometry.QuasicoherentDescentData`.**  Granted that the
pseudofunctor of quasi-coherent modules is a stack for the fpqc topology, the category of
quasi-coherent modules on `S` is equivalent to `AlgebraicGeometry.QuasicoherentDescentData f` for
an fpqc covering family, by pullback followed by `Stacks.Descent.descentDataEquivalence`. -/
theorem isEquivalence_toDescentData_comp_descentDataEquivalence
    [qcohPseudofunctor.{u}.IsStack Scheme.fpqcTopology.{u}]
    (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} S) :
    (qcohPseudofunctor.toDescentData f ⋙
      (descentDataEquivalence (f := f)).functor).IsEquivalence :=
  have := isEquivalence_toDescentData_fpqc hf
  inferInstance

/-- **Stacks 023T, full faithfulness.**  Pullback along an fpqc covering family is fully faithful
on quasi-coherent modules. -/
theorem nonempty_fullyFaithful_toDescentData_fpqc
    [qcohPseudofunctor.{u}.IsStack Scheme.fpqcTopology.{u}]
    (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} S) :
    Nonempty (qcohPseudofunctor.toDescentData f).FullyFaithful :=
  have := isEquivalence_toDescentData_fpqc hf
  ⟨.ofFullyFaithful _⟩

/-- **Stacks 023T, effectivity.**  Every descent datum for the pseudofunctor of quasi-coherent
modules relative to an fpqc covering family is, up to isomorphism, the pullback of a
quasi-coherent module on the base. -/
theorem essImage_toDescentData_fpqc
    [qcohPseudofunctor.{u}.IsStack Scheme.fpqcTopology.{u}]
    (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} S)
    (D : qcohPseudofunctor.DescentData f) :
    (qcohPseudofunctor.toDescentData f).essImage D :=
  have := isEquivalence_toDescentData_fpqc hf
  Functor.EssSurj.mem_essImage _ _

end Fpqc

end Stacks.Descent

end
