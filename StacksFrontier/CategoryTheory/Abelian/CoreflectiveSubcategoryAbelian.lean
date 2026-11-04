module

public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.CategoryTheory.Adjunction.CoreflectorOfFullyFaithfulLeftAdjoint

/-!
# Abelian coreflective subcategories with a right exact coreflector

Mathlib's `CategoryTheory.abelianOfAdjunction` transfers abelianness to an additive category `C`
along a *left exact left adjoint* `G : D ⥤ C` of a functor `F : C ⥤ D` with `F ⋙ G ≅ 𝟭 C`
(reflective subcategories, **Stacks 03A3**).  This file proves the dual statement: abelianness
transfers along a *right exact right adjoint* `G` of `F` with `F ⋙ G ≅ 𝟭 C` (coreflective
subcategories).  A right adjoint preserves all limits, so `G` is then exact, and the proof is the
one of Mathlib with the roles of limits and colimits exchanged; finite products of `C` are not
assumed but produced, as `G` applied to the finite coproducts of `D`.

It is applied to the coreflector `CategoryTheory.ObjectProperty.coreflectorOfLeftAdjoint`
`L ⥤ P` built from a fully faithful left adjoint `G ⊣ R`, for `L` a weak Serre subcategory of an
abelian category and `R` right exact: the coreflector is right exact
(`CategoryTheory.ObjectProperty.preservesFiniteColimits_coreflectorOfLeftAdjoint`), so `P` is
abelian (`CategoryTheory.ObjectProperty.abelianOfCoreflectorOfLeftAdjoint`) and the coreflector
is exact.  For an algebraic stack this is **Stacks 0779** (3) and the abelianness of
`QCoh(𝒪_𝒳)` it carries (Remark 0GQL), with `P = QCoh(𝒪_𝒳)`, `L = LQCoh^fbc(𝒪_𝒳)` and
`G ⊣ R` the lower shriek and the restriction to the flat-fppf site.

## Main definitions

* `CategoryTheory.abelianOfCoreflectionOfCompIso`: the transfer.
* `CategoryTheory.ObjectProperty.abelianOfCoreflectorOfLeftAdjoint`: the abelian structure on
  `P` for the coreflector of a fully faithful left adjoint.

## Main results

* `CategoryTheory.ObjectProperty.preservesFiniteColimits_coreflectorOfLeftAdjoint`: right
  exactness of the coreflector; its left exactness is that of a right adjoint.

## References

* [Stacks Project, Tag 03A3](https://stacks.math.columbia.edu/tag/03A3)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 0GQL](https://stacks.math.columbia.edu/tag/0GQL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

namespace AbelianOfCoreflection

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (F : C ⥤ D) (G : D ⥤ C) [G.PreservesZeroMorphisms] [PreservesFiniteColimits G]

/-- A category with a right exact functor `G` and `F ⋙ G ≅ 𝟭 C` has cokernels: the cokernel of
`f` is `G` applied to the cokernel of `F.map f`. -/
theorem hasCokernels (i : F ⋙ G ≅ 𝟭 C) : HasCokernels C :=
  { has_colimit {X Y} f := by
      have : i.inv.app X ≫ G.map (F.map f) ≫ i.hom.app Y = f := by
        simpa using NatIso.naturality_1 i f
      rw [← this]
      have : HasCokernel (G.map (F.map f) ≫ i.hom.app _) := Limits.hasCokernel_comp_iso _ _
      apply Limits.hasCokernel_epi_comp }

omit [Preadditive C] [G.PreservesZeroMorphisms] in
/-- A category with a right exact functor `G` and `F ⋙ G ≅ 𝟭 C` has finite coproducts: the
coproduct of a family is `G` applied to the coproduct of its image under `F`. -/
theorem hasFiniteCoproducts (i : F ⋙ G ≅ 𝟭 C) : HasFiniteCoproducts C :=
  ⟨fun n => ⟨fun K => by
    have : HasColimit ((K ⋙ F) ⋙ G) :=
      ⟨⟨⟨_, isColimitOfPreserves G (colimit.isColimit (K ⋙ F))⟩⟩⟩
    exact hasColimit_of_iso ((Functor.rightUnitor K).symm ≪≫ Functor.isoWhiskerLeft K i.symm ≪≫
      (Functor.associator K F G).symm)⟩⟩

end AbelianOfCoreflection

open AbelianOfCoreflection in
/-- **Abelianness transfers along a right exact right adjoint.**  If `C` is preadditive, `D` is
abelian, `F ⊣ G` with `G : D ⥤ C` right exact (it is left exact, being a right adjoint), and
`F ⋙ G ≅ 𝟭 C`, then `C` is abelian.  This is the dual of `CategoryTheory.abelianOfAdjunction`. -/
@[instance_reducible]
def abelianOfCoreflectionOfCompIso {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] (F : C ⥤ D)
    (G : D ⥤ C) [G.PreservesZeroMorphisms] [PreservesFiniteColimits G] (i : F ⋙ G ≅ 𝟭 C)
    (adj : F ⊣ G) : Abelian C := by
  haveI : PreservesLimits G := adj.rightAdjoint_preservesLimits
  haveI := AbelianOfAdjunction.hasKernels F G i
  haveI := hasCokernels F G i
  haveI := hasFiniteCoproducts F G i
  haveI : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteCoproducts
  have : ∀ {X Y : C} (f : X ⟶ Y), IsIso (Abelian.coimageImageComparison f) := by
    intro X Y f
    let arrowIso : Arrow.mk (G.map (F.map f)) ≅ Arrow.mk f :=
      ((Functor.mapArrowFunctor _ _).mapIso i).app (Arrow.mk f)
    let iso : Arrow.mk (G.map (Abelian.coimageImageComparison (F.map f))) ≅
        Arrow.mk (Abelian.coimageImageComparison f) :=
      Abelian.PreservesCoimageImageComparison.iso G (F.map f) ≪≫
        Abelian.coimageImageComparisonFunctor.mapIso arrowIso
    rw [Arrow.isIso_iff_isIso_of_isIso iso.inv]
    infer_instance
  exact Abelian.ofCoimageImageComparisonIsIso

namespace ObjectProperty

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D]
  [Preadditive D]
  {G : D ⥤ C} {R : C ⥤ D} (adj : G ⊣ R) [IsIso adj.unit] [PreservesFiniteColimits R]
  {P L : ObjectProperty C} [L.IsWeakSerreClass] (hPL : P ≤ L)
  (hA : ∀ F, L F → P (G.obj (R.obj F)))

omit [Preadditive D] [IsIso adj.unit] in
include adj in
/-- **The coreflector of a fully faithful left adjoint is right exact** on a weak Serre
subcategory `L`, as soon as `R` is: finite colimits of `L` are computed in `C`, `R` and `G`
preserve them (`G` being a left adjoint), and the inclusion of `P` reflects them. -/
theorem preservesFiniteColimits_coreflectorOfLeftAdjoint :
    PreservesFiniteColimits (coreflectorOfLeftAdjoint G R P L hA) := by
  have : PreservesFiniteColimits L.ι := L.preservesFiniteColimits_ι_of_isWeakSerreClass
  have : PreservesColimits G := adj.leftAdjoint_preservesColimits
  refine ⟨fun J _ _ => ⟨fun {K} => ⟨fun {c} hc => ?_⟩⟩⟩
  exact ⟨isColimitOfReflects P.ι (isColimitOfPreserves (L.ι ⋙ R ⋙ G) hc)⟩

variable (hB : ∀ M, P M → IsIso (adj.counit.app M))

omit [PreservesFiniteColimits R] [L.IsWeakSerreClass] in
/-- The coreflector preserves zero morphisms, `G` and `R` doing so. -/
theorem preservesZeroMorphisms_coreflectorOfLeftAdjoint [R.PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] :
    (coreflectorOfLeftAdjoint G R P L hA).PreservesZeroMorphisms :=
  ⟨fun X Y => InducedCategory.hom_ext (by
    show G.map (R.map 0) = 0
    rw [Functor.map_zero, Functor.map_zero])⟩

/-- **`P` is abelian**, for the coreflector of a fully faithful left adjoint `G ⊣ R` with `R`
right exact and `L` weak Serre: `CategoryTheory.abelianOfCoreflectionOfCompIso` applied to the
inclusion `P ⊆ L` and the coreflector. -/
@[instance_reducible]
def abelianOfCoreflectorOfLeftAdjoint [R.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] :
    Abelian P.FullSubcategory :=
  haveI := preservesZeroMorphisms_coreflectorOfLeftAdjoint (G := G) (R := R) hA
  haveI := preservesFiniteColimits_coreflectorOfLeftAdjoint adj hA
  abelianOfCoreflectionOfCompIso (ιOfLE hPL) (coreflectorOfLeftAdjoint G R P L hA)
    (coreflectorOfLeftAdjointCompIso adj hPL hA hB)
    (coreflectorOfLeftAdjointAdjunction adj hPL hA hB)

omit [Abelian C] [Preadditive D] [PreservesFiniteColimits R] [L.IsWeakSerreClass] in
include hPL hB in
/-- **The coreflector is left exact**, being a right adjoint. -/
theorem preservesFiniteLimits_coreflectorOfLeftAdjoint :
    PreservesFiniteLimits (coreflectorOfLeftAdjoint G R P L hA) :=
  have : PreservesLimits (coreflectorOfLeftAdjoint G R P L hA) :=
    (coreflectorOfLeftAdjointAdjunction adj hPL hA hB).rightAdjoint_preservesLimits
  inferInstance

end ObjectProperty

end CategoryTheory
