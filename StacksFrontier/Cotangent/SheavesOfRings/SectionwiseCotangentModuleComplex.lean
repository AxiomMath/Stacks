module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.LocallyQuasiIso
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseSheafification

/-!
# The sectionwise cotangent complex as a complex of presheaves of modules

Let `A ⟶ B` be a homomorphism of sheaves of commutative rings on a site. The terms
`U ↦ L^j_{B(U)/A(U)}` of the cotangent complexes of the ring maps on sections form presheaves of
`B`-modules (`CategoryTheory.Sheaf.sectionwiseCotangentTerm`), and the differentials of the
sectionwise complexes are compatible with the restriction maps, so they form a complex of
presheaves of `B`-modules. It has a canonical map to `L_{B/A}`, and its sheafification is
`L_{B/A}` as complexes of sheaves of `B`-modules.

## Main definitions

* `CategoryTheory.Sheaf.sectionwiseCotangentModuleComplex`: the complex of presheaves of
  `B`-modules `U ↦ L_{B(U)/A(U)}`.
* `CategoryTheory.Sheaf.sectionwiseCotangentModuleComplexComparison`: its canonical map to the
  complex of underlying presheaves of `L_{B/A}`.
* `CategoryTheory.Sheaf.sheafifiedSectionwiseCotangentModuleComplexIso`: the sheafification of
  `U ↦ L_{B(U)/A(U)}` is `L_{B/A}`, as complexes of sheaves of `B`-modules.

## Main results

* `PresheafOfModules.quasiIso_sheafification_map_of_sectionwise`: sheafification carries a map
  of complexes of presheaves of modules which is a quasi-isomorphism over every object to a
  quasi-isomorphism.

## References

* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace PresheafOfModules

universe v v' u'

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{v}} [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasSheafify J AddCommGrpCat.{v}]

/-- Sheafification carries a map of complexes of presheaves of modules which is a
quasi-isomorphism over every object of the site to a quasi-isomorphism of complexes of sheaves of
modules. -/
theorem quasiIso_sheafification_map_of_sectionwise {ι : Type*} {cs : ComplexShape ι}
    {K L : HomologicalComplex (PresheafOfModules.{v} R.obj) cs} (φ : K ⟶ L)
    (h : ∀ U : Cᵒᵖ, QuasiIso (((evaluation.{v} R.obj U).mapHomologicalComplex cs).map φ)) :
    QuasiIso (((sheafification.{v} (𝟙 R.obj)).mapHomologicalComplex cs).map φ) := by
  refine quasiIso_sheafification_map_of_exists_mem_sieve (𝟙 R.obj) φ fun n V =>
    ⟨⊤, J.top_mem V, fun Y _ _ => ?_⟩
  rw [isIso_homologyMap_app_iff]
  exact (h (op Y)).quasiIsoAt n

end PresheafOfModules

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)

/-- The complex of presheaves of `B`-modules `U ↦ L_{B(U)/A(U)}`: in degree `j` the presheaf
`CategoryTheory.Sheaf.sectionwiseCotangentTerm`, with the differentials of the sectionwise
cotangent complexes. -/
noncomputable def sectionwiseCotangentModuleComplex :
    CochainComplex (PresheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj) ℤ where
  X j := sectionwiseCotangentTerm J f j
  d i j :=
    { app U := (CommAlgCat.cotangentComplex.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U)).d i j
      naturality g := (CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
        (sectionsRestrictionSquare J f g)).comm i j }
  shape i j h := PresheafOfModules.Hom.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext
    fun x => ConcreteCategory.congr_hom ((CommAlgCat.cotangentComplex.{max u v w, max u v w}
      (A.obj.obj U) (sectionsAlgebra J f U)).shape i j h) x))
  d_comp_d' i j k _ _ := PresheafOfModules.Hom.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext
    fun x => ConcreteCategory.congr_hom ((CommAlgCat.cotangentComplex.{max u v w, max u v w}
      (A.obj.obj U) (sectionsAlgebra J f U)).d_comp_d i j k) x))

/-- The value of `U ↦ L_{B(U)/A(U)}` over `U` is `L_{B(U)/A(U)}`. -/
theorem sectionwiseCotangentModuleComplex_evaluation (U : Cᵒᵖ) :
    ((PresheafOfModules.evaluation _ U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (sectionwiseCotangentModuleComplex J f) =
      CommAlgCat.cotangentComplex.{max u v w, max u v w} (A.obj.obj U) (sectionsAlgebra J f U) :=
  rfl

/-- The canonical maps `L_{B(U)/A(U)} ⟶ L_{B/A}(U)`, as a map of complexes of presheaves of
`B`-modules. -/
noncomputable def sectionwiseCotangentModuleComplexComparison :
    sectionwiseCotangentModuleComplex J f ⟶
      ((SheafOfModules.forget _).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (cotangentComplex J f) where
  f j := sectionwiseCotangentTermComparison J f j
  comm' i j _ := PresheafOfModules.Hom.ext (funext fun U =>
    (sectionsCotangentComplexComparison J f U).comm i j)

/-- The sheafification of `U ↦ L_{B(U)/A(U)}` is `L_{B/A}`, as complexes of sheaves of
`B`-modules; in each degree the isomorphism is the adjunct of the canonical map. -/
noncomputable def sheafifiedSectionwiseCotangentModuleComplexIso :
    ((PresheafOfModules.sheafification.{max u v w}
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (sectionwiseCotangentModuleComplex J f) ≅
      cotangentComplex J f :=
  HomologicalComplex.Hom.isoOfComponents
    (fun j => @asIso _ _ _ _ _ (isIso_sheafify_sectionwiseCotangentTermComparison J f j)) (by
      intro i j _
      let R := Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B
      let adj := PresheafOfModules.sheafificationAdjunction.{max u v w} (𝟙 R.obj)
      have he (P : PresheafOfModules.{max u v w} R.obj) (L : SheafOfModules.{max u v w} R) :
          adj.homEquiv P L = PresheafOfModules.sheafificationHomEquiv.{max u v w} (𝟙 R.obj) :=
        Equiv.ext fun g => PresheafOfModules.sheafificationAdjunction_homEquiv_apply _ g
      have h₁ := adj.homEquiv_naturality_right_symm (sectionwiseCotangentTermComparison J f i)
        ((cotangentComplex J f).d i j)
      have h₂ := adj.homEquiv_naturality_left_symm ((sectionwiseCotangentModuleComplex J f).d i j)
        (sectionwiseCotangentTermComparison J f j)
      rw [he, he] at h₁ h₂
      exact h₁.symm.trans ((congrArg
        (PresheafOfModules.sheafificationHomEquiv.{max u v w} (𝟙 R.obj)).symm
        ((sectionwiseCotangentModuleComplexComparison J f).comm i j)).trans h₂))

end CategoryTheory.Sheaf

end
