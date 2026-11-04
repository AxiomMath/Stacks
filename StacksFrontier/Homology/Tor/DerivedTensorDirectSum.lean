module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
import StacksFrontier.Homology.HomologyColimit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived tensor product of an arbitrary direct sum

Tensoring commutes with arbitrary direct sums, and so does homology in an abelian category whose
coproducts are exact. Putting the two together: if `H ⁱ(E[0] ⊗ᴸ N[0])` vanishes for each member of
a family `E`, then `H ⁱ((⊕ E)[0] ⊗ᴸ N[0])` vanishes as well. Equivalently, `Tor` commutes with
arbitrary direct sums in its first variable.

## Main definitions

* `Stacks.DerivedTensor.tensorComplexRight` — the functor `M ↦ P ⊗ M` for a fixed complex `P`.

## Main results

* `Stacks.DerivedTensor.homologyFunctor_preservesColimitsOfShape` — homology of complexes
  commutes with colimits of a shape whose colimits are exact. For a discrete shape, the
  exactness hypothesis is Grothendieck's axiom AB4.
* `Stacks.DerivedTensor.isZero_derivedTensorHomology_coprod_single` — the vanishing statement for
  a coproduct of modules.
* `Stacks.DerivedTensor.isZero_derivedTensorHomology_directSum_single` — the same with the
  coproduct spelled as a `DirectSum` of copies of one module.

## References

* [Stacks Project, Tag 0ECC](https://stacks.math.columbia.edu/tag/0ECC)
* [Stacks Project, Tag 079B](https://stacks.math.columbia.edu/tag/079B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.DerivedTensor

universe u

namespace Stacks.DerivedTensor

/-! ### Colimits of zero objects -/

/-- A colimit of zero objects is zero. -/
theorem isZero_colimit_of_isZero {J : Type*} [Category J] {C : Type*} [Category C]
    [HasZeroMorphisms C] (F : J ⥤ C) [HasColimit F] (h : ∀ j, IsZero (F.obj j)) :
    IsZero (colimit F) :=
  (IsZero.iff_id_eq_zero _).2 (colimit.hom_ext (fun j => by
    rw [Category.comp_id, Limits.comp_zero]
    exact (h j).eq_of_src _ _))

/-! ### Homology and exact colimits -/

section Homology

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]

/-- **Homology of short complexes commutes with exact colimits.** If colimits of shape `J` in `𝒜`
are exact, the homology of a colimit of short complexes of shape `J` is the colimit of the
homologies. -/
theorem shortComplexHomologyFunctor_preservesColimitsOfShape {J : Type*} [Category J]
    [HasColimitsOfShape J 𝒜] [HasExactColimitsOfShape J 𝒜] :
    PreservesColimitsOfShape J (ShortComplex.homologyFunctor 𝒜) := by
  refine ⟨fun {E} => preservesColimit_of_preserves_colimit_cocone
    (ShortComplex.isColimitColimitCocone E) ?_⟩
  refine IsColimit.ofIsoColimit
    ((IsColimit.precomposeHomEquiv (Stacks.HomologyColimit.compHomologyFunctorIso E)
      (colimit.cocone ((ShortComplex.FunctorEquivalence.inverse J 𝒜).obj E).homology)).symm
      (colimit.isColimit _))
    (Cocone.ext (((ShortComplex.FunctorEquivalence.inverse J 𝒜).obj E).mapHomologyIso
      (colim : (J ⥤ 𝒜) ⥤ 𝒜)).symm (fun j => ?_))
  set T := (ShortComplex.FunctorEquivalence.inverse J 𝒜).obj E with hT
  let ι : (evaluation J 𝒜).obj j ⟶ (colim : (J ⥤ 𝒜) ⥤ 𝒜) :=
    { app := fun X => colimit.ι X j
      naturality := fun X Y f => by simp }
  have key : ι.app T.homology = (T.mapHomologyIso ((evaluation J 𝒜).obj j)).inv ≫
      ShortComplex.homologyMap (T.mapNatTrans ι) ≫ (T.mapHomologyIso colim).hom :=
    NatTrans.app_homology ι T
  show ((T.mapHomologyIso ((evaluation J 𝒜).obj j)).hom ≫ ι.app T.homology) ≫
      (T.mapHomologyIso (colim : (J ⥤ 𝒜) ⥤ 𝒜)).inv
    = ShortComplex.homologyMap (T.mapNatTrans ι)
  rw [key]
  simp

/-- The functor sending a complex to the short complex in degrees `prev i`, `i`, `next i`
preserves colimits of shape `J`. -/
theorem shortComplexFunctor_preservesColimitsOfShape {J : Type*} [Category J]
    [HasColimitsOfShape J 𝒜] {ι : Type*} (c : ComplexShape ι) (i : ι) :
    PreservesColimitsOfShape J (HomologicalComplex.shortComplexFunctor 𝒜 c i) :=
  ⟨fun {_} => ⟨fun hs => ⟨ShortComplex.isColimitOfIsColimitπ _
    (isColimitOfPreserves (HomologicalComplex.eval 𝒜 c _) hs)
    (isColimitOfPreserves (HomologicalComplex.eval 𝒜 c _) hs)
    (isColimitOfPreserves (HomologicalComplex.eval 𝒜 c _) hs)⟩⟩⟩

/-- **Homology commutes with exact colimits.** If colimits of shape `J` in `𝒜` are exact, the
degree-`i` homology functor on complexes preserves colimits of shape `J`. -/
theorem homologyFunctor_preservesColimitsOfShape {J : Type*} [Category J]
    [HasColimitsOfShape J 𝒜] [HasExactColimitsOfShape J 𝒜] {ι : Type*} (c : ComplexShape ι)
    (i : ι) :
    PreservesColimitsOfShape J (HomologicalComplex.homologyFunctor 𝒜 c i) :=
  have := shortComplexFunctor_preservesColimitsOfShape (𝒜 := 𝒜) (J := J) c i
  have := shortComplexHomologyFunctor_preservesColimitsOfShape (𝒜 := 𝒜) (J := J)
  preservesColimitsOfShape_of_natIso (HomologicalComplex.homologyFunctorIso 𝒜 c i).symm

end Homology

/-! ### Termwise tensor product with a fixed complex -/

variable (A : Type u) [CommRing A]

attribute [local instance] HasDerivedCategory.standard

/-- The termwise tensor product `P ⊗ M` of a fixed cochain complex `P` with a module `M`, as a
functor of `M`. -/
def tensorComplexRight (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    ModuleCat.{u} A ⥤ CochainComplex (ModuleCat.{u} A) ℤ where
  obj M := ((tensorRight M).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  map {_ _} f :=
    { f := fun n => P.X n ◁ f
      comm' := fun n m _ => by simpa using whisker_exchange (P.d n m) f }
  map_id _ := by ext n; simp
  map_comp _ _ := by ext n; simp

/-- Tensoring a fixed complex termwise with a module preserves coproducts. -/
theorem tensorComplexRight_preservesColimitsOfShape (J : Type u)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    PreservesColimitsOfShape (Discrete J) (tensorComplexRight A P) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun n => by
    show PreservesColimitsOfShape (Discrete J) (tensorLeft (P.X n))
    infer_instance)

/-! ### The vanishing statement -/

/-- The degree-`i` cohomology of `N[0] ⊗ᴸ M[0]` is the degree-`i` cohomology of the termwise
tensor product of a bounded-above flat resolution of `N` with `M`. -/
@[sga "4½ Rapport 4.1" "special case"]
private def derivedTensorHomologyIsoOfFlat
    {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (hbounded : ∃ n : ℤ, ∀ j : ℤ, n < j → IsZero (P.X j))
    (hflat : ∀ j : ℤ, Module.Flat A (P.X j)) {N : ModuleCat.{u} A}
    (eP : DerivedCategory.Q.obj P ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)
    (M : ModuleCat.{u} A) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (((canonicalDerivedTensorProductFunctor A).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) ≅
      ((tensorComplexRight A P).obj M).homology i :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso
      (((canonicalDerivedTensorProductFunctor A).mapIso eP.symm).app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) ≪≫
    StacksDraft.TorAmplitude.certifiedTensorHomologyIsoOfFlat
      (StacksDraft.TorAmplitude.canonicalTensorComparison A)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived A) P hbounded hflat M i

/-- **The derived tensor product against a coproduct.** If `H ⁱ(E j[0] ⊗ᴸ N[0])` vanishes for
every `j`, then so does `H ⁱ((∐ E)[0] ⊗ᴸ N[0])`. -/
theorem isZero_derivedTensorHomology_coprod_single {J : Type u} (E : J → ModuleCat.{u} A)
    (N : ModuleCat.{u} A) (i : ℤ)
    (h : ∀ j : J, IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (((canonicalDerivedTensorProductFunctor A).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (E j))).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)))) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (((canonicalDerivedTensorProductFunctor A).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (∐ E))).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N))) := by
  classical
  let Q := ProjectiveResolution.of N
  let P := Q.cochainComplex
  have hbounded : ∃ n : ℤ, ∀ j : ℤ, n < j → IsZero (P.X j) :=
    ⟨0, fun j hj => CochainComplex.isZero_of_isStrictlyLE P 0 j hj⟩
  have hflat : ∀ j : ℤ, Module.Flat A (P.X j) := by
    intro j
    have : Module.Projective A (P.X j) := ModuleCat.projective_of_module_projective _
    infer_instance
  let eP : DerivedCategory.Q.obj P ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N :=
    asIso (DerivedCategory.Q.map Q.π')
  have hiso : ∀ M : ModuleCat.{u} A,
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          (((canonicalDerivedTensorProductFunctor A).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)) ≅
        ((tensorComplexRight A P).obj M).homology i :=
    fun M => (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso
      (derivedTensorProductCommIso _ _) ≪≫
        derivedTensorHomologyIsoOfFlat A hbounded hflat eP M i
  have hz : ∀ j : J, IsZero (((tensorComplexRight A P).obj (E j)).homology i) := fun j =>
    IsZero.of_iso (h j) (hiso (E j)).symm
  have h1 := tensorComplexRight_preservesColimitsOfShape A J P
  have h2 := homologyFunctor_preservesColimitsOfShape (𝒜 := ModuleCat.{u} A)
    (J := Discrete J) (ComplexShape.up ℤ) i
  let G := tensorComplexRight A P ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) i
  have hcop : IsZero (G.obj (∐ E)) :=
    IsZero.of_iso (isZero_colimit_of_isZero _ (fun j => hz j.as))
      (preservesColimitIso G (Discrete.functor E))
  exact IsZero.of_iso hcop (hiso (∐ E))

/-- **The derived tensor product against a direct sum of copies of one module.** If
`H ⁱ(E[0] ⊗ᴸ N[0])` vanishes and `M` is a direct sum of copies of `E`, then
`H ⁱ(M[0] ⊗ᴸ N[0])` vanishes. -/
theorem isZero_derivedTensorHomology_directSum_single {J : Type u} (E : Type u)
    [AddCommGroup E] [Module A E] (M N : ModuleCat.{u} A)
    (e : M ≃ₗ[A] DirectSum J (fun _ : J => E)) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (((canonicalDerivedTensorProductFunctor A).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A E))).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)))) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (((canonicalDerivedTensorProductFunctor A).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N))) := by
  classical
  have hsum := isZero_derivedTensorHomology_coprod_single A (fun _ : J => ModuleCat.of A E) N i
    (fun _ => h)
  refine IsZero.of_iso hsum ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso
    (((canonicalDerivedTensorProductFunctor A).mapIso
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso
        (e.toModuleIso ≪≫ (ModuleCat.coprodIsoDirectSum
          (fun _ : J => ModuleCat.of A E)).symm))).app _))

end Stacks.DerivedTensor

end
