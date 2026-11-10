module

public import StacksFrontier.CategoryTheory.Sites.Point.QuasiIsoFibers
public import StacksFrontier.Algebra.Homology.InjectiveQuasiIsoMap
public import Mathlib.Algebra.Category.ModuleCat.Injective

/-!
# Sectionwise functors on quasi-isomorphisms of complexes with injective stalks

Let `P` be a conservative family of points of a site and `H : Mod_R ⥤ Mod_S` an additive functor
preserving limits and filtered colimits, so that applying `H` to sections defines a functor
`H_sh` on sheaves (`CategoryTheory.sheafCompose`) commuting with taking fibers. If `φ : K ⟶ L`
is a quasi-isomorphism of bounded below complexes of sheaves of `R`-modules all of whose fibers
at points of `P` are injective modules, then `H_sh(φ)` is a quasi-isomorphism, although `H` need
not be exact: on fibers, `H(φ_Φ)` is `H` applied to a quasi-isomorphism of bounded below complexes
of injective modules, which is a homotopy equivalence.

In Step 7 of the proof of [Stacks, Tag 03UG] this computes `RΓ` of `Hom_{A[G]}(M^*, f_* A)` from
an injective resolution of `f_* A`: the stalks of `f_* A` are free over the self-injective ring
`A[G]`, and the stalks of injective sheaves are injective.

## Main results

* `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.quasiIso_sheafCompose_map`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u u'

namespace CategoryTheory

/-- Applying an additive functor to sections is additive on sheaves. -/
instance sheafCompose_additive {C : Type*} [Category* C] (J : GrothendieckTopology C)
    {A B : Type*} [Category* A] [Preadditive A] [Category* B] [Preadditive B] (T : A ⥤ B)
    [T.Additive] [J.HasSheafCompose T] : (sheafCompose J T).Additive where
  map_add := by
    intro X Y f g
    ext U
    exact T.map_add

end CategoryTheory

namespace CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R S : Type u'} [Ring R]
  [Ring S] {P : ObjectProperty (GrothendieckTopology.Point.{max u' w} J)}
  (hP : P.IsConservativeFamilyOfPoints) [LocallySmall.{max u' w} C]
  [J.HasSheafCompose (forget (ModuleCat.{max u' w} S))]
  [CategoryWithHomology (Sheaf J (ModuleCat.{max u' w} S))]
  [CategoryWithHomology (Sheaf J (ModuleCat.{max u' w} R))]
  (H : ModuleCat.{max u' w} R ⥤ ModuleCat.{max u' w} S) [H.Additive] [J.HasSheafCompose H]
  [PreservesFilteredColimitsOfSize.{max u' w, max u' w} H]

include hP in
/-- **A sectionwise functor carries a quasi-isomorphism of bounded below complexes of sheaves
with injective fibers to a quasi-isomorphism.** -/
theorem quasiIso_sheafCompose_map {K L : CochainComplex (Sheaf J (ModuleCat.{max u' w} R)) ℤ}
    (φ : K ⟶ L) [QuasiIso φ] (d : ℤ) [K.IsStrictlyGE d] [L.IsStrictlyGE d]
    [∀ Φ : P.FullSubcategory, (Φ.obj.sheafFiber (A := ModuleCat.{max u' w} R)).Additive]
    [∀ Φ : P.FullSubcategory, (Φ.obj.sheafFiber (A := ModuleCat.{max u' w} S)).Additive]
    [∀ Φ : P.FullSubcategory, (Φ.obj.sheafFiber (A := ModuleCat.{max u' w} R)).PreservesHomology]
    [∀ Φ : P.FullSubcategory, (Φ.obj.sheafFiber (A := ModuleCat.{max u' w} S)).PreservesHomology]
    (hK : ∀ (Φ : P.FullSubcategory) (n : ℤ),
      Module.Injective R ((Φ.obj.sheafFiber (A := ModuleCat.{max u' w} R)).obj (K.X n)))
    (hL : ∀ (Φ : P.FullSubcategory) (n : ℤ),
      Module.Injective R ((Φ.obj.sheafFiber (A := ModuleCat.{max u' w} R)).obj (L.X n))) :
    QuasiIso (((sheafCompose J H).mapHomologicalComplex _).map φ) := by
  refine hP.quasiIso_of_sheafFiber _ fun Φ => ?_
  let F := Φ.obj.sheafFiber (A := ModuleCat.{max u' w} R)
  have e : Arrow.mk (((Φ.obj.sheafFiber (A := ModuleCat.{max u' w} S)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (((sheafCompose J H).mapHomologicalComplex _).map φ)) ≅
      Arrow.mk ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)) :=
    ((Functor.mapArrowFunctor _ _).mapIso
      (Functor.mapHomologicalComplexCompIso (F := sheafCompose J H)
          (G := Φ.obj.sheafFiber (A := ModuleCat.{max u' w} S)) (Iso.refl _) (ComplexShape.up ℤ) ≪≫
        NatIso.mapHomologicalComplex (Φ.obj.sheafFiberCompIso H) _ ≪≫
        (Functor.mapHomologicalComplexCompIso (F := F) (G := H) (Iso.refl _)
          (ComplexShape.up ℤ)).symm)).app (Arrow.mk φ)
  rw [quasiIso_iff_of_arrow_mk_iso _ _ e]
  have : ∀ n, Injective (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).X n) :=
    fun n => @Module.injective_object_of_injective_module R _ _ _ _ (hK Φ n)
  have : ∀ n, Injective (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).X n) :=
    fun n => @Module.injective_object_of_injective_module R _ _ _ _ (hL Φ n)
  exact CochainComplex.quasiIso_map_of_injective H _ d

end CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints

end
