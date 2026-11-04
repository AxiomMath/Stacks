module

public import StacksFrontier.RingTheory.LocalCohomology.CechFormula.Basic
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Local cohomology and derived tensor products

For a finitely generated ideal `I` of a commutative ring `A`, local cohomology with support in
`V(I)` commutes with derived tensor product in either variable:

$$ RΓ_Z(K \otimes^{\mathbf L}_A L) \;=\; K \otimes^{\mathbf L}_A RΓ_Z(L)
   \;=\; RΓ_Z(K) \otimes^{\mathbf L}_A L
   \;=\; RΓ_Z(K) \otimes^{\mathbf L}_A RΓ_Z(L), $$

and tensoring a complex whose cohomology is `I`-power torsion with anything again gives such a
complex. The identities are stated as natural isomorphisms of bifunctors joining successive
terms of the chain.

## Main definitions

* `Stacks.LocalCohomology.CechFormula.localCohomologyEndofunctor` — local cohomology as an
  endofunctor of `D(A)`.
* `Stacks.LocalCohomology.CechFormula.derivedTensorProductBifunctor` — the canonical derived
  tensor product as a bifunctor out of `D(A) × D(A)`.

## Main results

* `Stacks.LocalCohomology.CechFormula.localCohomology_derivedTensorProduct_right` and
  `..._left` — the natural tensor-compatibility isomorphisms.
* `Stacks.LocalCohomology.CechFormula.localCohomology_derivedTensorProduct_both` — local
  cohomology in both factors agrees with local cohomology in the left factor alone.
* `Stacks.LocalCohomology.CechFormula.derivedTensorProduct_mem_powerTorsion_left` and
  `..._right` — closure of the power-torsion subcategory under tensoring on either side.

## References

* [Stacks Project, Tag 0ALY](https://stacks.math.columbia.edu/tag/0ALY)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor
open CochainComplex.DerivedTensor

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology.CechFormula

/-- **Local cohomology as an endofunctor of `D(A)`**: the coreflection onto the complexes with
`I`-power-torsion cohomology, composed with the inclusion of that subcategory. -/
abbrev localCohomologyEndofunctor
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  Dualizing.localCohomologyFunctor A I hI ⋙
    (Dualizing.derivedPowerTorsionProperty A I hI).ι

/-- The canonical derived tensor product, as a bifunctor out of the product of two copies of
`D(A)`. -/
abbrev derivedTensorProductBifunctor (A : Type u) [CommRing A] :
    DerivedCategory (ModuleCat.{u} A) × DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} A) :=
  Functor.uncurry.obj (canonicalDerivedTensorProductFunctor A)

section Formal

variable {C : Type*} [Category C]

/-- Tensoring on the left by `M`, read through the tensor bifunctor: the associator. -/
private def tensorLeftTensorIso [MonoidalCategory C] (M : C) :
    tensor C ⋙ tensorLeft M ≅ (Functor.prod (tensorLeft M) (𝟭 C)) ⋙ tensor C :=
  NatIso.ofComponents (fun X => (α_ M X.1 X.2).symm) (by
    intro X Y g
    change (M ◁ (g.1 ⊗ₘ g.2)) ≫ (α_ M Y.1 Y.2).inv =
      (α_ M X.1 X.2).inv ≫ ((M ◁ g.1) ⊗ₘ g.2)
    simpa only [id_tensorHom] using associator_inv_naturality (𝟙 M) g.1 g.2)

/-- Tensoring on the right by `M`, read through the tensor bifunctor: the associator. -/
private def tensorRightTensorIso [MonoidalCategory C] (M : C) :
    tensor C ⋙ tensorRight M ≅ (Functor.prod (𝟭 C) (tensorRight M)) ⋙ tensor C :=
  NatIso.ofComponents (fun X => α_ X.1 X.2 M) (by
    intro X Y g
    change ((g.1 ⊗ₘ g.2) ▷ M) ≫ (α_ Y.1 Y.2 M).hom =
      (α_ X.1 X.2 M).hom ≫ (g.1 ⊗ₘ (g.2 ▷ M))
    simpa only [tensorHom_id] using associator_naturality g.1 g.2 (𝟙 M))

/-- An endofunctor identified with tensoring by `M` moves into the left factor of any bifunctor
identified with the monoidal product. -/
private def tensorLeftCompatibility [MonoidalCategory C]
    (B : C × C ⥤ C) (F : C ⥤ C) (M : C)
    (b : B ≅ tensor C) (e : F ≅ tensorLeft M) :
    B ⋙ F ≅ (Functor.prod F (𝟭 C)) ⋙ B :=
  isoWhiskerRight b F ≪≫ isoWhiskerLeft (tensor C) e ≪≫ tensorLeftTensorIso M ≪≫
    isoWhiskerRight (NatIso.prod e.symm (Iso.refl (𝟭 C))) (tensor C) ≪≫
    isoWhiskerLeft (Functor.prod F (𝟭 C)) b.symm

/-- The same, into the right factor; the braiding converts left tensoring into right
tensoring. -/
private def tensorRightCompatibility [MonoidalCategory C] [BraidedCategory C]
    (B : C × C ⥤ C) (F : C ⥤ C) (M : C)
    (b : B ≅ tensor C) (e : F ≅ tensorLeft M) :
    B ⋙ F ≅ (Functor.prod (𝟭 C) F) ⋙ B := by
  let e' := e ≪≫ BraidedCategory.tensorLeftIsoTensorRight M
  exact isoWhiskerRight b F ≪≫ isoWhiskerLeft (tensor C) e' ≪≫ tensorRightTensorIso M ≪≫
    isoWhiskerRight (NatIso.prod (Iso.refl (𝟭 C)) e'.symm) (tensor C) ≪≫
    isoWhiskerLeft (Functor.prod (𝟭 C) F) b.symm

/-- **A coreflection is idempotent**: `R ⋙ L ≅ (R ⋙ L) ⋙ (R ⋙ L)`. -/
private def coreflectorIdempotentIso {D : Type*} [Category D]
    (L : C ⥤ D) (R : D ⥤ C) [L.Full] [L.Faithful] (adj : L ⊣ R) :
    R ⋙ L ≅ (R ⋙ L) ⋙ (R ⋙ L) :=
  NatIso.ofComponents (fun X => L.mapIso (asIso (adj.unit.app (R.obj X)))) (by
    intro X Y g
    simpa only [Functor.comp_map, Functor.mapIso_hom, asIso_hom,
      ← Functor.map_comp, Functor.id_map] using
      congrArg L.map (adj.unit.naturality (R.map g)))

/-- Uncurrying the curried monoidal product gives back the tensor bifunctor. -/
private def uncurryTensorIso [MonoidalCategory C] :
    Functor.uncurry.obj (curriedTensor C) ≅ tensor C :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y g
    simp only [Functor.uncurry_obj_map, curriedTensor_map_app, curriedTensor_obj_map,
      tensor_map, tensorHom_def, Iso.refl_hom, Category.comp_id, Category.id_comp])

/-- Applying an idempotent endofunctor in both factors of a bifunctor agrees with applying it in
the left factor alone. -/
private def tensorBothCompatibility
    (B : C × C ⥤ C) (F : C ⥤ C)
    (er : B ⋙ F ≅ (Functor.prod (𝟭 C) F) ⋙ B)
    (el : B ⋙ F ≅ (Functor.prod F (𝟭 C)) ⋙ B)
    (ee : F ≅ F ⋙ F) :
    (Functor.prod F (𝟭 C)) ⋙ B ≅ (Functor.prod F F) ⋙ B :=
  isoWhiskerRight (NatIso.prod ee (Iso.refl (𝟭 C))) B ≪≫
    (isoWhiskerLeft (Functor.prod F (𝟭 C)) el).symm ≪≫
    isoWhiskerLeft (Functor.prod F (𝟭 C)) er

end Formal

/-- **The two tensor-compatibility isomorphisms of local cohomology**, moving local cohomology of
a derived tensor product into the right, resp. the left, factor. -/
private def localCohomologyTensorCompatibility
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    (derivedTensorProductBifunctor A ⋙ localCohomologyEndofunctor A I hI ≅
      (Functor.prod (𝟭 _) (localCohomologyEndofunctor A I hI)) ⋙
        derivedTensorProductBifunctor A) ×
    (derivedTensorProductBifunctor A ⋙ localCohomologyEndofunctor A I hI ≅
      (Functor.prod (localCohomologyEndofunctor A I hI) (𝟭 _)) ⋙
        derivedTensorProductBifunctor A) := by
  apply Classical.choice
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  obtain ⟨m, s, t, -⟩ :=
    DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory A
  let := m
  let := s
  let C := cechRegularObject.{u, u} f
  let e : localCohomologyEndofunctor A I hI ≅ tensorLeft C :=
    localCohomologyCechIso A I hI f hf ≪≫ (t.app C).symm
  let b : derivedTensorProductBifunctor A ≅ tensor (DerivedCategory (ModuleCat.{u} A)) :=
    Functor.uncurry.mapIso t.symm ≪≫ uncurryTensorIso
  exact ⟨tensorRightCompatibility _ _ C b e, tensorLeftCompatibility _ _ C b e⟩

/-- An object isomorphic to a local cohomology object has `I`-power-torsion cohomology. -/
private theorem powerTorsion_of_iso_localCohomology
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    {K L : DerivedCategory (ModuleCat.{u} A)}
    (e : (localCohomologyEndofunctor A I hI).obj K ≅ L) :
    Dualizing.derivedPowerTorsionProperty A I hI L := fun i =>
  (Dualizing.powerTorsionModuleProperty A I hI).prop_of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso e)
    (((Dualizing.localCohomologyFunctor A I hI).obj K).property i)

/-- On a power-torsion object the unit of the local-cohomology adjunction is invertible, so the
object is its own local cohomology. -/
private def powerTorsionLocalCohomologyIso
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : Dualizing.derivedPowerTorsionProperty A I hI K) :
    K ≅ (localCohomologyEndofunctor A I hI).obj K :=
  (Dualizing.derivedPowerTorsionProperty A I hI).ι.mapIso
    (asIso ((Dualizing.localCohomologyAdjunction A I hI).unit.app ⟨K, hK⟩))

/-- Local cohomology of a derived tensor product is naturally the tensor product
with local cohomology in the right variable. -/
@[stacks 0ALY "local cohomology on the right"]
def localCohomology_derivedTensorProduct_right
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    derivedTensorProductBifunctor A ⋙ localCohomologyEndofunctor A I hI ≅
      (Functor.prod (𝟭 _) (localCohomologyEndofunctor A I hI)) ⋙
        derivedTensorProductBifunctor A :=
  Classical.choice (by exact ⟨(localCohomologyTensorCompatibility A I hI).1⟩)

/-- Tensoring local cohomology in the right variable is naturally isomorphic to
tensoring it in the left variable. -/
@[stacks 0ALY "local cohomology on the left"]
def localCohomology_derivedTensorProduct_left
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    (Functor.prod (𝟭 _) (localCohomologyEndofunctor A I hI)) ⋙
        derivedTensorProductBifunctor A ≅
      (Functor.prod (localCohomologyEndofunctor A I hI) (𝟭 _)) ⋙
        derivedTensorProductBifunctor A :=
  Classical.choice (by
    exact ⟨(localCohomologyTensorCompatibility A I hI).1.symm ≪≫
      (localCohomologyTensorCompatibility A I hI).2⟩)

/-- Applying local cohomology in both tensor factors is naturally equivalent to
applying it in just the left factor. -/
@[stacks 0ALY "local cohomology in both factors"]
def localCohomology_derivedTensorProduct_both
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    (Functor.prod (localCohomologyEndofunctor A I hI) (𝟭 _)) ⋙
        derivedTensorProductBifunctor A ≅
      (Functor.prod (localCohomologyEndofunctor A I hI)
        (localCohomologyEndofunctor A I hI)) ⋙
        derivedTensorProductBifunctor A :=
  Classical.choice (by
    exact ⟨tensorBothCompatibility _ _
      (localCohomologyTensorCompatibility A I hI).1
      (localCohomologyTensorCompatibility A I hI).2
      (coreflectorIdempotentIso _ _
        (Dualizing.localCohomologyAdjunction A I hI))⟩)

/-- Tensoring on the right preserves a complex with `I`-power-torsion
cohomology. -/
@[stacks 0ALY "torsion in the left factor"]
theorem derivedTensorProduct_mem_powerTorsion_left
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (K L : DerivedCategory (ModuleCat.{u} A))
    (hK : Dualizing.derivedPowerTorsionProperty A I hI K) :
    Dualizing.derivedPowerTorsionProperty A I hI
      ((derivedTensorProductBifunctor A).obj (K, L)) := by
  exact powerTorsion_of_iso_localCohomology A I hI
    ((localCohomologyTensorCompatibility A I hI).2.app (K, L) ≪≫
      (derivedTensorProductBifunctor A).mapIso
        ((powerTorsionLocalCohomologyIso A I hI K hK).symm.prod (Iso.refl L)))

/-- Tensoring on the left preserves a complex with `I`-power-torsion
cohomology. -/
@[stacks 0ALY "torsion in the right factor"]
theorem derivedTensorProduct_mem_powerTorsion_right
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (K L : DerivedCategory (ModuleCat.{u} A))
    (hL : Dualizing.derivedPowerTorsionProperty A I hI L) :
    Dualizing.derivedPowerTorsionProperty A I hI
      ((derivedTensorProductBifunctor A).obj (K, L)) := by
  exact powerTorsion_of_iso_localCohomology A I hI
    ((localCohomologyTensorCompatibility A I hI).1.app (K, L) ≪≫
      (derivedTensorProductBifunctor A).mapIso
        ((Iso.refl K).prod (powerTorsionLocalCohomologyIso A I hI L hL).symm))

end Stacks.LocalCohomology.CechFormula
