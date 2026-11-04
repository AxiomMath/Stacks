module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePointUniverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.Homology.KFlat.BifunctorLocalization

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AbelianTensor.InverseImageMonoidal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AbelianTensor.Flat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AbelianTensor.Additive
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedStalkLeftAdjoint
public import StacksFrontier.CategoryTheory.Sites.Point.SkyscraperSection
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
public import StacksFrontier.Homology.KFlat.TransportKFlat
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Sites.Point.Monoidal

/-!
# Stalks and inverse images of abelian étale sheaves preserve K-flatness

For the tensor product of abelian sheaves on small étale sites
(`Stacks.EtaleCohomology.etaleAbelianTensor`) and of abelian groups, this file proves:

* the stalk functor at a point of the small étale site (relative to the coefficient universe) is
  monoidal (Mathlib) and carries complexes K-flat for the tensor product of sheaves to complexes
  K-flat for the tensor product of abelian groups ([Stacks, Tag 06YB]), in both variables;
* a complex of abelian étale sheaves all of whose stalks at the residue geometric points are
  K-flat is K-flat;
* consequently the inverse image `f⁻¹` along a morphism of schemes carries K-flat complexes to
  K-flat complexes ([Stacks, Tag 06YC]), in both variables, and flat sheaves to flat sheaves.

The remaining inputs of `CochainComplex.KFlatBifunctor.derivedTransportIso` for `f⁻¹` are found by
instance search: `f⁻¹` preserves the antidiagonal coproducts of a total complex because it is a
left adjoint (`Stacks.EtaleCohomology.etaleAbelianInverseImage_isLeftAdjoint`), and the total
complexes exist by `Stacks.EtaleCohomology.etaleAbelian_hasTotal`.

## Main results

* `Stacks.EtaleCohomology.kFlat_sheafFiber_mapHomologicalComplex`,
  `Stacks.EtaleCohomology.kFlatLeft_sheafFiber_mapHomologicalComplex`: stalks preserve
  (left) K-flatness.
* `Stacks.EtaleCohomology.kFlat_of_forall_kFlat_sheafFiber`,
  `Stacks.EtaleCohomology.kFlatLeft_of_forall_kFlatLeft_sheafFiber`: (left) K-flatness is detected
  at the residue geometric points.
* `Stacks.EtaleCohomology.kFlat_etaleAbelianInverseImage_mapHomologicalComplex`,
  `Stacks.EtaleCohomology.kFlatLeft_etaleAbelianInverseImage_mapHomologicalComplex`: the inverse
  image preserves (left) K-flatness.
* `Stacks.EtaleCohomology.isFlat_etaleAbelianInverseImage_obj`: the inverse image preserves
  flatness.

## Implementation notes

The two halves are the generic statements of `StacksFrontier.Homology.KFlat.TransportKFlat`. For the
stalk the input is the retract of `StacksFrontier.CategoryTheory.Sites.Point.SkyscraperSection`: an
acyclic complex `N` of abelian groups is a retract of the stalk of its skyscraper complex, which is
acyclic because the skyscraper functor is exact (abelian groups satisfy AB4*). For the detection
the input is the conservativity of the residue geometric points of a scheme, and for the inverse
image the identification of the stalk of an inverse image at a geometric point with the stalk at
the image point (`Stacks.EtaleCohomology.etaleAbelianInverseImageSheafFiberIso`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Functor.OplaxMonoidal
open AlgebraicGeometry

universe u v

namespace Stacks.EtaleCohomology

attribute [local instance] AddCommGrpCat.monoidalCategory AddCommGrpCat.braidedCategoryGeneral
  AddCommGrpCat.monoidalClosedGeneral etaleAbelianMonoidalCategory isMonoidal_W_smallEtale

open CochainComplex.KFlatBifunctor

section Stalk

variable {X : Scheme.{u}} (Φ : GrothendieckTopology.Point.{max (u + 1) v} X.smallEtaleTopology)

/-- The stalk functor of a point of the small étale site relative to the coefficient universe is
additive, being left exact. -/
instance additive_sheafFiber_etaleAbelian :
    (Φ.sheafFiber (A := AddCommGrpCat.{max (u + 1) v})).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The skyscraper sheaf functor of a point of the small étale site is additive, being a right
adjoint. -/
instance additive_skyscraperSheafFunctor_etaleAbelian :
    (Φ.skyscraperSheafFunctor (A := AddCommGrpCat.{max (u + 1) v})).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- An acyclic complex of abelian groups is a retract of the stalk of its skyscraper complex,
which is acyclic. -/
theorem exists_retract_sheafFiber_skyscraper (N : CochainComplex AddCommGrpCat.{max (u + 1) v} ℤ)
    (hN : N.Acyclic) :
    ∃ (N' : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
      (i : N ⟶ (Φ.sheafFiber.mapHomologicalComplex (ComplexShape.up ℤ)).obj N')
      (p : (Φ.sheafFiber.mapHomologicalComplex (ComplexShape.up ℤ)).obj N' ⟶ N),
      N'.Acyclic ∧ i ≫ p = 𝟙 N := by
  refine ⟨(Φ.skyscraperSheafFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).obj N,
    { f n := Φ.skyscraperSection.app (N.X n)
      comm' i j _ := (Φ.skyscraperSection.naturality (N.d i j)).symm },
    { f n := Φ.skyscraperSheafAdjunction.counit.app (N.X n)
      comm' i j _ := (Φ.skyscraperSheafAdjunction.counit.naturality (N.d i j)).symm },
    hN.map Φ.skyscraperSheafFunctor, ?_⟩
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  exact Φ.skyscraperSection_comp_counit (N.X n)

/-- **The stalk of a K-flat complex of abelian étale sheaves is K-flat** ([Stacks, Tag 06YB]),
for the tensor product of abelian groups. The stalk functor is monoidal (Mathlib's
`CategoryTheory.GrothendieckTopology.Point.instMonoidalSheafSheafFiber`). -/
theorem kFlat_sheafFiber_mapHomologicalComplex
    (P : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    (hP : KFlat (etaleAbelianTensor.{u, v} X) P) :
    KFlat (curriedTensor AddCommGrpCat.{max (u + 1) v})
      ((Φ.sheafFiber.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  kFlat_map_of_retract_of_monoidal
    (A := Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (A' := AddCommGrpCat.{max (u + 1) v}) Φ.sheafFiber
    (exists_retract_sheafFiber_skyscraper Φ) P hP

/-- **The stalk of a left K-flat complex of abelian étale sheaves is left K-flat**
([Stacks, Tag 06YB]), for the tensor product of abelian groups. -/
theorem kFlatLeft_sheafFiber_mapHomologicalComplex
    (P : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    (hP : KFlatLeft (etaleAbelianTensor.{u, v} X) P) :
    KFlatLeft (curriedTensor AddCommGrpCat.{max (u + 1) v})
      ((Φ.sheafFiber.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  kFlatLeft_map_of_retract_of_monoidal
    (A := Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (A' := AddCommGrpCat.{max (u + 1) v}) Φ.sheafFiber
    (exists_retract_sheafFiber_skyscraper Φ) P hP

end Stalk

section Detection

variable (X : Scheme.{u})

/-- The residue geometric points of a scheme, as points of its small étale site relative to the
coefficient universe. -/
abbrev residueGeometricPointsUnconditional :
    ObjectProperty (GrothendieckTopology.Point.{max (u + 1) v} X.smallEtaleTopology) :=
  ObjectProperty.ofObj
    (fun x : X ↦ (Scheme.pointSmallEtale (residueGeometricPoint X x)).ulift.{max (u + 1) v})

/-- The residue geometric points of a scheme form a conservative family of points of its small
étale site: their images cover the scheme. -/
theorem isConservativeFamilyOfPoints_residueGeometricPoints_unconditional :
    (residueGeometricPointsUnconditional.{u, v} X).IsConservativeFamilyOfPoints :=
  Scheme.isConservative_pointSmallEtale_ulift.{v, u} (residueGeometricPoint X)
    (Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2
      ⟨x, default, residueGeometricPoint_apply X x default⟩)

variable {X}

/-- **K-flatness of a complex of abelian étale sheaves is detected at the stalks**: a complex
whose stalks at the residue geometric points are K-flat for the tensor product of abelian groups
is K-flat. -/
theorem kFlat_of_forall_kFlat_sheafFiber
    (P : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    (h : ∀ x : X, KFlat (curriedTensor AddCommGrpCat.{max (u + 1) v})
      ((((Scheme.pointSmallEtale
        (residueGeometricPoint X x)).ulift.{max (u + 1) v}).sheafFiber.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)) :
    KFlat (etaleAbelianTensor.{u, v} X) P :=
  kFlat_of_forall_kFlat_map_of_monoidal
    (A := Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (A' := AddCommGrpCat.{max (u + 1) v})
    (fun Ψ : (residueGeometricPointsUnconditional.{u, v} X).FullSubcategory ↦ Ψ.obj.sheafFiber)
    ((isConservativeFamilyOfPoints_residueGeometricPoints_unconditional
      X).jointlyReflectIsomorphisms
      AddCommGrpCat.{max (u + 1) v}) P (by rintro ⟨_, ⟨x⟩⟩; exact h x)

/-- **Left K-flatness of a complex of abelian étale sheaves is detected at the stalks.** -/
theorem kFlatLeft_of_forall_kFlatLeft_sheafFiber
    (P : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    (h : ∀ x : X, KFlatLeft (curriedTensor AddCommGrpCat.{max (u + 1) v})
      ((((Scheme.pointSmallEtale
        (residueGeometricPoint X x)).ulift.{max (u + 1) v}).sheafFiber.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)) :
    KFlatLeft (etaleAbelianTensor.{u, v} X) P :=
  kFlatLeft_of_forall_kFlatLeft_map_of_monoidal
    (A := Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (A' := AddCommGrpCat.{max (u + 1) v})
    (fun Ψ : (residueGeometricPointsUnconditional.{u, v} X).FullSubcategory ↦ Ψ.obj.sheafFiber)
    ((isConservativeFamilyOfPoints_residueGeometricPoints_unconditional
      X).jointlyReflectIsomorphisms
      AddCommGrpCat.{max (u + 1) v}) P (by rintro ⟨_, ⟨x⟩⟩; exact h x)

end Detection

section InverseImage

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The stalk at a geometric point `s` of `X` of the inverse image along `f` of a complex of
abelian étale sheaves is the stalk of that complex at `s ≫ f`. -/
noncomputable def sheafFiberInverseImageComplexIso {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X)
    (P : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ) :
    ((((Scheme.pointSmallEtale (s ≫ f)).ulift.{max (u + 1) v}).sheafFiber.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) ≅
      ((((Scheme.pointSmallEtale s).ulift.{max (u + 1) v}).sheafFiber.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          (((etaleAbelianInverseImage.{u, v} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)) :=
  ((Functor.mapHomologicalComplexCompIso (etaleAbelianInverseImageSheafFiberIso.{u, v} f s)
      (ComplexShape.up ℤ)).app P).symm

/-- **The inverse image of a K-flat complex of abelian étale sheaves is K-flat**
([Stacks, Tag 06YC]), for the tensor products of abelian étale sheaves: its stalk at a geometric
point is the stalk of the complex at the image point, which is K-flat. -/
theorem kFlat_etaleAbelianInverseImage_mapHomologicalComplex
    (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    (hK : KFlat (etaleAbelianTensor.{u, v} Y) K) :
    KFlat (etaleAbelianTensor.{u, v} X)
      (((etaleAbelianInverseImage.{u, v} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  kFlat_of_forall_kFlat_sheafFiber _ fun x ↦
    KFlat.of_iso _ (kFlat_sheafFiber_mapHomologicalComplex
      ((Scheme.pointSmallEtale (residueGeometricPoint X x ≫ f)).ulift.{max (u + 1) v}) K hK)
      (sheafFiberInverseImageComplexIso f (residueGeometricPoint X x) K)

/-- **The inverse image of a left K-flat complex of abelian étale sheaves is left K-flat**
([Stacks, Tag 06YC]). -/
theorem kFlatLeft_etaleAbelianInverseImage_mapHomologicalComplex
    (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    (hK : KFlatLeft (etaleAbelianTensor.{u, v} Y) K) :
    KFlatLeft (etaleAbelianTensor.{u, v} X)
      (((etaleAbelianInverseImage.{u, v} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  kFlatLeft_of_forall_kFlatLeft_sheafFiber _ fun x ↦ by
    have h := kFlatLeft_sheafFiber_mapHomologicalComplex
      ((Scheme.pointSmallEtale (residueGeometricPoint X x ≫ f)).ulift.{max (u + 1) v}) K hK
    rw [kFlatLeft_iff_kFlat_flip] at h ⊢
    exact KFlat.of_iso _ h (sheafFiberInverseImageComplexIso f (residueGeometricPoint X x) K)

/-- **The inverse image of a flat abelian étale sheaf is flat**: flatness is torsion-freeness
(`Stacks.EtaleCohomology.isFlat_iff_mono_zsmul`), and the inverse image is additive and preserves
monomorphisms. -/
theorem isFlat_etaleAbelianInverseImage_obj
    {F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (hF : IsFlat F) :
    IsFlat ((etaleAbelianInverseImage.{u, v} f).obj F) := by
  rw [isFlat_iff_mono_zsmul] at hF ⊢
  intro n hn
  have := hF n hn
  rw [← (etaleAbelianInverseImage.{u, v} f).map_id, ← Functor.map_zsmul]
  infer_instance

end InverseImage

end Stacks.EtaleCohomology
