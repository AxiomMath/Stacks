module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.AlgebraicGeometry.Modules.TildeKFlat
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.AffineTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.TotalComplexTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.OnARingedSpace
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.Homology.KFlat.ChosenResolution

/-!
# The derived tensor product of associated complexes on an affine scheme

Let `R` be a commutative ring and `X = Spec R`. Sheafification `M ↦ M̃` carries a complex `M^•`
of `R`-modules to a complex `M̃^•` of `𝒪_X`-modules, and the exactness of `M ↦ M̃` makes this
descend to a functor `D(R) ⥤ D(𝒪_X)`. This file proves that derived sheafification is monoidal
for the two derived tensor products: for `M^•, K^•` in `D(R)` there is a canonical isomorphism

`M̃^• ⊗_{𝒪_X}^{L} K̃^•  ≅  (M^• ⊗_R^{L} K^•)~`

for each pair of objects of `D(R)`.

The isomorphism is not an arbitrary one. Both arguments are replaced by K-flat representatives,
where both derived tensor products are computed by ordinary total tensor complexes, and there the
comparison is the totalisation of the degreewise affine comparison
`(M ⊗_R N)~ ≅ M̃ ⊗_{𝒪_X} Ñ` of [Stacks, Tag 01I8]. The representatives are supplied by definite
choices, so the construction is a function of its two arguments.

## Main definitions

* `AlgebraicGeometry.affineTensorComplexIso` is the totalised ordinary tensor comparison
  `(Tot(M^• ⊗_R K^•))~ ≅ Tot(M̃^• ⊗_{𝒪_X} K̃^•)`, together with the formula for its value on
  each tensor summand. The summand formula is carried in the type, as a subtype, because it is
  what singles the isomorphism out among all isomorphisms of those two complexes.
* `AlgebraicGeometry.affineDerivedTensorIso` is the comparison isomorphism of [Stacks, Tag 08DX,
  part (2)] for two objects of `D(R)`.
* `AlgebraicGeometry.tildeDS` is derived sheafification with the module side read at the standard
  model of `D(R)`, which is the model the derived tensor product of `R`-modules is stated at.

## Main results

`AlgebraicGeometry.affineDerivedTensorIso` is the displayed identification of the source's
part (2), one isomorphism for each pair of objects of `D(R)`. It is stated objectwise rather than
as an isomorphism of bifunctors: the two derived tensor products involved are stated at two
different models of `D(R)` (see the implementation notes).

## Implementation notes

The source states part (2) as an equality of objects of `D(𝒪_X)`. An equality of objects is not
available in a formalisation where the two are built differently, so it is expressed here as an
isomorphism; what makes that faithful rather than weaker is naturality together with the K-flat
normalisation, since an isomorphism natural in both variables and prescribed on K-flat
representatives is unique.

Two spellings of the category of `𝒪_{Spec R}`-modules meet in this statement. Mathlib's
`AlgebraicGeometry.tilde.functor` lands in `AlgebraicGeometry.Scheme.Modules`, an opaque
definition carrying its own category instance, whereas the tensor product of sheaves of modules
and K-flatness are stated for `SheafOfModules` over `Stacks.SheafOfModules.Tensor.ringSheaf`.
The two agree, but only at default transparency, so a rewrite in a goal mentioning both can
produce a term that is not type-correct at the transparency `rewrite` builds its motive at.
Retyping sheafification once through the reducible abbreviation
`AlgebraicGeometry.SpecModules` — the private `tildeF` below — puts every expression of the
degreewise comparison in a single category with a single instance, and that is what lets the
file be written without relaxing transparency anywhere. The same reason explains why the
structure sheaf is named by `AlgebraicGeometry.specCommRingSheaf` rather than by `(Spec R).sheaf`:
the latter is wrapped in `TopCat.Sheaf`, which is again opaque.

The totalisation of the degreewise comparison is `CategoryTheory.Functor.mapBifunctorTotalIso`,
instantiated at sheafification in all three variables, at the tensor bifunctor
`MonoidalCategory.curriedTensor (ModuleCat R)` of modules and at the tensor bifunctor
`Stacks.SheafOfModules.Tensor.sheafTensor` of sheaves of modules. Its two hypotheses are the two
one-sided halves of the naturality of [Stacks, Tag 01I8], obtained from the two-sided statement
`AlgebraicGeometry.tildeTensorIso_natural` by setting one argument to an identity; that
two-sided statement is phrased with `AlgebraicGeometry.tildeTensorSheafMap`, and
`tildeTensorSheafMap_eq` below identifies it with the composite of the two one-sided maps of
`sheafTensor`, which for a curried monoidal product is exactly
`MonoidalCategory.tensorHom_def`. Sheafification preserves the antidiagonal coproducts occurring
in the total complex because it is a left adjoint.

**Two models of `D(R)` meet here, and that is why the comparison is objectwise.** The derived
tensor product of `R`-modules, `CochainComplex.DerivedTensor.canonicalDerivedTensorProduct`, is
stated at the *standard* model: its carrier `CochainComplex.DerivedTensor.DObj` elaborates to
`DerivedCategory.{u + 1, u, u + 1} (ModuleCat.{u} R)`, as one sees from the universes of
`canonicalDerivedTensorProductFunctor`, whose type is
`Functor.{u + 1, u + 1, u + 1, u + 1} (DObj R) _`. The derived tensor product of sheaves,
`Stacks.Cohomology.TorAmplitude.derTensor`, and the sheaf side of derived sheafification resolve
instead at the locally small model `HasDerivedCategory.{u}`. An object-level statement crosses the
two freely, because `CategoryTheory.Functor.obj` does not mention the `Category` instance; a
statement using `.map` on the module side does not.

`AlgebraicGeometry.tildeDS` therefore reads derived sheafification as
`(tilde.functor R).mapDerivedCategory.{u + 1, u}` — module side standard, sheaf side locally
small — and the module-side instance is supplied by the `scoped instance`
`AlgebraicGeometry.StandardDerivedModuleCat.hasDerivedCategory`. A bare
`attribute [local instance] HasDerivedCategory.standard` does not serve: once the locally small
instance `ModuleCat.hasDerivedCategory` is in scope, `HasDerivedCategory.{u + 1} (ModuleCat.{u} R)`
is not synthesizable from it. The instance is `scoped` so that no importer has it in scope, where
it would compete with the locally small model that [Stacks, Tag 06Z0] and
`Stacks.Duality.quasiCoherentDerivedTensor` require; it is public rather than private because it
appears in the instance argument of `tildeDS`.

## References

* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08DV](https://stacks.math.columbia.edu/tag/08DV)
* [Stacks Project, Tag 0BYI](https://stacks.math.columbia.edu/tag/0BYI)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Functor Stacks.SheafOfModules.Tensor

universe u

attribute [local instance] Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor

namespace AlgebraicGeometry

/-! ### The degreewise comparison, read in one category -/

/-- Sheafification `M ↦ M̃` on `Spec R`, read as a functor into `AlgebraicGeometry.SpecModules R`,
the spelling of the category of `𝒪_{Spec R}`-modules in which the tensor product of sheaves of
modules is defined. -/
private abbrev tildeF (R : CommRingCat.{u}) : ModuleCat.{u} R ⥤ SpecModules R :=
  tilde.functor R

private instance tildeF_additive (R : CommRingCat.{u}) : (tildeF R).Additive :=
  inferInstanceAs (tilde.functor R).Additive

private instance tildeF_preservesCoproducts (R : CommRingCat.{u}) (n : ℤ) :
    PreservesColimitsOfShape
      (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⁻¹' {n})) (tildeF R) :=
  inferInstanceAs (PreservesColimitsOfShape
      (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⁻¹' {n})) (tilde.functor R))

/-- The complex of `𝒪_{Spec R}`-modules associated degreewise to a complex of `R`-modules. -/
private abbrev tildeC (R : CommRingCat.{u}) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (SpecModules R) ℤ :=
  (tildeF R).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The map of tensor-product sheaves induced by two module maps is the composite of the two
one-sided tensor maps of `Stacks.SheafOfModules.Tensor.sheafTensor`. The tensor product of
sheaves of modules is a sheafified curried monoidal product, so this is
`MonoidalCategory.tensorHom_def` for presheaves of modules with sheafification applied. -/
private lemma tildeTensorSheafMap_eq (R : CommRingCat.{u}) {M M' N N' : ModuleCat.{u} R}
    (f : M ⟶ M') (g : N ⟶ N') :
    tildeTensorSheafMap R f g =
      ((sheafTensor.{u, u, u, u, u} (specCommRingSheaf R)).map
          ((tildeF R).map f)).app ((tildeF R).obj N) ≫
        ((sheafTensor.{u, u, u, u, u} (specCommRingSheaf R)).obj ((tildeF R).obj M')).map
          ((tildeF R).map g) := by
  have key : ((PresheafOfModules.tensorBifunctor.{u, u, u, u, u} (specCommRingSheaf R).obj).map
          (tilde.map f).val).app (tilde N).val ≫
        ((PresheafOfModules.tensorBifunctor.{u, u, u, u, u}
          (specCommRingSheaf R).obj).obj (tilde M').val).map
          (tilde.map g).val =
      PresheafOfModules.Monoidal.tensorHom (R := (Spec R).presheaf)
        (tilde.map f).val (tilde.map g).val :=
    (MonoidalCategory.tensorHom_def
      (C := PresheafOfModules.{u} ((Spec R).presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
      (tilde.map f).val (tilde.map g).val).symm
  exact (congrArg (PresheafOfModules.sheafification.{u}
      (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf (specCommRingSheaf R)).obj)
      (R := Stacks.SheafOfModules.Tensor.ringSheaf (specCommRingSheaf R))
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (specCommRingSheaf R)).obj)).map
    key.symm).trans (Functor.map_comp _ _ _)

/-- The affine tensor comparison of [Stacks, Tag 01I8], read as an isomorphism between the two
tensor bifunctors transported by sheafification. -/
private def tildeTensorIsoF (R : CommRingCat.{u}) (M N : ModuleCat.{u} R) :
    (tildeF R).obj (((curriedTensor (ModuleCat.{u} R)).obj M).obj N) ≅
      ((sheafTensor.{u, u, u, u, u} (specCommRingSheaf R)).obj ((tildeF R).obj M)).obj
        ((tildeF R).obj N) :=
  tildeTensorIso R M N

private lemma tildeTensorIsoF_natural (R : CommRingCat.{u}) {M M' N N' : ModuleCat.{u} R}
    (f : M ⟶ M') (g : N ⟶ N') :
    (tildeF R).map (f ⊗ₘ g) ≫ (tildeTensorIsoF R M' N').hom =
      (tildeTensorIsoF R M N).hom ≫
        (((sheafTensor.{u, u, u, u, u} (specCommRingSheaf R)).map
            ((tildeF R).map f)).app ((tildeF R).obj N) ≫
          ((sheafTensor.{u, u, u, u, u} (specCommRingSheaf R)).obj ((tildeF R).obj M')).map
            ((tildeF R).map g)) := by
  rw [← tildeTensorSheafMap_eq]
  exact tildeTensorIso_natural R f g

private lemma tildeTensorIsoF_naturality_left (R : CommRingCat.{u})
    {M M' : ModuleCat.{u} R} (f : M ⟶ M') (N : ModuleCat.{u} R) :
    (tildeF R).map (((curriedTensor (ModuleCat.{u} R)).map f).app N) ≫
        (tildeTensorIsoF R M' N).hom =
      (tildeTensorIsoF R M N).hom ≫
        ((sheafTensor.{u, u, u, u, u} (specCommRingSheaf R)).map
          ((tildeF R).map f)).app ((tildeF R).obj N) := by
  have h := tildeTensorIsoF_natural R f (𝟙 N)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id] at h
  rwa [MonoidalCategory.tensorHom_id] at h

private lemma tildeTensorIsoF_naturality_right (R : CommRingCat.{u}) (M : ModuleCat.{u} R)
    {N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    (tildeF R).map (((curriedTensor (ModuleCat.{u} R)).obj M).map g) ≫
        (tildeTensorIsoF R M N').hom =
      (tildeTensorIsoF R M N).hom ≫
        ((sheafTensor.{u, u, u, u, u} (specCommRingSheaf R)).obj ((tildeF R).obj M)).map
          ((tildeF R).map g) := by
  have h := tildeTensorIsoF_natural R (𝟙 M) g
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp] at h
  rwa [MonoidalCategory.id_tensorHom] at h

/-! ### The totalised ordinary comparison -/

private abbrev affineTotalIso (R : CommRingCat.{u})
    (M K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (tildeC R).obj (M ⊗ K) ≅
      ((tensorComplex.{u, u, u} (specCommRingSheaf R)).obj ((tildeC R).obj M)).obj
        ((tildeC R).obj K) :=
  Functor.mapBifunctorTotalIso (curriedTensor (ModuleCat.{u} R))
    (sheafTensor.{u, u, u, u, u} (specCommRingSheaf R)) (tildeF R) (tildeF R) (tildeF R)
    (tildeTensorIsoF R) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (tildeTensorIsoF_naturality_left R) (tildeTensorIsoF_naturality_right R) M K

/-- **The totalised affine tensor comparison.** For complexes `M^•` and `K^•` of `R`-modules, the
complex of `𝒪_{Spec R}`-modules associated to the total tensor complex `Tot(M^• ⊗_R K^•)` is
canonically the total tensor complex `Tot(M̃^• ⊗_{𝒪_{Spec R}} K̃^•)` of the associated complexes.

The isomorphism is returned together with the formula for its value on the summand of total
degree `n` indexed by `(i, j)`: there it is the degreewise comparison
`AlgebraicGeometry.tildeTensorIso` of [Stacks, Tag 01I8] at `M^i` and `K^j`. That formula
determines the isomorphism, since the source of total degree `n` is the direct sum of those
summands, so it is carried in the type rather than stated separately. -/
@[stacks 08DX "part (2): the totalised ordinary comparison", no_expose]
public def affineTensorComplexIso (R : CommRingCat.{u})
    (M K : CochainComplex (ModuleCat.{u} R) ℤ) :
    { e : tildeComplexMod (A := R) (M ⊗ K) ≅
        ((tensorComplex.{u, u, u} (specCommRingSheaf R)).obj (tildeComplexMod (A := R) M)).obj
          (tildeComplexMod (A := R) K) //
      ∀ (i j n : ℤ) (h : i + j = n),
        (tilde.functor R).map (HomologicalComplex.ιMapBifunctor M K
            (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ) i j n h) ≫ e.hom.f n =
          (tildeTensorIso R (M.X i) (K.X j)).hom ≫
            HomologicalComplex.ιMapBifunctor (tildeComplexMod (A := R) M)
              (tildeComplexMod (A := R) K)
              (sheafTensor.{u, u, u, u, u} (specCommRingSheaf R)) (ComplexShape.up ℤ) i j n h } :=
  ⟨affineTotalIso R M K, fun i j n h =>
    Functor.ι_mapBifunctorTotalIso_hom (curriedTensor (ModuleCat.{u} R))
      (sheafTensor.{u, u, u, u, u} (specCommRingSheaf R)) (tildeF R) (tildeF R) (tildeF R)
      (tildeTensorIsoF R) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (tildeTensorIsoF_naturality_left R) (tildeTensorIsoF_naturality_right R) M K i j n h⟩

/-! ### The derived comparison -/

namespace StandardDerivedModuleCat

/-- The standard model of the derived category of `R`-modules, seated as an instance. The
module-side derived tensor product of [Stacks, Tag 0BYI] is stated at this model, so a statement
relating it to the derived tensor product of sheaves must use it; it is `scoped` so that no
importer has it in scope, where it would compete with the locally small model. -/
scoped instance hasDerivedCategory (R : Type u) [CommRing R] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} R) := HasDerivedCategory.standard _

end StandardDerivedModuleCat

open scoped StandardDerivedModuleCat

/-- Derived sheafification `D(R) ⥤ D(𝒪_{Spec R})`, with the module side at the standard model
and the sheaf side at the locally small one. -/
public abbrev tildeDS (R : CommRingCat.{u}) :
    CochainComplex.DerivedTensor.DObj (R : Type u) ⥤ DerivedCategory (SpecModules R) :=
  (tilde.functor R).mapDerivedCategory.{u + 1, u}

/-- A K-flat complex representing an object of `D(R)`, together with the isomorphism.
Both `CategoryTheory.Functor.objPreimage` and `CochainComplex.KFlat.chosenResolution` are definite
choices, so this is a function and not merely an existence statement. -/
private def kFlatRep (R : CommRingCat.{u})
    (M : CochainComplex.DerivedTensor.DObj (R : Type u)) :
    Σ' P : CochainComplex (ModuleCat.{u} R) ℤ,
      PProd (CochainComplex.KFlat.{u, u} P)
        ((DerivedCategory.Q.{u + 1}).obj P ≅ M) :=
  let C := (DerivedCategory.Q.{u + 1}).objPreimage M
  let res := CochainComplex.KFlat.chosenResolution.{u, u} C
  ⟨res.complex, ⟨res.kFlat,
    haveI := res.quasiIso
    (asIso ((DerivedCategory.Q.{u + 1}).map res.π)) ≪≫
      (DerivedCategory.Q.{u + 1}).objObjPreimageIso M⟩⟩

/-- **[Stacks, Tag 08DX] part (2) on K-flat complexes.** For K-flat `P^•` and `P'^•` the derived
tensor product of the associated complexes is the complex associated to the derived tensor
product over `R`. Both derived tensor products are computed by ordinary total tensor complexes
there — on the sheaf side because `P̃^•` is K-flat by [Stacks, Tag 08DV] — and the comparison is
the totalised ordinary comparison `affineTensorComplexIso`. -/
private def affineDerivedTensorIsoOfKFlat (R : CommRingCat.{u})
    (P P' : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : CochainComplex.KFlat.{u, u} P) (hP' : CochainComplex.KFlat.{u, u} P') :
    (((Stacks.Cohomology.TorAmplitude.derTensor.{u, u} (Spec R).toRingedSpace).tensor.obj
          ((tildeDS R).obj ((DerivedCategory.Q.{u + 1}).obj P))).obj
        ((tildeDS R).obj ((DerivedCategory.Q.{u + 1}).obj P'))) ≅
      (tildeDS R).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
          (R : Type u)).tensor.obj ((DerivedCategory.Q.{u + 1}).obj P)).obj
            ((DerivedCategory.Q.{u + 1}).obj P') ) :=
  ((Stacks.Cohomology.TorAmplitude.derTensor.{u, u} (Spec R).toRingedSpace).tensor.mapIso
      ((tilde.functor R).mapDerivedCategoryFactors.{u + 1, u}.app P)).app _ ≪≫
    ((Stacks.Cohomology.TorAmplitude.derTensor.{u, u} (Spec R).toRingedSpace).tensor.obj
        ((DerivedCategory.Q.{u}).obj (tildeComplexMod (A := R) P))).mapIso
      ((tilde.functor R).mapDerivedCategoryFactors.{u + 1, u}.app P') ≪≫
    (Stacks.Cohomology.TorAmplitude.derTensor.{u, u} (Spec R).toRingedSpace).comparison _ _
      (kFlat_tilde P hP) (kFlat_tilde P' hP') ≪≫
    (DerivedCategory.Q.{u}).mapIso (affineTensorComplexIso R P P').1.symm ≪≫
    ((tilde.functor R).mapDerivedCategoryFactors.{u + 1, u}.app (P ⊗ P')).symm ≪≫
    (tildeDS R).mapIso
      ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        (R : Type u)).comparison P P' hP hP').symm

/-- **Stacks Project, Tag 08DX, part (2).** On the spectrum of a commutative ring `R`, the
derived tensor product of two associated complexes of sheaves of modules is the complex
associated to their derived tensor product over `R`:

`M̃^• ⊗_{𝒪_{Spec R}}^{L} K̃^•  ≅  (M^• ⊗_R^{L} K^•)~`.

Both arguments are replaced by K-flat representatives, where the two derived tensor products are
computed by ordinary total tensor complexes and the comparison is the totalised ordinary
comparison `affineTensorComplexIso` of [Stacks, Tag 01I8]; the representatives are supplied by
the definite choices of `kFlatRep`. -/
@[stacks 08DX "part (2): the affine comparison", no_expose]
public def affineDerivedTensorIso (R : CommRingCat.{u})
    (M K : CochainComplex.DerivedTensor.DObj (R : Type u)) :
    (((Stacks.Cohomology.TorAmplitude.derTensor.{u, u} (Spec R).toRingedSpace).tensor.obj
          ((tildeDS R).obj M)).obj ((tildeDS R).obj K)) ≅
      (tildeDS R).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
          (R : Type u)).tensor.obj M).obj K) :=
  let rP := kFlatRep R M
  let rK := kFlatRep R K
  ((Stacks.Cohomology.TorAmplitude.derTensor.{u, u} (Spec R).toRingedSpace).tensor.mapIso
      ((tildeDS R).mapIso rP.2.2.symm)).app _ ≪≫
    ((Stacks.Cohomology.TorAmplitude.derTensor.{u, u} (Spec R).toRingedSpace).tensor.obj
        ((tildeDS R).obj ((DerivedCategory.Q.{u + 1}).obj rP.1))).mapIso
      ((tildeDS R).mapIso rK.2.2.symm) ≪≫
    affineDerivedTensorIsoOfKFlat R rP.1 rK.1 rP.2.1 rK.2.1 ≪≫
    (tildeDS R).mapIso
      (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
          (R : Type u)).tensor.mapIso rP.2.2).app _ ≪≫
        ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
          (R : Type u)).tensor.obj M).mapIso rK.2.2)


end AlgebraicGeometry

end
