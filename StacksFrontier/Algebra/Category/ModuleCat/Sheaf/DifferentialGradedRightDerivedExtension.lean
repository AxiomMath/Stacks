module

public import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategoryLocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPushforward
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedKInjectiveExistence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedKInjectiveLocal
public import StacksFrontier.CategoryTheory.Functor.Derived.CoresolutionCriterion

/-!
# Right derived extensions along the derived category of a sheaf of differential graded algebras

Let `X` be a ringed site and let `A` be a sheaf of differential graded algebras on it. Every
right differential graded `A`-module admits a quasi-isomorphism into a graded injective and
K-injective one (Tag 0FT0), and such a module is local for the quasi-isomorphisms, so a functor
`T` out of `K(Mod(A, d))` has a right derived extension `RT : D(A, d) ⥤ D` along the
localization, and `RT` takes the image of a graded injective K-injective module `I` to `T(I)`.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.rightDerivedExtension` is the total right derived
  functor of `T` along the localization, with
  `SheafOfModules.DifferentialGradedModule.rightDerivedExtensionUnit` its comparison map.
* `SheafOfModules.DifferentialGradedModule.rigidRightDerivedExtension` is the same functor with
  its object map replaced by the isomorphic one whose value at the image of a graded injective
  K-injective module `I` *is* `T(I)`.

## Main results

* `SheafOfModules.DifferentialGradedModule.exists_rightDerivedExtension`: every functor out of
  `K(Mod(A, d))` has a right derived extension along the localization whose value at the image of
  a graded injective K-injective module `I` is `T(I)`.
* `SheafOfModules.DifferentialGradedModule.exists_derivedInternalHom_and_derivedPushforward`: the
  right derived extensions of homotopy-preserving functors of modules and of direct images.
* `SheafOfModules.DifferentialGradedModule.computesOnDGInjective_rigidRightDerivedExtension` and
  `SheafOfModules.DifferentialGradedModule.isDerivedPushforward_rigidRightDerivedExtension`: the
  rigidified extension of a functor of right differential graded modules inhabits
  `ComputesOnDGInjective`, and the rigidified extension of the direct image inhabits
  `IsDerivedPushforward`.

## Implementation notes

**Why the value is an equality and not an isomorphism.** The value of a right derived functor at
an object is a colimit, so it is determined only up to canonical isomorphism, whereas the source
reads off an equality `RT(I) = T(I)`. An object of `derivedCategory A` *is* a right differential
graded module — formally inverting arrows leaves the objects alone, so
`SheafOfModules.DifferentialGradedModule.derivedCategoryModule` reads it back off and the round
trip is `rfl` — so the object map may be replaced, by `CategoryTheory.Functor.copyObj`, with one
that takes the prescribed value on the nose. This changes nothing:
`SheafOfModules.DifferentialGradedModule.isoRigidRightDerivedExtension` identifies the two
functors, and the transported comparison map still exhibits the transported functor as the right
derived functor. It is the right derived twin of
`SheafOfModules.DifferentialGradedModule.rigidDerivedPullbackTensor`.

**No triangulated hypothesis.** The source states Tag 0FTN for an exact functor of triangulated
categories; neither exactness nor a triangulated structure on the target enters the argument, and
the statement below is for an arbitrary functor out of `K(Mod(A, d))`, which contains the exact
ones.

**The base and the universes.** The resolutions of Tag 0FT0 are produced over a ringed site whose
site, morphism and ring universes agree, and in the module universe `max u v w` where the category
of right differential graded modules is Grothendieck abelian; those are the standing hypotheses
here, as throughout this chapter. The source has no universes.

## References

* [Stacks Project, Tag 0FTN](https://stacks.math.columbia.edu/tag/0FTN)
* [Stacks Project, Tag 0FTP](https://stacks.math.columbia.edu/tag/0FTP)
* [Stacks Project, Tag 0FT0](https://stacks.math.columbia.edu/tag/0FT0)
* [Stacks Project, Tag 0FT5](https://stacks.math.columbia.edu/tag/0FT5)
-/


@[expose] public noncomputable section

open CategoryTheory

universe u v w u' v' a'

namespace SheafOfModules.DifferentialGradedModule

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  [HasWeakSheafify X.J (Type max u v w)]
  [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]

/-- Every object of the homotopy category admits a quasi-isomorphism into the image of a graded
injective K-injective right differential graded module. This is Tag 0FT0, read in the homotopy
category. -/
theorem exists_quasiIso_isDGInjective
    (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (K : HomotopyCategory.{u, v, max u v w} A) :
    ∃ (I : HomotopyCategory.{u, v, max u v w} A) (s : K ⟶ I),
      quasiIsomorphisms.{u, v, max u v w} A s ∧ IsKInjective I.as ∧ GradedInjective I.as := by
  obtain ⟨I, f, hf, hGI, hKI⟩ := hasKInjectiveResolutions_dg.{u, v, w} A K.as
  exact ⟨(HomotopyCategory.quotient A).obj I, (HomotopyCategory.quotient A).map f,
    (quasiIsomorphisms_quotient_map_iff f).2 hf, hKI, hGI⟩

/-! ### The right derived extension of a functor out of the homotopy category -/

section RightDerived

variable {H : Type*} [Category H] (T : HomotopyCategory.{u, v, max u v w} A ⥤ H)

/-- The right derived extension `RT : D(A, d) ⥤ D` of a functor `T` out of the homotopy category
of right differential graded `A`-modules: the total right derived functor of `T` along the
localization at the quasi-isomorphisms. -/
def rightDerivedExtension : derivedCategory.{u, v, max u v w} A ⥤ H :=
  have := hasRightDerivedFunctor_of_hasKInjectiveResolutions
    (hasKInjectiveResolutions_dg.{u, v, w} A) T
  T.totalRightDerived (toDerivedCategory.{u, v, max u v w} A)
    (quasiIsomorphisms.{u, v, max u v w} A)

/-- The comparison map `T ⟶ Q ⋙ RT` of the right derived extension. -/
def rightDerivedExtensionUnit :
    T ⟶ toDerivedCategory.{u, v, max u v w} A ⋙ rightDerivedExtension T :=
  have := hasRightDerivedFunctor_of_hasKInjectiveResolutions
    (hasKInjectiveResolutions_dg.{u, v, w} A) T
  T.totalRightDerivedUnit (toDerivedCategory.{u, v, max u v w} A)
    (quasiIsomorphisms.{u, v, max u v w} A)

/-- The right derived extension is the right derived functor of `T` with the comparison map as
its unit. -/
theorem isRightDerivedFunctor_rightDerivedExtension :
    (rightDerivedExtension T).IsRightDerivedFunctor (rightDerivedExtensionUnit T)
      (quasiIsomorphisms.{u, v, max u v w} A) := by
  have := hasRightDerivedFunctor_of_hasKInjectiveResolutions
    (hasKInjectiveResolutions_dg.{u, v, w} A) T
  exact inferInstanceAs ((T.totalRightDerived (toDerivedCategory.{u, v, max u v w} A)
      (quasiIsomorphisms.{u, v, max u v w} A)).IsRightDerivedFunctor
    (T.totalRightDerivedUnit (toDerivedCategory.{u, v, max u v w} A)
      (quasiIsomorphisms.{u, v, max u v w} A))
    (quasiIsomorphisms.{u, v, max u v w} A))

/-- The comparison map of the right derived extension is invertible at a graded injective
K-injective right differential graded module. -/
theorem isIso_rightDerivedExtensionUnit_app
    {I : DifferentialGradedModule.{u, v, max u v w} A} (hI : IsDGInjective I) :
    IsIso ((rightDerivedExtensionUnit T).app ((HomotopyCategory.quotient A).obj I)) := by
  have := hasPointwiseRightDerivedFunctor_of_hasKInjectiveResolutions
    (hasKInjectiveResolutions_dg.{u, v, w} A) T
  have := isRightDerivedFunctor_rightDerivedExtension T
  exact (Functor.LeftExtension.mk _ (rightDerivedExtensionUnit T)).isIso_hom_app_of_bijective
    (Functor.isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor _ _
      (quasiIsomorphisms.{u, v, max u v w} A) _)
    fun Y => bijective_toDerivedCategory_map (hasKInjectiveResolutions_dg.{u, v, w} A) Y hI.2 hI.1

/-- The identification, at a graded injective K-injective right differential graded module `I`, of
the value of the right derived extension at the image of `I` with `T(I)`: the inverse of the
comparison map, which is invertible there. -/
def rightDerivedExtensionObjIso {I : DifferentialGradedModule.{u, v, max u v w} A}
    (hI : IsDGInjective I) :
    (rightDerivedExtension T).obj ((toDerivedCategory.{u, v, max u v w} A).obj
        ((HomotopyCategory.quotient A).obj I)) ≅ T.obj ((HomotopyCategory.quotient A).obj I) :=
  haveI := isIso_rightDerivedExtensionUnit_app T hI
  (asIso ((rightDerivedExtensionUnit T).app ((HomotopyCategory.quotient A).obj I))).symm

/-- Conjugating the right derived extension by those identifications at the two ends gives the
value of `T` on the homotopy class. -/
@[reassoc]
theorem rightDerivedExtensionObjIso_inv_map_hom
    {I I' : DifferentialGradedModule.{u, v, max u v w} A} (hI : IsDGInjective I)
    (hI' : IsDGInjective I') (ψ : I ⟶ I') :
    (rightDerivedExtensionObjIso T hI).inv ≫
        (rightDerivedExtension T).map ((toDerivedCategory.{u, v, max u v w} A).map
          ((HomotopyCategory.quotient A).map ψ)) ≫
        (rightDerivedExtensionObjIso T hI').hom =
      T.map ((HomotopyCategory.quotient A).map ψ) := by
  have := isIso_rightDerivedExtensionUnit_app T hI'
  have hnat := (rightDerivedExtensionUnit T).naturality ((HomotopyCategory.quotient A).map ψ)
  simp only [Functor.comp_map] at hnat
  change (rightDerivedExtensionUnit T).app ((HomotopyCategory.quotient A).obj I) ≫
    (rightDerivedExtension T).map _ ≫ _ = _
  rw [← Category.assoc, ← hnat, Category.assoc]
  simp [rightDerivedExtensionObjIso]

/-! ### The right derived extension with its value on the nose -/

/-- The object map of the rigidified right derived extension: at an object of `D(A, d)`
representing a graded injective K-injective module `I` it is `T(I)`, and elsewhere it is the value
of `rightDerivedExtension`. -/
def rigidRightDerivedExtensionObj : derivedCategory.{u, v, max u v w} A → H := fun Z =>
  @dite _ (IsDGInjective (derivedCategoryModule A Z)) (Classical.dec _)
    (fun _ => T.obj ((HomotopyCategory.quotient A).obj (derivedCategoryModule A Z)))
    (fun _ => (rightDerivedExtension T).obj Z)

/-- At the image of a graded injective K-injective right differential graded module the object map
is `T(I)`. -/
theorem rigidRightDerivedExtensionObj_of_isDGInjective
    {I : DifferentialGradedModule.{u, v, max u v w} A} (hI : IsDGInjective I) :
    rigidRightDerivedExtensionObj T ((toDerivedCategory.{u, v, max u v w} A).obj
        ((HomotopyCategory.quotient A).obj I)) =
      T.obj ((HomotopyCategory.quotient A).obj I) :=
  dite_eq_left hI

/-- Away from the graded injective K-injective modules the object map is the value of
`rightDerivedExtension`. -/
theorem rigidRightDerivedExtensionObj_of_not_isDGInjective
    {Z : derivedCategory.{u, v, max u v w} A} (hZ : ¬ IsDGInjective (derivedCategoryModule A Z)) :
    rigidRightDerivedExtensionObj T Z = (rightDerivedExtension T).obj Z :=
  dite_eq_right hZ

/-- The isomorphism between the right derived extension and the object map above: the inverse of
the comparison map at a graded injective K-injective module, and the identity elsewhere. -/
def rigidRightDerivedExtensionObjIso (Z : derivedCategory.{u, v, max u v w} A) :
    (rightDerivedExtension T).obj Z ≅ rigidRightDerivedExtensionObj T Z :=
  @dite _ (IsDGInjective (derivedCategoryModule A Z)) (Classical.dec _)
    (fun h => rightDerivedExtensionObjIso T h ≪≫
      eqToIso (rigidRightDerivedExtensionObj_of_isDGInjective T h).symm)
    (fun h => eqToIso (rigidRightDerivedExtensionObj_of_not_isDGInjective T h).symm)

/-- At the image of a graded injective K-injective right differential graded module that
isomorphism is the inverse of the comparison map. -/
theorem rigidRightDerivedExtensionObjIso_of_isDGInjective
    {I : DifferentialGradedModule.{u, v, max u v w} A} (hI : IsDGInjective I) :
    rigidRightDerivedExtensionObjIso T ((toDerivedCategory.{u, v, max u v w} A).obj
        ((HomotopyCategory.quotient A).obj I)) =
      rightDerivedExtensionObjIso T hI ≪≫
        eqToIso (rigidRightDerivedExtensionObj_of_isDGInjective T hI).symm :=
  dite_eq_left hI

/-- **The rigidified right derived extension** `RT : D(A, d) ⥤ D`: the right derived extension
with its object map replaced by the isomorphic one above, so that its value at the image of a
graded injective K-injective right differential graded module `I` is `T(I)` on the nose. -/
def rigidRightDerivedExtension : derivedCategory.{u, v, max u v w} A ⥤ H :=
  (rightDerivedExtension T).copyObj (rigidRightDerivedExtensionObj T)
    (rigidRightDerivedExtensionObjIso T)

/-- The rigidified functor is isomorphic to the right derived extension. -/
def isoRigidRightDerivedExtension : rightDerivedExtension T ≅ rigidRightDerivedExtension T :=
  (rightDerivedExtension T).isoCopyObj _ _

/-- The comparison map of the rigidified right derived extension: the comparison map of
`rightDerivedExtension` followed by the identification of the two functors. -/
def rigidRightDerivedExtensionUnit :
    T ⟶ toDerivedCategory.{u, v, max u v w} A ⋙ rigidRightDerivedExtension T :=
  rightDerivedExtensionUnit T ≫
    Functor.whiskerLeft (toDerivedCategory.{u, v, max u v w} A)
      (isoRigidRightDerivedExtension T).hom

/-- The value of the rigidified right derived extension at the image of a graded injective
K-injective right differential graded module `I` is `T(I)`. -/
theorem rigidRightDerivedExtension_obj_of_isDGInjective
    {I : DifferentialGradedModule.{u, v, max u v w} A} (hI : IsDGInjective I) :
    (rigidRightDerivedExtension T).obj ((toDerivedCategory.{u, v, max u v w} A).obj
        ((HomotopyCategory.quotient A).obj I)) =
      T.obj ((HomotopyCategory.quotient A).obj I) :=
  rigidRightDerivedExtensionObj_of_isDGInjective T hI

/-- The comparison map of the rigidified right derived extension is invertible at a graded
injective K-injective right differential graded module. -/
theorem isIso_rigidRightDerivedExtensionUnit_app
    {I : DifferentialGradedModule.{u, v, max u v w} A} (hI : IsDGInjective I) :
    IsIso ((rigidRightDerivedExtensionUnit T).app ((HomotopyCategory.quotient A).obj I)) := by
  have := isIso_rightDerivedExtensionUnit_app T hI
  simp only [rigidRightDerivedExtensionUnit, NatTrans.comp_app, Functor.whiskerLeft_app]
  infer_instance

/-- On the image of a homomorphism of graded injective K-injective right differential graded
modules the rigidified right derived extension is `T` of that homomorphism, read through the two
identifications of its value. -/
theorem rigidRightDerivedExtension_map_of_isDGInjective
    {I I' : DifferentialGradedModule.{u, v, max u v w} A} (hI : IsDGInjective I)
    (hI' : IsDGInjective I') (ψ : I ⟶ I') :
    (rigidRightDerivedExtension T).map ((toDerivedCategory.{u, v, max u v w} A).map
          ((HomotopyCategory.quotient A).map ψ)) =
      eqToHom (rigidRightDerivedExtension_obj_of_isDGInjective T hI) ≫
        T.map ((HomotopyCategory.quotient A).map ψ) ≫
          eqToHom (rigidRightDerivedExtension_obj_of_isDGInjective T hI').symm := by
  change (rigidRightDerivedExtensionObjIso T _).inv ≫ (rightDerivedExtension T).map _ ≫
    (rigidRightDerivedExtensionObjIso T _).hom = _
  rw [rigidRightDerivedExtensionObjIso_of_isDGInjective T hI,
    rigidRightDerivedExtensionObjIso_of_isDGInjective T hI']
  simp only [Iso.trans_inv, Iso.trans_hom, eqToIso.inv, eqToIso.hom, Category.assoc,
    rightDerivedExtensionObjIso_inv_map_hom_assoc T hI hI' ψ]
  rfl

/-- The rigidified functor, with its transported comparison map, is still the right derived
functor of `T`. -/
theorem isRightDerivedFunctor_rigidRightDerivedExtension :
    (rigidRightDerivedExtension T).IsRightDerivedFunctor (rigidRightDerivedExtensionUnit T)
      (quasiIsomorphisms.{u, v, max u v w} A) := by
  refine Functor.isRightDerivedFunctor_of_coresolutions
    (L := toDerivedCategory.{u, v, max u v w} A) (quasiIsomorphisms.{u, v, max u v w} A) _
    (fun Z => IsKInjective Z.as ∧ GradedInjective Z.as) (exists_quasiIso_isDGInjective A)
    (fun I hI Y => bijective_toDerivedCategory_map (hasKInjectiveResolutions_dg.{u, v, w} A) Y
      hI.1 hI.2)
    fun I hI => isIso_rigidRightDerivedExtensionUnit_app T ⟨hI.2, hI.1⟩

end RightDerived

/-! ### The right derived extension of a functor of differential graded modules -/

section ModuleFunctor

variable {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'}
  {R' : Sheaf J' RingCat.{u}} {B : DifferentialGradedAlgebra.{u, a'} R'}
  [HasSheafify J' AddCommGrpCat.{max u v w}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]

/-- **The right derived extension of a functor of right differential graded modules is computed by
the graded injective K-injective modules.** For a functor `S : Mod^dg(A, d) ⥤ Mod^dg(B, d)`
preserving homotopy, the rigidified right derived extension of the descended functor followed by
the localization takes the image of a graded injective K-injective module `I` to the image of
`S(I)`, compatibly with homomorphisms of such modules. This inhabits
`SheafOfModules.DifferentialGradedModule.ComputesOnDGInjective`. -/
theorem computesOnDGInjective_rigidRightDerivedExtension
    (S : DifferentialGradedModule.{u, v, max u v w} A ⥤
      DifferentialGradedModule.{u, a', max u v w} B) (hS : PreservesHomotopic S) :
    ComputesOnDGInjective S (rigidRightDerivedExtension
      (HomotopyCategory.descend S hS ⋙ toDerivedCategory.{u, a', max u v w} B)) where
  obj_eq hI := rigidRightDerivedExtension_obj_of_isDGInjective _ hI
  map_eq hI hI' ψ := rigidRightDerivedExtension_map_of_isDGInjective _ hI hI' ψ

variable {g : C' ⥤ X.C} [g.IsContinuous J' X.J]
  {σ : R'.obj ⟶ g.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj}

/-- **The derived pushforward is a term of
`SheafOfModules.DifferentialGradedModule.IsDerivedPushforward`.** The rigidified right derived
extension of the direct image, followed by the localization, takes the image of a graded injective
K-injective right differential graded `A`-module `I` to the image of `f_*I`, compatibly with
homomorphisms of such modules. -/
theorem isDerivedPushforward_rigidRightDerivedExtension
    (φ : DifferentialGradedAlgebra.SemilinearHom g σ B A) :
    IsDerivedPushforward (φ := φ) (rigidRightDerivedExtension
      (homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{u, a', max u v w} B)) :=
  computesOnDGInjective_rigidRightDerivedExtension (pushforwardFunctor.{u, v, max u v w} φ)
    (preservesHomotopic_pushforwardFunctor φ)

end ModuleFunctor

/-! ### Tag 0FTN -/

/-- Let `X` be a ringed site and let `(A, d)` be a sheaf of differential graded algebras on it.
Every functor `T : K(Mod(A, d)) ⥤ D` out of the homotopy category of right differential graded
`A`-modules has a right derived extension `RT : D(A, d) ⥤ D` along the localization, and the value
of `RT` on a graded injective and K-injective right differential graded `A`-module `I` is
`T(I)`. -/
@[stacks 0FTN]
theorem exists_rightDerivedExtension
    (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {H : Type*} [Category H] (T : HomotopyCategory.{u, v, max u v w} A ⥤ H) :
    ∃ (RT : derivedCategory.{u, v, max u v w} A ⥤ H)
      (β : T ⟶ toDerivedCategory.{u, v, max u v w} A ⋙ RT),
      RT.IsRightDerivedFunctor β (quasiIsomorphisms.{u, v, max u v w} A) ∧
        ∀ I : DifferentialGradedModule.{u, v, max u v w} A,
          GradedInjective I → IsKInjective I →
            RT.obj ((toDerivedCategory.{u, v, max u v w} A).obj
                ((HomotopyCategory.quotient A).obj I)) =
              T.obj ((HomotopyCategory.quotient A).obj I) :=
  ⟨rigidRightDerivedExtension T, rigidRightDerivedExtensionUnit T,
    isRightDerivedFunctor_rigidRightDerivedExtension T,
    fun _ hGI hKI => rigidRightDerivedExtension_obj_of_isDGInjective T ⟨hGI, hKI⟩⟩

/-! ### Right derived extensions of functors of modules and of direct images -/

section DerivedInternalHomAndPushforward

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
  [HasWeakSheafify X.J (Type max u v w)]
  [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]

/-- **Right derived extensions of functors of modules and of direct images.**

(1) For sheaves of differential graded algebras `A₁`, `A₂` on a ringed site `X` and a functor `S`
of right differential graded modules from `A₂` to `A₁` preserving homotopy — the internal hom
functor `SheafHom^dg_{A₂}(N, -)` of a differential graded `(A₁, A₂)`-bimodule `N` is such a
functor — the right derived extension `RS : D(A₂, d) ⥤ D(A₁, d)` of `S` exists, and its value on
a graded injective and K-injective right differential graded `A₂`-module `I` is the image of
`S(I)`. For the internal hom functor this `RS` is the *derived internal hom*.

(2) For a morphism of ringed sites out of `X`, a sheaf of differential graded algebras `A` on
`X`, a sheaf of differential graded algebras `B` on the target and a homomorphism
`φ : B ⟶ f_*A`, the right derived extension `Rf_* : D(A, d) ⥤ D(B, d)` of the direct image `f_*`
exists, and its value on a graded injective and K-injective right differential graded `A`-module
`I` is the image of `f_*I`. This is the *derived pushforward*.

Each part also records its value clause in the vocabulary of
`SheafOfModules.DifferentialGradedModule.ComputesOnDGInjective`, which adds to it the
compatibility with homomorphisms of graded injective K-injective modules; for part (2) that is
`SheafOfModules.DifferentialGradedModule.IsDerivedPushforward`. -/
theorem exists_derivedInternalHom_and_derivedPushforward :
    (∀ (A₁ A₂ : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (S : DifferentialGradedModule.{u, v, max u v w} A₂ ⥤
          DifferentialGradedModule.{u, v, max u v w} A₁) (hS : PreservesHomotopic S),
      ∃ (RS : derivedCategory.{u, v, max u v w} A₂ ⥤ derivedCategory.{u, v, max u v w} A₁)
        (β : HomotopyCategory.descend S hS ⋙ toDerivedCategory.{u, v, max u v w} A₁ ⟶
          toDerivedCategory.{u, v, max u v w} A₂ ⋙ RS),
        RS.IsRightDerivedFunctor β (quasiIsomorphisms.{u, v, max u v w} A₂) ∧
          (∀ I : DifferentialGradedModule.{u, v, max u v w} A₂,
            GradedInjective I → IsKInjective I →
              RS.obj ((toDerivedCategory.{u, v, max u v w} A₂).obj
                  ((HomotopyCategory.quotient A₂).obj I)) =
                (toDerivedCategory.{u, v, max u v w} A₁).obj
                  ((HomotopyCategory.quotient A₁).obj (S.obj I))) ∧
            ComputesOnDGInjective S RS) ∧
      ∀ (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          {C' : Type u'} [Category.{v'} C']
          {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{u}}
          {B : DifferentialGradedAlgebra.{u, a'} R'}
          [HasSheafify J' AddCommGrpCat.{max u v w}]
          [J'.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
          {g : C' ⥤ X.C} [g.IsContinuous J' X.J]
          {σ : R'.obj ⟶ g.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj}
          (φ : DifferentialGradedAlgebra.SemilinearHom g σ B A),
        ∃ (Rf : derivedCategory.{u, v, max u v w} A ⥤ derivedCategory.{u, a', max u v w} B)
          (β : homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{u, a', max u v w} B ⟶
            toDerivedCategory.{u, v, max u v w} A ⋙ Rf),
          Rf.IsRightDerivedFunctor β (quasiIsomorphisms.{u, v, max u v w} A) ∧
            (∀ I : DifferentialGradedModule.{u, v, max u v w} A,
              GradedInjective I → IsKInjective I →
                Rf.obj ((toDerivedCategory.{u, v, max u v w} A).obj
                    ((HomotopyCategory.quotient A).obj I)) =
                  (toDerivedCategory.{u, a', max u v w} B).obj
                    ((HomotopyCategory.quotient B).obj ((pushforwardFunctor φ).obj I))) ∧
              IsDerivedPushforward (φ := φ) Rf := by
  constructor
  · intro A₁ A₂ S hS
    exact ⟨rigidRightDerivedExtension
        (HomotopyCategory.descend S hS ⋙ toDerivedCategory.{u, v, max u v w} A₁),
      rigidRightDerivedExtensionUnit _,
      isRightDerivedFunctor_rigidRightDerivedExtension _,
      fun _ hGI hKI => rigidRightDerivedExtension_obj_of_isDGInjective _ ⟨hGI, hKI⟩,
      computesOnDGInjective_rigidRightDerivedExtension S hS⟩
  · intro A C' _ J' R' B _ _ g _ σ φ
    exact ⟨rigidRightDerivedExtension
        (homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{u, a', max u v w} B),
      rigidRightDerivedExtensionUnit _,
      isRightDerivedFunctor_rigidRightDerivedExtension _,
      fun _ hGI hKI => rigidRightDerivedExtension_obj_of_isDGInjective _ ⟨hGI, hKI⟩,
      isDerivedPushforward_rigidRightDerivedExtension φ⟩

end DerivedInternalHomAndPushforward

end SheafOfModules.DifferentialGradedModule

end
