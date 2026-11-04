module

public import StacksFrontier.AlgebraicGeometry.Perfect.QuasiCoherentDerived.DGAModel
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexOverRing.CompactGeneratorEquivalence
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexOverRing.QuasicoherentImage
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexOverRing.Linear
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.PowerTorsionGlobalSection
public import StacksFrontier.CategoryTheory.Sites.Modules.ComplexesDGCategoryBaseRing

/-!
# The construction of Tag 09M5 over a base ring

Let `X` be a quasi-compact and quasi-separated scheme over a ring `R`, i.e. with a morphism
`X ⟶ Spec R`. Then the sheaves of `𝒪_X`-modules are `R`-linear: a scalar acts through its image
in `Γ(X, 𝒪_X)`, which is the datum of a sheaf of `R`-algebras on `𝒪_X` as in Tag 0CS6.
For a K-injective complex `K` of `𝒪_X`-modules representing a perfect generator of
`D_QCoh(𝒪_X)`, the endomorphism differential graded algebra `E = Hom_{Comp^dg(𝒪_X)}(K, K)` is
then a differential graded `R`-algebra, and the construction of the proof of Tag 09M5 gives the
equivalence

`- ⊗_E^𝐋 K : D(E, d) ⥤ D_QCoh(𝒪_X)`,

which is `R`-linear and, through the sign-twisted identity, exact.

## Main definitions

* `AlgebraicGeometry.overRingHom`: the ring map `R → Γ(X, 𝒪_X)` of a scheme over `R`, read as
  global sections of the structure sheaf of the site of opens.
* `AlgebraicGeometry.overRingLinear`, `AlgebraicGeometry.overRingScalarSections`: the resulting
  `R`-linear structure on `𝒪_X`-modules, with its scalars being sections of `𝒪_X`.
* `AlgebraicGeometry.overRingLinearModules`: the same `R`-linear structure on `X.Modules`.
* `AlgebraicGeometry.IsPerfectGeneratorRepresentative`: `K` is K-injective and represents a perfect
  generator of `D_QCoh(𝒪_X)`.
* `AlgebraicGeometry.dgaModelEquivalence`: the equivalence `D(E, d) ≌ D_QCoh(𝒪_X)` of the
  construction, at the standard model of `D(𝒪_X)`.

## Main results

* `AlgebraicGeometry.dgaModelEquivalence_functor_linear`: it is `R`-linear.
* `AlgebraicGeometry.dgaModelEquivalence_functor_isTriangulated`: it is exact.

## References

* [Stacks Project, Tag 09M5](https://stacks.math.columbia.edu/tag/09M5)
* [Stacks Project, Tag 09SU](https://stacks.math.columbia.edu/tag/09SU)
* [Stacks Project, Tag 0CS6](https://stacks.math.columbia.edu/tag/0CS6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Duality.CompactBoundedness StacksDraft.DerivedModel

namespace AlgebraicGeometry

universe u

/-- The scheme read as a ringed site. -/
local notation "𝒮" X => Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite X

variable {X : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R)

/-- The structure map of a scheme over `R` on global sections: `R ≅ Γ(Spec R, 𝒪) → Γ(X, 𝒪_X)`,
read as a compatible family of sections of the structure sheaf of the site of opens of `X`. -/
def overRingHom : R →+* ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (𝒮 X).O)) :=
  (@Stacks.ExtensionByZero.globalScalarHom _ (Stacks.SheafOfModules.Tensor.ringSheaf (𝒮 X).O)
    (fun U => RingedSite.ringSheafSectionsIsMulCommutative (𝒮 X) U)).comp
    ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom

/-- The `R`-linear structure on `𝒪_X`-modules of a scheme over `R`: a scalar acts through its
image in `Γ(X, 𝒪_X)`. -/
@[instance_reducible]
def overRingLinear : Linear R (RingedSite.TensorModO.{u, u, u, u, u} (𝒮 X)) :=
  Linear.ofRingHom (overRingHom f)

/-- The scalars of `overRingLinear` act by multiplication by sections of `𝒪_X`: they are the
datum of a sheaf of `R`-algebras on `𝒪_X`. -/
@[instance_reducible]
def overRingScalarSections :
    letI := overRingLinear f
    RingedSite.ScalarSections.{u, u, u, u, u, u} (𝒮 X) R :=
  letI := overRingLinear f
  { scalarSection r U := (overRingHom f r).val U
    smul_app r P Q g U y := by
      change ((Stacks.Cohomology.SiteModules.globalSmul
        (Stacks.SheafOfModules.Tensor.ringSheaf (𝒮 X).O) (overRingHom f r) P ≫ g).val.app U) y = _
      rw [SheafOfModules.comp_val, PresheafOfModules.comp_app]
      change (g.val.app U) ((Stacks.Cohomology.SiteModules.globalSmul
        (Stacks.SheafOfModules.Tensor.ringSheaf (𝒮 X).O) (overRingHom f r) P).val.app U y) = _
      rw [Stacks.Cohomology.SiteModules.globalSmul_app]
      exact map_smul (g.val.app U).hom _ y }

/-- The `R`-linear structure on `X.Modules` of a scheme over `R`. -/
@[instance_reducible]
def overRingLinearModules : Linear R X.Modules :=
  overRingLinear f

/-! ### The construction of Tag 09M5 over the base ring -/

section Construction

variable (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
  (R : Type u) [CommRing R] [Linear R (RingedSite.TensorModO.{u, u, u, u, u} (𝒮 X))]
  [RingedSite.ScalarSections.{u, u, u, u, u, u} (𝒮 X) R]
  (K : CochainComplex (RingedSite.ModO.{u, u, u, u} (𝒮 X)) ℤ)

/-- The hypotheses of the construction of Tag 09M5 on a complex `K`: it is K-injective (as the
complex `liftComplex K` that the endomorphism algebra is formed from), and it represents a perfect
generator of `D_QCoh(𝒪_X)`. -/
structure IsPerfectGeneratorRepresentative : Prop where
  isKInjective : (RingedSite.liftComplex.{u, u, u, u, u} (𝒮 X) K).IsKInjective
  isPerfect : IsPerfectStd (show Dstd X from
    (stdQ X).obj (RingedSite.liftComplex.{u, u, u, u, u} (𝒮 X) K))
  generates : ∀ L : stdDerived X, qcohDerivedProperty X L →
    (∀ (n : ℤ) (g : ((stdQ X).obj (RingedSite.liftComplex.{u, u, u, u, u} (𝒮 X) K))⟦n⟧ ⟶ L),
      g = 0) → IsZero L

variable {X K}

omit [CompactSpace X] [QuasiSeparatedSpace X] in
/-- `D_QCoh(𝒪_X)` is closed under direct sums. -/
theorem qcohDerivedProperty_sum : ∀ {ι : Type u} (Z : ι → stdDerived X) (c : Cofan Z),
    IsColimit c → (∀ i, qcohDerivedProperty X (Z i)) → qcohDerivedProperty X c.pt :=
  fun Z c hc hZ =>
    RingedSite.derivedCategoryB_prop_of_isColimit.{u, u, u, u, u} (𝒮 X)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) (isWeakSerre_isQuasicoherent X)
      (fun M hM => Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_isColimit
        (fun i => hM i.as) (coproductIsCoproduct M)) Z c hc hZ

omit [CompactSpace X] [QuasiSeparatedSpace X] in
/-- `K` lies in `D_QCoh(𝒪_X)`. -/
theorem IsPerfectGeneratorRepresentative.mem (hK : IsPerfectGeneratorRepresentative X K) :
    qcohDerivedProperty X ((stdQ X).obj (RingedSite.liftComplex.{u, u, u, u, u} (𝒮 X) K)) :=
  isQuasicoherent_of_isPerfectStd _ hK.isPerfect

omit [CompactSpace X] [QuasiSeparatedSpace X] in
/-- `- ⊗_E^𝐋 K` lands in `D_QCoh(𝒪_X)` (Tag 09M3 over `R`). -/
theorem IsPerfectGeneratorRepresentative.tensor_mem (hK : IsPerfectGeneratorRepresentative X K)
    (M : DifferentialGradedModule.derivedCategory.{u, u, u}
      (RingedSite.Rep.{u, u, u, u, u, u} (𝒮 X) R K).algebra) :
    qcohDerivedProperty X
      ((RingedSite.tensorWithComplexDerived.{u, u, u, u, u, u} (𝒮 X) R K).obj M) := by
  have hK' : RingedSite.tensorModOQuasicoherentDerived.{u, u, u, u, u} (𝒮 X)
      ((stdQ X).obj (RingedSite.liftComplex.{u, u, u, u, u} (𝒮 X) K)) := by
    rw [RingedSite.tensorModOQuasicoherentDerived,
      RingedSite.tensorModOQuasicoherent_schemeRingedSite_eq X]
    exact hK.mem
  exact RingedSite.derivedCategoryB_isQuasicoherent_tensorWithComplexDerived_obj_schemeOver X R K
    hK' M

/-- `K` is a compact object of `D_QCoh(𝒪_X)` (Tag 09M1). -/
theorem IsPerfectGeneratorRepresentative.isCompactObject
    (hK : IsPerfectGeneratorRepresentative X K) :
    IsCompactObject.{u} (⟨(stdQ X).obj (RingedSite.liftComplex.{u, u, u, u, u} (𝒮 X) K), hK.mem⟩ :
      (qcohDerivedProperty X).FullSubcategory) :=
  isCompactObject_stdDerived X _ hK.isPerfect hK.mem

/-- The equivalence of the construction of Tag 09M5, over `R`: `- ⊗_E^𝐋 K : D(E, d) ≌
D_QCoh(𝒪_X)` for the endomorphism differential graded `R`-algebra `E` of `K`, at the standard
model of `D(𝒪_X)`. Its functor is `- ⊗_E^𝐋 K` (followed by the sign-twisted identity of `D(𝒪_X)`,
which is the identity on objects and morphisms and only changes the commutation with the shift). -/
def dgaModelEquivalence (hK : IsPerfectGeneratorRepresentative X K) :
    DifferentialGradedModule.derivedCategory.{u, u, u}
        (RingedSite.Rep.{u, u, u, u, u, u} (𝒮 X) R K).algebra ≌
      (qcohDerivedProperty X).FullSubcategory :=
  haveI := hK.isKInjective
  RingedSite.tensorWithComplexDerivedLiftEquivalenceOver.{u, u, u, u, u, u} (𝒮 X) R K
    (qcohDerivedProperty X) (hK.tensor_mem R) qcohDerivedProperty_sum hK.mem hK.isCompactObject
    hK.generates

/-- The functor of `AlgebraicGeometry.dgaModelEquivalence`, followed by the inclusion of
`D_QCoh(𝒪_X)`, is `- ⊗_E^𝐋 K`. -/
theorem dgaModelEquivalence_functor_comp_ι (hK : IsPerfectGeneratorRepresentative X K) :
    (dgaModelEquivalence R hK).functor ⋙ (qcohDerivedProperty X).ι =
      RingedSite.tensorWithComplexDerived.{u, u, u, u, u, u} (𝒮 X) R K :=
  rfl



section Triangulated

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

/-- The functor of the equivalence of the construction commutes with the translations, as
`- ⊗_E^𝐋 K` followed by the sign-twisted identity of `D(𝒪_X)`. -/
instance dgaModelEquivalence_functor_commShift (hK : IsPerfectGeneratorRepresentative X K) :
    (dgaModelEquivalence R hK).functor.CommShift ℤ := by
  haveI := hK.isKInjective
  exact (inferInstance : (RingedSite.tensorWithComplexDerivedLiftTwistOver.{u, u, u, u, u, u} (𝒮 X)
    R K (qcohDerivedProperty X) (hK.tensor_mem R)).CommShift ℤ)

/-- The functor of the equivalence of the construction is exact. -/
instance dgaModelEquivalence_functor_isTriangulated (hK : IsPerfectGeneratorRepresentative X K) :
    (dgaModelEquivalence R hK).functor.IsTriangulated := by
  have := hK.isKInjective
  exact (inferInstance : (RingedSite.tensorWithComplexDerivedLiftTwistOver.{u, u, u, u, u, u} (𝒮 X)
    R K (qcohDerivedProperty X) (hK.tensor_mem R)).IsTriangulated)

end Triangulated

/-- The functor of the equivalence of the construction is `R`-linear. -/
instance dgaModelEquivalence_functor_linear (hK : IsPerfectGeneratorRepresentative X K) :
    (dgaModelEquivalence R hK).functor.Linear R where
  map_smul g r := ObjectProperty.hom_ext _
    ((RingedSite.tensorWithComplexDerived.{u, u, u, u, u, u} (𝒮 X) R K).map_smul r g)

end Construction

end AlgebraicGeometry

end
