module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.InverseImage
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.StratificationSupplement
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.ChangeOfRings
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.BoundedComplexes

/-!
# Constructible pro-étale sheaves and change of rings

Let `X` be a scheme and `f : Λ →+* S` a surjective homomorphism of Noetherian rings, for
instance `Λ → Λ/I`. A sheaf of `S`-modules on the small pro-étale site of `X` is constructible
(Tag 09AJ) exactly when it is constructible as a sheaf of `Λ`-modules. Constant sheaves on
finitely generated modules are constructible.

## Main definitions

* `AlgebraicGeometry.ProEtale.proetaleModuleInverseImageRestrictScalarsIso`: inverse image
  commutes with restriction of scalars.

## Main results

* `AlgebraicGeometry.ProEtale.isConstructibleModuleSheaf'_restrictScalars_iff`: constructibility
  is detected by restriction of scalars along a surjective ring map.
* `AlgebraicGeometry.ProEtale.isConstructibleModuleSheaf'_constantSheaf`: the constant sheaf on
  a finitely generated module is constructible.

## Implementation notes

Both coefficient rings live in the universe `max (u + 1) w` of the module sections, as in
`StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.DerivedTensor`. The same constructible
partition serves both rings: restriction of scalars commutes with inverse image to a stratum,
and local constancy of finite type is detected by restriction of scalars
(`Stacks.ModuleSheaf.isFiniteTypeLocallyConstantModuleSheaf_restrictScalars_iff`).

## References

* [Stacks Project, Tag 09AJ](https://stacks.math.columbia.edu/tag/09AJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.ProEtale

variable {X : Scheme.{u}} {Λ S : Type (max (u + 1) w)} [CommRing Λ] [CommRing S]

/-- **Inverse image commutes with restriction of scalars.** -/
def proetaleModuleInverseImageRestrictScalarsIso {Z : Scheme.{u}} (g : Z ⟶ X) (f : Λ →+* S) :
    proetaleModuleInverseImage.{u, max (u + 1) w, w} g S ⋙
        Stacks.ModuleSheaf.restrictScalars (Scheme.ProEt.topology Z) f ≅
      Stacks.ModuleSheaf.restrictScalars (Scheme.ProEt.topology X) f ⋙
        proetaleModuleInverseImage.{u, max (u + 1) w, w} g Λ :=
  Stacks.ModuleSheaf.restrictScalarsSheafPullbackIso f
    (proetaleModuleInverseImageAdjunction.{u, max (u + 1) w, w} S g)
    (proetaleModuleInverseImageAdjunction.{u, max (u + 1) w, w} Λ g)

variable [IsNoetherianRing Λ] [IsNoetherianRing S]

/-- **Constructibility is detected by restriction of scalars along a surjective ring map.** A
sheaf of `S`-modules on the small pro-étale site of `X` is constructible exactly when it is
constructible as a sheaf of `Λ`-modules. -/
theorem isConstructibleModuleSheaf'_restrictScalars_iff {f : Λ →+* S}
    (hf : Function.Surjective f)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} S)) :
    IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X Λ
        ((Stacks.ModuleSheaf.restrictScalars (Scheme.ProEt.topology X) f).obj F) ↔
      IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X S F := by
  refine forall_congr' fun U => exists_congr fun s => forall_congr' fun i => ?_
  rw [← Stacks.ModuleSheaf.isFiniteTypeLocallyConstantModuleSheaf_restrictScalars_iff
    (Scheme.ProEt.topology (s.piece i)) hf]
  exact ObjectProperty.prop_iff_of_iso _
    ((proetaleModuleInverseImageRestrictScalarsIso (s.inclusion i) f).app F).symm

omit [IsNoetherianRing S] in
/-- **The constant sheaf on a finitely generated module is constructible**: on every stratum
of the trivial partition of an affine open, its inverse image is locally constant of finite
type. -/
theorem isConstructibleModuleSheaf'_constantSheaf (M : ModuleCat.{max (u + 1) w} Λ)
    (hM : ModuleCat.isFG Λ M) :
    IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X Λ
      ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj M) :=
  fun U => ⟨Scheme.ConstructibleStratification.single X U.1, fun _ =>
    isFiniteTypeLocallyConstantModuleSheaf_proetaleModuleInverseImage _ _
      (Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_of_constant _ Λ hM
        (Iso.refl _))⟩

end AlgebraicGeometry.ProEtale
