module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact

/-!
# Localized rings and derived base change on an affine scheme

For a commutative ring `R` and `f : R`, the ring `R_f` is taken to be the ring of sections
`Γ(Spec R, D(f))`, a localization of `R` away from `f`. This file fixes the localization maps
`R ⟶ R_f`, the restriction maps `R_f ⟶ R_g` for `D(g) ⊆ D(f)`, their flatness, derived extension
of scalars along them, the groups `Ext^n_{R_f}(K ⊗_R R_f, L ⊗_R R_f)` and their restriction maps,
and the cohomology sheaves of `R𝓗om(K̃, L̃)`.

## Main definitions

* `AlgebraicGeometry.AffineExt.localizedExt`: `Ext^n_{R_f}(K ⊗_R R_f, L ⊗_R R_f)`.
* `AlgebraicGeometry.AffineExt.localizedExtRestrict`: its restriction to `D(g) ⊆ D(f)`, derived
  extension of scalars along `R_f ⟶ R_g`.
* `AlgebraicGeometry.AffineExt.cohomologySheaf`: the `n`-th cohomology sheaf of `R𝓗om(K̃, L̃)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.AffineExt

attribute [local instance 10000] HasDerivedCategory.standard
    AlgebraicGeometry.tilde.preservesFiniteLimits
  Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor

variable (R : CommRingCat.{u})

/-- The principal open `D(f)` of `Spec R`. -/
abbrev basicOpen (f : R) : (Spec R).Opens := PrimeSpectrum.basicOpen f

/-- The ring `R_f` of sections of `Spec R` over the principal open `D(f)`. -/
abbrev locRing (f : R) : CommRingCat.{u} := Γ(Spec R, basicOpen R f)

/-- The localization map `R ⟶ R_f`. -/
abbrev locMap (f : R) : R ⟶ locRing R f :=
  (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map (homOfLE le_top).op

/-- The restriction map `R_f ⟶ R_g` for `D(g) ⊆ D(f)`. -/
abbrev resMap {f g : R} (h : basicOpen R g ≤ basicOpen R f) :
    locRing R f ⟶ locRing R g :=
  (Spec R).presheaf.map (homOfLE h).op

/-- For `D(g) ⊆ D(f)`, the composite `R ⟶ R_f ⟶ R_g` is the localization map `R ⟶ R_g`. -/
lemma locMap_comp_resMap {f g : R} (h : basicOpen R g ≤ basicOpen R f) :
    locMap R f ≫ resMap R h = locMap R g :=
  (Category.assoc _ _ _).trans (congrArg _ ((Spec R).presheaf.map_comp _ _).symm)

/-- The ring `R_f` is a localization of `R` away from `f`. -/
instance (f : R) : IsLocalization.Away f (locRing R f) := inferInstance

/-- The localization map `R ⟶ R_f` is flat. -/
instance flat_locMap (f : R) : Fact (locMap R f).hom.Flat :=
  ⟨RingHom.flat_algebraMap_iff.2 (IsLocalization.flat (locRing R f) (Submonoid.powers f))⟩

/-- For `D(g) ⊆ D(f)`, the restriction map `R_f ⟶ R_g` is flat. -/
instance flat_resMap {f g : R} (h : basicOpen R g ≤ basicOpen R f) :
    Fact (resMap R h).hom.Flat := by
  let : Algebra (locRing R f) (locRing R g) := (resMap R h).hom.toAlgebra
  have : IsScalarTower R (locRing R f) (locRing R g) := IsScalarTower.of_algebraMap_eq
    fun r => (ConcreteCategory.congr_hom (locMap_comp_resMap R h) r).symm
  have : Module.Flat R (locRing R g) := IsLocalization.flat (locRing R g) (Submonoid.powers g)
  exact ⟨(Module.flat_iff_of_isLocalization (locRing R f) (Submonoid.powers f)
    (locRing R g)).2 this⟩

/-- Extension of scalars along a flat ring map is left exact. -/
instance preservesFiniteLimits_extendScalars {A B : CommRingCat.{u}} (φ : A ⟶ B)
    [hφ : Fact φ.hom.Flat] : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} φ.hom) :=
  extendScalars_preservesFiniteLimits_of_flat'.{u, u} φ.hom hφ.out

/-- Extension of scalars is a left adjoint, so it is right exact. -/
instance preservesFiniteColimits_extendScalars {A B : CommRingCat.{u}} (φ : A ⟶ B) :
    PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} φ.hom) :=
  haveI : PreservesColimitsOfSize.{0, 0} (ModuleCat.extendScalars.{u, u, u} φ.hom) :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ.hom).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _

/-- Derived extension of scalars along a flat ring map. -/
abbrev extD {A B : CommRingCat.{u}} (φ : A ⟶ B) [Fact φ.hom.Flat] :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} B) :=
  (ModuleCat.extendScalars.{u, u, u} φ.hom).mapDerivedCategory

/-- `Ext^n_{R_f}(K ⊗_R R_f, L ⊗_R R_f)`, for `K`, `L` in `D(R)`. -/
abbrev localizedExt (K L : DerivedCategory (ModuleCat.{u} R)) (f : R) (n : ℤ) :=
  (extD (locMap R f)).obj K ⟶ ((extD (locMap R f)).obj L)⟦n⟧

/-- Extension of scalars along `R ⟶ R_f ⟶ R_g` is extension of scalars along `R ⟶ R_g`. -/
def extendScalarsCompIso {f g : R} (h : basicOpen R g ≤ basicOpen R f) :
    ModuleCat.extendScalars.{u, u, u} (locMap R f).hom ⋙
        ModuleCat.extendScalars.{u, u, u} (resMap R h).hom ≅
      ModuleCat.extendScalars.{u, u, u} (locMap R g).hom :=
  (ModuleCat.extendScalarsComp (locMap R f).hom (resMap R h).hom).symm ≪≫
    eqToIso (by rw [← CommRingCat.hom_comp, locMap_comp_resMap])

/-- Derived extension of scalars along `R ⟶ R_f ⟶ R_g` is derived extension of scalars along
`R ⟶ R_g`. -/
def extDCompIso {f g : R} (h : basicOpen R g ≤ basicOpen R f) :
    extD (locMap R f) ⋙ extD (resMap R h) ≅ extD (locMap R g) :=
  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _).symm ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _ (extendScalarsCompIso R h)

/-- **The restriction maps of the `Ext` presheaf.** For `D(g) ⊆ D(f)`, the map
`Ext^n_{R_f}(K ⊗ R_f, L ⊗ R_f) ⟶ Ext^n_{R_g}(K ⊗ R_g, L ⊗ R_g)` induced by derived extension of
scalars along `R_f ⟶ R_g`. -/
def localizedExtRestrict (K L : DerivedCategory (ModuleCat.{u} R)) {f g : R}
    (h : basicOpen R g ≤ basicOpen R f) (n : ℤ) :
    localizedExt R K L f n → localizedExt R K L g n := fun α =>
  ((extDCompIso R h).app K).inv ≫ (extD (resMap R h)).map α ≫
    ((extD (resMap R h)).commShiftIso n).hom.app _ ≫ ((extDCompIso R h).app L).hom⟦n⟧'

/-- The `n`-th cohomology sheaf of `R𝓗om(K̃, L̃)` on `Spec R`. -/
abbrev cohomologySheaf (K L : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) : (Spec R).Modules :=
  (DerivedCategory.homologyFunctor (Stacks.SheafOfModules.StructureSheafModules (Spec R).sheaf)
      n).obj
    (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
      (op ((tilde.functor R).mapDerivedCategory.obj K))).obj
        ((tilde.functor R).mapDerivedCategory.obj L))

end AlgebraicGeometry.AffineExt
