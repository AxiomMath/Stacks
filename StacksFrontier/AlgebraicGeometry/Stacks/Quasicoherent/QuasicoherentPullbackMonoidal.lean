module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorMonoidal
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RestrictedStackHigherDirectImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackBraided
public import StacksFrontier.CategoryTheory.Monoidal.BraidedFunctorTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedMonoidalStructure

/-!
# The inverse image of modules on algebraic stacks is a braided monoidal functor

Let `g : 𝒰 ⟶ 𝒳` be a 1-morphism of algebraic stacks. `Mod(𝒪_𝒳)` carries the symmetric monoidal
structure of Tag 01CA (`AlgebraicGeometry.Stack.AlgebraicStacks.fppfModulesMonoidal`), and so
does `QCoh(𝒪_𝒳)`, a monoidal subcategory by Stacks 0GQM. This file makes the inverse image
`g^* : Mod(𝒪_𝒳) ⥤ Mod(𝒪_𝒰)` and its restriction `g^* : QCoh(𝒪_𝒳) ⥤ QCoh(𝒪_𝒰)` braided
monoidal functors.

The inverse image is the pullback of modules along the morphism of ringed topoi of `g`
(Stacks 06TW), by `AlgebraicGeometry.FibredSite.pullbackModulesIsoModulePullback`, and that
pullback is braided monoidal by Tag 03EL
(`Stacks.SheafOfModules.RingedToposPullback.pullbackBraided`). The structures here are
transported along that identification, so the oplax tensorator of `g^*` is the comparison
`g^*(M ⊗ N) ⟶ g^*M ⊗ g^*N` of Tag 03EL read through it.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.fppfModulesRingedToposHom`: the morphism of ringed
  topoi of `g` (Stacks 06TW) on the fppf sites.
* `AlgebraicGeometry.Stack.AlgebraicStacks.fppfModulesPullbackMonoidal` and
  `fppfModulesPullbackBraided`: `g^*` on `Mod(𝒪)` as a monoidal and as a braided functor.
* `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentPullbackMonoidal` and
  `quasicoherentPullbackBraided`: the same on `QCoh(𝒪)`.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 06TW](https://stacks.math.columbia.edu/tag/06TW)
* [Stacks Project, Tag 0GQM](https://stacks.math.columbia.edu/tag/0GQM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] hasSheafCompose_forget_ringCat
  hasSheafCompose_forget_commRingCat Stacks.hasSheafCompose_forget₂_commRingCat
  FlatFppf.hasSheafify_addCommGrpCat FlatFppf.wEqualsLocallyBijective_addCommGrpCat
  FlatFppf.hasSheafify_fppf_addCommGrpCat FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat
  FlatFppf.hasSheafify_associatedTopology_ab
  FlatFppf.wEqualsLocallyBijective_fppfTopology_addCommGrpCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒰 ⟶ 𝒳)

/-- **The morphism of ringed topoi of a 1-morphism `g` of algebraic stacks on the fppf sites**
(Stacks 06TW), in the four-field form the pullback of modules of Tag 03EL is stated for. -/
abbrev fppfModulesRingedToposHom :=
  (FibredSite.ringedToposMorphism B S hS 𝒰.val.val.p 𝒳.val.val.p
    𝒰.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor g.hom)
    (𝒳.val.isFiberedInGroupoids.isFibredOneMorphism
      (CatFiberedInGroupoids.homFunctor_comp_p g.hom)) .fppf).toModulesHom

local notation "ψ" => fppfModulesRingedToposHom g

/-- The pullback of modules along `ψ` is the inverse image `g^*`. -/
local notation "𝔦" => FibredSite.pullbackModulesIsoModulePullback B S hS 𝒰.val.val.p
  𝒳.val.val.p 𝒰.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
  (CatFiberedInGroupoids.homFunctor g.hom) (𝒳.val.isFiberedInGroupoids.isFibredOneMorphism
    (CatFiberedInGroupoids.homFunctor_comp_p g.hom)) SiteKind.fppf

/-- **The inverse image `g^* : Mod(𝒪_𝒳) ⥤ Mod(𝒪_𝒰)` along a 1-morphism of algebraic stacks is a
monoidal functor** for the monoidal structures of Tag 01CA: the monoidal structure of the
pullback of modules along the morphism of ringed topoi of `g` (Tag 03EL), transported along
`AlgebraicGeometry.FibredSite.pullbackModulesIsoModulePullback`. -/
@[instance_reducible]
def fppfModulesPullbackMonoidal :
    letI := fppfModulesMonoidal B S hS 𝒰
    letI := fppfModulesMonoidal B S hS 𝒳
    (fppfModulesPullback B S hS g).Monoidal :=
  @Functor.Monoidal.transport (Stack.fppfModules B S hS 𝒳) _ (fppfModulesMonoidal B S hS 𝒳)
    (Stack.fppfModules B S hS 𝒰) _ (fppfModulesMonoidal B S hS 𝒰) (ψ).pullbackModules
    (fppfModulesPullback B S hS g)
    (Stacks.SheafOfModules.RingedToposPullback.pullbackMonoidal ψ) 𝔦

/-- **The inverse image `g^* : Mod(𝒪_𝒳) ⥤ Mod(𝒪_𝒰)` along a 1-morphism of algebraic stacks is a
braided monoidal functor** for the symmetric monoidal structures of Tag 01CA. Its underlying
monoidal structure is `fppfModulesPullbackMonoidal` (`fppfModulesPullbackBraided_toMonoidal`). -/
@[instance_reducible]
def fppfModulesPullbackBraided :
    letI := fppfModulesMonoidal B S hS 𝒰
    letI := fppfModulesMonoidal B S hS 𝒳
    letI := fppfModulesBraided B S hS 𝒰
    letI := fppfModulesBraided B S hS 𝒳
    (fppfModulesPullback B S hS g).Braided :=
  @Functor.Braided.transport (Stack.fppfModules B S hS 𝒳) (Stack.fppfModules B S hS 𝒰) _ _
    (fppfModulesMonoidal B S hS 𝒳) (fppfModulesMonoidal B S hS 𝒰)
    (fppfModulesBraided B S hS 𝒳) (fppfModulesBraided B S hS 𝒰) (ψ).pullbackModules
    (fppfModulesPullback B S hS g)
    (Stacks.SheafOfModules.RingedToposPullback.pullbackBraided ψ) 𝔦

/-- The monoidal structure underlying `fppfModulesPullbackBraided` is
`fppfModulesPullbackMonoidal`. -/
theorem fppfModulesPullbackBraided_toMonoidal :
    (fppfModulesPullbackBraided g).toMonoidal = fppfModulesPullbackMonoidal g :=
  rfl

section Quasicoherent

attribute [local instance] fppfModulesMonoidal fppfModulesBraided fppfModulesSymmetric

/-- **The inverse image `g^* : QCoh(𝒪_𝒳) ⥤ QCoh(𝒪_𝒰)` along a 1-morphism of algebraic stacks is
a monoidal functor**: `fppfModulesPullbackMonoidal` restricted to the monoidal subcategories of
quasi-coherent modules (Stacks 0GQM). Its unit and tensorator are those of `g^*` on modules. -/
@[instance_reducible]
def quasicoherentPullbackMonoidal : (quasicoherentPullback B S hS g).Monoidal :=
  letI := fppfModulesPullbackMonoidal g
  ObjectProperty.liftMonoidal _ _ _

/-- **The inverse image `g^* : QCoh(𝒪_𝒳) ⥤ QCoh(𝒪_𝒰)` along a 1-morphism of algebraic stacks is
a braided monoidal functor** for the symmetric monoidal structures of Stacks 0GQM. Its underlying
monoidal structure is `quasicoherentPullbackMonoidal`. -/
@[instance_reducible]
def quasicoherentPullbackBraided : (quasicoherentPullback B S hS g).Braided :=
  letI := fppfModulesPullbackBraided g
  letI := quasicoherentPullbackMonoidal g
  { braided := fun M N => (ObjectProperty.liftLaxBraided _ _ _).braided M N }

/-- The monoidal structure underlying `quasicoherentPullbackBraided` is
`quasicoherentPullbackMonoidal`. -/
theorem quasicoherentPullbackBraided_toMonoidal :
    (quasicoherentPullbackBraided g).toMonoidal = quasicoherentPullbackMonoidal g :=
  rfl

/-- The tensorator of `quasicoherentPullbackMonoidal` is that of `fppfModulesPullbackMonoidal`,
on the underlying modules. -/
theorem quasicoherentPullbackMonoidal_μ_hom (M N : quasicoherentModules B S hS 𝒳) :
    (Functor.LaxMonoidal.μ (self := (quasicoherentPullbackMonoidal g).toLaxMonoidal)
        (quasicoherentPullback B S hS g) M N).hom =
      Functor.LaxMonoidal.μ (self := (fppfModulesPullbackMonoidal g).toLaxMonoidal)
        (fppfModulesPullback B S hS g) M.obj N.obj :=
  rfl

/-- The unit morphism of `quasicoherentPullbackMonoidal` is that of `fppfModulesPullbackMonoidal`,
on the underlying modules. -/
theorem quasicoherentPullbackMonoidal_ε_hom :
    (Functor.LaxMonoidal.ε (self := (quasicoherentPullbackMonoidal g).toLaxMonoidal)
        (quasicoherentPullback B S hS g)).hom =
      Functor.LaxMonoidal.ε (self := (fppfModulesPullbackMonoidal g).toLaxMonoidal)
        (fppfModulesPullback B S hS g) :=
  rfl

end Quasicoherent

end AlgebraicGeometry.Stack.AlgebraicStacks
