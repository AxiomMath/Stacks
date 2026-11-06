module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ZariskiModuleDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOfToposHom

/-!
# The small crystalline topos and the small Zariski topos as ringed topoi

The base change map of [Stacks, Tag 07MS] is the base change map of [Stacks, Tag 07A7] for the
square of ringed topoi formed by the structure morphisms `τ_{X/S}`, `τ_{X'/S'}`, the morphism
`f_cris` of [Stacks, Tag 07IK] and the Zariski morphism `S ⟶ S'`.  The derived pullback,
pushforward and base change map of `Stacks.Cohomology.DerivedBaseChangeOfToposHom` are stated for
`AlgebraicGeometry.RingedTopos`, a site with a sheaf of *commutative* rings whose sections live in
the universe of the topos.  This file supplies the two ringed topoi.

* The crystalline topos `(X/S)_cris` is `Sheaf (smallTopology S) (Type (u + 1))`, so its structure
  sheaf is `𝒪_{X/S}` with sections raised to `CommRingCat.{u + 1}`: `commStructureSheafULift`.
  Modules over it are the chapter's `ModuleSheaf S`, by `crisModuleEquivalence`, which changes
  neither the presheaf of sections nor the morphisms.
* The Zariski topos of a scheme `Z ∈ Scheme.{u}` is likewise taken at `Type (u + 1)`, the universe
  of `Crystalline.GlobalCrystallineSituation.structureToposMorphism`, with `𝒪_Z` raised to
  `CommRingCat.{u + 1}`: `zariskiRingedTopos`.  Its derived category of modules is the
  `D(𝒪_Z)` the sheaf-level base change map of [Stacks, Tag 07MS] lives in.

Both are supplied with the instances — sheafification of abelian sheaves, Grothendieck
abelianness of the modules — under which the unbounded derived pullback, pushforward and the
base change map of [Stacks, Tag 07A7] exist for morphisms between them.

## Main definitions

* `commStructureSheafULift`, `crisRingedTopos`, `crisModuleEquivalence`.
* `zariskiStructureSheafULift`, `zariskiRingedTopos`.

## References

* [Stacks Project, Tag 07MS](https://stacks.math.columbia.edu/tag/07MS)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-! ### The crystalline topos -/

/-- **`𝒪_{X/S}` with its sections raised to `CommRingCat.{u + 1}`**, as a sheaf of commutative
rings on the small crystalline site.  Its sections over `(U, T, δ)` are `ULift Γ(T, 𝒪_T)`; the
sheaf condition is that of the sets of sections, `...SmallSite.isSheafType_crisRing`. -/
def commStructureSheafULift : Sheaf (smallTopology S) CommRingCat.{u + 1} :=
  have : HasLimitsOfSize.{u, u + 1} CommRingCat.{u + 1} :=
    hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _
  ⟨Stacks.Modules.ringULift.{u + 1, u, u, u} (structurePresheaf S),
    (Presheaf.isSheaf_iff_isSheaf_comp (smallTopology S) _
      (CategoryTheory.forget CommRingCat.{u + 1})).mpr
      (Presheaf.isSheaf_comp_of_isSheaf (smallTopology S) _
        CategoryTheory.uliftFunctor.{u + 1, u} (isSheafType_crisRing S))⟩

/-- **The crystalline topos `(X/S)_cris` as a ringed topos**: the small crystalline site with the
structure sheaf `𝒪_{X/S}`, its sections raised to the universe `u + 1` of the topos. -/
abbrev crisRingedTopos : RingedTopos.{u, u + 1, u + 1} :=
  ⟨CrystallineThickening S, smallTopology S, commStructureSheafULift S⟩

/-- The sheaf condition for commutative rings with sections in `Type (u + 1)` on the small
crystalline site is preserved by forgetting commutativity. -/
instance : (crisRingedTopos S).J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  Stacks.hasSheafCompose_forget₂_commRingCat.{u + 1} _

/-- The sheaf of rings underlying the structure sheaf of `crisRingedTopos` is
`...SmallSite.structureSheafULift`, on the nose. -/
theorem ringSheaf_crisRingedTopos :
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (crisRingedTopos S).J))
        (crisRingedTopos S).O =
      structureSheafULift S :=
  rfl

/-- **Sheaves of modules on the crystalline ringed topos are the chapter's sheaves of
`𝒪_{X/S}`-modules**: `...SmallSite.moduleRingULiftEquivalence`, an isomorphism of categories
changing neither the sections nor the morphisms. -/
def crisModuleEquivalence :
    ModuleSheaf S ≌
      SheafOfModules.{u + 1}
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (crisRingedTopos S).J))
          (crisRingedTopos S).O) :=
  moduleRingULiftEquivalence S

/-! ### The Zariski topos of a scheme -/

variable (Z : Scheme.{u})

/-- **`𝒪_Z` with its sections raised to `CommRingCat.{u + 1}`**, as a sheaf of commutative rings
on the small Zariski site of `Z`. -/
def zariskiStructureSheafULift :
    Sheaf (Opens.grothendieckTopology Z.carrier) CommRingCat.{u + 1} :=
  have : HasLimitsOfSize.{u, u} CommRingCat.{u + 1} :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  ⟨Stacks.Modules.ringULift.{u, u, u, u + 1} Z.presheaf,
    (Presheaf.isSheaf_iff_isSheaf_comp (Opens.grothendieckTopology Z.carrier) _
      (CategoryTheory.forget CommRingCat.{u + 1})).mpr
      (Presheaf.isSheaf_comp_of_isSheaf (Opens.grothendieckTopology Z.carrier) _
        CategoryTheory.uliftFunctor.{u + 1, u}
        ((Presheaf.isSheaf_iff_isSheaf_comp (Opens.grothendieckTopology Z.carrier) _
          (CategoryTheory.forget CommRingCat.{u})).mp Z.sheaf.property))⟩

/-- **The small Zariski topos of `Z` as a ringed topos**, at the universe `u + 1` of sheaves of
sets: the opens of `Z` with `𝒪_Z`, its sections raised to `u + 1`. -/
abbrev zariskiRingedTopos : RingedTopos.{u, u, u + 1} :=
  ⟨Opens Z.carrier, Opens.grothendieckTopology Z.carrier, zariskiStructureSheafULift Z⟩

/-! ### The instances the derived functors of ringed topoi need -/

/-- Abelian sheaves on the small crystalline site admit sheafification at the universe of the
topos. -/
instance : HasSheafify (crisRingedTopos S).J AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _

/-- Sheafification of abelian presheaves on the small crystalline site inverts exactly the locally
bijective morphisms. -/
instance : (crisRingedTopos S).J.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u, u + 1} _

/-- Modules on the crystalline ringed topos form an abelian category. -/
instance : Abelian (SheafOfModules.{u + 1}
    ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (crisRingedTopos S).J))
      (crisRingedTopos S).O)) :=
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian.{u + 1, u, u + 1, u} _

/-- Modules on the crystalline ringed topos form a Grothendieck abelian category, so every
complex has a K-injective resolution. -/
instance : IsGrothendieckAbelian.{u + 1} (SheafOfModules.{u + 1}
    ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (crisRingedTopos S).J))
      (crisRingedTopos S).O)) :=
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck.{u + 1, u, u + 1, u} _

/-- The sheaf condition for commutative rings on the opens of `Z` is preserved by forgetting
commutativity. -/
instance : (zariskiRingedTopos Z).J.HasSheafCompose
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  Stacks.hasSheafCompose_forget₂_commRingCat.{u + 1} _

/-- Abelian sheaves on the opens of `Z` admit sheafification at the universe `u + 1`. -/
instance : HasSheafify (zariskiRingedTopos Z).J AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u} _

/-- Sheafification of abelian presheaves on the opens of `Z` inverts exactly the locally bijective
morphisms. -/
instance : (zariskiRingedTopos Z).J.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u, u} _

/-- Modules on the Zariski ringed topos form an abelian category. -/
instance : Abelian (SheafOfModules.{u + 1}
    ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u + 1} (J := (zariskiRingedTopos Z).J))
      (zariskiRingedTopos Z).O)) :=
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian.{u, u, u + 1, u} _

/-- Modules on the Zariski ringed topos form a Grothendieck abelian category. -/
instance : IsGrothendieckAbelian.{u + 1} (SheafOfModules.{u + 1}
    ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u + 1} (J := (zariskiRingedTopos Z).J))
      (zariskiRingedTopos Z).O)) :=
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck.{u, u, u + 1, u} _

/-! ### The Zariski morphism of a morphism of schemes -/

variable {Z} in
/-- **The morphism of small Zariski ringed topoi `(Z_Zar, 𝒪_Z) ⟶ (Z'_Zar, 𝒪_{Z'})` of a morphism
of schemes `φ : Z ⟶ Z'`**, at the universe `u + 1` of sheaves of sets.  The underlying morphism of
topoi is `StacksZariskiSite.opensMapMorphismOfTopoi`, whose direct image is restriction along
`Opens.map φ`, and the structure map `𝒪_{Z'} ⟶ φ_*𝒪_Z` is `φ^♯`, its sections raised to `u + 1`;
it is read in the direct image of sheaves of commutative rings through
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso`, which is the identity on sections. -/
def zariskiRingedHom {Z' : Scheme.{u}} (φ : Z ⟶ Z') :
    RingedToposHom (zariskiRingedTopos Z) (zariskiRingedTopos Z') where
  toToposHom := StacksZariskiSite.opensMapMorphismOfTopoi φ.base
  fSharp :=
    (ObjectProperty.homMk
        (Functor.whiskerRight φ.c AlgebraicGeometry.SheafOfModules.commRingCatULift.{u, u + 1}) :
      zariskiStructureSheafULift Z' ⟶
        ((Opens.map φ.base).sheafPushforwardContinuous CommRingCat.{u + 1}
          (Opens.grothendieckTopology Z') (Opens.grothendieckTopology Z)).obj
          (zariskiStructureSheafULift Z)) ≫
      (Stacks.Sheaves.ToposPullback.restrictionCommRingIso (Opens.grothendieckTopology Z')
        (Opens.grothendieckTopology Z) (Opens.map φ.base) (zariskiStructureSheafULift Z)).inv

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
