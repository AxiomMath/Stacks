module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentFlatBaseChangeSheafFppf

/-!
# The coherator of Stacks 0778 on the faithful `LQCoh^fbc(𝒪_𝒳)`, through `Mod(𝒪_𝒳)`

The coherator `Q : LQCoh^fbc(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)` of **Stacks 0778** is the right adjoint of the
inclusion `i : QCoh(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒳)` of
`AlgebraicGeometry.Stack.quasicoherentToFlatBaseChangeSheaf`.  It is built here as the composite
of the fully faithful functor `j : LQCoh^fbc(𝒪_𝒳) ⥤ Mod(𝒪_𝒳)` of **Stacks 0771** (1),
`AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeSheafToFppf`, with the coherator
`Mod(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)` of **Stacks 0781** (2), `AlgebraicGeometry.FibredSite.moduleCoherator`:
`i` followed by `j` is the inclusion `QCoh(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`, so the adjunction of 0781 (2)
restricts along `j` (`CategoryTheory.Adjunction.restrictFullyFaithful`).

The closure of quasi-coherence under colimits that the coherator of 0781 (2) needs is
**Stacks 03DX** (1) at the big fppf site,
`AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'`.

## Main definitions

* `AlgebraicGeometry.Stack.flatBaseChangeSheafQuasicoherator`: the coherator `Q = j ⋙ Q_Mod`.
* `AlgebraicGeometry.Stack.flatBaseChangeSheafQuasicoheratorAdjunction`: `i ⊣ Q`.
* `AlgebraicGeometry.Stack.flatBaseChangeSheafQuasicoheratorCompInclusionIsoId`: `i ⋙ Q ≅ 𝟭`.

## Implementation notes

Two inputs are hypotheses: `hfbc`, the flat base change half of `QCoh(𝒪_𝒳) ⊆ LQCoh^fbc(𝒪_𝒳)`
(the sheaf-level reading of clause (b) of the forward direction of **Stacks 06WK**), and `hsep`,
the separator of **Stacks 0781** (1) together with the abelian structure of **Stacks 06WV** (2).

## References

* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0781](https://stacks.math.columbia.edu/tag/0781)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] [EssentiallySmall.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **`Mod(𝒪_𝒳)` is locally `u`-small**: the category of sheaves of modules on the associated
fppf site is locally `u`-small. -/
theorem locallySmall_fppfModules :
    LocallySmall.{u} (SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf)) :=
  have : HasSheafify (BigFppfOver.associatedTopology B S hS p SiteKind.fppf) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  have : (BigFppfOver.associatedTopology B S hS p SiteKind.fppf).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u + 1, u + 1, u} _
  (SheafOfModules.isGrothendieckAbelian_of_essentiallySmall
    (FibredSite.ringStructureSheafCore B S hS p hp .fppf)).locallySmall

/-- The inclusion `QCoh(𝒪_𝒳) ⟶ LQCoh^fbc(𝒪_𝒳)` followed by `j : LQCoh^fbc(𝒪_𝒳) ⟶ Mod(𝒪_𝒳)` of
**Stacks 0771** (1) is the inclusion `QCoh(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`; all three are the identity on
underlying presheaves of modules. -/
def quasicoherentToFlatBaseChangeSheafCompIso
    (hfbc : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp,
      HasFlatBaseChangePropertySheaf B (associatedBigEtaleSite B) rfl S hS p hp
        ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS p hp .etale).obj F)) :
    𝟭 _ ⋙ (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.ringStructureSheafCore B S hS p hp .fppf)).ι ≅
      quasicoherentToFlatBaseChangeSheaf B S hS p hp hfbc ⋙
        locallyQuasicoherentFlatBaseChangeSheafToFppf B (associatedBigEtaleSite B) rfl S hS p hp :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl

section Coherator

variable [Abelian (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp)]
  (hfbc : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp,
    HasFlatBaseChangePropertySheaf B (associatedBigEtaleSite B) rfl S hS p hp
      ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS p hp .etale).obj F))
  (hsep : HasSeparator (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp))

/-- **The coherator `Q : LQCoh^fbc(𝒪_𝒳) ⟶ QCoh(𝒪_𝒳)` of Stacks 0778**, on the subcategory of the
source: the functor `j : LQCoh^fbc(𝒪_𝒳) ⟶ Mod(𝒪_𝒳)` of **Stacks 0771** (1) followed by the
coherator `Mod(𝒪_𝒳) ⟶ QCoh(𝒪_𝒳)` of **Stacks 0781** (2). -/
def flatBaseChangeSheafQuasicoherator :
    locallyQuasicoherentFlatBaseChangeSheafModules B S hS p hp ⥤
      FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp :=
  locallyQuasicoherentFlatBaseChangeSheafToFppf B (associatedBigEtaleSite B) rfl S hS p hp ⋙
    FibredSite.moduleCoherator B S hS p hp
      (FibredSite.closedUnderColimitsOfSize_quasicoherentModules_of_surjective B S hS p hp
        (BigFppfOver.quasicoherentIsEssImageAssociatedModule' B))
      (FibredSite.locallySmall_quasicoherentModules B S hS p hp)
      (locallySmall_fppfModules B S hS p hp)
      (FibredSite.wellPowered_op_quasicoherentModules B S hS p hp) hsep

/-- **The coherator is right adjoint to the inclusion** (Stacks 0778).  The inclusion
`QCoh(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)` factors through `j`, which is fully faithful, so the adjunction of
**Stacks 0781** (2) restricts. -/
def flatBaseChangeSheafQuasicoheratorAdjunction :
    quasicoherentToFlatBaseChangeSheaf B S hS p hp hfbc ⊣
      flatBaseChangeSheafQuasicoherator B S hS p hp hsep :=
  Adjunction.restrictFullyFaithful
    (FibredSite.moduleCoheratorAdjunction B S hS p hp
      (FibredSite.closedUnderColimitsOfSize_quasicoherentModules_of_surjective B S hS p hp
        (BigFppfOver.quasicoherentIsEssImageAssociatedModule' B))
      (FibredSite.locallySmall_quasicoherentModules B S hS p hp)
      (locallySmall_fppfModules B S hS p hp)
      (FibredSite.wellPowered_op_quasicoherentModules B S hS p hp) hsep)
    (Functor.FullyFaithful.id _)
    (fullyFaithfulLocallyQuasicoherentFlatBaseChangeSheafToFppf B (associatedBigEtaleSite B) rfl
      S hS p hp)
    (quasicoherentToFlatBaseChangeSheafCompIso B S hS p hp hfbc) (Functor.rightUnitor _).symm

/-- **`Q ∘ i` is the identity functor** (Stacks 0778): the inclusion is fully faithful, so the
unit of the adjunction is an isomorphism. -/
def flatBaseChangeSheafQuasicoheratorCompInclusionIsoId :
    quasicoherentToFlatBaseChangeSheaf B S hS p hp hfbc ⋙
        flatBaseChangeSheafQuasicoherator B S hS p hp hsep ≅
      𝟭 (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp) :=
  letI := (fullyFaithfulQuasicoherentToFlatBaseChangeSheaf B S hS p hp hfbc).full
  letI := (fullyFaithfulQuasicoherentToFlatBaseChangeSheaf B S hS p hp hfbc).faithful
  (asIso (flatBaseChangeSheafQuasicoheratorAdjunction B S hS p hp hfbc hsep).unit).symm

end Coherator

/-! ### The coherator on `LQCoh^fbc(𝒪_𝒳)` read inside `Mod(𝒪_𝒳)` -/

/-- **The inclusion `QCoh(𝒪_𝒳) ⟶ LQCoh^fbc(𝒪_𝒳)`, with `LQCoh^fbc(𝒪_𝒳)` read inside
`Mod(𝒪_𝒳)`.** -/
def quasicoherentToFlatBaseChangeSheafFppf
    (hfbc : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp,
      HasFlatBaseChangePropertySheaf B (associatedBigEtaleSite B) rfl S hS p hp
        ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS p hp .etale).obj F)) :
    FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp ⥤
      (locallyQuasicoherentFlatBaseChangeSheafFppf B (associatedBigEtaleSite B) rfl S hS p
        hp).FullSubcategory :=
  ObjectProperty.lift _ (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS p hp .fppf)).ι
    fun F => ⟨isLocallyQuasicoherent_toSiteModules_etale B (associatedBigEtaleSite B) rfl S hS p
      hp F, hfbc F⟩

/-- The inclusion `QCoh(𝒪_𝒳) ⟶ LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)` is the inclusion
`QCoh(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`. -/
def quasicoherentToFlatBaseChangeSheafFppfCompIso
    (hfbc : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp,
      HasFlatBaseChangePropertySheaf B (associatedBigEtaleSite B) rfl S hS p hp
        ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS p hp .etale).obj F)) :
    𝟭 _ ⋙ (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.ringStructureSheafCore B S hS p hp .fppf)).ι ≅
      quasicoherentToFlatBaseChangeSheafFppf B S hS p hp hfbc ⋙
        (locallyQuasicoherentFlatBaseChangeSheafFppf B (associatedBigEtaleSite B) rfl S hS p
          hp).ι :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl

section CoheratorFppf

variable [Abelian (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp)]
  (hfbc : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp,
    HasFlatBaseChangePropertySheaf B (associatedBigEtaleSite B) rfl S hS p hp
      ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS p hp .etale).obj F))
  (hsep : HasSeparator (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp))

/-- **The coherator `Q : LQCoh^fbc(𝒪_𝒳) ⟶ QCoh(𝒪_𝒳)` of Stacks 0778**, with
`LQCoh^fbc(𝒪_𝒳)` read inside `Mod(𝒪_𝒳)`: the coherator of **Stacks 0781** (2) restricted to
`LQCoh^fbc(𝒪_𝒳)`. -/
def flatBaseChangeSheafFppfQuasicoherator :
    (locallyQuasicoherentFlatBaseChangeSheafFppf B (associatedBigEtaleSite B) rfl S hS p
        hp).FullSubcategory ⥤
      FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp :=
  (locallyQuasicoherentFlatBaseChangeSheafFppf B (associatedBigEtaleSite B) rfl S hS p hp).ι ⋙
    FibredSite.moduleCoherator B S hS p hp
      (FibredSite.closedUnderColimitsOfSize_quasicoherentModules_of_surjective B S hS p hp
        (BigFppfOver.quasicoherentIsEssImageAssociatedModule' B))
      (FibredSite.locallySmall_quasicoherentModules B S hS p hp)
      (locallySmall_fppfModules B S hS p hp)
      (FibredSite.wellPowered_op_quasicoherentModules B S hS p hp) hsep

/-- **The coherator is right adjoint to the inclusion** (Stacks 0778), with `LQCoh^fbc(𝒪_𝒳)`
read inside `Mod(𝒪_𝒳)`. -/
def flatBaseChangeSheafFppfQuasicoheratorAdjunction :
    quasicoherentToFlatBaseChangeSheafFppf B S hS p hp hfbc ⊣
      flatBaseChangeSheafFppfQuasicoherator B S hS p hp hsep :=
  Adjunction.restrictFullyFaithful
    (FibredSite.moduleCoheratorAdjunction B S hS p hp
      (FibredSite.closedUnderColimitsOfSize_quasicoherentModules_of_surjective B S hS p hp
        (BigFppfOver.quasicoherentIsEssImageAssociatedModule' B))
      (FibredSite.locallySmall_quasicoherentModules B S hS p hp)
      (locallySmall_fppfModules B S hS p hp)
      (FibredSite.wellPowered_op_quasicoherentModules B S hS p hp) hsep)
    (Functor.FullyFaithful.id _)
    (ObjectProperty.fullyFaithfulι _)
    (quasicoherentToFlatBaseChangeSheafFppfCompIso B S hS p hp hfbc) (Functor.rightUnitor _).symm

end CoheratorFppf

end AlgebraicGeometry.Stack

end
