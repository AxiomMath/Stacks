module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Adjunction.Comma
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentColimitsOfSize
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSmoothLocal

/-!
# The coherator on an algebraic stack

Let `𝒳` be a category fibred in groupoids over the schemes over `S`, and let `QCoh(𝒪_𝒳)` be its
category of quasi-coherent modules. Two inclusions of `QCoh(𝒪_𝒳)` have a right adjoint, and the
right adjoint is the same construction in both cases:

* the inclusion `QCoh(𝒪_𝒳) → Mod(𝒪_𝒳)` into all modules on the associated fppf site, and
* the inclusion `QCoh(𝒪_𝒳) → LQCoh^fbc(𝒪_𝒳)` into the locally quasi-coherent modules with the
  flat base change property on the associated étale site.

That right adjoint is the *coherator*. For an ambient module `A`, an object of
`CostructuredArrow i A` is a quasi-coherent module `G` together with a map `i G ⟶ A`, and the
coherator at `A` is the terminal such `G`; the adjunction bijection `Hom(G, Q A) ≃ Hom(i G, A)`
is the universal property of that terminal object. The terminal object exists when `QCoh(𝒪_𝒳)`
is cocomplete, the inclusion preserves its colimits, and `QCoh(𝒪_𝒳)` is locally small and
well-copowered with a separator. Since the inclusions are fully faithful, the coherator composed
with the inclusion is the identity of `QCoh(𝒪_𝒳)`.

`QCoh(𝒪_𝒳)` is a Grothendieck abelian category under local smallness, the exactness of filtered
colimits and the existence of a separator; it then has enough injectives and all limits.

## Main definitions

* `AlgebraicGeometry.FibredSite.moduleCoherator`: the coherator `Q : Mod(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)`,
  with `AlgebraicGeometry.FibredSite.moduleCoheratorAdjunction` and
  `AlgebraicGeometry.FibredSite.moduleCoheratorCompInclusionIsoId`.
* `AlgebraicGeometry.Stack.quasicoherentToFlatBaseChange`: the inclusion
  `i : QCoh(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒳)`, the restriction of an fppf module to the étale site, with
  the membership of its image in `LQCoh^fbc(𝒪_𝒳)` as a hypothesis.
* `AlgebraicGeometry.Stack.flatBaseChangeQuasicoherator`: the coherator
  `Q : LQCoh^fbc(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)`, with
  `AlgebraicGeometry.Stack.flatBaseChangeQuasicoheratorAdjunction` and
  `AlgebraicGeometry.Stack.flatBaseChangeQuasicoheratorCompInclusionIsoId`.

## Main results

* `AlgebraicGeometry.FibredSite.hasTerminal_costructuredArrow_of_quasicoherentModules`: over a
  functor out of `QCoh(𝒪_𝒳)` preserving colimits, every object of the target has a terminal
  quasi-coherent module mapping to it.
* `AlgebraicGeometry.FibredSite.isGrothendieckAbelian_quasicoherentModules`: `QCoh(𝒪_𝒳)` is a
  Grothendieck abelian category, with
  `AlgebraicGeometry.FibredSite.enoughInjectives_quasicoherentModules` and
  `AlgebraicGeometry.FibredSite.hasLimitsOfSize_quasicoherentModules` its two consequences.
* `AlgebraicGeometry.Stack.fullyFaithful_quasicoherentToFlatBaseChange`: the inclusion
  `QCoh(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒳)` is fully faithful.

## References

* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0781](https://stacks.math.columbia.edu/tag/0781)
* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] [EssentiallySmall.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The category `QCoh(𝒪_𝒳)` of quasi-coherent modules on the associated fppf site of a category
fibred in groupoids is a Grothendieck abelian category, provided quasi-coherence is closed under
colimits (`hclosed`), `QCoh(𝒪_𝒳)` is locally small (`hls`), its filtered colimits are exact
(`hab5`) and it has a separator (`hsep`). -/
@[stacks 0781 "part (1): QCoh(𝒪_𝒳) is Grothendieck abelian, over local smallness, the exactness \
  of filtered colimits, and the separator the source gets from a groupoid presentation"]
theorem isGrothendieckAbelian_quasicoherentModules
    [Abelian (quasicoherentModules.{u, u + 1, u, u} B S hS p hp)]
    (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf))
    (hls : LocallySmall.{u} (quasicoherentModules.{u, u + 1, u, u} B S hS p hp))
    (hab5 : ∀ (K : Type u) [Category.{u} K] [IsFiltered K]
      [HasColimitsOfShape K (quasicoherentModules.{u, u + 1, u, u} B S hS p hp)],
      HasExactColimitsOfShape K (quasicoherentModules.{u, u + 1, u, u} B S hS p hp))
    (hsep : HasSeparator (quasicoherentModules.{u, u + 1, u, u} B S hS p hp)) :
    IsGrothendieckAbelian.{u} (quasicoherentModules.{u, u + 1, u, u} B S hS p hp) :=
  let := hasColimitsOfSize_quasicoherentModules B S hS p hp hclosed
  { locallySmall := hls
    ab5OfSize := ⟨fun K _ _ => hab5 K⟩
    hasSeparator := hsep }

/-- Under the hypotheses of
`AlgebraicGeometry.FibredSite.isGrothendieckAbelian_quasicoherentModules`, `QCoh(𝒪_𝒳)` has
enough injectives. -/
@[stacks 0781 "part (1), its consequence: QCoh(𝒪_𝒳) has enough injectives"]
theorem enoughInjectives_quasicoherentModules
    [Abelian (quasicoherentModules.{u, u + 1, u, u} B S hS p hp)]
    (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf))
    (hls : LocallySmall.{u} (quasicoherentModules.{u, u + 1, u, u} B S hS p hp))
    (hab5 : ∀ (K : Type u) [Category.{u} K] [IsFiltered K]
      [HasColimitsOfShape K (quasicoherentModules.{u, u + 1, u, u} B S hS p hp)],
      HasExactColimitsOfShape K (quasicoherentModules.{u, u + 1, u, u} B S hS p hp))
    (hsep : HasSeparator (quasicoherentModules.{u, u + 1, u, u} B S hS p hp)) :
    EnoughInjectives (quasicoherentModules.{u, u + 1, u, u} B S hS p hp) :=
  let := isGrothendieckAbelian_quasicoherentModules B S hS p hp hclosed hls hab5 hsep
  inferInstance

/-- Under the hypotheses of
`AlgebraicGeometry.FibredSite.isGrothendieckAbelian_quasicoherentModules`, `QCoh(𝒪_𝒳)` has all
limits. -/
@[stacks 0781 "part (1), its consequence: QCoh(𝒪_𝒳) has all limits"]
theorem hasLimitsOfSize_quasicoherentModules
    [Abelian (quasicoherentModules.{u, u + 1, u, u} B S hS p hp)]
    (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf))
    (hls : LocallySmall.{u} (quasicoherentModules.{u, u + 1, u, u} B S hS p hp))
    (hab5 : ∀ (K : Type u) [Category.{u} K] [IsFiltered K]
      [HasColimitsOfShape K (quasicoherentModules.{u, u + 1, u, u} B S hS p hp)],
      HasExactColimitsOfShape K (quasicoherentModules.{u, u + 1, u, u} B S hS p hp))
    (hsep : HasSeparator (quasicoherentModules.{u, u + 1, u, u} B S hS p hp)) :
    HasLimitsOfSize.{u, u} (quasicoherentModules.{u, u + 1, u, u} B S hS p hp) :=
  let := isGrothendieckAbelian_quasicoherentModules B S hS p hp hclosed hls hab5 hsep
  inferInstance

section Coherator

/-- **Every object of a category receiving `QCoh(𝒪_𝒳)` by a colimit-preserving functor has a
terminal quasi-coherent module mapping to it**, provided both categories are locally `u`-small and
`QCoh(𝒪_𝒳)` is cocomplete and well-copowered with a separator. -/
theorem hasTerminal_costructuredArrow_of_quasicoherentModules
    {D : Type v} [Category.{w} D]
    (i : quasicoherentModules.{u, u + 1, u, u} B S hS p hp ⥤ D)
    (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf))
    (hpres : PreservesColimitsOfSize.{u, u} i)
    (hls : LocallySmall.{u} (quasicoherentModules.{u, u + 1, u, u} B S hS p hp))
    (hlsD : LocallySmall.{u} D)
    (hwp : WellPowered.{u} (quasicoherentModules.{u, u + 1, u, u} B S hS p hp)ᵒᵖ)
    (hsep : HasSeparator (quasicoherentModules.{u, u + 1, u, u} B S hS p hp))
    (A : D) : HasTerminal (CostructuredArrow i A) :=
  let := hasColimitsOfSize_quasicoherentModules B S hS p hp hclosed
  let := hpres
  let := hls
  let := hlsD
  let := hwp
  let := hsep
  let := hasFiniteColimits_of_hasColimitsOfSize
    (quasicoherentModules.{u, u + 1, u, u} B S hS p hp)
  let := PreservesColimitsOfSize.preservesFiniteColimits i
  hasTerminal_of_isSeparating.{u}
    (CostructuredArrow.isSeparating_inverseImage_proj i A
      (isSeparator_separator (quasicoherentModules.{u, u + 1, u, u} B S hS p hp)))

/-- **The coherator on `Mod(𝒪_𝒳)`.** The right adjoint of the inclusion of `QCoh(𝒪_𝒳)` into all
modules on the associated fppf site of `𝒳`: it sends a module `A` to the terminal quasi-coherent
module equipped with a map to `A`. -/
@[stacks 0781 "part (2): the coherator Q : Mod(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)"]
def moduleCoherator
    (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf))
    (hls : LocallySmall.{u} (quasicoherentModules.{u, u + 1, u, u} B S hS p hp))
    (hlsD : LocallySmall.{u} (SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf)))
    (hwp : WellPowered.{u} (quasicoherentModules.{u, u + 1, u, u} B S hS p hp)ᵒᵖ)
    (hsep : HasSeparator (quasicoherentModules.{u, u + 1, u, u} B S hS p hp)) :
    SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf) ⥤
      quasicoherentModules.{u, u + 1, u, u} B S hS p hp :=
  letI := fun A => hasTerminal_costructuredArrow_of_quasicoherentModules B S hS p hp
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf)).ι hclosed
    (preservesColimitsOfSize_quasicoherentInclusion B S hS p hp hclosed) hls hlsD hwp hsep A
  rightAdjointOfCostructuredArrowTerminals
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf)).ι

/-- **The coherator on `Mod(𝒪_𝒳)` is right adjoint to the inclusion.** The adjunction is the
universal property of the terminal objects the coherator is built from. -/
@[stacks 0781 "part (2): the adjunction between the inclusion and the coherator"]
def moduleCoheratorAdjunction
    (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf))
    (hls : LocallySmall.{u} (quasicoherentModules.{u, u + 1, u, u} B S hS p hp))
    (hlsD : LocallySmall.{u} (SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf)))
    (hwp : WellPowered.{u} (quasicoherentModules.{u, u + 1, u, u} B S hS p hp)ᵒᵖ)
    (hsep : HasSeparator (quasicoherentModules.{u, u + 1, u, u} B S hS p hp)) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringStructureSheafCore B S hS p hp .fppf)).ι ⊣
      moduleCoherator B S hS p hp hclosed hls hlsD hwp hsep :=
  letI := fun A => hasTerminal_costructuredArrow_of_quasicoherentModules B S hS p hp
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf)).ι hclosed
    (preservesColimitsOfSize_quasicoherentInclusion B S hS p hp hclosed) hls hlsD hwp hsep A
  adjunctionOfCostructuredArrowTerminals
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf)).ι

/-- **The coherator fixes the quasi-coherent modules.** The composite of the inclusion with the
coherator is the identity functor of `QCoh(𝒪_𝒳)`: `Q 𝓕 ≅ 𝓕` for quasi-coherent `𝓕`. -/
@[stacks 0781 "part (2): the coherator composed with the inclusion is the identity"]
def moduleCoheratorCompInclusionIsoId
    (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf))
    (hls : LocallySmall.{u} (quasicoherentModules.{u, u + 1, u, u} B S hS p hp))
    (hlsD : LocallySmall.{u} (SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf)))
    (hwp : WellPowered.{u} (quasicoherentModules.{u, u + 1, u, u} B S hS p hp)ᵒᵖ)
    (hsep : HasSeparator (quasicoherentModules.{u, u + 1, u, u} B S hS p hp)) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (ringStructureSheafCore B S hS p hp .fppf)).ι ⋙
        moduleCoherator B S hS p hp hclosed hls hlsD hwp hsep ≅
      𝟭 (quasicoherentModules.{u, u + 1, u, u} B S hS p hp) :=
  (asIso (moduleCoheratorAdjunction B S hS p hp hclosed hls hlsD hwp hsep).unit).symm

end Coherator

end AlgebraicGeometry.FibredSite

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] [EssentiallySmall.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **The inclusion `i : QCoh(𝒪_𝒳) → LQCoh^fbc(𝒪_𝒳)`.** A quasi-coherent module on the
associated fppf site of `𝒳`, restricted by `AlgebraicGeometry.FibredSite.toSiteModules` to a
module on the associated étale site with the same presheaf of modules; that the restriction is
locally quasi-coherent and has the flat base change property is the hypothesis `hinc`. -/
def quasicoherentToFlatBaseChange
    (hinc : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp,
      IsLocallyQuasicoherentWithFlatBaseChange B E h S hS p hp
        ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS p hp .etale).obj F).val) :
    FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp ⥤
      locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS p hp where
  obj F := ⟨(FibredSite.toSiteModules.{u, u + 1, u, u} B S hS p hp .etale).obj F, hinc F⟩
  map f := ⟨(FibredSite.toSiteModules.{u, u + 1, u, u} B S hS p hp .etale).map f⟩

/-- The inclusion `i : QCoh(𝒪_𝒳) → LQCoh^fbc(𝒪_𝒳)` is fully faithful. -/
def fullyFaithful_quasicoherentToFlatBaseChange
    (hinc : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp,
      IsLocallyQuasicoherentWithFlatBaseChange B E h S hS p hp
        ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS p hp .etale).obj F).val) :
    (quasicoherentToFlatBaseChange B E h S hS p hp hinc).FullyFaithful where
  preimage {_ _} f := ObjectProperty.homMk ⟨f.hom.val⟩
  map_preimage _ := rfl
  preimage_map _ := rfl

/-- **The coherator on `LQCoh^fbc(𝒪_𝒳)`.** The right adjoint of the inclusion
`i : QCoh(𝒪_𝒳) → LQCoh^fbc(𝒪_𝒳)`: it sends a locally quasi-coherent module with the flat base
change property to the terminal quasi-coherent module equipped with a map to it. -/
@[stacks 0778 "the right adjoint Q : LQCoh^fbc(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)"]
def flatBaseChangeQuasicoherator
    (hinc : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp,
      IsLocallyQuasicoherentWithFlatBaseChange B E h S hS p hp
        ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS p hp .etale).obj F).val)
    (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS p hp .fppf))
    (hpres : PreservesColimitsOfSize.{u, u} (quasicoherentToFlatBaseChange B E h S hS p hp hinc))
    (hls : LocallySmall.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp))
    (hlsD : LocallySmall.{u}
      (locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS p hp))
    (hwp : WellPowered.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp)ᵒᵖ)
    (hsep : HasSeparator (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp)) :
    locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS p hp ⥤
      FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp :=
  letI := fun A => FibredSite.hasTerminal_costructuredArrow_of_quasicoherentModules B S hS p hp
    (quasicoherentToFlatBaseChange B E h S hS p hp hinc) hclosed hpres hls hlsD hwp hsep A
  rightAdjointOfCostructuredArrowTerminals
    (quasicoherentToFlatBaseChange B E h S hS p hp hinc)

/-- **The coherator on `LQCoh^fbc(𝒪_𝒳)` is right adjoint to the inclusion.** The adjunction is
the universal property of the terminal objects the coherator is built from. -/
@[stacks 0778 "the adjunction between the inclusion and the right adjoint"]
def flatBaseChangeQuasicoheratorAdjunction
    (hinc : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp,
      IsLocallyQuasicoherentWithFlatBaseChange B E h S hS p hp
        ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS p hp .etale).obj F).val)
    (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS p hp .fppf))
    (hpres : PreservesColimitsOfSize.{u, u} (quasicoherentToFlatBaseChange B E h S hS p hp hinc))
    (hls : LocallySmall.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp))
    (hlsD : LocallySmall.{u}
      (locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS p hp))
    (hwp : WellPowered.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp)ᵒᵖ)
    (hsep : HasSeparator (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp)) :
    quasicoherentToFlatBaseChange B E h S hS p hp hinc ⊣
      flatBaseChangeQuasicoherator B E h S hS p hp hinc hclosed hpres hls hlsD hwp hsep :=
  letI := fun A => FibredSite.hasTerminal_costructuredArrow_of_quasicoherentModules B S hS p hp
    (quasicoherentToFlatBaseChange B E h S hS p hp hinc) hclosed hpres hls hlsD hwp hsep A
  adjunctionOfCostructuredArrowTerminals
    (quasicoherentToFlatBaseChange B E h S hS p hp hinc)

/-- **`Q ∘ i` is the identity functor** of `QCoh(𝒪_𝒳)`, for the coherator `Q` on
`LQCoh^fbc(𝒪_𝒳)` and the inclusion `i`. -/
@[stacks 0778 "the composite of the right adjoint with the inclusion is the identity functor"]
def flatBaseChangeQuasicoheratorCompInclusionIsoId
    (hinc : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp,
      IsLocallyQuasicoherentWithFlatBaseChange B E h S hS p hp
        ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS p hp .etale).obj F).val)
    (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS p hp .fppf))
    (hpres : PreservesColimitsOfSize.{u, u} (quasicoherentToFlatBaseChange B E h S hS p hp hinc))
    (hls : LocallySmall.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp))
    (hlsD : LocallySmall.{u}
      (locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS p hp))
    (hwp : WellPowered.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp)ᵒᵖ)
    (hsep : HasSeparator (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp)) :
    quasicoherentToFlatBaseChange B E h S hS p hp hinc ⋙
        flatBaseChangeQuasicoherator B E h S hS p hp hinc hclosed hpres hls hlsD hwp hsep ≅
      𝟭 (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp) :=
  letI := (fullyFaithful_quasicoherentToFlatBaseChange B E h S hS p hp hinc).full
  letI := (fullyFaithful_quasicoherentToFlatBaseChange B E h S hS p hp hinc).faithful
  (asIso (flatBaseChangeQuasicoheratorAdjunction B E h S hS p hp hinc hclosed hpres hls hlsD
    hwp hsep).unit).symm

end AlgebraicGeometry.Stack

end
