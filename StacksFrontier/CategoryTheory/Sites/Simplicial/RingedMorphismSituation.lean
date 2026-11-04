module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingImageAdjunction
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalMorphism
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalMorphismCaseA
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalMorphismOfTopoi

/-!
# Morphisms between ringed simplicial sites

A ringed simplicial site is a simplicial site together with a sheaf of rings on its total site.
A morphism between two of them is a morphism `h` of the underlying simplicial sites together
with a homomorphism of sheaves of rings from the inverse image of the target ring sheaf to the
source ring sheaf, taken along the induced morphism of total topoi. Equivalently, it is a
homomorphism from the target ring sheaf to the direct image of the source ring sheaf.

A morphism between simplicial sites induces a morphism between the total topoi in both cases of
Situation 09WE, so both the notion and the bijection between the two forms of its homomorphism
of sheaves of rings are stated here once, for a morphism between simplicial-site *situations*,
and the two cases of Situation 09WE share that one statement.

## Main definitions

* `CategoryTheory.SimplicialSiteMorphism.totalInverseImageRingFunctor` and
  `.totalPushforwardRingFunctor`, and their values
  `CategoryTheory.SimplicialSiteMorphism.totalInverseImageRing` and `.totalPushforwardRing`: the
  inverse image and the direct image of a sheaf of rings along it.
* `CategoryTheory.SimplicialSiteMorphism.ringHomEquiv`: the bijection between the inverse-image
  and the direct-image form of a homomorphism of sheaves of rings on the total site.
* `CategoryTheory.SimplicialSiteSituation.RingedMorphism`: a morphism between ringed simplicial
  sites, with the homomorphism of sheaves of rings in inverse-image form.
* `CategoryTheory.SimplicialSiteSituation.RingedMorphism.ringHomPushforward`: that homomorphism
  in direct-image form.
* `CategoryTheory.SimplicialSiteSituation.RingedMorphism.ofPushforward`: the morphism between
  ringed simplicial sites determined by a homomorphism in direct-image form.

## Main results

* `CategoryTheory.SimplicialSiteMorphism.ringHomEquiv_apply` and `.ringHomEquiv_symm_apply`: the
  bijection and its inverse are the usual ones, `φ ↦ ringUnit ≫ h_{total, *} φ` and
  `ψ ↦ h_total⁻¹ ψ ≫ ringCounit`.
* `CategoryTheory.SimplicialSiteSituation.RingedMorphism.ringHomPushforward_eq`: the
  direct-image form is the unit of the ring-level adjunction followed by the direct image of the
  inverse-image form.

## Implementation notes

The bijection is `Stacks.Sheaves.ToposPushforward.ringImageAdjunction` — the adjunction between
the inverse image and the direct image of sheaves of rings along a morphism of topoi, which
Stacks 00YV provides for a general algebraic structure — applied to the morphism of total topoi.
Nothing about the simplicial situation enters beyond the existence of that morphism of topoi,
which is why one statement covers both cases: the morphism of total topoi is available in case
(A) by `CategoryTheory.SimplicialSite.Morphism.totalMorphism` and in case (B) by
`CategoryTheory.CocontinuousSimplicialSite.Morphism.totalMorphism`, and
`CategoryTheory.SimplicialSiteMorphism.totalMorphism` is the two of them read off the
constructors of the inductive, exactly as
`CategoryTheory.SimplicialSiteMorphism.componentMorphism` does in each simplicial degree. For the
same reason the underlying morphism of a `RingedMorphism` is an element of that inductive rather
than a morphism of one of the two cases, so the notion is stated once too.

The homomorphism of sheaves of rings is stored in the inverse-image form in which the source
states it first, and its direct-image form is the value of the bijection. So no new comparison
of the two forms is needed, and either form determines a morphism.

The universe is a single `u`: the morphism of total topoi is a morphism of topoi of sheaves of
sets valued in `Type u`, and this pins the universe of the sheaves of rings on both total sites.
The inverse and direct images of a sheaf of rings are given their own names, as functors and as
values, because their universe parameters are not determined by their arguments alone: a bare
`inverseImageRingFunctor h.totalMorphism` in a position that does not already fix them leaves
them as metavariables and is elaborated at `Type 1`.

## References

* [Stacks Project, Tag 0DGZ](https://stacks.math.columbia.edu/tag/0DGZ)
* [Stacks Project, Tag 0D95](https://stacks.math.columbia.edu/tag/0D95)
* [Stacks Project, Tag 0D96](https://stacks.math.columbia.edu/tag/0D96)
* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Sheaves.ToposPushforward

universe u

namespace CategoryTheory

namespace SimplicialSiteMorphism

variable {S S' : SimplicialSiteSituation.{u}}

/-- In case (A), the morphism of total topoi of a morphism between simplicial sites is the one
of `SimplicialSite.Morphism.totalMorphism`. -/
@[simp]
theorem totalMorphism_ofMorphismOfSites {C C' : SimplicialSite.{u}}
    (h : SimplicialSite.Morphism C C') :
    (ofMorphismOfSites h).totalMorphism = h.totalMorphism :=
  rfl

/-- In case (B), the morphism of total topoi of a morphism between simplicial sites is the one
of `CocontinuousSimplicialSite.Morphism.totalMorphism`. -/
@[simp]
theorem totalMorphism_ofCocontinuous {C C' : CocontinuousSimplicialSite.{u}}
    (h : CocontinuousSimplicialSite.Morphism C C') :
    (ofCocontinuous h).totalMorphism = h.totalMorphism :=
  rfl

/-- The inverse image of sheaves of rings along the morphism of total topoi of a morphism
between simplicial sites, as a functor. -/
abbrev totalInverseImageRingFunctor (h : SimplicialSiteMorphism S S') :
    Sheaf S'.totalTopology RingCat.{u} ⥤ Sheaf S.totalTopology RingCat.{u} :=
  inverseImageRingFunctor.{u, u} h.totalMorphism

/-- The direct image of sheaves of rings along the morphism of total topoi of a morphism between
simplicial sites, as a functor. -/
abbrev totalPushforwardRingFunctor (h : SimplicialSiteMorphism S S') :
    Sheaf S.totalTopology RingCat.{u} ⥤ Sheaf S'.totalTopology RingCat.{u} :=
  pushforwardRingFunctor.{u, u} h.totalMorphism

/-- The inverse image, along the morphism of total topoi of a morphism between simplicial sites,
of a sheaf of rings on the total site of the target. -/
abbrev totalInverseImageRing (h : SimplicialSiteMorphism S S')
    (O' : Sheaf S'.totalTopology RingCat.{u}) : Sheaf S.totalTopology RingCat.{u} :=
  h.totalInverseImageRingFunctor.obj O'

/-- The direct image, along the morphism of total topoi of a morphism between simplicial sites,
of a sheaf of rings on the total site of the source. -/
abbrev totalPushforwardRing (h : SimplicialSiteMorphism S S')
    (O : Sheaf S.totalTopology RingCat.{u}) : Sheaf S'.totalTopology RingCat.{u} :=
  h.totalPushforwardRingFunctor.obj O

/-- **Stacks 0DGZ**, both cases of Situation 09WE. A homomorphism of sheaves of rings
`h_total⁻¹ 𝒪' ⟶ 𝒪` is the same thing as a homomorphism `𝒪' ⟶ h_{total, *} 𝒪`: the two are
exchanged by the adjunction between the inverse image and the direct image of sheaves of rings
along the morphism of total topoi. -/
@[stacks 0DGZ "the two equivalent forms of the ring map, case (A)",
  stacks 0DGZ "the two equivalent forms of the ring map, case (B)",
  sga "4 XVII 0.2.1" "ringed simplicial sites"]
def ringHomEquiv (h : SimplicialSiteMorphism S S')
    (O : Sheaf S.totalTopology RingCat.{u}) (O' : Sheaf S'.totalTopology RingCat.{u}) :
    (h.totalInverseImageRing O' ⟶ O) ≃ (O' ⟶ h.totalPushforwardRing O) :=
  (ringImageAdjunction h.totalMorphism).homEquiv O' O

/-- The direct-image form of a homomorphism of sheaves of rings is the unit of the ring-level
adjunction followed by the direct image of the inverse-image form. -/
theorem ringHomEquiv_apply (h : SimplicialSiteMorphism S S')
    (O : Sheaf S.totalTopology RingCat.{u}) (O' : Sheaf S'.totalTopology RingCat.{u})
    (φ : h.totalInverseImageRing O' ⟶ O) :
    h.ringHomEquiv O O' φ =
      ringUnit h.totalMorphism O' ≫ h.totalPushforwardRingFunctor.map φ :=
  (ringImageAdjunction h.totalMorphism).homEquiv_unit O' O φ

/-- The inverse-image form of a homomorphism of sheaves of rings is the inverse image of the
direct-image form followed by the counit of the ring-level adjunction. -/
theorem ringHomEquiv_symm_apply (h : SimplicialSiteMorphism S S')
    (O : Sheaf S.totalTopology RingCat.{u}) (O' : Sheaf S'.totalTopology RingCat.{u})
    (ψ : O' ⟶ h.totalPushforwardRing O) :
    (h.ringHomEquiv O O').symm ψ =
      h.totalInverseImageRingFunctor.map ψ ≫ ringCounit h.totalMorphism O :=
  (ringImageAdjunction h.totalMorphism).homEquiv_counit O' O ψ

end SimplicialSiteMorphism

/-- **Stacks 0DGZ**, both cases of Situation 09WE. A morphism between ringed simplicial sites: a
morphism `h` between the underlying simplicial sites, together with a homomorphism of sheaves of
rings `h♯ : h_total⁻¹ 𝒪' ⟶ 𝒪` on the total site. -/
@[stacks 0DGZ "ringed simplicial site morphism, case (A) of Situation 09WE",
  stacks 0DGZ "ringed simplicial site morphism, case (B) of Situation 09WE"]
structure SimplicialSiteSituation.RingedMorphism (S S' : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology RingCat.{u})
    (O' : Sheaf S'.totalTopology RingCat.{u}) where
  /-- The underlying morphism between the simplicial sites. -/
  hom : SimplicialSiteMorphism S S'
  /-- The homomorphism of sheaves of rings `h_total⁻¹ 𝒪' ⟶ 𝒪`. -/
  ringHom : hom.totalInverseImageRing O' ⟶ O

namespace SimplicialSiteSituation.RingedMorphism

variable {S S' : SimplicialSiteSituation.{u}}
  {O : Sheaf S.totalTopology RingCat.{u}}
  {O' : Sheaf S'.totalTopology RingCat.{u}}

/-- The homomorphism of sheaves of rings of a morphism between ringed simplicial sites, in its
direct-image form `𝒪' ⟶ h_{total, *} 𝒪`. -/
def ringHomPushforward (h : RingedMorphism S S' O O') :
    O' ⟶ h.hom.totalPushforwardRing O :=
  h.hom.ringHomEquiv O O' h.ringHom

/-- The bijection `ringHomEquiv` sends the inverse-image form of the homomorphism of sheaves of
rings to its direct-image form. -/
@[simp]
theorem ringHomEquiv_ringHom (h : RingedMorphism S S' O O') :
    h.hom.ringHomEquiv O O' h.ringHom = h.ringHomPushforward :=
  rfl

/-- The inverse of `ringHomEquiv` sends the direct-image form of the homomorphism of sheaves of
rings to its inverse-image form. -/
@[simp]
theorem ringHomEquiv_symm_ringHomPushforward (h : RingedMorphism S S' O O') :
    (h.hom.ringHomEquiv O O').symm h.ringHomPushforward = h.ringHom :=
  (h.hom.ringHomEquiv O O').symm_apply_apply h.ringHom

/-- The direct-image form of the homomorphism of sheaves of rings is the unit of the ring-level
adjunction followed by the direct image of the inverse-image form. -/
theorem ringHomPushforward_eq (h : RingedMorphism S S' O O') :
    h.ringHomPushforward = ringUnit h.hom.totalMorphism O' ≫
      (pushforwardRingFunctor h.hom.totalMorphism).map h.ringHom :=
  h.hom.ringHomEquiv_apply O O' h.ringHom

/-- A morphism between ringed simplicial sites given by the direct-image form
`𝒪' ⟶ h_{total, *} 𝒪` of its homomorphism of sheaves of rings. -/
def ofPushforward (h : SimplicialSiteMorphism S S')
    (φ : O' ⟶ h.totalPushforwardRing O) : RingedMorphism S S' O O' where
  hom := h
  ringHom := (h.ringHomEquiv O O').symm φ

/-- The underlying morphism of simplicial sites of `ofPushforward h φ` is `h`. -/
@[simp]
theorem ofPushforward_hom (h : SimplicialSiteMorphism S S')
    (φ : O' ⟶ h.totalPushforwardRing O) :
    (ofPushforward h φ).hom = h :=
  rfl

/-- The inverse-image form of the homomorphism of sheaves of rings of `ofPushforward h φ` is the
image of `φ` under the inverse of `ringHomEquiv`. -/
@[simp]
theorem ofPushforward_ringHom (h : SimplicialSiteMorphism S S')
    (φ : O' ⟶ h.totalPushforwardRing O) :
    (ofPushforward h φ).ringHom = (h.ringHomEquiv O O').symm φ :=
  rfl

/-- The direct-image form of the homomorphism of sheaves of rings of `ofPushforward h φ` is
`φ`. -/
@[simp]
theorem ringHomPushforward_ofPushforward (h : SimplicialSiteMorphism S S')
    (φ : O' ⟶ h.totalPushforwardRing O) :
    (ofPushforward h φ).ringHomPushforward = φ :=
  (h.ringHomEquiv O O').apply_symm_apply φ

end SimplicialSiteSituation.RingedMorphism

end CategoryTheory

end
