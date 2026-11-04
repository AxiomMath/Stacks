module

public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.Topologies.InverseImageComposition

/-!
# The comparison `p⁻¹𝓕 ⟶ p^*𝓕` over the inverse image of the base

Let `p : W ⟶ X` and `a : X ⟶ S` be morphisms of schemes and write `f = p ∘ a`. A module over
`a^{-1}𝒪_S` has an inverse image along `p`, a module over `f^{-1}𝒪_S`, obtained by pullback
along the canonical morphism of ringed spaces `(W, f^{-1}𝒪_S) ⟶ (X, a^{-1}𝒪_S)`. For an
`𝒪_X`-module `𝓕` this file constructs the canonical comparison

`p^{-1}𝓕 ⟶ p^*𝓕`

of `f^{-1}𝒪_S`-modules, where the target is the `𝒪_W`-module `p^*𝓕` read by restriction of
scalars along `f^{-1}𝒪_S ⟶ 𝒪_W`.

## Main definitions

* `Stacks.DeRhamDirectImage.relativeInverseImageProjection`: the morphism of ringed spaces
  `(W, f^{-1}𝒪_S) ⟶ (X, a^{-1}𝒪_S)` over `p`.
* `Stacks.DeRhamDirectImage.relativeInverseImage`: the resulting inverse image
  `p^{-1} : Mod(a^{-1}𝒪_S) ⥤ Mod(f^{-1}𝒪_S)`.
* `Stacks.DeRhamDirectImage.relativeInverseImageToPullback`: **the comparison `p^{-1}𝓕 ⟶ p^*𝓕`.**

## Main results

* `Stacks.DeRhamDirectImage.relativeInverseImageProjection_comp`: the projections to `S` form a
  triangle, which characterises the structure map of `relativeInverseImageProjection`.
* `Stacks.DeRhamDirectImage.toInverseImageBase_comp_relativeInverseImageProjection`: the square
  comparing the two factorizations of `p` through the inverse images of `𝒪_S`.
* `Stacks.DeRhamDirectImage.homEquiv_relativeInverseImageToPullback`: the comparison is
  characterised by its transpose along `p^{-1} ⊣ p_*`, which is the unit of `p^* ⊣ p_*`
  corestricted along the square.

## Implementation notes

The square is proved by transposing both of its structure maps along `a^{-1} ⊣ a_*`, where both
become `(p ∘ a)^♯`; the direct image of a sheaf along a composite being the composite of the
direct images on the nose, no comparison of the two inverse images of `𝒪_S` on `W` enters.

The comparison is not the one of `AlgebraicGeometry.SheafOfModules.inverseImageToPullback`, which
compares `p^{-1}𝓕` with `p^*𝓕` as modules over `p^{-1}𝒪_X`; here both sides are modules over
`f^{-1}𝒪_S`, the ring over which the differentials of a relative de Rham complex are linear.

The comparison is the transpose of the unit of `p^* ⊣ p_*` read through the square, so the one
transport along an equality of morphisms of ringed spaces appears as an `eqToHom` between the
two direct images; this is the shape in which
`Stacks.Cohomology.DerivedKunneth.pullbackCounitLeg` carries the analogous datum.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 0097](https://stacks.math.columbia.edu/tag/0097)
* [Stacks Project, Tag 008C](https://stacks.math.columbia.edu/tag/008C)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open _root_.AlgebraicGeometry

universe u

namespace Stacks.DeRhamDirectImage

variable {W X S : Scheme.{u}} (p : W ⟶ X) (a : X ⟶ S)

/-- The canonical morphism of ringed spaces `(W, (p ∘ a)^{-1}𝒪_S) ⟶ (X, a^{-1}𝒪_S)` over `p`. -/
abbrev relativeInverseImageProjection :
    inverseImageBase (p ≫ a) ⟶ inverseImageBase a :=
  RingedSpace.inverseImageCompProjection S.toRingedSpace a.base p.base

/-- **The triangle over `S`**: the canonical morphism followed by the projection of
`(X, a^{-1}𝒪_S)` to `S` is the projection of `(W, (p ∘ a)^{-1}𝒪_S)` to `S`. -/
theorem relativeInverseImageProjection_comp :
    relativeInverseImageProjection p a ≫ inverseImageBaseProjection a =
      inverseImageBaseProjection (p ≫ a) :=
  RingedSpace.inverseImageCompProjection_comp S.toRingedSpace a.base p.base

/-- The structural map `(p ∘ a)^{-1}𝒪_S ⟶ 𝒪_W`, typed at the composite `p ∘ a` of the two
underlying continuous maps. -/
def compInverseImageStructureMap :
    (TopCat.Sheaf.pullback CommRingCat.{u} (p.base ≫ a.base)).obj S.sheaf ⟶ W.sheaf :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (p.base ≫ a.base)).homEquiv
    S.sheaf W.sheaf).symm ⟨(p ≫ a).c⟩

/-- The structural map `(p ∘ a)^{-1}𝒪_S ⟶ 𝒪_W` is the one attached to the composite morphism of
schemes. -/
theorem compInverseImageStructureMap_eq :
    compInverseImageStructureMap p a = inverseImageStructureMap (p ≫ a) := rfl

/-- `(p ∘ a)^♯` is recovered from the structural map `(p ∘ a)^{-1}𝒪_S ⟶ 𝒪_W` by adjunction. -/
theorem homEquiv_compInverseImageStructureMap :
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (p.base ≫ a.base)).homEquiv
        S.sheaf W.sheaf (compInverseImageStructureMap p a) = ⟨(p ≫ a).c⟩ :=
  Equiv.apply_symm_apply _ _

/-- The structure map of the canonical morphism, followed by the structural map
`(p ∘ a)^{-1}𝒪_S ⟶ 𝒪_W`, is the structural map `a^{-1}𝒪_S ⟶ 𝒪_X` followed by `p^♯`. -/
theorem inverseImageCompHom_comp_compInverseImageStructureMap :
    RingedSpace.inverseImageCompHom S.toRingedSpace a.base p.base ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} p.base).map
          (compInverseImageStructureMap p a) =
      inverseImageStructureMap a ≫ (⟨p.c⟩ :
        X.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} p.base).obj W.sheaf) := by
  refine ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} a.base).homEquiv
    S.sheaf ((TopCat.Sheaf.pushforward CommRingCat.{u} p.base).obj W.sheaf)).injective ?_
  refine Eq.trans
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} a.base).homEquiv_naturality_right
      (RingedSpace.inverseImageCompHom S.toRingedSpace a.base p.base)
      ((TopCat.Sheaf.pushforward CommRingCat.{u} p.base).map
        (compInverseImageStructureMap p a))) ?_
  refine Eq.trans ?_
    (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} a.base).homEquiv_naturality_right
      (inverseImageStructureMap a) (⟨p.c⟩ :
        X.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} p.base).obj W.sheaf)).symm)
  refine Eq.trans (congrArg
    (fun t => t ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} a.base).map
      ((TopCat.Sheaf.pushforward CommRingCat.{u} p.base).map (compInverseImageStructureMap p a)))
    (RingedSpace.homEquiv_inverseImageCompHom S.toRingedSpace a.base p.base)) ?_
  refine Eq.trans ((Adjunction.homEquiv_unit
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (p.base ≫ a.base))
    S.sheaf W.sheaf (compInverseImageStructureMap p a)).symm.trans
      (homEquiv_compInverseImageStructureMap p a)) ?_
  exact congrArg
    (fun t => t ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} a.base).map (⟨p.c⟩ :
      X.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} p.base).obj W.sheaf))
    (Equiv.apply_symm_apply
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} a.base).homEquiv
        S.sheaf X.sheaf)
      (⟨a.c⟩ : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} a.base).obj X.sheaf)).symm

/-- **The square comparing the two factorizations of `p`**: the identity-on-spaces morphism to
`(W, (p ∘ a)^{-1}𝒪_S)` followed by the canonical morphism equals `p` followed by the
identity-on-spaces morphism to `(X, a^{-1}𝒪_S)`. -/
theorem toInverseImageBase_comp_relativeInverseImageProjection :
    toInverseImageBase (p ≫ a) ≫ relativeInverseImageProjection p a =
      p.toLRSHom.toShHom ≫ toInverseImageBase a := by
  refine InducedCategory.hom_ext (PresheafedSpace.hext _ _ rfl (heq_of_eq ?_))
  exact congrArg (fun t => t.hom) (inverseImageCompHom_comp_compInverseImageStructureMap p a)

/-- **The inverse image `p^{-1} : Mod(a^{-1}𝒪_S) ⥤ Mod((p ∘ a)^{-1}𝒪_S)`**: pullback of sheaves
of modules along the canonical morphism of ringed spaces. -/
abbrev relativeInverseImage :
    Modules (inverseImageBase a) ⥤ Modules (inverseImageBase (p ≫ a)) :=
  pullback (relativeInverseImageProjection p a)

/-- The direct image `Mod((p ∘ a)^{-1}𝒪_S) ⥤ Mod(a^{-1}𝒪_S)` along the canonical morphism. -/
abbrev relativeInverseImagePushforward :
    Modules (inverseImageBase (p ≫ a)) ⥤ Modules (inverseImageBase a) :=
  pushforward (relativeInverseImageProjection p a)

/-- The transport of a direct image of `𝒪_W`-modules along the square. -/
def relativeSquareTransport (F : Modules W.toRingedSpace) :
    (pushforward (p.toLRSHom.toShHom ≫ toInverseImageBase a)).obj F ⟶
      (pushforward (toInverseImageBase (p ≫ a) ≫ relativeInverseImageProjection p a)).obj F :=
  eqToHom (congrArg (fun g : W.toRingedSpace ⟶ inverseImageBase a => (pushforward g).obj F)
    (toInverseImageBase_comp_relativeInverseImageProjection p a).symm)

/-- The unit of `p^* ⊣ p_*`, read through the square as a morphism of `a^{-1}𝒪_S`-modules into
the direct image along the canonical morphism of the restriction of scalars of `p^*𝓕`. -/
def relativeToPullbackLeg (F : Modules X.toRingedSpace) :
    (pushforward (toInverseImageBase a)).obj F ⟶
      (relativeInverseImagePushforward p a).obj
        ((pushforward (toInverseImageBase (p ≫ a))).obj
          ((pullback p.toLRSHom.toShHom).obj F)) :=
  (pushforward (toInverseImageBase a)).map
      ((pullbackPushforwardAdjunction p.toLRSHom.toShHom).unit.app F) ≫
    (pushforwardComp p.toLRSHom.toShHom (toInverseImageBase a)).inv.app _ ≫
    relativeSquareTransport p a _ ≫
    (pushforwardComp (toInverseImageBase (p ≫ a)) (relativeInverseImageProjection p a)).hom.app _

/-- **The comparison `p^{-1}𝓕 ⟶ p^*𝓕`** of `(p ∘ a)^{-1}𝒪_S`-modules, for an `𝒪_X`-module `𝓕`:
the transpose along `p^{-1} ⊣ p_*` of the unit of `p^* ⊣ p_*` read through the square. -/
def relativeInverseImageToPullback (F : Modules X.toRingedSpace) :
    (relativeInverseImage p a).obj ((pushforward (toInverseImageBase a)).obj F) ⟶
      (pushforward (toInverseImageBase (p ≫ a))).obj
        ((pullback p.toLRSHom.toShHom).obj F) :=
  ((pullbackPushforwardAdjunction (relativeInverseImageProjection p a)).homEquiv
    ((pushforward (toInverseImageBase a)).obj F) _).symm (relativeToPullbackLeg p a F)

/-- **The comparison is characterised by its transpose**: along `p^{-1} ⊣ p_*` it is the unit of
`p^* ⊣ p_*` read through the square. -/
theorem homEquiv_relativeInverseImageToPullback (F : Modules X.toRingedSpace) :
    (pullbackPushforwardAdjunction (relativeInverseImageProjection p a)).homEquiv
        ((pushforward (toInverseImageBase a)).obj F) _ (relativeInverseImageToPullback p a F) =
      relativeToPullbackLeg p a F :=
  Equiv.apply_symm_apply _ _

end Stacks.DeRhamDirectImage

end
