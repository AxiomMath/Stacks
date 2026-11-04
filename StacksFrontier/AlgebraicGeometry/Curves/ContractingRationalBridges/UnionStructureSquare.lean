module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.StructureDirectImage
public import StacksFrontier.AlgebraicGeometry.Duality.AffinePushforwardQcohExact
public import StacksFrontier.AlgebraicGeometry.Pushout.SquareSections
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.ClosedUnionPushout
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The structure sheaf of a scheme covered by two closed subschemes

Let `I` and `J` be quasi-coherent ideal sheaves on a scheme `S` with `I ⊓ J = ⊥`, that is, two
closed subschemes whose scheme-theoretic union is all of `S`. This file records the square

```
𝒪_S           ⟶  (ι_J)_* 𝒪_{V(J)}
  ↓                  ↓
(ι_I)_* 𝒪_{V(I)}  ⟶  (ι_{I ⊔ J})_* 𝒪_{V(I ⊔ J)}
```

of modules over `𝒪_S` as a fibre square, derives from it the short exact sequence of
[Stacks, Tag 0C4J], and shows that a direct image which is affine on `V(J)` carries the second
arrow of that sequence to an epimorphism.

## Main results

* `AlgebraicGeometry.isPushout_subscheme_of_inf_eq_bot` — the two closed subschemes exhibit `S`
  as the pushout of their inclusions along their intersection.
* `AlgebraicGeometry.isPullback_structureSheaf_union` — the displayed square is a fibre square.
* `AlgebraicGeometry.unionStructureSheafShortComplex_shortExact` — the short exact sequence.
* `AlgebraicGeometry.epi_pushforward_map_pushedForwardStructureSheafToComposite` — a direct
  image affine on `V(J)` carries the second arrow to an epimorphism.

## Implementation notes

The square is the module-theoretic form of the structure-sheaf assertion of [Stacks, Tag 0E25],
`AlgebraicGeometry.pushoutModuleSquare_isPullback`, applied to the scheme pushout of
[Stacks, Tag 0C4J], `AlgebraicGeometry.Scheme.IdealSheafData.isPushout_subscheme_inf`, with the
intersection `I ⊓ J` identified with `S` because it is the zero ideal sheaf. Its sections
hypothesis is discharged by
`AlgebraicGeometry.structureSheaf_isPullback_of_isPushout_of_isAffineHom`, the inclusion of a
closed subscheme being affine.

The short exact sequence is the one `CategoryTheory.CommSq.shortComplex'` attaches to a cartesian
square, so exactness in the middle and injectivity on the left are the fibre square itself; the
surjectivity on the right comes from the first summand, where the comparison map of a closed
immersion is already surjective.

Everything here is stated through `AlgebraicGeometry.structureSheafToPushforward` and
`AlgebraicGeometry.pushedForwardStructureSheafToComposite` rather than through
`AlgebraicGeometry.Scheme.IdealSheafData.closedSubschemeRestriction`: the latter carries an
`eqToHom` inside its definition, and unfolding it to the composite it is made of is beyond the
kernel's heartbeat budget, so the surjectivity statement cannot be transported to it.

## References

* [Stacks Project, Tag 0C4J](https://stacks.math.columbia.edu/tag/0C4J)
* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} (I J : S.IdealSheafData)

/-- **Two closed subschemes whose scheme-theoretic union is the whole scheme exhibit it as the
pushout of their inclusions along their scheme-theoretic intersection.** This is
[Stacks, Tag 0C4J] with the vertex `V(I ⊓ J)` of the pushout square identified with `S`, which
happens exactly when `I ⊓ J = ⊥`. -/
theorem isPushout_subscheme_of_inf_eq_bot (hbot : I ⊓ J = ⊥) :
    IsPushout (Scheme.IdealSheafData.inclusion (I := J) (J := I ⊔ J) le_sup_right)
      (Scheme.IdealSheafData.inclusion (I := I) (J := I ⊔ J) le_sup_left)
      J.subschemeι I.subschemeι := by
  have : IsIso (I ⊓ J).subschemeι := hbot ▸ inferInstance
  refine ((Scheme.IdealSheafData.isPushout_subscheme_inf I J).flip).of_iso (Iso.refl _)
    (Iso.refl _) (Iso.refl _) (asIso (I ⊓ J).subschemeι) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simpa using (Scheme.IdealSheafData.inclusion_subschemeι
      (inf_le_right : I ⊓ J ≤ J)).symm
  · simpa using (Scheme.IdealSheafData.inclusion_subschemeι
      (inf_le_left : I ⊓ J ≤ I)).symm

/-- **The structure sheaf of a scheme covered by two closed subschemes is the fibre product of
their structure sheaves over the structure sheaf of their intersection.** This is
[Stacks, Tag 0E25] in its module-theoretic form, applied to the presentation of `S` as the
pushout of the two closed immersions. -/
theorem isPullback_structureSheaf_union (hbot : I ⊓ J = ⊥) :
    IsPullback (structureSheafToPushforward J.subschemeι)
      (structureSheafToPushforward I.subschemeι)
      (pushedForwardStructureSheafToComposite
        (Scheme.IdealSheafData.inclusion (I := J) (J := I ⊔ J) le_sup_right) J.subschemeι)
      (pushedForwardStructureSheafToComposite
          (Scheme.IdealSheafData.inclusion (I := I) (J := I ⊔ J) le_sup_left) I.subschemeι ≫
        (Scheme.Modules.pushforwardCongr
          (isPushout_subscheme_of_inf_eq_bot I J hbot).w.symm).hom.app _) :=
  pushoutModuleSquare_isPullback _ _ _ _ (isPushout_subscheme_of_inf_eq_bot I J hbot)
    fun U => structureSheaf_isPullback_of_isPushout_of_isAffineHom
      (isPushout_subscheme_of_inf_eq_bot I J hbot) U

/-- **The comparison map of a closed immersion is an epimorphism of structure sheaves.** -/
theorem epi_structureSheafToPushforward_of_isClosedImmersion {Z W : Scheme.{u}} (i : Z ⟶ W)
    [IsClosedImmersion i] : Epi (structureSheafToPushforward i) :=
  Stacks.AlgebraicGeometry.ClosedImmersionTFAE.epi_unitToPushforwardObjUnit_of_isClosedImmersion i

/-- **The comparison map of a closed immersion stays an epimorphism after a direct image along
an affine morphism.** The direct image along an affine morphism is right exact on quasi-coherent
modules (`Stacks.AlgebraicGeometry.AffineQcohExactness.epi_pushforward_map`). -/
theorem epi_pushforward_map_structureSheafToPushforward {Z W P : Scheme.{u}} (i : Z ⟶ W)
    (g : W ⟶ P) [IsClosedImmersion i] [IsAffineHom g] :
    Epi ((Scheme.Modules.pushforward g).map (structureSheafToPushforward i)) := by
  have : Epi (structureSheafToPushforward i) :=
    epi_structureSheafToPushforward_of_isClosedImmersion i
  have : (structureSheafModule Z).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit Z
  have : ((Scheme.Modules.pushforward i).obj (structureSheafModule Z)).IsQuasicoherent :=
    inferInstance
  exact Stacks.AlgebraicGeometry.AffineQcohExactness.epi_pushforward_map g _

/-- **The restriction of structure sheaves along a closed immersion stays an epimorphism after a
direct image along an affine morphism.** The comparison map of the composition is the
pushed-forward comparison map followed by an isomorphism. -/
theorem epi_pushedForwardStructureSheafToComposite {Z W P : Scheme.{u}} (i : Z ⟶ W) (a : W ⟶ P)
    [IsClosedImmersion i] [IsAffineHom a] :
    Epi (pushedForwardStructureSheafToComposite i a) := by
  have := epi_pushforward_map_structureSheafToPushforward i a
  exact epi_comp ((Scheme.Modules.pushforward a).map (structureSheafToPushforward i))
    ((Scheme.Modules.pushforwardComp i a).hom.app (structureSheafModule Z))

/-- **A direct image carries the restriction of structure sheaves along a closed immersion to an
epimorphism as soon as it is affine on the larger subscheme.** This is the surjectivity the
contraction of a rational bridge needs: functions on the larger closed subscheme restrict onto
the smaller one, and that stays so after a direct image which is affine there. -/
@[ega "I 4.1.7" "special case"]
theorem epi_pushforward_map_pushedForwardStructureSheafToComposite
    {Z W P T : Scheme.{u}} (i : Z ⟶ W) (a : W ⟶ P) (g : P ⟶ T)
    [IsClosedImmersion i] [IsAffineHom (a ≫ g)] :
    Epi ((Scheme.Modules.pushforward g).map (pushedForwardStructureSheafToComposite i a)) := by
  have : Epi ((Scheme.Modules.pushforward g).map
      ((Scheme.Modules.pushforward a).map (structureSheafToPushforward i))) :=
    epi_pushforward_map_structureSheafToPushforward i (a ≫ g)
  have hdef : pushedForwardStructureSheafToComposite i a =
      (Scheme.Modules.pushforward a).map (structureSheafToPushforward i) ≫
        (Scheme.Modules.pushforwardComp i a).hom.app (structureSheafModule Z) := rfl
  rw [hdef, Functor.map_comp]
  exact epi_comp _ _

/-- The first arrow of the union sequence of [Stacks, Tag 0C4J]: the pair of restrictions of a
function on `S` to the two closed subschemes. -/
def unionStructureSheafToBiprod :
    structureSheafModule S ⟶
      pushedForwardStructureSheaf J.subschemeι ⊞ pushedForwardStructureSheaf I.subschemeι :=
  biprod.lift (structureSheafToPushforward J.subschemeι)
    (structureSheafToPushforward I.subschemeι)

/-- The second arrow of the union sequence of [Stacks, Tag 0C4J]: the difference of the two
restrictions to the scheme-theoretic intersection. -/
def unionBiprodToIntersection (hbot : I ⊓ J = ⊥) :
    pushedForwardStructureSheaf J.subschemeι ⊞ pushedForwardStructureSheaf I.subschemeι ⟶
      pushedForwardStructureSheaf
        (Scheme.IdealSheafData.inclusion (I := J) (J := I ⊔ J) le_sup_right ≫ J.subschemeι) :=
  biprod.desc
    (pushedForwardStructureSheafToComposite
      (Scheme.IdealSheafData.inclusion (I := J) (J := I ⊔ J) le_sup_right) J.subschemeι)
    (-(pushedForwardStructureSheafToComposite
        (Scheme.IdealSheafData.inclusion (I := I) (J := I ⊔ J) le_sup_left) I.subschemeι ≫
      (Scheme.Modules.pushforwardCongr
        (isPushout_subscheme_of_inf_eq_bot I J hbot).w.symm).hom.app _))

/-- Restricting a function from the closed subscheme cut out by `J` and taking the difference of
the two restrictions to the intersection is restriction to the intersection: the other
restriction contributes nothing. -/
theorem biprod_inl_comp_unionBiprodToIntersection (hbot : I ⊓ J = ⊥) :
    (biprod.inl : pushedForwardStructureSheaf J.subschemeι ⟶ _) ≫
      unionBiprodToIntersection I J hbot =
      pushedForwardStructureSheafToComposite
        (Scheme.IdealSheafData.inclusion (I := J) (J := I ⊔ J) le_sup_right) J.subschemeι := by
  simp [unionBiprodToIntersection]

/-- **A direct image which is affine on the closed subscheme cut out by `J` carries the second
arrow of the union sequence to an epimorphism.** The witness is the first summand, where the
arrow is restriction from `V(J)` to the intersection. -/
theorem epi_pushforward_map_unionBiprodToIntersection {T : Scheme.{u}} (hbot : I ⊓ J = ⊥)
    (g : S ⟶ T) [IsAffineHom (J.subschemeι ≫ g)] :
    Epi ((Scheme.Modules.pushforward g).map (unionBiprodToIntersection I J hbot)) := by
  have := epi_pushforward_map_pushedForwardStructureSheafToComposite
    (Scheme.IdealSheafData.inclusion (I := J) (J := I ⊔ J) le_sup_right) J.subschemeι g
  refine epi_of_epi_fac (f := (Scheme.Modules.pushforward g).map
      (biprod.inl : pushedForwardStructureSheaf J.subschemeι ⟶ _))
    (h := (Scheme.Modules.pushforward g).map (pushedForwardStructureSheafToComposite
      (Scheme.IdealSheafData.inclusion (I := J) (J := I ⊔ J) le_sup_right) J.subschemeι)) ?_
  rw [← Functor.map_comp, biprod_inl_comp_unionBiprodToIntersection I J hbot]

/-- **The union sequence of [Stacks, Tag 0C4J] for two closed subschemes covering the whole
scheme.** Exactness in the middle and injectivity on the left are the fibre square
`AlgebraicGeometry.isPullback_structureSheaf_union`; surjectivity on the right comes from the
first summand, the comparison map of the closed immersion of the intersection into `V(J)` being
surjective. -/
theorem unionStructureSheafShortComplex_shortExact (hbot : I ⊓ J = ⊥) :
    ∃ zero : unionStructureSheafToBiprod I J ≫ unionBiprodToIntersection I J hbot = 0,
      (ShortComplex.mk (unionStructureSheafToBiprod I J)
        (unionBiprodToIntersection I J hbot) zero).ShortExact := by
  have hp := isPullback_structureSheaf_union I J hbot
  have hzero : unionStructureSheafToBiprod I J ≫ unionBiprodToIntersection I J hbot = 0 :=
    hp.toCommSq.shortComplex'.zero
  refine ⟨hzero, ?_⟩
  have hex : (ShortComplex.mk (unionStructureSheafToBiprod I J)
      (unionBiprodToIntersection I J hbot) hzero).Exact := hp.exact_shortComplex'
  have hmono : Mono (ShortComplex.mk (unionStructureSheafToBiprod I J)
      (unionBiprodToIntersection I J hbot) hzero).f := hp.mono_shortComplex'_f
  have hepi : Epi (ShortComplex.mk (unionStructureSheafToBiprod I J)
      (unionBiprodToIntersection I J hbot) hzero).g := by
    have : Epi (pushedForwardStructureSheafToComposite
        (Scheme.IdealSheafData.inclusion (I := J) (J := I ⊔ J) le_sup_right) J.subschemeι) :=
      epi_pushedForwardStructureSheafToComposite _ _
    exact epi_of_epi_fac (biprod_inl_comp_unionBiprodToIntersection I J hbot)
  exact ShortComplex.ShortExact.mk' hex hmono hepi

end AlgebraicGeometry

end
