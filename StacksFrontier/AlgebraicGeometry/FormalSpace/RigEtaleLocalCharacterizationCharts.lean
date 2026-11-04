module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineEtaleChartTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleLocalCharacterization

/-!
# Stacks 0GCZ with condition (2) read literally

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
locally Noetherian formal algebraic spaces over `S`. Condition (2) of **Stacks 0GCZ** asks that
for every commutative square

    U ⟶ X
    ↓     ↓
    V ⟶ Y

with `U`, `V` affine formal algebraic spaces and `U ⟶ X`, `V ⟶ Y` representable by algebraic
spaces and étale, the morphism `U ⟶ V` *corresponds to a rig-étale map in `WAdm^{Noeth}`*: `U`
and `V` are formal spectra of Noetherian adic rings and `U ⟶ V` is the formal spectrum of a
rig-étale homomorphism.

`AlgebraicGeometry.FormalSpace.isRigEtale_tfae_of_isLocallyNoetherian` states Stacks 0GCZ with
condition (2) read through `AlgebraicGeometry.FormalSpace.HasPropertyOnEveryAffineEtaleDiagram`:
every Noetherian presentation of `U ⟶ V` is rig-étale. As a conclusion that is weaker than the
source's condition unless the charts are known to have Noetherian presentations. They do: an
affine formal algebraic space representable étale over a locally Noetherian formal algebraic
space is Noetherian, which is Stacks 0AKX
(`AlgebraicGeometry.FormalSpace.isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale`).
This file uses it to show that the two readings of condition (2) agree, and states Stacks 0GCZ
with the source's reading.

## Main definitions

* `AlgebraicGeometry.FormalSpace.CorrespondsToRigEtaleMapOnEveryAffineEtaleDiagram`: condition
  (2) of Stacks 0GCZ in the source's words.

## Main results

* `AlgebraicGeometry.FormalSpace.correspondsToRigEtaleMapOnEveryAffineEtaleDiagram_iff`: for a
  morphism of locally Noetherian formal algebraic spaces the source's condition (2) is
  equivalent to the library's reading of it.
* `AlgebraicGeometry.FormalSpace.isRigEtale_tfae_of_isLocallyNoetherian'`: **Stacks 0GCZ**.

## References

* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0AKY](https://stacks.math.columbia.edu/tag/0AKY)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0GCZ](https://stacks.math.columbia.edu/tag/0GCZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalRing

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0GCZ, condition (2).** For every commutative square with `U`, `V` affine formal
algebraic spaces and `U ⟶ X`, `V ⟶ Y` representable by algebraic spaces and étale, the morphism
`U ⟶ V` corresponds to a rig-étale map in `WAdm^{Noeth}`. -/
abbrev CorrespondsToRigEtaleMapOnEveryAffineEtaleDiagram {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) : Prop :=
  ∀ (U V : FppfSheaf B S hS) (a : U ⟶ X) (b : V ⟶ Y) (t : U ⟶ V),
    IsAffineFormalAlgebraicSpace B S hS U → IsAffineFormalAlgebraicSpace B S hS V →
    IsRepresentableEtale B S hS a → IsRepresentableEtale B S hS b →
    a ≫ f = t ≫ b → CorrespondsToRigEtaleMap B S hS t

/-- A Noetherian affine formal algebraic space is the formal spectrum of a Noetherian adic ring:
its presenting ring is one, and the presentation identifies the space with the formal spectrum
of the quotient system it carries. -/
theorem exists_iso_formalSpectrum_of_isNoetherian {U : FppfSheaf B S hS}
    (hU : IsNoetherian B S hS U) :
    ∃ (R : Type u) (_ : CommRing R) (_ : TopologicalSpace R) (_ : IsTopologicalRing R)
      (_ : IsLinearTopology R R) (E : QuotientSystem B S hS R),
      IsNoetherianAdic R ∧ Nonempty (U ≅ formalSpectrum E) := by
  obtain ⟨-, R, hRR, hRT, hRTR, hRLT, ⟨-, ⟨P⟩⟩, hRnoeth, hRadic⟩ := hU
  exact ⟨R, hRR, hRT, hRTR, hRLT, P.quotientSystem, ⟨hRadic, hRnoeth⟩, ⟨P.formalSpectrumIso⟩⟩

/-- **The two readings of condition (2) of Stacks 0GCZ agree.** For a morphism `f : X ⟶ Y` of
locally Noetherian formal algebraic spaces, every affine étale square over `f` has its upper map
corresponding to a rig-étale map in `WAdm^{Noeth}` if and only if every Noetherian presentation
of that upper map is rig-étale.

A map corresponding to a rig-étale map has every Noetherian presentation rig-étale (Stacks 0AN0).
Conversely the two charts of a square are Noetherian by Stacks 0AKX, hence formal spectra of
Noetherian adic rings, and a presentation of the upper map between them exists by Stacks 0AN0. -/
theorem correspondsToRigEtaleMapOnEveryAffineEtaleDiagram_iff {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y) :
    CorrespondsToRigEtaleMapOnEveryAffineEtaleDiagram B S hS f ↔
      HasPropertyOnEveryAffineEtaleDiagram B S hS IsNoetherianAdic IsRigEtaleHom f := by
  refine ⟨fun h U V a b t hU hV ha hb hsq ↦
    hasPropertyOnAffineChartMap_of_correspondsToRigEtaleMap B S hS
      (h U V a b t hU hV ha hb hsq), fun h U V a b t hU hV ha hb hsq ↦ ?_⟩
  obtain ⟨R, _, _, _, _, E, hCR, ⟨eU⟩⟩ := exists_iso_formalSpectrum_of_isNoetherian B S hS
    (isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS hX a hU ha)
  obtain ⟨A, _, _, _, _, D, hCA, ⟨eV⟩⟩ := exists_iso_formalSpectrum_of_isNoetherian B S hS
    (isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS hY b hV hb)
  exact correspondsToRigEtaleMap_of_hasPropertyOnAffineChartMap B S hS
    (h U V a b t hU hV ha hb hsq) hCA hCR D E eU eV

/-- **Stacks 0GCZ.** Let `f : X ⟶ Y` be a morphism of locally Noetherian formal algebraic spaces
over `S`. The following are equivalent:

1. `f` is rig-étale (Definition 0AQM);
2. for every commutative square with `U`, `V` affine formal algebraic spaces and `U ⟶ X`,
   `V ⟶ Y` representable by algebraic spaces and étale, the morphism `U ⟶ V` corresponds to a
   rig-étale map in `WAdm^{Noeth}`;
3. there exist a covering `{Yⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Xⱼᵢ ⟶ Yⱼ ×_Y X}` as in Definition 0AIM such that each `Xⱼᵢ ⟶ Yⱼ` corresponds to a
   rig-étale map in `WAdm^{Noeth}`;
4. there exist a covering `{Xᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Xᵢ ⟶ Yᵢ ⟶ Y` where `Yᵢ` is an affine formal algebraic space, `Yᵢ ⟶ Y` is representable by
   algebraic spaces and étale, and `Xᵢ ⟶ Yᵢ` corresponds to a rig-étale map in
   `WAdm^{Noeth}`;
5. for every commutative square as in (2), every presentation of `U ⟶ V` by Noetherian adic rings
   is rig-étale.

Conditions (1) to (4) are the source's. In (2) the charts `U` and `V` are formal spectra of
Noetherian adic rings and `U ⟶ V` is the formal spectrum of a rig-étale homomorphism. Condition
(5) is the library's reading of Definition 0AQM, the form condition (2) takes in
`isRigEtale_tfae_of_isLocallyNoetherian`; it is recorded so that this statement contains that
one. Conditions (2) and (5) agree by `correspondsToRigEtaleMapOnEveryAffineEtaleDiagram_iff`,
which uses Stacks 0AKX, and the remaining implications are those of
`isRigEtale_tfae_of_isLocallyNoetherian`. -/
@[stacks 0GCZ]
theorem isRigEtale_tfae_of_isLocallyNoetherian' {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y) :
    List.TFAE
      [IsRigEtale B S hS f,
        CorrespondsToRigEtaleMapOnEveryAffineEtaleDiagram B S hS f,
        CorrespondsToRigEtaleMapAfterTargetCover B S hS f,
        CorrespondsToRigEtaleMapAfterSourceCover B S hS f,
        HasPropertyOnEveryAffineEtaleDiagram B S hS IsNoetherianAdic IsRigEtaleHom f] := by
  have h2 := correspondsToRigEtaleMapOnEveryAffineEtaleDiagram_iff B S hS f hX hY
  tfae_have 1 ↔ 2 := (isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f).trans h2.symm
  tfae_have 2 → 3 := fun h ↦
    correspondsToRigEtaleMapAfterTargetCover_of_hasPropertyOnEveryAffineEtaleDiagram B S hS f hX hY
      (h2.1 h)
  tfae_have 3 → 4 := correspondsToRigEtaleMapAfterSourceCover_of_afterTargetCover B S hS f
  tfae_have 4 → 2 := fun h ↦ h2.2
    (hasPropertyOnEveryAffineEtaleDiagram_of_correspondsToRigEtaleMapAfterSourceCover B S hS f h)
  tfae_have 2 ↔ 5 := h2
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
