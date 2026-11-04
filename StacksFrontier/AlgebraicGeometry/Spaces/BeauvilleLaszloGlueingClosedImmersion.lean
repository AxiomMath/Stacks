module

public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingAffineCanonicalRestriction
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingPropertyTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms

/-!
# Closed immersions of affine algebraic spaces from their glueing components (Stacks 0F9R)

Let `(g : R → R', f)` be a Beauville--Laszlo glueing pair, and write `X = Spec R`,
`U = Spec R_f`, `U' = Spec R'_{gf}` and `X' = Spec R'`. The glueing functor of Stacks 0F9N sends
a morphism of algebraic spaces over `X` to the triple of its base changes to `U`, `U'` and `X'`.
Stacks 0F9R says that the morphism has a property exactly when the three components do. For `P` a
closed immersion and in the language of algebraic spaces, we prove that a morphism of affine
algebraic spaces over `X` is a closed immersion as soon as its three components are; the full
biconditional, in the language of affine schemes over `X`, is
`BeauvilleLaszlo.isClosedImmersion_iff_baseChange`.

Being a closed immersion is a relatively representable condition (Stacks 02YU), so no glueability
hypothesis is needed.

## Main results

* `BeauvilleLaszlo.Space.isClosedImmersion_of_isClosedImmersion_glueingComponents`: a morphism of
  algebraic spaces over `X` between two affine ones is a closed immersion as soon as its three
  base changes to `U`, `U'` and `X'` are.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 0F9N](https://stacks.math.columbia.edu/tag/0F9N)
* [Stacks Project, Tag 0F9R](https://stacks.math.columbia.edu/tag/0F9R)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace BeauvilleLaszlo.Space

/-- **Stacks 0F9R for `P` a closed immersion, in the language of algebraic spaces.** Let
`(g : R → R', f)` be a glueing pair. A morphism `p : L → V` of algebraic spaces over `X = Spec R`
with `L` and `V` affine is a closed immersion as soon as its three base changes to
`U = Spec R_f`, `U' = Spec R'_{gf}` and `X' = Spec R'` — the three components of its image under
the glueing functor of Stacks 0F9N — are closed immersions. -/
theorem isClosedImmersion_of_isClosedImmersion_glueingComponents
    {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f) (B : BigFppfSite.{u})
    (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R'))) (hX : B.Contains (Spec (.of R)))
    {L V : AlgebraicSpaces B (Spec (.of R)) hX} (p : L ⟶ V)
    (hLa : AlgebraicGeometry.Space.IsAffineSpace B (Spec (.of R)) hX L.1)
    (hVa : AlgebraicGeometry.Space.IsAffineSpace B (Spec (.of R)) hX V.1)
    (hpU : AlgebraicGeometry.Space.IsClosedImmersion B (Spec (.of (Localization.Away f))) hU
      ((baseChange B (Spec (.of (Localization.Away f))) (Spec (.of R)) hU hX
        (canJU f B hU hX)).map p).hom)
    (hpU' : AlgebraicGeometry.Space.IsClosedImmersion B
      (Spec (.of (Localization.Away (g f)))) hU'
      ((baseChange B (Spec (.of (Localization.Away (g f)))) (Spec (.of R)) hU' hX
        (canGU g f B hU' hU ≫ canJU f B hU hX)).map p).hom)
    (hpX' : AlgebraicGeometry.Space.IsClosedImmersion B (Spec (.of R')) hX'
      ((baseChange B (Spec (.of R')) (Spec (.of R)) hX' hX (canJX' g B hX' hX)).map p).hom) :
    AlgebraicGeometry.Space.IsClosedImmersion B (Spec (.of R)) hX p.hom := by
  let : Algebra R R' := g.toAlgebra
  obtain ⟨TL, hTL, ⟨eL0⟩⟩ := hLa
  obtain ⟨A, hA, φA, ⟨eL1⟩⟩ := BigFppfOver.exists_specOver B hX TL hTL
  obtain ⟨TV, hTV, ⟨eV0⟩⟩ := hVa
  obtain ⟨C, hC, φC, ⟨eV1⟩⟩ := BigFppfOver.exists_specOver B hX TV hTV
  let : Algebra R A := φA.hom.toAlgebra
  let : Algebra R C := φC.hom.toAlgebra
  obtain ⟨eL, eV, ψ, hψ⟩ :
      ∃ (eL : L.1 ≅ yoneda.obj (BigFppfOver.specOver B hX hA φA))
        (eV : V.1 ≅ yoneda.obj (BigFppfOver.specOver B hX hC φC))
        (ψ : BigFppfOver.specOver B hX hA φA ⟶ BigFppfOver.specOver B hX hC φC),
        yoneda.map ψ = eL.inv ≫ p.hom ≫ eV.hom :=
    ⟨eL0 ≪≫ yoneda.mapIso eL1, eV0 ≪≫ yoneda.mapIso eV1, yoneda.preimage _,
      yoneda.map_preimage _⟩
  let h : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (A : Type u)))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (C : Type u)))) :=
    Over.homMk ((BigFppfOver.toScheme B (Spec (.of R)) hX).map ψ)
      (BigFppfOver.specOverHomMap_comp B hX hA hC φA φC ψ)
  have hh : h.left = (BigFppfOver.toScheme B (Spec (.of R)) hX).map ψ := rfl
  have hmain : IsClosedImmersion ((BigFppfOver.toScheme B (Spec (.of R)) hX).map ψ) := by
    rw [← hh]
    refine prop_of_presheaf_baseChange_triple (@IsClosedImmersion.{u})
      IsClosedImmersion.isStableUnderBaseChange B (Spec (.of R)) _ _ _ hX hU hU' hX'
      (canJU f B hU hX) (canGU g f B hU' hU ≫ canJU f B hU hX) (canJX' g B hX' hX)
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (algebraMap R R' f)))))
      (Spec.map (CommRingCat.ofHom (algebraMap R R')))
      rfl ?_ rfl ψ h hh p.hom eL eV hψ hpU hpU' hpX' ?_
    · rw [Functor.map_comp]
      change Spec.map (CommRingCat.ofHom (Localization.awayMap g f)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))) = _
      rw [← Spec.map_comp]
      congr 1
      ext r
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
        CommRingCat.hom_ofHom, Localization.awayMap, IsLocalization.Away.map,
        IsLocalization.map_eq]
      rfl
    · exact fun h₁ h₂ h₃ ↦
        (_root_.BeauvilleLaszlo.isClosedImmersion_iff_baseChange f hglue h).mpr ⟨h₁, h₂, h₃⟩
  exact presheaf_of_prop_toScheme_map (@IsClosedImmersion.{u})
    IsClosedImmersion.isStableUnderBaseChange B (Spec (.of R)) hX ψ p.hom eL eV hψ hmain

end BeauvilleLaszlo.Space

end
