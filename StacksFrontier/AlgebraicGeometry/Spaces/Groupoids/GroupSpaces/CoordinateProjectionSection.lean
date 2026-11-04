module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceRationalPoint
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.ReducedSmoothLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.CoordinateProjection
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A finite power of the projective line is reduced, and its coordinate projections split

Let `k` be a field and `B` a big fppf site containing `Spec k`. This file supplies the two
properties of `(ℙ¹_k)^n` and of its coordinate projections which the descent of the contraction
step of [Stacks, Tag 0AEM] along a field extension consumes, namely the hypotheses `hXred` and
`s`, `hsp` of
`AlgebraicGeometry.Space.exists_index_factorization_finite_fibres_of_relocalizeRestrict`:

* the power is *reduced* as an algebraic space over `k`, in the sense of
  `AlgebraicGeometry.Space.HasEtaleLocalProperty` — this is what makes the agreement locus of
  two morphisms out of it decide their equality;
* each coordinate projection `(ℙ¹_k)^n ⟶ (ℙ¹_k)^I` has a *section*, so it is a split
  epimorphism and a morphism factors through it in at most one way.

## Main definitions

* `AlgebraicGeometry.Space.projectiveLineSiteSection`: the `k`-rational point of `ℙ¹_k` all of
  whose homogeneous coordinates are `1`, as a section of the structure morphism of the object
  of the site representing the projective line.
* `AlgebraicGeometry.Space.projectiveLinePoint` and
  `AlgebraicGeometry.Space.projectiveLinePowerPoint`: that point, and the point of a power all
  of whose coordinates are it, as morphisms from the terminal presheaf.
* `AlgebraicGeometry.Space.coordinateProjectionSection`: the section of the coordinate
  projection which fills the discarded coordinates with that point.

## Main results

* `AlgebraicGeometry.Space.isReduced_projectiveLinePowerSiteObject`: the scheme underlying the
  object of the site representing `(ℙ¹_k)^n` is reduced.
* `AlgebraicGeometry.Space.hasEtaleLocalProperty_isReduced_projectiveLinePower`: **`(ℙ¹_k)^n`
  is reduced as an algebraic space over `k`.**
* `AlgebraicGeometry.Space.coordinateProjectionSection_comp`: **the coordinate projection is a
  split epimorphism.**

## Implementation notes

Reducedness is read off the representing object of the site. `(ℙ¹_k)^n` is represented by the
`n`-fold product of `AlgebraicGeometry.Space.projectiveLineSiteObject` in the big fppf site over
`Spec k` (`AlgebraicGeometry.Space.projectiveLinePowerRepresentationIso`), and
`AlgebraicGeometry.Space.hasEtaleLocalProperty_of_representable` turns a property of the
underlying scheme of a representing object into the étale-local property of the space — the
identity being a surjective étale atlas — with no locality hypothesis needed.

For the underlying scheme the property wanted is reducedness, and the route to it is
smoothness: a product in the site is a fibre product of schemes over `Spec k`, so the structure
morphism of the `n`-fold power is smooth as soon as the structure morphism of one factor is,
being built from base changes and composites of it. That is the content of the three private
lemmas `property_site_of_iso`, `property_site_product` and `property_site_power`, stated for an
arbitrary morphism property stable under base change and composition and containing the
identities; `AlgebraicGeometry.projectiveSpaceOver.smooth` starts the induction. A scheme
smooth over a reduced one is reduced, because reducedness is local for the smooth topology
(`AlgebraicGeometry.isReduced_isLocal_smooth`, Tag 034E) and a single smooth morphism together
with the identity of its target is a smooth covering of that target.

The section comes from the product decomposition
`AlgebraicGeometry.Space.isLimit_binaryFan_coordinateProjection`: the projection onto the
coordinates in `I` and the projection onto those outside `I` exhibit `(ℙ¹_k)^n` as a product, so
a section of the first is obtained by pairing the identity of `(ℙ¹_k)^I` with any morphism
`(ℙ¹_k)^I ⟶ (ℙ¹_k)^{Iᶜ}`. The morphism taken is the constant one at the rational point of
`ℙ¹_k` all of whose homogeneous coordinates are `1`,
`AlgebraicGeometry.allOnesSection`; no hypothesis on `I` is needed, the empty
subset included, since the base is terminal among presheaves on the site. The abstract form of
that construction is `AlgebraicGeometry.Space.prodSectionOfPoint`, which is stated for the
*canonical* binary product and its `CategoryTheory.Limits.prod.snd`; the coordinate projection
is a projection of a binary fan which is not that canonical one, so the limiting property of
the fan is used directly rather than transporting along the comparison isomorphism.

## References

* [Stacks Project, Tag 034E](https://stacks.math.columbia.edu/tag/034E)
* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
* [Stacks Project, Tag 0B2P](https://stacks.math.columbia.edu/tag/0B2P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space

/-! ### Reducedness from smoothness -/

/-- A scheme smooth over a reduced scheme is reduced: reducedness is local for the smooth
topology, and a smooth morphism together with the identity of its target is a smooth covering
of that target. -/
@[sga "3 XV 6.9" "(a)"]
private theorem isReduced_of_smooth_map {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : Smooth f)
    (hY : IsReduced Y) : IsReduced X := by
  let Z : Bool → Scheme.{u} := fun | true => X | false => Y
  let g : ∀ i, Z i ⟶ Y := fun | true => f | false => 𝟙 Y
  have hcover : Presieve.ofArrows Z g ∈ Scheme.precoverage (@Smooth.{u}) Y := by
    rw [Scheme.ofArrows_mem_precoverage_iff (P := (@Smooth.{u}))]
    exact ⟨fun y => ⟨false, y, rfl⟩, fun
      | false => inferInstanceAs (Smooth (𝟙 Y))
      | true => hf⟩
  exact CategoryTheory.ObjectProperty.IsLocal.component
    (P := fun W : Scheme.{u} => IsReduced W) hcover f (Presieve.ofArrows.mk true) hY

/-! ### A property of the structure morphism of a finite power in the site -/

section SiteProducts

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The structure morphism of an object of the big fppf site factors through the structure
morphism of its target along any morphism of the site. -/
private theorem inclusion_map_hom_eq_left_comp {X Y : BigFppfOver B S hS} (f : X ⟶ Y) :
    B.inclusion.map X.hom = B.inclusion.map f.left ≫ B.inclusion.map Y.hom := by
  rw [← B.inclusion.map_comp, Over.w]

/-- A property of morphisms of schemes stable under isomorphisms holds of the structure
morphism of an object of the big fppf site exactly when it holds of that of an isomorphic
object. -/
private theorem property_site_of_iso (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X Y : BigFppfOver B S hS} (e : X ≅ Y) (hY : P (B.inclusion.map Y.hom)) :
    P (B.inclusion.map X.hom) := by
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  rw [inclusion_map_hom_eq_left_comp B S hS e.hom]
  exact (P.cancel_left_of_respectsIso _ _).mpr hY

/-- A property of morphisms of schemes stable under base change and composition holds of the
structure morphism of a product of two objects of the big fppf site as soon as it holds of the
two structure morphisms: the first projection of the product is the base change of the second
structure morphism. -/
private theorem property_site_product (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    (X Y : BigFppfOver B S hS) [HasBinaryProduct X Y]
    (hX : P (B.inclusion.map X.hom)) (hY : P (B.inclusion.map Y.hom)) :
    P (B.inclusion.map (X ⨯ Y).hom) := by
  rw [inclusion_map_hom_eq_left_comp B S hS (prod.fst : X ⨯ Y ⟶ X)]
  exact P.comp_mem _ _ (MorphismProperty.of_isPullback
    ((Over.isPullback_of_binaryFan_isLimit _ (prodIsProd X Y)).map B.inclusion).flip hY) hX

/-- Such a property, true of the identities, holds of the structure morphism of a finite power
of an object of the big fppf site as soon as it holds of the structure morphism of that
object. -/
private theorem property_site_power [HasFiniteProducts (BigFppfOver B S hS)]
    (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    (hPid : ∀ W : Scheme.{u}, P (𝟙 W))
    (X : BigFppfOver B S hS) (hX : P (B.inclusion.map X.hom)) (n : ℕ) :
    P (B.inclusion.map (∏ᶜ fun _ : Fin n => X).hom) := by
  induction n with
  | zero =>
    have ht : IsTerminal (∏ᶜ fun _ : Fin 0 => X) :=
      IsTerminal.ofUniqueHom (fun _ => Pi.lift fun i => Fin.elim0 i)
        (fun _ _ => Pi.hom_ext _ _ fun i => Fin.elim0 i)
    refine property_site_of_iso B S hS P (ht.uniqueUpToIso Over.mkIdTerminal) ?_
    simpa using hPid _
  | succ n ih =>
    exact property_site_of_iso B S hS P (piFinSuccIso X n)
      (property_site_product B S hS P _ X ih hX)

end SiteProducts

/-! ### A finite power of the projective line is reduced -/

variable (k : Type u) [Field k] (B : BigFppfSite.{u})
  (hk : B.Contains (Spec (CommRingCat.of k)))

/-- The scheme underlying the object of the big fppf site representing `(ℙ¹_k)^n` is reduced:
its structure morphism to `Spec k` is smooth, being built by base change and composition from
the smooth morphism `ℙ¹_k ⟶ Spec k`, and `Spec k` is reduced. -/
theorem isReduced_projectiveLinePowerSiteObject (n : ℕ) :
    IsReduced ((BigFppfOver.toScheme B (Spec (CommRingCat.of k)) hk).obj
      (projectiveLinePowerSiteObject k B hk n)) := by
  have : HasBinaryProducts (BigFppfOver B (Spec (CommRingCat.of k)) hk) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have : HasFiniteProducts (BigFppfOver B (Spec (CommRingCat.of k)) hk) :=
    hasFiniteProducts_of_has_binary_and_terminal
  have hsm : Smooth (B.inclusion.map (projectiveLinePowerSiteObject k B hk n).hom) :=
    property_site_power B (Spec (CommRingCat.of k)) hk (@Smooth.{u})
      (fun W => inferInstanceAs (Smooth (𝟙 W))) (projectiveLineSiteObject k B hk)
      (inferInstance : Smooth
        (projectiveSpaceOverRing 1 (CommRingCat.of k) ↘ Spec (CommRingCat.of k))) n
  exact isReduced_of_smooth_map _ hsm
    (inferInstance : IsReduced (Spec (CommRingCat.of k)))

/-- **A finite power of the projective line is reduced as an algebraic space over `k`.** It is
represented by an object of the big fppf site whose underlying scheme is reduced, and an
isomorphism onto a representable presheaf is a surjective étale atlas. -/
theorem hasEtaleLocalProperty_isReduced_projectiveLinePower (n : ℕ) :
    HasEtaleLocalProperty B (Spec (CommRingCat.of k)) hk
      (projectiveLinePower k B hk (Fin n)) (fun W : Scheme.{u} => IsReduced W) :=
  hasEtaleLocalProperty_of_representable B (Spec (CommRingCat.of k)) hk _ _
    (projectiveLinePowerSiteObject k B hk n)
    (projectiveLinePowerRepresentationIso k B hk n)
    (isReduced_projectiveLinePowerSiteObject k B hk n)

/-! ### A rational point of the projective line and of its powers -/

/-- The `k`-rational point of `ℙ¹_k` all of whose homogeneous coordinates are `1`, as a section
of the structure morphism of the object of the site representing the projective line. -/
noncomputable def projectiveLineSiteSection :
    Over.mk (𝟙 (B.obj hk)) ⟶ projectiveLineSiteObject k B hk :=
  Over.homMk (ObjectProperty.homMk (allOnesSection (Spec (CommRingCat.of k)) 1))
    (ObjectProperty.hom_ext _ (allOnesSection_comp_structureMorphism (Spec (CommRingCat.of k)) 1))

/-- That rational point of `ℙ¹_k`, as a morphism from the terminal presheaf on the big fppf site
over `Spec k` to the projective line as an algebraic space. -/
noncomputable def projectiveLinePoint :
    yoneda.obj (Over.mk (𝟙 (B.obj hk))) ⟶ projectiveLineFunctor k B hk :=
  yoneda.map (projectiveLineSiteSection k B hk) ≫
    (projectiveLineRestrictedYonedaIso k B hk).inv

/-- The point of a power of the projective line all of whose coordinates are the rational point
`AlgebraicGeometry.Space.projectiveLinePoint`. -/
noncomputable def projectiveLinePowerPoint (α : Type v) [Small.{u} α] :
    yoneda.obj (Over.mk (𝟙 (B.obj hk))) ⟶ projectiveLinePower k B hk α :=
  Pi.lift fun _ => projectiveLinePoint k B hk

/-! ### The coordinate projection is a split epimorphism -/

/-- The section of the coordinate projection `(ℙ¹_k)^n ⟶ (ℙ¹_k)^I` which keeps the coordinates
in `I` and gives every coordinate outside `I` the rational point
`AlgebraicGeometry.Space.projectiveLinePoint`.

It is the morphism into the product of `(ℙ¹_k)^I` with `(ℙ¹_k)^{Iᶜ}` pairing the identity with
the constant morphism at that point, the base being terminal among presheaves on the site. -/
noncomputable def coordinateProjectionSection (n : ℕ) (I : Finset (Fin n)) :
    projectiveLinePower k B hk I ⟶ projectiveLinePower k B hk (Fin n) :=
  (isLimit_binaryFan_coordinateProjection k B hk n I).lift
    (BinaryFan.mk (𝟙 (projectiveLinePower k B hk I))
      ((base_isTerminal k B hk).from (projectiveLinePower k B hk I) ≫
        projectiveLinePowerPoint k B hk {j : Fin n // j ∉ I}))

/-- **The coordinate projection `(ℙ¹_k)^n ⟶ (ℙ¹_k)^I` is a split epimorphism**, for every `n`
and every finite subset `I ⊆ Fin n`, the empty subset included. -/
theorem coordinateProjectionSection_comp (n : ℕ) (I : Finset (Fin n)) :
    coordinateProjectionSection k B hk n I ≫ coordinateProjection k B hk n I =
      𝟙 (projectiveLinePower k B hk I) :=
  (isLimit_binaryFan_coordinateProjection k B hk n I).fac _ ⟨WalkingPair.left⟩

end AlgebraicGeometry.Space

end
