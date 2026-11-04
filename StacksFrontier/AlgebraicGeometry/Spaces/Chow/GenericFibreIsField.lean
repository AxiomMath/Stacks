module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFibreChartPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalFunctionsTransport

/-!
# The ring of the fibre over a point with a single preimage is a field

Let `p : X ⟶ Y` be a relatively representable *finite* morphism of algebraic spaces over a scheme
`S` of a big fppf site `B`, with `X` and `Y` decent and reduced, and let `x` be a point of `X`
whose image `ξ = p(x)` has local ring of dimension zero and is hit by `|p|` at `x` alone. Then the
fibre `X ×_Y Spec κ(ξ)` is `Spec D` with

* `D` a finite `κ(ξ)`-algebra, by `AlgebraicGeometry.Space.finite_appTop_pullback_fieldMorphism`;
* `D` reduced, by `AlgebraicGeometry.Space.isReduced_appTop_pullback_residueFieldMorphism`;
* `Spec D` a single point, because `Spec κ(ξ) ⟶ Y` is a monomorphism (Stacks 0EMW) so the
  projection `Spec D ⟶ X` is one too, and the points of `Spec D` therefore inject into the fibre
  of `|p|` over `ξ`;
* `Spec D` nonempty, because the comparison morphism
  `AlgebraicGeometry.Space.residueFibreComparison` out of `Spec κ(x)` lands in it.

A nontrivial reduced ring with a one-point spectrum is a field, by
`PrimeSpectrum.subsingleton_iff_isField_of_isReduced`. So **`D` is a field**.

## Main results

* `AlgebraicGeometry.Space.subsingleton_points_pullback_residueFieldMorphism` and
  `AlgebraicGeometry.Space.subsingleton_toScheme_obj_pullback_residueFieldMorphism`: the fibre
  `X ×_Y Spec κ(ξ)` has at most one point, on the space and on the representing scheme.
* `AlgebraicGeometry.Space.nonempty_toScheme_obj_pullback_residueFieldMorphism`: the fibre over
  the image of a point of `X` is nonempty.
* `AlgebraicGeometry.Space.isField_appTop_pullback_residueFieldMorphism`: **the ring of the fibre
  is a field.**

## References

* [Stacks Project, Tag 0EMW](https://stacks.math.columbia.edu/tag/0EMW)
* [Stacks Project, Tag 0EMX](https://stacks.math.columbia.edu/tag/0EMX)
* [Stacks Project, Tag 0EQ4](https://stacks.math.columbia.edu/tag/0EQ4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] AlgebraicGeometry.BigFppfSite.hasPullbacks_schemes

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The spectrum of the residue field at a point -/

/-- The presheaf represented by the chosen field-valued representative of a point of a decent
algebraic space has at most one point. -/
theorem subsingleton_points_siteObject_residueFieldRepresentative
    (hdecY : IsDecentSpace B S hS Y) (ξ : points B S hS Y) :
    Subsingleton (points B S hS
      (yoneda.obj ((residueFieldRepresentative B S hS Y hdecY ξ).1.siteObject B S hS Y))) :=
  have := subsingleton_toScheme_siteObject B S hS Y
    (residueFieldRepresentative B S hS Y hdecY ξ).1
  ⟨fun _ _ => injective_pointsToScheme B S hS _ (Subsingleton.elim _ _)⟩

/-- The residue field morphism at `ξ` carries every point of its source to `ξ`. -/
theorem pointsMap_residueFieldMorphism_eq (hdecY : IsDecentSpace B S hS Y)
    (ξ : points B S hS Y) (z : points B S hS
      (yoneda.obj ((residueFieldRepresentative B S hS Y hdecY ξ).1.siteObject B S hS Y))) :
    pointsMap B S hS _ (residueFieldMorphism B S hS Y hdecY ξ) z = ξ := by
  have := subsingleton_points_siteObject_residueFieldRepresentative B S hS hdecY ξ
  rw [Subsingleton.elim z
      (((residueFieldRepresentative B S hS Y hdecY ξ).1.tautologicalPoint B S hS Y).class
        B S hS _),
    pointsMap_fieldMorphism_tautologicalPoint]
  exact (residueFieldRepresentative B S hS Y hdecY ξ).2.1

/-! ### The fibre has at most one point -/

/-- A fibre of `|p|` which is a singleton has at most one point. -/
theorem subsingleton_fibre_of_fibre_eq_singleton (p : X ⟶ Y) (ξ : points B S hS Y)
    {x₀ : points B S hS X}
    (h : {x : points B S hS X | pointsMap B S hS X p x = ξ} = {x₀}) :
    ∀ x x' : points B S hS X, pointsMap B S hS X p x = ξ →
      pointsMap B S hS X p x' = ξ → x = x' := by
  obtain ⟨-, h⟩ := Set.eq_singleton_iff_unique_mem.mp h
  exact fun x x' hx hx' => (h x hx).trans (h x' hx').symm

/-- **The fibre `X ×_Y Spec κ(ξ)` has at most one point** when the fibre of `|p|` over `ξ`
does. -/
theorem subsingleton_points_pullback_residueFieldMorphism {p : X ⟶ Y}
    (hrep : yoneda.relativelyRepresentable p) (hdecY : IsDecentSpace B S hS Y)
    (ξ : points B S hS Y)
    (hfib : ∀ x x' : points B S hS X, pointsMap B S hS X p x = ξ →
      pointsMap B S hS X p x' = ξ → x = x') :
    Subsingleton (points B S hS
      (yoneda.obj (hrep.pullback (residueFieldMorphism B S hS Y hdecY ξ)))) := by
  have hmono : Mono (residueFieldMorphism B S hS Y hdecY ξ) :=
    (residueFieldRepresentative B S hS Y hdecY ξ).2.2
  have : Mono (hrep.fst (residueFieldMorphism B S hS Y hdecY ξ)) :=
    mono_fst_fieldMorphism B S hS hrep _ hmono
  have himg : ∀ θ : points B S hS
      (yoneda.obj (hrep.pullback (residueFieldMorphism B S hS Y hdecY ξ))),
      pointsMap B S hS X p
        (pointsMap B S hS _ (hrep.fst (residueFieldMorphism B S hS Y hdecY ξ)) θ) = ξ := by
    intro θ
    rw [← pointsMap_comp_apply, hrep.w, pointsMap_comp_apply]
    exact pointsMap_residueFieldMorphism_eq B S hS hdecY ξ _
  exact ⟨fun θ θ' => pointsMap_injective_of_mono B S hS _ (hfib _ _ (himg θ) (himg θ'))⟩

/-- **The representing scheme of the fibre `X ×_Y Spec κ(ξ)` has at most one point** when the
fibre of `|p|` over `ξ` does. -/
theorem subsingleton_toScheme_obj_pullback_residueFieldMorphism {p : X ⟶ Y}
    (hrep : yoneda.relativelyRepresentable p) (hdecY : IsDecentSpace B S hS Y)
    (ξ : points B S hS Y)
    (hfib : ∀ x x' : points B S hS X, pointsMap B S hS X p x = ξ →
      pointsMap B S hS X p x' = ξ → x = x') :
    Subsingleton ((BigFppfOver.toScheme B S hS).obj
      (hrep.pullback (residueFieldMorphism B S hS Y hdecY ξ))) :=
  have := subsingleton_points_pullback_residueFieldMorphism B S hS hrep hdecY ξ hfib
  (pointsEquivScheme B S hS _).symm.injective.subsingleton

/-! ### The fibre over the image of a point is nonempty -/

/-- **The fibre of `p` over the image of a point `x` of `X` is nonempty**: the representing
scheme of `X ×_Y Spec κ(p(x))` has a point. -/
theorem nonempty_toScheme_obj_pullback_residueFieldMorphism {p : X ⟶ Y}
    (hrep : yoneda.relativelyRepresentable p) (hY : IsAlgebraicSpace B S hS Y)
    (hdecX : IsDecentSpace B S hS X) (hdecY : IsDecentSpace B S hS Y)
    (x : points B S hS X) :
    Nonempty ((BigFppfOver.toScheme B S hS).obj
      (hrep.pullback (residueFieldMorphism B S hS Y hdecY (pointsMap B S hS X p x)))) := by
  obtain ⟨g, -, hg⟩ := residueFieldHom_spec B S hS X Y hY hdecX hdecY p x
  exact ⟨(BigFppfOver.toScheme B S hS).map
    (residueFibreComparison B S hS hrep hdecX hdecY x g hg)
    (IsLocalRing.closedPoint (residueField B S hS X hdecX x))⟩

/-! ### The ring of the fibre is a field -/

/-- **The ring of the fibre of a finite morphism over the image of a point with no other
preimage is a field**, as soon as the source and target are reduced and the local ring of the
target at that image has dimension zero. -/
theorem isField_appTop_pullback_residueFieldMorphism {p : X ⟶ Y}
    (hrep : yoneda.relativelyRepresentable p) (hp : IsFinite B S hS p)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hdecX : IsDecentSpace B S hS X) (hdecY : IsDecentSpace B S hS Y)
    (hredX : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsReduced T))
    (hredY : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsReduced T))
    (x : points B S hS X)
    (hdim : localRingDimension B S hS (pointsMap B S hS X p x) = 0)
    (hfib : ∀ y y' : points B S hS X, pointsMap B S hS X p y = pointsMap B S hS X p x →
      pointsMap B S hS X p y' = pointsMap B S hS X p x → y = y') :
    IsField Γ((BigFppfOver.toScheme B S hS).obj
      (hrep.pullback (residueFieldMorphism B S hS Y hdecY
        (pointsMap B S hS X p x))), ⊤) := by
  set T := (BigFppfOver.toScheme B S hS).obj
    (hrep.pullback (residueFieldMorphism B S hS Y hdecY (pointsMap B S hS X p x)))
  have : IsAffine T := isAffine_toScheme_obj_pullback_fieldMorphism B S hS hrep
    (residueFieldRepresentative B S hS Y hdecY (pointsMap B S hS X p x)).1 hp
  have : Nonempty T :=
    nonempty_toScheme_obj_pullback_residueFieldMorphism B S hS hrep hY hdecX hdecY x
  have : Nontrivial Γ(T, ⊤) := PrimeSpectrum.nontrivial (T.isoSpec.hom (Classical.arbitrary T))
  have : _root_.IsReduced Γ(T, ⊤) :=
    isReduced_appTop_pullback_residueFieldMorphism B S hS hrep hX hY hdecY hredX hredY hdim
  have : Subsingleton T :=
    subsingleton_toScheme_obj_pullback_residueFieldMorphism B S hS hrep hdecY _ hfib
  exact PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mp
    (Scheme.homeoOfIso T.isoSpec).symm.toEquiv.subsingleton

end AlgebraicGeometry.Space

end
