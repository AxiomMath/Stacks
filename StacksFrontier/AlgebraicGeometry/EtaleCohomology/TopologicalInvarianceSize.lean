module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceThickening
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# The étale lift across a thickening stays inside a big fppf site

Let `i : S₀ ⟶ S` be a closed immersion which is surjective on points and let `p : U ⟶ S₀` be
étale. Stacks 039R, in the form
`Stacks.Etale.exists_etale_pullback_iso_of_isClosedImmersion_of_surjective`, produces a scheme
`V` étale over `S` whose base change along `i` is `U`. That statement gives no control on the
size of `V`, so it cannot by itself place `V` in the underlying category `Sch_κ` of a big fppf
site. This file supplies the missing bound: if `U` and `S` both lie in `Sch_κ` then so does `V`.

## Main results

* `AlgebraicGeometry.Scheme.size_le_max_of_locallyOfFiniteType_of_isHomeomorph`: a scheme
  locally of finite type over `W` and homeomorphic to a scheme `U` has size at most
  `max (size U) (size W)`.
* `Stacks.Etale.contains_of_etale_of_isHomeomorph`: a scheme étale over an object of a big
  fppf site and homeomorphic to an object of that site is itself an object of it.
* `Stacks.Etale.exists_etale_pullback_iso_contains_of_isClosedImmersion_of_surjective`:
  **Stacks 039R with size control.** The étale lift of `U` across a thickening `i : S₀ ⟶ S`
  can be taken inside the site as soon as `U` and `S` are.

## Implementation notes

**Why a homeomorphism is enough.** The size of a scheme, `AlgebraicGeometry.Scheme.size`, is
bounded on an open cover by Stacks 000Q: `size X ≤ max #I (⨆ i, size (U i))`. Taking for the
cover the preimages of the affine opens of the homeomorphic model `U` bounds the index type by
`size U`, and each member of the cover is *quasi-compact* — being homeomorphic to an affine open
of `U` — so Stacks 04T7 bounds its size by `size W`. Only compactness of the members is used,
not affineness.

This is what makes the bound available at an arbitrary thickening. Reading the cover as a cover
by *affine* opens would need a thickening of an affine scheme to be affine, which is Stacks 07VT
in general and
`Stacks.Thickenings.isAffine_of_isFirstOrderThickening` at first order; neither is needed here,
because quasi-compactness of an open subscheme is a purely topological condition and the
homeomorphism transports it.

**Where the homeomorphism comes from.** A closed immersion surjective on points is a universal
homeomorphism, `Stacks.Etale.universalHomeomorphism_of_isClosedImmersion_of_surjective`, so the
projection `V ×_S S₀ ⟶ V` of any base change along it is a homeomorphism by
`Stacks.Etale.isHomeomorph_pullbackFst`. Composing its inverse with the isomorphism
`V ×_S S₀ ≅ U` supplied by Stacks 039R gives a homeomorphism `V ≃ₜ U`.

## References

* [Stacks Project, Tag 000Q](https://stacks.math.columbia.edu/tag/000Q)
* [Stacks Project, Tag 039R](https://stacks.math.columbia.edu/tag/039R)
* [Stacks Project, Tag 04T7](https://stacks.math.columbia.edu/tag/04T7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry

/-- The preimage of an open subset of `U` along a homeomorphism `θ : V → U`, as an open
subscheme of `V`. -/
def Scheme.isHomeomorphComapOpens {V U : Scheme.{u}} {θ : V → U} (hθ : IsHomeomorph θ)
    (a : U.Opens) : V.Opens :=
  ⟨θ ⁻¹' (a : Set U), a.2.preimage hθ.continuous⟩

/-- The underlying set of `Scheme.isHomeomorphComapOpens hθ a` is the preimage `θ ⁻¹' a`. -/
@[simp]
theorem Scheme.coe_isHomeomorphComapOpens {V U : Scheme.{u}} {θ : V → U} (hθ : IsHomeomorph θ)
    (a : U.Opens) :
    ((Scheme.isHomeomorphComapOpens hθ a : V.Opens) : Set V) = θ ⁻¹' (a : Set U) := rfl

/-- **A scheme locally of finite type over `W` and homeomorphic to `U` has size at most
`max (size U) (size W)`.** -/
theorem Scheme.size_le_max_of_locallyOfFiniteType_of_isHomeomorph {V U W : Scheme.{u}}
    (q : V ⟶ W) [LocallyOfFiniteType q] (θ : V → U) (hθ : IsHomeomorph θ) :
    V.size ≤ max U.size W.size := by
  have hne : Nonempty U.affineOpens := ⟨⟨⊥, isAffineOpen_bot U⟩⟩
  have hcov : ⨆ a : U.affineOpens, Scheme.isHomeomorphComapOpens hθ a.1 = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    have hx : θ x ∈ ⨆ a : U.affineOpens, (a.1 : U.Opens) := by
      rw [iSup_affineOpens_eq_top]
      trivial
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, ha⟩
  refine (Scheme.size_le_of_iSup_eq_top _ hcov).trans (max_le ?_ (ciSup_le' fun a => ?_))
  · exact (Scheme.mk_affineOpens_le_size U).trans (le_max_left _ _)
  · have hcptV : IsCompact ((Scheme.isHomeomorphComapOpens hθ a.1 : V.Opens) : Set V) :=
      ((hθ.homeomorph θ).isCompact_preimage).2 a.2.isCompact
    have : CompactSpace ((Scheme.isHomeomorphComapOpens hθ a.1 : V.Opens) : Scheme.{u}) :=
      isCompact_iff_compactSpace.1 hcptV
    exact (Scheme.size_le_of_locallyOfFiniteType
      ((Scheme.isHomeomorphComapOpens hθ a.1).ι ≫ q)).trans (le_max_right _ _)

end AlgebraicGeometry

namespace Stacks.Etale

open AlgebraicGeometry

/-- **A scheme étale over an object of a big fppf site and homeomorphic to an object of that
site is an object of that site.** Both size bounds of
`AlgebraicGeometry.Scheme.size_le_max_of_locallyOfFiniteType_of_isHomeomorph` lie below the
cutoff. -/
theorem contains_of_etale_of_isHomeomorph (B : BigFppfSite.{u}) {V U W : Scheme.{u}}
    (q : V ⟶ W) (hq : Etale q) (θ : V → U) (hθ : IsHomeomorph θ)
    (hU : B.Contains U) (hW : B.Contains W) : B.Contains V := by
  have : Etale q := hq
  have : LocallyOfFiniteType q := inferInstance
  exact (Scheme.size_le_max_of_locallyOfFiniteType_of_isHomeomorph q θ hθ).trans_lt
    (max_lt hU hW)

/-- **Stacks 039R with size control.** Let `i : S₀ ⟶ S` be a closed immersion which is
surjective on points, with `S` an object of a big fppf site `B`, and let `p : U ⟶ S₀` be étale
with `U` an object of `B`. Then the scheme étale over `S` whose base change along `i` is `U` may
be taken to be an object of `B` as well.

This is the size clause the étale lift of Stacks 039R does not carry: its conclusion is a bare
`AlgebraicGeometry.Scheme`, and a presentation of an algebraic space needs its chart to lie in
the site. -/
theorem exists_etale_pullback_iso_contains_of_isClosedImmersion_of_surjective
    (B : BigFppfSite.{u}) {S₀ S : Scheme.{u}} (i : S₀ ⟶ S) [IsClosedImmersion i]
    (hi : Function.Surjective i.base) (hS : B.Contains S) (U : Scheme.{u})
    (hU : B.Contains U) (p : U ⟶ S₀) (hp : Etale p) :
    ∃ (V : Scheme.{u}) (q : V ⟶ S) (_ : Etale q) (e : pullback q i ≅ U),
      e.hom ≫ p = pullback.snd q i ∧ B.Contains V := by
  obtain ⟨V, q, hq, e, he⟩ :=
    exists_etale_pullback_iso_of_isClosedImmersion_of_surjective i hi U p hp
  have huh : UniversalHomeomorphism i :=
    universalHomeomorphism_of_isClosedImmersion_of_surjective i hi
  refine ⟨V, q, hq, e, he, ?_⟩
  have h₁ : (pullback q i : Scheme.{u}) ≃ₜ V :=
    (isHomeomorph_pullbackFst i q).homeomorph _
  have h₂ : (pullback q i : Scheme.{u}) ≃ₜ U := Scheme.Hom.homeomorph e.hom
  exact contains_of_etale_of_isHomeomorph B q hq (h₁.symm.trans h₂)
    (Homeomorph.isHomeomorph _) hU hS

/-- **Stacks 039R for objects of a big fppf site.** Let `j : W₀ ⟶ W` be a morphism of the big
fppf category over `S` whose underlying closed immersion of schemes is surjective on points,
and let `p` be an étale morphism of schemes from the scheme underlying an object `U` of the
category to the scheme underlying `W₀`. Then the étale lift of `U` across `j` is itself an
object of the big fppf category over `S`, with its structure morphism and its morphism to `W`
in the category.

Both size bounds of
`Stacks.Etale.exists_etale_pullback_iso_contains_of_isClosedImmersion_of_surjective` are
available here because an object of the category is a scheme below the site's cutoff, and the
lifted morphism to `W` lies over `S` by construction, so
`AlgebraicGeometry.BigFppfOver.exists_hom_of_comp_eq` turns it into a morphism of the
category. -/
theorem exists_bigFppfOver_etale_pullback_iso_of_isClosedImmersion_of_surjective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W₀ W : BigFppfOver B S hS} (j : W₀ ⟶ W)
    [IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)]
    (hj : Function.Surjective ((BigFppfOver.toScheme B S hS).map j).base)
    (U : BigFppfOver B S hS)
    (p : (BigFppfOver.toScheme B S hS).obj U ⟶ (BigFppfOver.toScheme B S hS).obj W₀)
    (hp : Etale p) :
    ∃ (V : BigFppfOver B S hS) (q : V ⟶ W)
      (_ : Etale ((BigFppfOver.toScheme B S hS).map q))
      (e : pullback ((BigFppfOver.toScheme B S hS).map q)
          ((BigFppfOver.toScheme B S hS).map j) ≅ (BigFppfOver.toScheme B S hS).obj U),
      e.hom ≫ p = pullback.snd ((BigFppfOver.toScheme B S hS).map q)
        ((BigFppfOver.toScheme B S hS).map j) := by
  obtain ⟨V₀, q₀, hq₀, e, he, hV₀⟩ :=
    exists_etale_pullback_iso_contains_of_isClosedImmersion_of_surjective B
      ((BigFppfOver.toScheme B S hS).map j) hj W.left.2
      ((BigFppfOver.toScheme B S hS).obj U) U.left.2 p hp
  obtain ⟨q, hqmap⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS
    (X := BigFppfOver.mk B S hS hV₀ (q₀ ≫ B.inclusion.map W.hom)) (Y := W) q₀ rfl
  refine ⟨BigFppfOver.mk B S hS hV₀ (q₀ ≫ B.inclusion.map W.hom), q, ?_⟩
  rw [hqmap]
  exact ⟨hq₀, e, he⟩

end Stacks.Etale

end
