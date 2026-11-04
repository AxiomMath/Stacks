module

public import Mathlib.AlgebraicGeometry.Gluing
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SmallSite

/-!
# Cardinality bounds for schemes, monomorphisms and glueings

Three size estimates used to keep a construction inside a big fppf site. The point set of a
scheme is bounded by the power set of its affine opens, hence by `2 ^ size`. The source of an
arbitrary monomorphism of schemes — with no finiteness hypothesis on the morphism — is
bounded by `2 ^ 2 ^ size` of the target. The scheme glued from a glueing datum is bounded by
the number of charts and their sizes.

## Main results

* `AlgebraicGeometry.mk_scheme_le_two_power_size`: `#X ≤ 2 ^ X.size`.
* `AlgebraicGeometry.size_le_of_mono_double_power`: the source of a monomorphism `X ⟶ Y`
  satisfies `X.size ≤ 2 ^ 2 ^ Y.size`.
* `AlgebraicGeometry.scheme_glueData_size_le`: the size of a glued scheme is bounded by the
  maximum of the number of charts and the supremum of their sizes.
* `AlgebraicGeometry.Space.mk_points_lt_cutoff`: an object of the big fppf site over `S` has
  fewer points than the cutoff of the site.

## Implementation notes

Unlike `AlgebraicGeometry.Scheme.size_le_of_mono_quasiCompact` and
`AlgebraicGeometry.Scheme.size_le_of_mono_locallyOfFinitePresentation`, which give the sharp
bound `X.size ≤ Y.size` under a finiteness hypothesis on the morphism, the estimate here
needs no hypothesis beyond monomorphy. It covers `X` by the affine opens contained in the
preimage of an affine open of `Y`; each such open is affine with an affine quasi-compact
monomorphism to an affine open of `Y`, so the sharp bound applies chartwise, and the index
set of the cover is bounded by the double power set. The double power is what makes this
usable inside a big fppf site, whose cutoff is a strong limit cardinal.
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The point set of a scheme injects into the power set of its affine opens, because the
affine opens are a basis and distinct points are separated by a basic open. -/
theorem mk_scheme_le_two_power_size (X : Scheme.{u}) : #X ≤ 2 ^ X.size := by
  let f : X → Set X.affineOpens := fun x => {U | x ∈ U.1}
  have hf : Function.Injective f := by
    intro x y h
    refine Inseparable.eq (X.isBasis_affineOpens.inseparable_iff.2 ?_)
    rintro _ ⟨U, hU, rfl⟩
    exact Set.ext_iff.mp h ⟨U, hU⟩
  exact ((mk_le_of_injective hf).trans_eq mk_set).trans
    (power_le_power_left two_ne_zero X.mk_affineOpens_le_size)

/-- The source of a monomorphism of schemes has size at most the double power of the size of
the target. No finiteness hypothesis on the morphism is needed. -/
theorem size_le_of_mono_double_power {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f] :
    X.size ≤ (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ Y.size) := by
  let μ : Cardinal.{u} := (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ Y.size)
  have hYsize : Y.size ≤ μ := (cantor Y.size).le.trans (cantor (2 ^ Y.size)).le
  have hXaff : #X.affineOpens ≤ μ :=
    calc
      #X.affineOpens ≤ #(Set X) := mk_le_of_injective (f := fun U => (U.1 : Set X))
        (fun _ _ h => Subtype.ext (Opens.ext h))
      _ = 2 ^ #X := mk_set
      _ ≤ μ := power_le_power_left two_ne_zero
        ((mk_le_of_injective (Scheme.Hom.injective f)).trans (mk_scheme_le_two_power_size Y))
  let I := {p : Y.affineOpens × X.affineOpens // p.2.1 ≤ f ⁻¹ᵁ p.1.1}
  let U : I → X.Opens := fun i => i.1.2.1
  have _ : Nonempty I := ⟨⟨(⟨⊥, isAffineOpen_bot Y⟩, ⟨⊥, isAffineOpen_bot X⟩), bot_le⟩⟩
  have hI : #I ≤ μ :=
    calc
      #I ≤ #(Y.affineOpens × X.affineOpens) := mk_subtype_le _
      _ = #Y.affineOpens * #X.affineOpens := by simp only [mk_prod, lift_id]
      _ ≤ μ * μ := mul_le_mul' (Y.mk_affineOpens_le_size.trans hYsize) hXaff
      _ = μ := mul_eq_self (Y.aleph0_le_size.trans hYsize)
  have hcover : ⨆ i, U i = ⊤ := by
    refine top_unique fun x _ => ?_
    obtain ⟨V, hV, hxV, _⟩ := (Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
      (show f x ∈ (⊤ : Y.Opens) from trivial)
    obtain ⟨W, hW, hxW, hWV⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
      (show x ∈ f ⁻¹ᵁ V from hxV)
    exact Opens.mem_iSup.mpr ⟨⟨(⟨V, hV⟩, ⟨W, hW⟩), hWV⟩, hxW⟩
  have hU (i : I) : (U i).toScheme.size ≤ μ := by
    let g : (U i).toScheme ⟶ i.1.1.1.toScheme :=
      IsOpenImmersion.lift i.1.1.1.ι ((U i).ι ≫ f) (by
        rintro _ ⟨x, rfl⟩
        exact ⟨⟨f x.1, i.2 x.2⟩, rfl⟩)
    have _ : Mono g := mono_of_mono_fac (IsOpenImmersion.lift_fac _ _ _)
    have _ : IsAffine (U i).toScheme := i.1.2.2
    have _ : IsAffine i.1.1.1.toScheme := i.1.1.2
    exact ((Scheme.size_le_of_mono_quasiCompact g).trans
      (Scheme.size_coe_opens_le Y i.1.1.1)).trans hYsize
  exact (Scheme.size_le_of_iSup_eq_top U hcover).trans
    (max_le hI (ciSup_le' hU))

/-- The scheme glued from a glueing datum with a nonempty set of charts has size at most the
maximum of the number of charts and the supremum of their sizes. -/
theorem scheme_glueData_size_le (D : Scheme.GlueData.{u}) [Nonempty D.J] :
    D.glued.size ≤ max #D.J (⨆ i : D.J, (D.U i).size) := by
  convert Scheme.size_le_of_iSup_eq_top
    (fun i => (D.ι i).opensRange) D.openCover.iSup_opensRange using 1
  congr 2
  funext i
  simpa only [Scheme.Hom.image_top_eq_opensRange] using
    Scheme.size_congr ((D.U i).topIso.symm ≪≫ (D.ι i).isoImage ⊤)

namespace Space

/-- An object of the big fppf site over `S` has fewer points than the cutoff of the site:
the cutoff is a strong limit cardinal and the object's size is below it. -/
theorem mk_points_lt_cutoff (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS) :
    #((BigFppfOver.toScheme B S hS).obj T) < B.cutoff :=
  (mk_scheme_le_two_power_size ((BigFppfOver.toScheme B S hS).obj T)).trans_lt
    (B.cutoff_isStrongPrelimit T.left.property)

end Space

end AlgebraicGeometry

end
