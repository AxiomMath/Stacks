module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.BaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.PrincipalCenter
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The ideal of a closed-immersion modification is annihilated by a power of the centre

Let `X` be an affine scheme, let `t` be a global function on it cutting out the centre of an
almost blowup square, and suppose the modification of the square is a closed immersion.  Then the
ideal of global functions cutting out the modification is annihilated by a single power of `t`.

This is the converse of the construction of Stacks 0EVG,
`AlgebraicGeometry.isAlmostBlowUpSquare_quotient_of_pow_mul_eq_zero`, which produces an almost
blowup square from a finitely generated ideal annihilated by a power of `t`.  Together the two
say that over an affine base the almost blowup squares with a closed-immersion modification and
a principal centre are exactly the squares of Example 0EVG, which is what lets the condition on
those squares in the h sheaf criterion Stacks 0EVI be applied to an arbitrary such square.

## Main results

* `AlgebraicGeometry.exists_pow_mul_eq_zero_of_fg_of_le_ker_away`: a finitely generated ideal
  inside the kernel of a localization away from `t` is annihilated by one power of `t`.
* `AlgebraicGeometry.exists_pow_mul_eq_zero_of_restrict_isIso`: the ideal of a closed immersion
  of finite presentation over an affine base which is an isomorphism away from the centre is
  annihilated by a power of a generator of the centre.
* `AlgebraicGeometry.exists_pow_mul_eq_zero_of_isAlmostBlowUpSquare`: the same for the
  modification of an almost blowup square.

## Implementation notes

The modification of an almost blowup square is an isomorphism over the complement of the centre,
which is Stacks 0EV6, `AlgebraicGeometry.isIso_restrict_compl_support`.  Its kernel therefore
has vanishing inverse image on that complement, so it is contained in the ideal of sections
supported on the centre by Stacks 0EV8,
`AlgebraicGeometry.isIso_restrict_iff_le_supportedSectionsIdeal`.  Over an affine base with
principal centre that ideal of supported sections is the kernel of the localization away from the
generator, by `AlgebraicGeometry.supportedSectionsIdeal_ideal_top_eq_ker`, so every function
killed by the modification is annihilated by some power of the generator; the modification is of
finite presentation, so its ideal is finitely generated and one power does for all of it.

## References

* [Stacks Project, Tag 0EVG](https://stacks.math.columbia.edu/tag/0EVG)
* [Stacks Project, Tag 0EV6](https://stacks.math.columbia.edu/tag/0EV6)
* [Stacks Project, Tag 0EV8](https://stacks.math.columbia.edu/tag/0EV8)
* [Stacks Project, Tag 0EVI](https://stacks.math.columbia.edu/tag/0EVI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- A finitely generated ideal contained in the kernel of a localization away from `t` is
annihilated by a single power of `t`: each of its finitely many generators is, and the largest of
the exponents works for every element. -/
public theorem exists_pow_mul_eq_zero_of_fg_of_le_ker_away {A : Type*} [CommRing A] (t : A)
    (L : Type*) [CommRing L] [Algebra A L] [IsLocalization.Away t L]
    (J : Ideal A) (hJ : J.FG) (hle : J ≤ RingHom.ker (algebraMap A L)) :
    ∃ n : ℕ, ∀ x ∈ J, t ^ n * x = 0 := by
  classical
  obtain ⟨S, hS⟩ := hJ
  have hpow : ∀ s ∈ S, ∃ n : ℕ, t ^ n * s = 0 := by
    intro s hs
    have hsJ : s ∈ J := by
      rw [← hS]
      exact Ideal.subset_span hs
    exact (IsLocalization.Away.algebraMap_eq_zero_iff (S := L) t s).1
      (RingHom.mem_ker.mp (hle hsJ))
  choose! n hn using hpow
  refine ⟨S.sup n, fun x hx => ?_⟩
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := n) hs)
    rw [hk, pow_add, mul_comm (t ^ n s) (t ^ k), mul_assoc, hn s hs, mul_zero]
  | zero => exact mul_zero _
  | add a b _ _ ha hb => rw [mul_add, ha, hb, add_zero]
  | smul c a _ ha =>
    have hca : t ^ S.sup n * (c • a) = c * (t ^ S.sup n * a) := by
      rw [smul_eq_mul]; ring
    rw [hca, ha, mul_zero]

/-- The ideal of global sections of the kernel ideal sheaf of a morphism into an affine scheme
is the kernel of the map on global sections. -/
private theorem ker_ideal_top_eq_ker_appTop {X X' : Scheme.{u}} [IsAffine X] (b : X' ⟶ X)
    [IsClosedImmersion b] :
    b.ker.ideal ⟨⊤, isAffineOpen_top X⟩ = RingHom.ker (b.appTop).hom := by
  rw [Scheme.ker_of_isAffine b]
  exact (Scheme.IdealSheafData.equivOfIsAffine (X := X)).apply_symm_apply _

/-- **The ideal of a closed immersion of finite presentation into an affine scheme is finitely
generated.** The closed immersion is its own scheme-theoretic image up to an isomorphism, so the
inclusion of that image is of finite presentation, and over an affine base finite presentation of
a closed immersion is finite generation of its ideal of global sections. -/
@[sga "3 XI 6.4" "special case"]
public theorem fg_ker_appTop_of_finitePresentation {X X' : Scheme.{u}} [IsAffine X]
    (b : X' ⟶ X) [IsClosedImmersion b] (hb : FinitePresentation b) :
    (RingHom.ker (b.appTop).hom).FG := by
  have hker := ker_ideal_top_eq_ker_appTop b
  have hfp : FinitePresentation b.ker.subschemeι := by
    have he : inv b.toImage ≫ b = b.ker.subschemeι :=
      (IsIso.inv_comp_eq b.toImage).2 (Scheme.Hom.toImage_imageι b).symm
    rw [← he]
    refine FinitePresentation.mk ?_ ?_ ?_
    · have : LocallyOfFinitePresentation b := hb.locallyOfFinitePresentation
      infer_instance
    · have : QuasiCompact b := hb.quasiCompact
      infer_instance
    · have : QuasiSeparated b := hb.quasiSeparated
      infer_instance
  rw [← hker]
  exact (Stacks.Flatness.finitePresentation_subschemeι_iff b.ker).1 hfp _

/-- **The ideal of a closed immersion which is an isomorphism away from a principal centre is
annihilated by a power of the generator.**  Let `X` be an affine scheme, let `b : X' ⟶ X` be a
closed immersion of finite presentation which is an isomorphism over the complement of the
support of `I`, and let `t` be a global function generating `I`.  Then a single power of `t`
annihilates the ideal of global functions cutting out `X'`.

Only two of the five requirements on an almost blowup square are used, and this is the form in
which the statement is applied where the square is not yet known to be one. -/
public theorem exists_pow_mul_eq_zero_of_restrict_isIso {X X' : Scheme.{u}} [IsAffine X]
    (I : X.IdealSheafData) (b : X' ⟶ X) [IsClosedImmersion b] (hfp : FinitePresentation b)
    (hiso : IsIso (b ∣_ (⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩ : X.Opens)))
    (t : Γ(X, ⊤)) (ht : I.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {t}) :
    ∃ n : ℕ, ∀ x ∈ RingHom.ker (b.appTop).hom, t ^ n * x = 0 := by
  -- the ideal of the modification, as an ideal of the global functions of the base
  have hker := ker_ideal_top_eq_ker_appTop b
  -- it is finitely generated, because the modification is of finite presentation
  have hfg : (RingHom.ker (b.appTop).hom).FG :=
    fg_ker_appTop_of_finitePresentation b hfp
  -- the modification is an isomorphism away from the centre, so its ideal is supported there
  have hle : b.ker ≤ supportedSectionsIdeal (I.support : Set X) := by
    refine (isIso_restrict_iff_le_supportedSectionsIdeal (I.support : Set X)
      I.support.isClosed b.ker).1 ?_
    refine (restrict_isIso_iff_comap_bot b.ker _).2 ?_
    rw [← ker_morphismRestrict_eq_comap b]
    have := hiso
    exact Scheme.Hom.ker_eq_bot_of_isIso _
  -- over an affine base with principal centre that ideal is the kernel of a localization
  have hle' : RingHom.ker (b.appTop).hom ≤
      RingHom.ker (algebraMap Γ(X, ⊤) (Localization.Away t)) := by
    have h1 := hle ⟨⊤, isAffineOpen_top X⟩
    rwa [hker, supportedSectionsIdeal_ideal_top_eq_ker I t ht] at h1
  exact exists_pow_mul_eq_zero_of_fg_of_le_ker_away t (Localization.Away t) _ hfg hle'

/-- **The ideal of a closed-immersion modification is annihilated by a power of the centre.**
Let `X` be an affine scheme, let `b : X' ⟶ X` be a closed immersion which is the modification of
an almost blowup square with centre `I`, and let `t` be a global function generating `I`.  Then a
single power of `t` annihilates the ideal of global functions cutting out `X'`.

This is the converse of Stacks 0EVG: it says that such a square is one of the squares of
Example 0EVG.  Of the five requirements on an almost blowup square only finite presentation of
the modification and its being an isomorphism away from the centre are used, which is
`AlgebraicGeometry.exists_pow_mul_eq_zero_of_restrict_isIso`. -/
public theorem exists_pow_mul_eq_zero_of_isAlmostBlowUpSquare {X X' : Scheme.{u}} [IsAffine X]
    (I : X.IdealSheafData) (b : X' ⟶ X) [IsClosedImmersion b]
    (h : IsAlmostBlowUpSquare I b) (t : Γ(X, ⊤))
    (ht : I.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {t}) :
    ∃ n : ℕ, ∀ x ∈ RingHom.ker (b.appTop).hom, t ^ n * x = 0 :=
  exists_pow_mul_eq_zero_of_restrict_isIso I b h.finitePresentation
    (isIso_restrict_compl_support I b h) t ht

end AlgebraicGeometry

end
