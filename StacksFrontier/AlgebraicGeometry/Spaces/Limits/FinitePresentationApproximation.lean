module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationApproximationSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelativeApproximationEnlargement
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineScheme

/-!
# Approximation of a morphism of algebraic spaces by morphisms of finite presentation

Stacks 09NS: let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` with `X`
quasi-compact and quasi-separated and `Y` quasi-separated. Then `X = lim Xᵢ` is a limit of a
directed inverse system of algebraic spaces `Xᵢ` of finite presentation over `Y` with affine
transition morphisms over `Y`.

The proof is the one of the Stacks project. The image of `X` lies in a quasi-compact open subspace
`V` of `Y` (all viewed over `Spec ℤ`), and `X ⟶ V` is the limit of morphisms of quasi-separated
algebraic spaces of finite type over `Spec ℤ` with affine transition morphisms (Stacks 0GS3);
base changing the stages back to `Y` concludes
(`AlgebraicGeometry.Space.exists_isLimit_finitePresentation_of_hasRelativeApproximation`).

Stacks 0GS3 rests on absolute Noetherian approximation (Stacks 07SU), whose construction takes
limits over index sets as large as an étale atlas, and such limits are computed in the big fppf
site only below the cofinality of its size cutoff. The relative approximation is therefore built
on an enlargement `B'` of the site `B` whose cutoff has cofinality above the cutoff of `B`, where
every algebraic space coming from `B` has a small atlas, and descended to `B` along the fully
faithful inverse image functor (Stacks 04W1): its stages are of finite type over `Spec ℤ`
(`AlgebraicGeometry.Space.hasRelativeApproximation_of_changeBigSite`).

## Main results

* `AlgebraicGeometry.Space.exists_isLimit_finitePresentation`: Stacks 09NS.

## References

* [Stacks Project, Tag 09NS](https://stacks.math.columbia.edu/tag/09NS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **Relative approximation over `Spec ℤ`, on any big fppf site.** A morphism `f : X ⟶ Y` of
quasi-compact quasi-separated algebraic spaces over `Spec ℤ` is the limit of a directed inverse
system of morphisms of quasi-separated algebraic spaces of finite type over `Spec ℤ` with affine
transition morphisms. It is built on an enlargement of the site on which `X` and `Y` have small
atlases, and descended. -/
@[stacks 0GS3]
theorem hasRelativeApproximation_of_isQuasiCompactSpace (B : BigFppfSite.{u})
    (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (hY : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ Y)
    (hXqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X)
    (hYqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ Y)
    (hXqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X)
    (hYqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ Y) :
    HasRelativeApproximation B hZ f := by
  classical
  obtain ⟨B', h, hcof⟩ := B.exists_isContained_lt_cof B.cutoff
  let hZ' := largerContains h hZ
  let cbs := changeBigSite B B' h (⊤_ Scheme.{u}) hZ
  let XA : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ := ⟨X, hX⟩
  let YA : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ := ⟨Y, hY⟩
  let fA : XA ⟶ YA := ObjectProperty.homMk f
  -- on the enlarged site, every algebraic space coming from `B` has a small atlas
  have hsmall : ∀ (Z : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ),
      IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ Z.obj →
      IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ Z.obj →
      HasSmallNoetherianApproximation B' (⊤_ Scheme.{u}) hZ' hZ' (cbs.obj Z).obj := by
    intro Z hqc hqs
    obtain ⟨U, -, q, -, -, hqs', hqe', -, -, -⟩ := exists_atlasKernelPair B (⊤_ Scheme.{u}) hZ Z
    obtain ⟨-, -, -, q', hq's, hq'e, -, -⟩ :=
      changeBigSite_atlas B B' h (⊤_ Scheme.{u}) hZ Z q hqs' hqe'
    exact hasSmallNoetherianApproximation_of_etaleAtlas (cbs.obj Z).property
      (changeBigSite_isQuasiCompactSpace B B' h (⊤_ Scheme.{u}) hZ Z hqc)
      (changeBigSite_isAbsolutelyQuasiSeparated B B' h (⊤_ Scheme.{u}) hZ Z hqc hqs) _ q' hq's
      ((isEtale_iff_presheaf_of_yoneda B' (⊤_ Scheme.{u}) hZ' q').mpr hq'e)
      (lt_trans U.left.property hcof)
  exact hasRelativeApproximation_of_changeBigSite B B' h hZ fA
    (hasRelativeApproximation_of_hasSmallNoetherianApproximation B' hZ' (cbs.map fA).hom
      (cbs.obj XA).property (hsmall XA hXqc hXqs) (hsmall YA hYqc hYqs))

/-- **Stacks 09NS.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, with `X`
quasi-compact and quasi-separated and `Y` quasi-separated. Then `X` is the limit of a directed
inverse system of algebraic spaces `Xᵢ` of finite presentation over `Y`, with affine transition
morphisms over `Y`: an inverse system `D` of algebraic spaces over `S` with morphisms
`tᵢ : Xᵢ ⟶ Y` of finite presentation compatible with the affine transition morphisms, and a
limit cone `X ⟶ Xᵢ` over `Y`. -/
@[stacks 09NS]
theorem exists_isLimit_finitePresentation (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXqc : IsQuasiCompactSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y) :
    ∃ (I : Type (u + 1)) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirectedOrder I)
      (D : Iᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
      (t : D ⟶ (Functor.const Iᵒᵖ).obj Y) (p : (Functor.const Iᵒᵖ).obj X ⟶ D)
      (_ : IsLimit (Cone.mk X p)),
      (p ≫ t = (Functor.const Iᵒᵖ).map f) ∧
        (∀ i, IsAlgebraicSpace B S hS (D.obj i)) ∧
        (∀ i, IsFinitePresentation B S hS (t.app i)) ∧
        (∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom B S hS (D.map g)) := by
  classical
  let k : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  let L := OverShriek.relocalizePresheafFunctor k
  have hXZ := isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ k X hX
  have hYZ := isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ k Y hY
  have hXZqc := isQuasiCompactSpace_relocalize B S hS hZ k hXqc
  have hXZqs := isAbsolutelyQuasiSeparated_viewOverIntegers B S hS hZ X hXqs
  have hYZqs := isAbsolutelyQuasiSeparated_viewOverIntegers B S hS hZ Y hYqs
  obtain ⟨V, hV, ⟨fV, hfV⟩, hVqc⟩ :=
    exists_quasiCompact_openSubspace_factor B (⊤_ Scheme.{u}) hZ hXZ hYZ hXZqc (L.map f)
  have hVqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ V.toFunctor :=
    isAbsolutelyQuasiSeparated_of_mono _ _ _ _ hV.1 V.ι inferInstance hYZqs
  exact exists_isLimit_finitePresentation_of_hasRelativeApproximation B S hS f hX hY hYqs V hV
    hVqc fV hfV (hasRelativeApproximation_of_isQuasiCompactSpace B hZ fV hXZ hV.1 hXZqc hVqc
      hXZqs hVqs)

end AlgebraicGeometry.Space

end
