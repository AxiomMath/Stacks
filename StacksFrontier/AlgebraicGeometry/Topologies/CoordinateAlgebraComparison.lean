module

public import StacksFrontier.AlgebraicGeometry.Descent.Module.CechAmitsurComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.AffineSliceAlgebraAdjunction
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleBaseChangeNaturality

/-!
# The two coordinate-algebra functors on the slice at an affine object agree

Let `S` be a scheme and `U` an object of `Over S` with `U.left` affine, and put
`R = Γ(U.left, 𝒪)`. There are two functors `(Over U)ᵒᵖ ⥤ CommAlgCat (ULift R)` sending an object
over `U` to its coordinate ring, as an algebra over the lifted coordinate ring of `U`:

* `Stacks.Sites.gammaAlg`, which goes through `CategoryTheory.Under.opEquivOpOver` and
  `CategoryTheory.commAlgCatEquivUnder`, and whose structure map is `AlgebraicGeometry.Scheme.Γ`
  applied to the structure morphism;
* `AlgebraicGeometry.overAffineAlgΓ`, the left adjoint of `AlgebraicGeometry.overAffineAlgSpec`,
  which goes through `AlgebraicGeometry.algΓ` and `CategoryTheory.Over.iteratedSliceEquiv`.

Their underlying types are both `Γ(Z, 𝒪)`, but their algebra structures are not definitionally
equal: the structure map of `gammaAlg` is `Γ(Z.hom)` precomposed with the universe-lift
isomorphism, while that of `overAffineAlgΓ` is `Γ` of `Z.hom` followed by the identification of
`U.left` with `Spec (ULift R)`, precomposed with `AlgebraicGeometry.Scheme.ΓSpecIso`. The two
differ by one coherence of the `Γ ⊣ Spec` adjunction.

## Main definitions

* `AlgebraicGeometry.overAffineUnder`: the `CategoryTheory.Under`-valued functor through which
  `AlgebraicGeometry.overAffineAlgΓ` factors.
* `AlgebraicGeometry.gammaUnderIsoOverAffineUnder` and
  `AlgebraicGeometry.gammaAlgIsoOverAffineAlgΓ`: the identification of the two functors, first at
  the level of rings under the lifted coordinate ring and then at the level of algebras.
* `AlgebraicGeometry.powerSectionsAmitsurCoefficientsIso`: the identification whiskered with the
  power sections of an object over `U` and the Amitsur coefficients of a module.

## Main results

* `AlgebraicGeometry.ΓSpecIso_inv_comp_Γ_map_specOverAffineBaseRingIso_inv`: the composite
  `ULift Γ(U.left, 𝒪) ⟶ Γ(Spec (ULift Γ(U.left, 𝒪)), 𝒪) ⟶ Γ(U.left, 𝒪)` along
  `AlgebraicGeometry.specOverAffineBaseRingIso` is the universe-lift isomorphism.
* `AlgebraicGeometry.gammaUnder_hom_eq`: the two structure maps agree at every object.

## References

* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 01I1](https://stacks.math.columbia.edu/tag/01I1)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Sites

universe u m

namespace AlgebraicGeometry

variable {S : Scheme.{u}} (U : Over S) [IsAffine U.left]

/-- **The `Γ ⊣ Spec` coherence.** The composite
`ULift Γ(U.left, 𝒪) ⟶ Γ(Spec (ULift Γ(U.left, 𝒪)), 𝒪) ⟶ Γ(U.left, 𝒪)`, the second map being
`Γ` of `AlgebraicGeometry.specOverAffineBaseRingIso`, is the universe-lift isomorphism. -/
public theorem ΓSpecIso_inv_comp_Γ_map_specOverAffineBaseRingIso_inv :
    (Scheme.ΓSpecIso (overAffineBaseRing U)).inv ≫
        Scheme.Γ.map (specOverAffineBaseRingIso U).inv.op =
      uliftHom Γ(U.left, ⊤) := by
  simp [specOverAffineBaseRingIso, Scheme.isoSpec, uliftHom, uliftCommRingCatIso]

/-- The slice at `U` of all schemes over `S`, with its coordinate rings read as rings under the
universe-lifted coordinate ring of `U.left` through `AlgebraicGeometry.overAffineAlgΓ`. -/
public abbrev overAffineUnder : (Over U)ᵒᵖ ⥤ Under (overAffineBaseRing U) :=
  ((Over.iteratedSliceEquiv U).functor ⋙
    (Over.mapIso (specOverAffineBaseRingIso U)).inverse ⋙
      Over.post Scheme.Γ.rightOp ⋙
        Over.map (Scheme.ΓSpecIso (overAffineBaseRing U)).inv.op ⋙
          (Over.opEquivOpUnder (overAffineBaseRing U)).functor).leftOp

/-- The two routes to the structure map of the coordinate ring of an object over `U` agree. -/
public theorem gammaUnder_hom_eq (Z : (Over U)ᵒᵖ) :
    ((gammaUnder S (𝟭 (Over S)) U ⋙ Under.map (uliftHom Γ(U.left, ⊤))).obj Z).hom =
      ((overAffineUnder U).obj Z).hom := by
  change uliftHom Γ(U.left, ⊤) ≫ Scheme.Hom.appTop (Z.unop.hom.left) =
    (Scheme.ΓSpecIso (overAffineBaseRing U)).inv ≫
      Scheme.Hom.appTop (Z.unop.hom.left ≫ (specOverAffineBaseRingIso U).inv)
  rw [← Scheme.Γ_map_op (Over.Hom.left (unop Z).hom),
    ← Scheme.Γ_map_op (Over.Hom.left (unop Z).hom ≫ (specOverAffineBaseRingIso U).inv),
    op_comp, Scheme.Γ.map_comp]
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ Scheme.Γ.map (Over.Hom.left (unop Z).hom).op)
      (ΓSpecIso_inv_comp_Γ_map_specOverAffineBaseRingIso_inv U))).symm

/-- The two routes agree as functors into rings under the lifted coordinate ring. -/
public def gammaUnderIsoOverAffineUnder :
    gammaUnder S (𝟭 (Over S)) U ⋙ Under.map (uliftHom Γ(U.left, ⊤)) ≅ overAffineUnder U :=
  NatIso.ofComponents
    (fun Z => Under.isoMk (Iso.refl _) ((Category.comp_id _).trans (gammaUnder_hom_eq U Z)))
    (by intro X Y f; ext; rfl)

/-- **The two coordinate-algebra functors agree.** `Stacks.Sites.gammaAlg` is isomorphic to the
left adjoint `AlgebraicGeometry.overAffineAlgΓ` of `AlgebraicGeometry.overAffineAlgSpec`. -/
public def gammaAlgIsoOverAffineAlgΓ :
    gammaAlg S (𝟭 (Over S)) U ≅ (overAffineAlgΓ U).leftOp :=
  Functor.isoWhiskerRight (gammaUnderIsoOverAffineUnder U)
    (commAlgCatEquivUnder (overAffineBaseRing U)).inverse

/-- Whiskering `AlgebraicGeometry.gammaAlgIsoOverAffineAlgΓ`: the Amitsur coefficients of `M`
along the power sections of `Y` are the same whether the coordinate algebras are read through
`Stacks.Sites.gammaAlg` or through `AlgebraicGeometry.overAffineAlgΓ`. -/
public def powerSectionsAmitsurCoefficientsIso (Y : Over U) (M : Type m) [AddCommGroup M]
    [Module (Γ(U.left, ⊤) : Type u) M] :
    Stacks.CechSite.powerSections Y (gammaAlg S (𝟭 (Over S)) U) ⋙
        Stacks.Descent.amitsurCoefficients.{u, u, m} (Γ(U.left, ⊤) : Type u) M ≅
      Stacks.CechSite.powerSections Y ((overAffineAlgΓ U).leftOp) ⋙
        Stacks.Descent.amitsurCoefficients.{u, u, m} (Γ(U.left, ⊤) : Type u) M :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (cechNerveTerminalFrom Y).rightOp (gammaAlgIsoOverAffineAlgΓ U))
    (Stacks.Descent.amitsurCoefficients.{u, u, m} (Γ(U.left, ⊤) : Type u) M)

end AlgebraicGeometry

end
