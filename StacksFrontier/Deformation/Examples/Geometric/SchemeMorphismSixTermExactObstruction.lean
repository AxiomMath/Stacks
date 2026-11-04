module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionArrow
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionNatural
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismEndpointsSupplied

/-!
# The obstruction arrow of Stacks 0E3V as a `k`-linear map, from its two halves

The obstruction to deforming `f : X → Y` along a pair `(X_ε, Y_ε)` of first-order deformations of
its endpoints is a difference `ob(X_ε, Y_ε) = Push(Y_ε) − Pull(X_ε)` of two classes in
`Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X ⊗_k M)`, the first depending only on `Y_ε` and the second only on
`X_ε`, and it vanishes exactly when `f` lifts to `X_ε → Y_ε`. This file assembles, from any two
such classes that are invariant under isomorphism and natural in the coefficient module, the
`k`-linear sixth arrow `T(Def_X × Def_Y) → Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X)` of the source's sequence
and its exactness at `T(Def_X × Def_Y)`.

## Main definitions

* `Deformation.Examples.schemeMorphismObstructionLinearMapOfClassesAt`: the `k`-linear map
  `T Def_X(M) × T Def_Y(M) → Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X ⊗_k M)`, `(s, t) ↦ Push(t) − Pull(s)`.
* `Deformation.Examples.schemeMorphismObstructionLinearMapOfClasses`: the same at the rank-one
  coordinate module, untwisted to the source's sixth term.

## Main results

* `Deformation.Examples.exact_schemeMorphismTangentPair'_obstructionLinearMapOfClasses`:
  exactness at `T(Def_X × Def_Y)`.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

section OfClasses

variable
  (pull : ∀ M : FGModuleCat.{u} k,
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M) →
      (schemeMorphismObstructionExtFunctor f pY).obj M)
  (pullInv : ∀ M x x', IsIsomorphic x x' → pull M x = pull M x')
  (pullNat : ∀ {M N : FGModuleCat.{u} k} (g : M ⟶ N) x y (a : x.1 ⟶ y.1),
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).IsHomLift
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g) a →
      pull N y = (schemeMorphismObstructionExtFunctor f pY).map g (pull M x))
  (push : ∀ M : FGModuleCat.{u} k,
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M) →
      (schemeMorphismObstructionExtFunctor f pY).obj M)
  (pushInv : ∀ M y y', IsIsomorphic y y' → push M y = push M y')
  (pushNat : ∀ {M N : FGModuleCat.{u} k} (g : M ⟶ N) x y (a : x.1 ⟶ y.1),
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).IsHomLift
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g) a →
      push N y = (schemeMorphismObstructionExtFunctor f pY).map g (push M x))

/-- **The obstruction arrow at the coordinate module `M`**, `(s, t) ↦ Push(t) − Pull(s)`, from
the two classes descended to the tangent modules. -/
def schemeMorphismObstructionLinearMapOfClassesAt (M : FGModuleCat.{u} k) :
    ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
        (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk
            pX)) M) ×
      ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
        (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk
            pY)) M) →ₗ[k]
      (schemeMorphismObstructionExtFunctor f pY).obj M :=
  (tangentModuleDescendLinearMap (BasedCategory.ofFunctor
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
      (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))
      (schemeMorphismObstructionExtFunctor f pY) push pushInv pushNat M).comp
      (LinearMap.snd k _ _) -
    (tangentModuleDescendLinearMap (BasedCategory.ofFunctor
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
      (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))
      (schemeMorphismObstructionExtFunctor f pY) pull pullInv pullNat M).comp
      (LinearMap.fst k _ _)

/-- On the tangent classes of deformations `xε` of `X` and `yε` of `Y` over `k[M]`, the
obstruction arrow takes the value `Push(yε) − Pull(xε)`. -/
theorem schemeMorphismObstructionLinearMapOfClassesAt_tangentClassAt (M : FGModuleCat.{u} k)
    (xε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))
    (yε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)) :
    schemeMorphismObstructionLinearMapOfClassesAt f pX pY pull pullInv pullNat push pushInv
        pushNat M
        (tangentClassAt.{u, u, u} _ (isDeformationCategory_schemeDeformationCategoryProjection
          (Over.mk pX)) M xε,
        tangentClassAt.{u, u, u} _ (isDeformationCategory_schemeDeformationCategoryProjection
          (Over.mk pY)) M yε) = push M yε - pull M xε := by
  simp only [schemeMorphismObstructionLinearMapOfClassesAt, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.snd_apply, LinearMap.fst_apply]
  exact congrArg₂ (· - ·)
    (tangentModuleDescend_tangentClassAt (BasedCategory.ofFunctor
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
      (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))
      (schemeMorphismObstructionExtFunctor f pY) push pushInv M yε)
    (tangentModuleDescend_tangentClassAt (BasedCategory.ofFunctor
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
      (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))
      (schemeMorphismObstructionExtFunctor f pY) pull pullInv M xε)

/-- **The sixth arrow of Tag 0E3V, from the two classes**: the obstruction arrow at the rank-one
coordinate module, untwisted to the source's sixth term `Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X)` along
`Deformation.Examples.schemeMorphismObstructionExtRankOneEquiv`. -/
def schemeMorphismObstructionLinearMapOfClasses :
    letI := schemeMorphismObstructionExtModule f pY
    ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
        (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))
        (FGModuleCat.of k (ULift.{u} k))) ×
      ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
        (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))
        (FGModuleCat.of k (ULift.{u} k))) →ₗ[k]
      schemeMorphismObstructionExt f pY :=
  letI := schemeMorphismObstructionExtModule f pY
  letI := schemeMorphismObstructionExtTwistedModule f pY (FGModuleCat.of k (ULift.{u} k))
  (schemeMorphismObstructionExtRankOneEquiv f pY).toLinearMap ∘ₗ
    schemeMorphismObstructionLinearMapOfClassesAt f pX pY pull pullInv pullNat push pushInv pushNat
      (FGModuleCat.of k (ULift.{u} k))

/-- **Stacks 0E3V, exactness at `T(Def_X × Def_Y)`, from the two classes.** If the two classes
agree exactly when `f` lifts between the two first-order deformations, then the kernel of the
sixth arrow is the image of `T Def_{X → Y} → T(Def_X × Def_Y)`. -/
theorem exact_schemeMorphismTangentPair'_obstructionLinearMapOfClasses
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    (hkey : ∀ (xε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).Fiber
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj (FGModuleCat.of k (ULift.{u} k))))
      (yε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj (FGModuleCat.of k (ULift.{u} k)))),
      push _ yε = pull _ xε ↔
        Nonempty (globalLiftsOverBase f xε.1 yε.1 (eqToHom (yε.2.trans xε.2.symm)))) :
    letI := schemeMorphismObstructionExtModule f pY
    Function.Exact (schemeMorphismTangentPair' f pX pY hf hM (FGModuleCat.of k (ULift.{u} k)))
      (schemeMorphismObstructionLinearMapOfClasses f pX pY pull pullInv pullNat push pushInv
        pushNat) := by
  let := schemeMorphismObstructionExtModule f pY
  let := schemeMorphismObstructionExtTwistedModule f pY (FGModuleCat.of k (ULift.{u} k))
  rintro ⟨s, t⟩
  obtain ⟨xε, rfl⟩ := tangentClassAt_surjective.{u, u, u} _
    (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)) _ s
  obtain ⟨yε, rfl⟩ := tangentClassAt_surjective.{u, u, u} _
    (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)) _ t
  have hval : schemeMorphismObstructionLinearMapOfClasses f pX pY pull pullInv pullNat push pushInv
      pushNat (tangentClassAt.{u, u, u} _
        (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))
        _ xε, tangentClassAt.{u, u, u} _
        (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))
        _ yε) = schemeMorphismObstructionExtRankOneEquiv f pY (push _ yε - pull _ xε) :=
    congrArg (schemeMorphismObstructionExtRankOneEquiv f pY)
      (schemeMorphismObstructionLinearMapOfClassesAt_tangentClassAt f pX pY pull pullInv pullNat
        push pushInv pushNat _ xε yε)
  rw [hval]
  exact (LinearEquiv.map_eq_zero_iff _).trans (sub_eq_zero.trans ((hkey xε yε).trans
    ((nonempty_globalLiftsOverBase_iff_exists_schemeMorphismDeformation f pX pY hf hM
      (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))
      xε yε).trans (exists_schemeMorphismTangentPair'_eq_iff f pX pY hf hM _ xε yε).symm)))

end OfClasses

end Deformation.Examples
