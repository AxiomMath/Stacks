module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekGeometricStalkPBCSets
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekGeometricStalkSurjective

/-!
# The stalks of `f_!` are the compactly supported sections of the geometric fibres

Let `f : X ⟶ Y` be a morphism of a big étale site which is separated and locally of finite type,
`F` an abelian sheaf on the small étale site of `X` and `ȳ : Spec k ⟶ Y` a geometric point. Then
pulling sections back to the geometric fibre `X_ȳ` is an isomorphism

`(f_!F)_ȳ ≅ H⁰_c(X_ȳ, F|_{X_ȳ})`

([Stacks, Tag 0F76](https://stacks.math.columbia.edu/tag/0F76)).

The map is `AlgebraicGeometry.SmallEtale.fShriekStalkToCompactSections`. It is injective by
`AlgebraicGeometry.SmallEtale.fShriekStalkToCompactSections_injective`. Surjectivity reduces, by
a compactification (Stacks 0F41), to proper base change in degree `0`
(`AlgebraicGeometry.SmallEtale.fShriekStalkToCompactSections_surjective_of_properBaseChange`).
Proper base change in degree `0` is
`AlgebraicGeometry.SmallEtale.exists_geometricFibreRestriction_eq_of_isProper`.

## Main results

* `AlgebraicGeometry.SmallEtale.bijective_fShriekStalkToCompactSections`: the map of Stacks 0F76
  is bijective.
* `AlgebraicGeometry.SmallEtale.fShriekStalkEquivCompactSections`: the isomorphism of Stacks 0F76.
* `AlgebraicGeometry.SmallEtale.fShriekStalkEquivCompactSections_apply_germ`: on the germ of a
  section over an étale neighbourhood `(V, v̄)`, it is the pullback of that section along any
  morphism `X_ȳ ⟶ X_V` over `X` and `V`, which is unique.

## Implementation notes

The small étale sites are those of the big étale site `B` (Stacks 021B). So the spectrum of the
geometric point must lie in `B`, which is the hypothesis `hy : B.Contains y.source`. Without it
`X_ȳ` is not an object of `B`, and `H⁰_c(X_ȳ, -)` is not defined on its small étale site. It is
only a bound on the size of `k`. The étale neighbourhoods of `ȳ`, and hence `(f_!F)_ȳ`, depend
only on the separable closure of `κ(y)` inside `k` (Stacks 03PO). Every geometric point is
therefore equivalent, for the left-hand side, to one through the spectrum of an algebraic
closure of `κ(y)`. That field is small compared with the cutoff of `B`, which is an uncountable
strong limit cardinal above the size of `Y`, so its spectrum lies in `B`. This remark is not
formalized here.

## References

* [Stacks Project, Tag 0F76](https://stacks.math.columbia.edu/tag/0F76)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [IsSeparated (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
  (y : GeometricPoint Y.obj) (hy : B.Contains y.source)

/-- **The map of Stacks 0F76 is bijective.** It is injective by
`AlgebraicGeometry.SmallEtale.fShriekStalkToCompactSections_injective`, and surjective by the
reduction to a compactification
`AlgebraicGeometry.SmallEtale.fShriekStalkToCompactSections_surjective_of_properBaseChange`
together with proper base change in degree `0`,
`AlgebraicGeometry.SmallEtale.exists_geometricFibreRestriction_eq_of_isProper`. -/
theorem bijective_fShriekStalkToCompactSections :
    Function.Bijective (fShriekStalkToCompactSections B f y hy F) :=
  ⟨fShriekStalkToCompactSections_injective B f y hy F,
    fShriekStalkToCompactSections_surjective_of_properBaseChange B f y hy F
      fun f' _ y' hy' F' t => exists_geometricFibreRestriction_eq_of_isProper B f' y' hy' F' t⟩

/-- **Stacks 0F76.** Let `f : X ⟶ Y` be separated and locally of finite type, `F` an abelian
sheaf on `X_étale` and `ȳ : Spec k ⟶ Y` a geometric point. There is a canonical isomorphism
`(f_!F)_ȳ ≅ H⁰_c(X_ȳ, F|_{X_ȳ})` between the stalk at `ȳ` of the direct image with compact
support (Stacks 0F4X) and the compactly supported sections (Stacks 0F72) of the inverse image of
`F` on the geometric fibre `X_ȳ = X ×_Y Spec k` over `k`. It sends the germ of a section over an
étale neighbourhood `(V, v̄)` to its pullback along `X_ȳ ⟶ X_V`
(`AlgebraicGeometry.SmallEtale.fShriekStalkEquivCompactSections_apply_germ`). -/
@[stacks 0F76]
def fShriekStalkEquivCompactSections :
    ↥(etaleStalk B Y.obj Y.property y (fShriekSubsheaf B f F).val.obj.left.obj) ≃+
      geometricFibreCompactSections B f y hy F :=
  AddEquiv.ofBijective (fShriekStalkToCompactSections B f y hy F)
    (bijective_fShriekStalkToCompactSections B f F y hy)

/-- The isomorphism of Stacks 0F76 is the map
`AlgebraicGeometry.SmallEtale.fShriekStalkToCompactSections`. -/
@[simp]
theorem fShriekStalkEquivCompactSections_apply
    (g : ↥(etaleStalk B Y.obj Y.property y (fShriekSubsheaf B f F).val.obj.left.obj)) :
    fShriekStalkEquivCompactSections B f F y hy g = fShriekStalkToCompactSections B f y hy F g :=
  rfl

/-- **Stacks 0F76, the isomorphism on germs.** Let `(V, v̄)` be an étale neighbourhood of `ȳ`
and `s` a section of `f_!F` over `V`, that is a section of `F` over `X_V` with support proper over
`V`. Let `h : X_ȳ ⟶ X_ȳ ×_X X_V` be a morphism over `X_ȳ` whose composite to `V` is
`X_ȳ ⟶ Spec k ⟶ V`. Then the isomorphism sends the germ of `s` at `ȳ` to the pullback of `s`
along `h`. Such an `h` exists and is unique, `AlgebraicGeometry.SmallEtale.geometricFibreLift`;
this is the canonical map `c_ȳ` of the source. -/
@[stacks 0F76 "the isomorphism pulls a section on an étale neighbourhood back to the fibre"]
theorem fShriekStalkEquivCompactSections_apply_germ
    (N : (geometricPointFiber B Y.obj Y.property y).Elements)
    (s : (fShriekSubsheaf B f F).val.obj.left.obj.obj (op N.1))
    (h : final B (geometricFibreObj B f y hy).obj (geometricFibreObj B f y hy).property ⟶
      (smallEtaleBaseChange B (geometricFibreProj B f y hy)).obj
        ((smallEtaleBaseChange B f).obj N.1))
    (hh : (h.hom.left ≫ baseChangeObjProjection B (geometricFibreProj B f y hy)
        ((smallEtaleBaseChange B f).obj N.1)) ≫ pullback.fst N.1.obj.hom f =
      geometricFibreStruct B f y hy ≫ neighborhoodPointHom B y hy N) :
    (fShriekStalkEquivCompactSections B f F y hy
        (etaleGerm B Y.obj Y.property y _ N.1 N.2 s) : geometricFibreSections B f y hy F) =
      pullbackSectionAlongHom B (geometricFibreProj B f y hy) AddCommGrpCat.{max (u + 1) v} F
        ((smallEtaleBaseChange B f).obj N.1) _ h
        ((fShriekSubsheaf B f F).val.arrow.hom.app (op N.1) s) := by
  have hlift : h = geometricFibreLift B f y hy N := by
    apply baseChangeObj_hom_ext
    rw [geometricFibreLift_proj]
    apply pullback.hom_ext
    · exact hh.trans (geometricFibreToNeighborhood_fst B f y hy N).symm
    · refine Eq.trans ?_ (geometricFibreToNeighborhood_snd B f y hy N).symm
      exact (Category.assoc _ _ _).trans ((congrArg (h.hom.left ≫ ·)
        (isPullback_baseChangeObjProjection B (geometricFibreProj B f y hy)
          ((smallEtaleBaseChange B f).obj N.1)).w).trans ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ geometricFibreProj B f y hy) (Over.w h.hom)).trans
              (Category.id_comp _))))
  subst hlift
  exact fShriekStalkToCompactSections_germ B f y hy F N s

end AlgebraicGeometry.SmallEtale
