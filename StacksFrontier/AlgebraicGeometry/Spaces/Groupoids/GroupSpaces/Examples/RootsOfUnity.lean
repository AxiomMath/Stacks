module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.GeneralLinear
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.RootsOfUnity
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Roots of unity as a group algebraic space

Let `B` be an algebraic space over a scheme `S` and let `n` be a positive natural number.  The
functor sending a scheme `T` over `B` to the subgroup of `Γ(T, 𝒪_T^*)` consisting of the `n`-th
roots of unity is represented by the group algebraic space `μₙ,B = B ×_S μₙ,S`, the base change
to `B` of the group scheme of `n`-th roots of unity over `S`.

## Main definitions

* `AlgebraicGeometry.rootsOfUnityGroupOverFunctor` is the group-valued functor of `n`-th roots
  of unity in global sections, on schemes over `S`.
* `AlgebraicGeometry.Space.rootsOfUnitySiteObject` is the group scheme `μₙ,S`, read as an object
  of the big fppf site over `S`.
* `AlgebraicGeometry.Space.rootsOfUnitySpace`: **Stacks 043K**, the group algebraic space of
  `n`-th roots of unity over `B`.
* `AlgebraicGeometry.Space.rootsOfUnitySpacePoints`: **Stacks 043K**, its group of points over a
  scheme over `B`, identified with the group of `n`-th roots of unity in global sections.

## Main results

* `AlgebraicGeometry.rootsOfUnityBaseChangeGroupPointsIso`: **Stacks 040M**, the group-valued
  functor of points of `μₙ,S` is the functor of `n`-th roots of unity in global sections.
* `AlgebraicGeometry.Space.rootsOfUnitySpace_obj_X` identifies the underlying algebraic space
  with the fibre product of `B` and the functor of points of `μₙ,S`.
* `AlgebraicGeometry.Space.rootsOfUnitySpacePoints_apply` and
  `AlgebraicGeometry.Space.rootsOfUnitySpacePoints_naturality` pin the identification on points
  down, naturally in the test scheme.

## Implementation notes

The order `n` is positive, as in the source: the construction of `μₙ` as a group scheme in
**Stacks 040M** needs a unit of order dividing `n`, and gives no group scheme `μ₀`.  The
hypothesis is carried as `Fact (0 < n)`, which is how `AlgebraicGeometry.rootsOfUnityGrpObj`
states it.

The base `B` is an arbitrary algebraic space over `S`; it is not assumed to be a scheme.  The
group-valued functor of points of `μₙ,S` is obtained from that of `μₙ` over the integers by
`CategoryTheory.Over.pullbackPointsMulEquiv`, which identifies points of a pullback group object
with points of the original one compatibly with the group law, so the comparison with roots of
unity in global sections is a `MulEquiv` and not a mere bijection; it is the group-valued
refinement of **Stacks 040M**, whose set-level form is
`AlgebraicGeometry.rootsOfUnitySectionsOver_representableBy_rootsOfUnityBaseChange`.

The coordinate ring `ℤ[X]/(Xⁿ - 1)` is of finite type over the integers, so `μₙ` lies in every
big fppf site, by **Stacks 000R**; so does its base change, being a fibre product of two objects
of the site.

## References

* [Stacks Project, Tag 043K](https://stacks.math.columbia.edu/tag/043K)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

/-- The group-valued functor on schemes over `S` whose value on `T` is the group of `n`-th roots
of unity in `Γ(T, 𝒪_T)`. -/
@[stacks 040M "relative_functor_of_points", sga "1 XI 6.1", sga "3 I 4.4.4", sga "3 VIIA 4.1.4"]
noncomputable abbrev rootsOfUnityGroupOverFunctor (n : ℕ) (S : Scheme.{u}) :
    (Over S)ᵒᵖ ⥤ GrpCat.{u} :=
  (Over.map (specULiftZIsTerminal.from S)).op ⋙ rootsOfUnityGroupFunctor n

/-- The group scheme `μₙ,S` of `n`-th roots of unity over `S`, as an object of the category of
schemes over `S`. -/
@[sga "1 XI 6.1", sga "3 I 4.4.4", sga "3 VIIB 2.5.2.A" "partial"]
noncomputable abbrev rootsOfUnityBaseChangeOver (n : ℕ) (S : Scheme.{u}) : Over S :=
  (Over.pullback (specULiftZIsTerminal.from S)).obj
    (Over.mk (rootsOfUnity n ↘ Spec (.of (ULift.{u} ℤ))))

/-- **Stacks Project, Tag 040M.** The base change of the group scheme of `n`-th roots of unity
to a scheme `S` is a group scheme over `S`. -/
@[stacks 040M "base_change_group_scheme",
  sga "1 XI 6.1",
  sga "3 I 4.4.4",
  sga "3 VIIB 2.5.2.A" "more general"]
noncomputable instance rootsOfUnityBaseChangeOverGrpObj (n : ℕ) [Fact (0 < n)]
    (S : Scheme.{u}) : GrpObj (rootsOfUnityBaseChangeOver n S) := by
  unfold rootsOfUnityBaseChangeOver
  exact Over.grpObjMkPullbackSnd (f := rootsOfUnity n ↘ Spec (.of (ULift.{u} ℤ)))
    (g := specULiftZIsTerminal.from S)

/-- The group-valued points of `μₙ,S` over a scheme over `S` are the points of `μₙ` over that
scheme regarded over the integers. -/
noncomputable def rootsOfUnityPullbackYonedaGrpIso (n : ℕ) [Fact (0 < n)] (S : Scheme.{u}) :
    yonedaGrpObj (rootsOfUnityBaseChangeOver n S) ≅
      (Over.map (specULiftZIsTerminal.from S)).op ⋙
        yonedaGrpObj (Over.mk (rootsOfUnity n ↘ Spec (.of (ULift.{u} ℤ)))) := by
  refine NatIso.ofComponents (fun T =>
      (CategoryTheory.Over.pullbackPointsMulEquiv (T := T.unop)
        (b := specULiftZIsTerminal.from S)
        (h := rootsOfUnity n ↘ Spec (.of (ULift.{u} ℤ)))).toGrpIso) ?_
  intro X Y f
  ext g
  apply Over.OverMorphism.ext
  dsimp [CategoryTheory.Over.pullbackPointsMulEquiv, MulEquiv.toGrpIso, GrpCat.ofHom]
  change (f.unop.left ≫ g.left ≫
      pullback.fst (rootsOfUnity n ↘ Spec (.of (ULift.{u} ℤ)))
        (specULiftZIsTerminal.from S)) =
    f.unop.left ≫ (g.left ≫
      pullback.fst (rootsOfUnity n ↘ Spec (.of (ULift.{u} ℤ)))
        (specULiftZIsTerminal.from S))
  exact Category.assoc f.unop.left g.left
    (pullback.fst (rootsOfUnity n ↘ Spec (.of (ULift.{u} ℤ))) (specULiftZIsTerminal.from S))

/-- **Stacks Project, Tag 040M.** For every scheme `S`, the group-valued functor of points of
the group scheme `μₙ,S` of `n`-th roots of unity is naturally isomorphic to the group of `n`-th
roots of unity in the global sections of the varying `S`-scheme. -/
@[stacks 040M "relative_functor_of_points",
  sga "3 I 4.4.4" "μ_n(T)={f : f^n=1}",
  sga "1 XI 6.1",
  sga "3 VIIA 4.1.4" "partial",
  sga "3 VIIB 2.5.2.A" "more general"]
noncomputable def rootsOfUnityBaseChangeGroupPointsIso (n : ℕ) [Fact (0 < n)] (S : Scheme.{u}) :
    yonedaGrpObj (rootsOfUnityBaseChangeOver n S) ≅ rootsOfUnityGroupOverFunctor n S :=
  rootsOfUnityPullbackYonedaGrpIso n S ≪≫ Functor.isoWhiskerLeft
    (Over.map (specULiftZIsTerminal.from S)).op
    (yonedaGrpObjIsoOfRepresentableBy
      (Over.mk (rootsOfUnity n ↘ Spec (.of (ULift.{u} ℤ))))
      (rootsOfUnityGroupFunctor n) (rootsOfUnityRepresentableBy n Fact.out))

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S) (n : ℕ)

/-- The scheme of `n`-th roots of unity over the integers belongs to every big fppf site: its
coordinate ring is of finite type over the integers. -/
theorem contains_rootsOfUnity : 𝒞.Contains (rootsOfUnity.{u} n) :=
  Scheme.size_Spec_lt_of_finiteType 𝒞.aleph0_lt_cutoff 𝒞.cutoff_isStrongPrelimit
    (ULift.{u} ℤ) (rootsOfUnityCoordinateRing.{u} n) (contains_specULiftZ 𝒞)

/-- The group scheme `μₙ,S` of `n`-th roots of unity over `S` belongs to the big fppf site
of `S`. -/
theorem contains_rootsOfUnityBaseChange (hS : 𝒞.Contains S) :
    𝒞.Contains (rootsOfUnityBaseChangeOver n S).left :=
  Scheme.size_pullback_lt _ _ (contains_rootsOfUnity 𝒞 n) hS

/-- **Stacks Project, Tag 043K.** The group scheme `μₙ,S` of `n`-th roots of unity over `S`,
read as an object of the big fppf site over `S`. -/
@[stacks 043K "the roots-of-unity group scheme as an object of the site", sga "1 XI 6.1"]
noncomputable def rootsOfUnitySiteObject : BigFppfOver 𝒞 S hS :=
  Over.mk (ObjectProperty.homMk (rootsOfUnityBaseChangeOver n S).hom
    (X := 𝒞.obj (contains_rootsOfUnityBaseChange 𝒞 S n hS)) (Y := 𝒞.obj hS))

/-- The group-scheme structure of `μₙ,S` of **Stacks 040M**, read on the object of the site. -/
@[instance_reducible, sga "3 I 4.4.4"]
noncomputable def rootsOfUnitySiteObjectGrpObj [Fact (0 < n)] :
    GrpObj ((toSchemeOver 𝒞 S hS).obj (rootsOfUnitySiteObject 𝒞 S hS n)) :=
  rootsOfUnityBaseChangeOverGrpObj n S

/-- The restriction to the big fppf site over `S` of the functor of points of `μₙ,S`. -/
noncomputable abbrev rootsOfUnityPointsOnSite [Fact (0 < n)] :
    (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ GrpCat.{u} :=
  pointsOnSite 𝒞 S hS (rootsOfUnitySiteObject 𝒞 S hS n)
    (rootsOfUnitySiteObjectGrpObj 𝒞 S hS n)

/-- **Stacks Project, Tag 043K.** The group algebraic space `μₙ,B = B ×_S μₙ,S` of `n`-th roots
of unity over an algebraic space `B` over `S`. -/
@[stacks 043K]
noncomputable def rootsOfUnitySpace [Fact (0 < n)] (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (hB : IsAlgebraicSpace 𝒞 S hS B) : GroupAlgebraicSpace 𝒞 S hS B hB :=
  GroupAlgebraicSpace.ofGroupSchemeInSite 𝒞 S hS B hB (rootsOfUnitySiteObject 𝒞 S hS n)
    (rootsOfUnitySiteObjectGrpObj 𝒞 S hS n)

/-- **Stacks Project, Tag 043K.** The algebraic space underlying the group algebraic space of
`n`-th roots of unity is the fibre product `B ×_S μₙ,S`. -/
@[stacks 043K "the underlying base change"]
theorem rootsOfUnitySpace_obj_X [Fact (0 < n)] (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (hB : IsAlgebraicSpace 𝒞 S hS B) :
    (rootsOfUnitySpace 𝒞 S hS n B hB).obj.X =
      (Over.mk (prod.fst :
        B ⨯ (rootsOfUnityPointsOnSite 𝒞 S hS n ⋙ forget GrpCat) ⟶ B) : Over B) :=
  rfl

/-- **Stacks Project, Tag 043K.** The group of points of the group algebraic space of `n`-th
roots of unity over a scheme `T` over `B` is the group of `n`-th roots of unity in the global
sections of `T`. -/
@[stacks 043K "the functor of roots of unity"]
noncomputable def rootsOfUnitySpacePoints [Fact (0 < n)]
    (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) (T : BigFppfOver 𝒞 S hS) (b : yoneda.obj T ⟶ B) :
    ((Over.mk b : Over B) ⟶
        Over.mk (prod.fst :
          B ⨯ (rootsOfUnityPointsOnSite 𝒞 S hS n ⋙ forget GrpCat) ⟶ B)) ≃*
      (rootsOfUnityGroupOverFunctor n S).obj
        (Opposite.op ((toSchemeOver 𝒞 S hS).obj T)) :=
  GroupAlgebraicSpace.groupSchemePointsMulEquiv 𝒞 S hS B (rootsOfUnitySiteObject 𝒞 S hS n)
    (rootsOfUnitySiteObjectGrpObj 𝒞 S hS n) (rootsOfUnityGroupOverFunctor n S)
    (rootsOfUnityBaseChangeGroupPointsIso n S) T b

/-- `AlgebraicGeometry.Space.rootsOfUnitySpacePoints` reads a point through the second
projection of the fibre product and the canonical identification of **Stacks 040M**. -/
@[stacks 043K "the functor of roots of unity"]
theorem rootsOfUnitySpacePoints_apply [Fact (0 < n)]
    (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) (T : BigFppfOver 𝒞 S hS) (b : yoneda.obj T ⟶ B)
    (x : (Over.mk b : Over B) ⟶
      Over.mk (prod.fst : B ⨯ (rootsOfUnityPointsOnSite 𝒞 S hS n ⋙ forget GrpCat) ⟶ B)) :
    rootsOfUnitySpacePoints 𝒞 S hS n B T b x =
      (rootsOfUnityBaseChangeGroupPointsIso n S).hom.app
        (Opposite.op ((toSchemeOver 𝒞 S hS).obj T))
        (yonedaEquiv (x.left ≫ (prod.snd :
          B ⨯ (rootsOfUnityPointsOnSite 𝒞 S hS n ⋙ forget GrpCat) ⟶ _))) :=
  GroupAlgebraicSpace.groupSchemePointsMulEquiv_apply 𝒞 S hS B _ _ _ _ T b x

/-- `AlgebraicGeometry.Space.rootsOfUnitySpacePoints` is natural in the scheme over `B`, so
what is asserted is representability of the functor of roots of unity and not a family of
unrelated group isomorphisms. -/
@[stacks 043K "the functor of roots of unity"]
theorem rootsOfUnitySpacePoints_naturality [Fact (0 < n)]
    (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) (T U : BigFppfOver 𝒞 S hS) (f : T ⟶ U)
    (b : yoneda.obj U ⟶ B)
    (x : (Over.mk b : Over B) ⟶
      Over.mk (prod.fst : B ⨯ (rootsOfUnityPointsOnSite 𝒞 S hS n ⋙ forget GrpCat) ⟶ B)) :
    rootsOfUnitySpacePoints 𝒞 S hS n B T (yoneda.map f ≫ b)
        ((Over.homMk (yoneda.map f) :
          (Over.mk (yoneda.map f ≫ b) : Over B) ⟶ Over.mk b) ≫ x) =
      (rootsOfUnityGroupOverFunctor n S ⋙ forget GrpCat).map
        ((toSchemeOver 𝒞 S hS).map f).op
        (rootsOfUnitySpacePoints 𝒞 S hS n B U b x) :=
  GroupAlgebraicSpace.groupSchemePointsMulEquiv_naturality 𝒞 S hS B _ _ _ _ T U f b x

end AlgebraicGeometry.Space

end
