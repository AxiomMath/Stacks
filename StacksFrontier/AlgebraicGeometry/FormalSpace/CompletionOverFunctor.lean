module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFibreProduct
public import StacksFrontier.AlgebraicGeometry.Full.Square

/-!
# Completion along a set of points as a functor on slice categories

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a presheaf on the big fppf
site of `S` and let `T` be a set of points of `X`. For an object `h : M ⟶ X` of the category of
presheaves over `X` write `M_{/T} = M_{/|h|⁻¹T}` for the completion of `M` along the inverse
image of `T`.

Completion along `T` is a functor from the presheaves over `X` to the sheaves over `X_{/T}`: it
sends `h : M ⟶ X` to `h_{/T} : M_{/T} ⟶ X_{/T}` and a morphism `a : M ⟶ N` over `X` to the
completion `a_{/T} : M_{/T} ⟶ N_{/T}` of `a`.

## Main definitions

* `AlgebraicGeometry.Space.completionOverMap`: the completion of a morphism over `X`.
* `AlgebraicGeometry.Space.completionOverFunctor`: completion along `T` as a functor from the
  presheaves over `X` to the sheaves over `X_{/T}`.

## Main results

* `AlgebraicGeometry.Space.completionBaseChangeIso_naturality_fst`: the base-change
  isomorphism of `AlgebraicGeometry.Space.completionBaseChangeIso` is compatible with the
  completion of a morphism over `X`, on the first projection of the fibre product.
* `AlgebraicGeometry.Space.completionBaseChangeSquareIso`: completion commutes with base
  change as a natural isomorphism of functors, so the square formed by the two base-change
  functors and the two completion functors commutes.
* `AlgebraicGeometry.Space.restrictedCompletionBaseChangeSquareIso`: the same square on full
  subcategories, for any four functors restricting the four functors of the ambient square.

## Implementation notes

The completion `M_{/T}` is indexed by the set `|h|⁻¹T` of points of `M`, and a morphism
`a : M ⟶ N` over `X` presents that set in a second way, as `|a|⁻¹|N → X|⁻¹T`. The two agree, but
not definitionally: `pointsMap` is a map of quotients and its compatibility with composition is
proved pointwise. The arrow map therefore carries the transport along that equality, and the
functor laws are identities between morphisms with transports inserted.

All of them are proved by composing with the inclusion `M_{/T} ⟶ M` into the ambient sheaf,
which is a monomorphism by Stacks 0APV: the completion square of Stacks 0APV turns a completed
morphism followed by that inclusion into the inclusion followed by the sheafified universe lift
of the morphism, the transports collapse against the inclusion, and what remains is
functoriality of the sheafified universe lift.

The same argument shows that the base-change isomorphism of
`AlgebraicGeometry.Space.completionBaseChangeIso` is compatible with completed morphisms on the
first projection of the fibre product `M_{/T} ×_{X_{/T}} X_{1, /T_1}`: the two routes
`M ×_X X₁ ⟶ N` through the square of base changes agree in the slice over `X`, so their
completions agree.

Packaging those components as a natural isomorphism needs the component at `M` to carry the
functor-applied objects in its type and not the equal-but-differently-spelled fibre products:
with the objects spelled as applications of the two composite functors, the comparison of two
morphisms into a fibre product splits into the first projection, which is the naturality above,
and the second, which is the defining property of a morphism in a slice category. The first
projection of the arrow map of a pullback functor is
`CategoryTheory.Over.pullback_map_left_comp_fst`.

## References

* [Stacks Project, Tag 0APV](https://stacks.math.columbia.edu/tag/0APV)
* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The two descriptions of the points of an object over `X` lying over `T` -/

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- For a morphism `a : M ⟶ N` of presheaves over `X`, the points of `M` lying over `T` are the
points of `M` lying over the points of `N` lying over `T`. -/
theorem preimage_pointsMap_over (T : Set (points B S hS X)) {M N : Over X} (a : M ⟶ N) :
    pointsMap B S hS M.left M.hom ⁻¹' T =
      pointsMap B S hS M.left a.left ⁻¹' (pointsMap B S hS N.left N.hom ⁻¹' T) := by
  rw [← Set.preimage_comp, ← pointsMap_comp, Over.w a]

/-! ### Completed morphisms and the inclusion into the ambient sheaf -/

/-- The completion square of **Stacks 0APV** with a transport of the source along an equality
of the sets of points it is completed along: a completed morphism followed by the inclusion into
the ambient sheaf is the inclusion followed by the sheafified universe lift. -/
theorem completionSheafMap_inclusion_reindex {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X' ⟶ X) (T : Set (points B S hS X)) {A : Set (points B S hS X')}
    (h : A = pointsMap B S hS X' f ⁻¹' T) :
    eqToHom (congrArg (completionSheaf B S hS X') h) ≫ completionSheafMap B S hS f T ≫
        completionSheafInclusion B S hS X T =
      completionSheafInclusion B S hS X' A ≫ sheafifiedULiftMap B S hS f := by
  rw [← (isPullback_completionSheafMap B S hS f T).w, ← Category.assoc,
    completionSheafInclusion_transport B S hS X' h]

/-! ### The completion of a morphism over `X` -/

/-- Two morphisms into a completion agree if they agree after the inclusion into the ambient
sheaf. -/
private theorem hom_ext_of_comp_completionSheafInclusion {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {A : Set (points B S hS X')} {Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    {f g : Y ⟶ completionSheaf B S hS X' A}
    (h : f ≫ completionSheafInclusion B S hS X' A = g ≫ completionSheafInclusion B S hS X' A) :
    f = g := by
  have := mono_completionSheafInclusion B S hS X' A
  exact (cancel_mono _).1 h

/-- The completion along `T` of a morphism `a : M ⟶ N` of presheaves over `X`: the completion of
`a` along the points of `N` lying over `T`, with the source transported along
`AlgebraicGeometry.Space.preimage_pointsMap_over`. -/
def completionOverMap (T : Set (points B S hS X)) {M N : Over X} (a : M ⟶ N) :
    completionSheaf B S hS M.left (pointsMap B S hS M.left M.hom ⁻¹' T) ⟶
      completionSheaf B S hS N.left (pointsMap B S hS N.left N.hom ⁻¹' T) :=
  eqToHom (congrArg (completionSheaf B S hS M.left) (preimage_pointsMap_over B S hS T a)) ≫
    completionSheafMap B S hS a.left (pointsMap B S hS N.left N.hom ⁻¹' T)

/-- The completion of a morphism over `X` followed by the inclusion into the ambient sheaf is
the inclusion followed by the sheafified universe lift of the morphism. -/
@[reassoc]
theorem completionOverMap_comp_inclusion (T : Set (points B S hS X)) {M N : Over X}
    (a : M ⟶ N) :
    completionOverMap B S hS T a ≫
        completionSheafInclusion B S hS N.left (pointsMap B S hS N.left N.hom ⁻¹' T) =
      completionSheafInclusion B S hS M.left (pointsMap B S hS M.left M.hom ⁻¹' T) ≫
        sheafifiedULiftMap B S hS a.left := by
  rw [completionOverMap, Category.assoc]
  exact completionSheafMap_inclusion_reindex B S hS (Over.Hom.left a)
    (pointsMap B S hS N.left N.hom ⁻¹' T) (preimage_pointsMap_over B S hS T a)

/-- The completion of a morphism over `X` is a morphism over `X_{/T}`. -/
theorem completionOverMap_comp_completionSheafMap (T : Set (points B S hS X)) {M N : Over X}
    (a : M ⟶ N) :
    completionOverMap B S hS T a ≫ completionSheafMap B S hS N.hom T =
      completionSheafMap B S hS M.hom T := by
  refine hom_ext_of_comp_completionSheafInclusion B S hS ?_
  rw [Category.assoc,
    ← (isPullback_completionSheafMap B S hS N.hom T).w, completionOverMap_comp_inclusion_assoc,
    ← sheafifiedULiftMap_comp, Over.w a]
  exact (isPullback_completionSheafMap B S hS M.hom T).w

/-- The completion of an identity morphism over `X` is the identity. -/
theorem completionOverMap_id (T : Set (points B S hS X)) (M : Over X) :
    completionOverMap B S hS T (𝟙 M) = 𝟙 _ := by
  refine hom_ext_of_comp_completionSheafInclusion B S hS ?_
  rw [completionOverMap_comp_inclusion]
  simp

/-- The completion of a composite of morphisms over `X` is the composite of the completions. -/
theorem completionOverMap_comp (T : Set (points B S hS X)) {M N P : Over X} (a : M ⟶ N)
    (b : N ⟶ P) :
    completionOverMap B S hS T (a ≫ b) =
      completionOverMap B S hS T a ≫ completionOverMap B S hS T b := by
  refine hom_ext_of_comp_completionSheafInclusion B S hS ?_
  rw [completionOverMap_comp_inclusion, Category.assoc,
    completionOverMap_comp_inclusion, ← Category.assoc, completionOverMap_comp_inclusion,
    Category.assoc, ← sheafifiedULiftMap_comp]
  rfl

/-! ### Completion along `T` as a functor on slice categories -/

/-- **Completion along a set of points as a functor on slice categories.** Completion along a
set `T` of points of `X` carries an object `h : M ⟶ X` over `X` to `h_{/T} : M_{/T} ⟶ X_{/T}`
over `X_{/T}` and a morphism over `X` to its completion. -/
def completionOverFunctor (T : Set (points B S hS X)) :
    Over X ⥤ Over (completionSheaf B S hS X T) where
  obj M := Over.mk (completionSheafMap B S hS M.hom T)
  map a := Over.homMk (completionOverMap B S hS T a)
    (completionOverMap_comp_completionSheafMap B S hS T a)
  map_id M := Over.OverMorphism.ext (by simpa using completionOverMap_id B S hS T M)
  map_comp a b := Over.OverMorphism.ext (by simpa using completionOverMap_comp B S hS T a b)

/-- The completion functor carries an object `h : M ⟶ X` over `X` to `h_{/T}` over `X_{/T}`. -/
@[simp]
theorem completionOverFunctor_obj (T : Set (points B S hS X)) (M : Over X) :
    (completionOverFunctor B S hS T).obj M = Over.mk (completionSheafMap B S hS M.hom T) :=
  rfl

/-- The structure morphism of the completion of an object `h : M ⟶ X` over `X` is `h_{/T}`. -/
@[simp]
theorem completionOverFunctor_obj_hom (T : Set (points B S hS X)) (M : Over X) :
    ((completionOverFunctor B S hS T).obj M).hom = completionSheafMap B S hS M.hom T :=
  rfl

/-- The underlying morphism of the completion functor applied to a morphism over `X` is its
completion. -/
@[simp]
theorem completionOverFunctor_map_left (T : Set (points B S hS X)) {M N : Over X} (a : M ⟶ N) :
    ((completionOverFunctor B S hS T).map a).left = completionOverMap B S hS T a :=
  rfl

/-! ### Completion commutes with base change -/

/-- The first projection of the completed fibre square of
`AlgebraicGeometry.Space.completionBaseChangeIso`, followed by the inclusion into the ambient
sheaf. -/
@[reassoc]
theorem completionBaseChangeIso_hom_left_fst_inclusion
    {X' X₁ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X) (g : X₁ ⟶ X)
    (T : Set (points B S hS X)) :
    (completionBaseChangeIso B S hS f g T).hom.left ≫
        pullback.fst (completionSheafMap B S hS f T) (completionSheafMap B S hS g T) ≫
        completionSheafInclusion B S hS X' (pointsMap B S hS X' f ⁻¹' T) =
      completionSheafInclusion B S hS (pullback f g)
          (pointsMap B S hS (pullback f g) (pullback.snd f g) ⁻¹'
            (pointsMap B S hS X₁ g ⁻¹' T)) ≫
        sheafifiedULiftMap B S hS (pullback.fst f g) := by
  have hpre := preimage_pointsMap_eq_of_comm B S hS (IsPullback.of_hasPullback f g).w T
  have hfst : (completionBaseChangeIso B S hS f g T).hom.left ≫
      pullback.fst (completionSheafMap B S hS f T) (completionSheafMap B S hS g T) =
      eqToHom (congrArg (completionSheaf B S hS (pullback f g)) hpre.symm) ≫
        completionSheafMap B S hS (pullback.fst f g) (pointsMap B S hS X' f ⁻¹' T) := by
    simp only [completionBaseChangeIso, Over.isoMk_hom_left, Iso.trans_hom, Iso.symm_hom,
      eqToIso.inv, Category.assoc,
      (isPullback_completionSheafMap_of_isPullback B S hS (IsPullback.of_hasPullback f g)
        T).isoPullback_hom_fst]
  rw [← Category.assoc, hfst, Category.assoc,
    completionSheafMap_inclusion_reindex B S hS (pullback.fst f g)
      (pointsMap B S hS X' f ⁻¹' T) hpre.symm]

/-- Naturality of `AlgebraicGeometry.Space.completionBaseChangeIso` on the first projection of
the fibre product: the two routes `M ×_X X₁ ⟶ N` through the square of base changes have the
same completion. -/
theorem completionBaseChangeIso_naturality_fst {X₁ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : X₁ ⟶ X) (T : Set (points B S hS X)) {M N : Over X} (a : M ⟶ N) :
    completionOverMap B S hS (pointsMap B S hS X₁ g ⁻¹' T) ((Over.pullback g).map a) ≫
        (completionBaseChangeIso B S hS N.hom g T).hom.left ≫
        pullback.fst (completionSheafMap B S hS N.hom T) (completionSheafMap B S hS g T) =
      (completionBaseChangeIso B S hS M.hom g T).hom.left ≫
        pullback.fst (completionSheafMap B S hS M.hom T) (completionSheafMap B S hS g T) ≫
        completionOverMap B S hS T a := by
  have key : Over.Hom.left ((Over.pullback g).map a) ≫ pullback.fst N.hom g =
      pullback.fst M.hom g ≫ a.left := by
    simp only [Over.pullback_map_left, pullback.lift_fst]
  have hbc : completionOverMap B S hS (pointsMap B S hS X₁ g ⁻¹' T)
        ((Over.pullback g).map a) ≫
        completionSheafInclusion B S hS (pullback N.hom g)
          (pointsMap B S hS (pullback N.hom g) (pullback.snd N.hom g) ⁻¹'
            (pointsMap B S hS X₁ g ⁻¹' T)) =
      completionSheafInclusion B S hS (pullback M.hom g)
          (pointsMap B S hS (pullback M.hom g) (pullback.snd M.hom g) ⁻¹'
            (pointsMap B S hS X₁ g ⁻¹' T)) ≫
        sheafifiedULiftMap B S hS (Over.Hom.left ((Over.pullback g).map a)) :=
    completionOverMap_comp_inclusion B S hS (pointsMap B S hS X₁ g ⁻¹' T)
      ((Over.pullback g).map a)
  refine hom_ext_of_comp_completionSheafInclusion B S hS ?_
  simp only [Category.assoc, completionOverMap_comp_inclusion,
    completionBaseChangeIso_hom_left_fst_inclusion,
    completionBaseChangeIso_hom_left_fst_inclusion_assoc,
    ← sheafifiedULiftMap_comp]
  rw [← Category.assoc, hbc, Category.assoc, ← sheafifiedULiftMap_comp, key]

/-! ### The square of slice categories commutes -/

/-- The isomorphism of `AlgebraicGeometry.Space.completionBaseChangeIso` at an object over `X`:
the completion along `T₁` of the base change of `M` along `g` is the base change along
`X_{1, /T_1} ⟶ X_{/T}` of the completion of `M` along `T`. -/
def completionOverBaseChangeIso {X₁ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X₁ ⟶ X)
    (T : Set (points B S hS X)) (M : Over X) :
    (completionOverFunctor B S hS (pointsMap B S hS X₁ g ⁻¹' T)).obj
        ((Over.pullback g).obj M) ≅
      (Over.pullback (completionSheafMap B S hS g T)).obj
        ((completionOverFunctor B S hS T).obj M) :=
  completionBaseChangeIso B S hS M.hom g T

/-- **Completion commutes with base change.** For a morphism `g : X₁ ⟶ X` of presheaves on the
big fppf site of `S` and a set `T` of points of `X`, base change along `g` followed by
completion along `T₁ = |g|⁻¹T` is naturally isomorphic to completion along `T` followed by base
change along `X_{1, /T_1} ⟶ X_{/T}`: the square of slice categories commutes. -/
def completionBaseChangeSquareIso {X₁ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X₁ ⟶ X)
    (T : Set (points B S hS X)) :
    Over.pullback g ⋙ completionOverFunctor B S hS (pointsMap B S hS X₁ g ⁻¹' T) ≅
      completionOverFunctor B S hS T ⋙ Over.pullback (completionSheafMap B S hS g T) :=
  NatIso.ofComponents (fun M => completionOverBaseChangeIso B S hS g T M) <| by
    intro M N a
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
    · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc,
        Functor.comp_map, Functor.comp_map, Over.pullback_map_left_comp_fst]
      exact completionBaseChangeIso_naturality_fst B S hS g T a
    · exact (Over.w _).trans (Over.w _).symm

/-- The component at `M` of `AlgebraicGeometry.Space.completionBaseChangeSquareIso` is the
isomorphism `AlgebraicGeometry.Space.completionOverBaseChangeIso` at `M`. -/
@[simp]
theorem completionBaseChangeSquareIso_hom_app {X₁ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : X₁ ⟶ X) (T : Set (points B S hS X)) (M : Over X) :
    (completionBaseChangeSquareIso B S hS g T).hom.app M =
      (completionOverBaseChangeIso B S hS g T M).hom :=
  rfl

/-- The square of completion and base change on full subcategories of the four slice
categories: four functors which restrict the two base-change functors and the two completion
functors form a commutative square. -/
def restrictedCompletionBaseChangeSquareIso
    {X₁ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X₁ ⟶ X) (T : Set (points B S hS X))
    {P : ObjectProperty (Over X)} {P₁ : ObjectProperty (Over X₁)}
    {Q : ObjectProperty (Over (completionSheaf B S hS X T))}
    {Q₁ : ObjectProperty (Over (completionSheaf B S hS X₁ (pointsMap B S hS X₁ g ⁻¹' T)))}
    {A : P.FullSubcategory ⥤ P₁.FullSubcategory}
    {F : P.FullSubcategory ⥤ Q.FullSubcategory}
    {F₁ : P₁.FullSubcategory ⥤ Q₁.FullSubcategory}
    {D : Q.FullSubcategory ⥤ Q₁.FullSubcategory}
    (hA : A ⋙ P₁.ι ≅ P.ι ⋙ Over.pullback g)
    (hF : F ⋙ Q.ι ≅ P.ι ⋙ completionOverFunctor B S hS T)
    (hF₁ : F₁ ⋙ Q₁.ι ≅ P₁.ι ⋙ completionOverFunctor B S hS (pointsMap B S hS X₁ g ⁻¹' T))
    (hD : D ⋙ Q₁.ι ≅ Q.ι ⋙ Over.pullback (completionSheafMap B S hS g T)) :
    A ⋙ F₁ ≅ F ⋙ D :=
  Functor.fullyFaithfulCancelRight Q₁.ι
    (Functor.associator A F₁ Q₁.ι ≪≫ Functor.isoWhiskerLeft A hF₁ ≪≫
      (Functor.associator A P₁.ι _).symm ≪≫ Functor.isoWhiskerRight hA _ ≪≫
      Functor.associator P.ι (Over.pullback g) _ ≪≫
      Functor.isoWhiskerLeft P.ι (completionBaseChangeSquareIso B S hS g T) ≪≫
      (Functor.associator P.ι (completionOverFunctor B S hS T) _).symm ≪≫
      Functor.isoWhiskerRight hF.symm (Over.pullback (completionSheafMap B S hS g T)) ≪≫
      Functor.associator F Q.ι _ ≪≫ Functor.isoWhiskerLeft F hD.symm ≪≫
      (Functor.associator F D Q₁.ι).symm)

end AlgebraicGeometry.Space

end
