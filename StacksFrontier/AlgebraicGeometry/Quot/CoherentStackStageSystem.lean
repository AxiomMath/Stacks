module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStack
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitSystem
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPushforwardQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward

/-!
# The inverse system `X ×_Y T_j` of the proof of Stacks 08KD

In Situation 08KB let `f : X ⟶ Y` be of finite presentation, and let `T = lim T_j` be a
cofiltered limit of affine schemes of the big fppf site, taken in schemes, as in Artin's Axioms,
Definition 07XL. A morphism `g : T_i ⟶ Y` from one stage makes every later stage `T_k` (an
object `k ⟶ i` of `Over i`) and the limit `T` test schemes over `Y`, and the proof of Stacks
08KD works with the system of base changes `X_k = X ×_Y T_k` and its limit `X_T = X ×_Y T`.
This file records the properties of that system which the colimit statement of Stacks 07V7,
`AlgebraicGeometry.Space.finitePresentationModule_isColimit_of_isLimit`, asks for: the stages are
quasi-compact and quasi-separated algebraic spaces with affine transition morphisms, `X_T` is their
limit, and the system satisfies the chapter's convention (Stacks 07SD). The same results for the
system of test schemes `T_k` are the inputs of the descent results for Situation 084W stated over
that convention, through which the flatness and the properness of the support of a module descend
to a stage (Stacks 08K0, 08K2).

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.stageTestSystem` and
  `AlgebraicGeometry.Space.CoherentSituation.stageTestCone`: the test schemes `T_k` over `Y`,
  for `k ⟶ i`, and the limit `T` over `Y`.
* `AlgebraicGeometry.Space.CoherentSituation.stageSpaceSystem` and
  `AlgebraicGeometry.Space.CoherentSituation.stageSpaceCone`: the system of base changes `X_k`
  and its cone with vertex `X_T`, as presheaves.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.isLimit_stageSpaceCone`: `X_T = lim_k X_k`.
* `AlgebraicGeometry.Space.CoherentSituation.siteContainsBaseChangeLimits_stageSpaceSystem`: the
  system satisfies the chapter's convention (Stacks 07SD).
* `AlgebraicGeometry.Space.CoherentSituation.isAffineHom_stageSpaceSystem_map`,
  `AlgebraicGeometry.Space.CoherentSituation.isQuasiCompactSpace_space` and
  `AlgebraicGeometry.Space.CoherentSituation.isAbsolutelyQuasiSeparated_space`: the transition
  morphisms are affine and the stages are quasi-compact and quasi-separated.

## References

* [Stacks Project, Tag 08KD](https://stacks.math.columbia.edu/tag/08KD)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : CoherentSituation B S hS)

/-! ### Quasi-compactness and quasi-separatedness over an affine test scheme -/

/-- The base change `X_T` of the situation to an affine test scheme is quasi-compact. -/
theorem isQuasiCompactSpace_space (T : SchemesOver D.Y)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T.left)) :
    IsQuasiCompactSpace B S hS (D.space T).1 :=
  isQuasiCompactSpace_of_isFinitePresentation B S hS (D.projection T).hom
    ((schemeSpaceFunctor B S hS).obj T.left).2
    (isQuasiCompactSpace_yoneda_of_isAffine B S hS T.left hT) (D.isFinitePresentation_projection T)

/-- The base change `X_T` of the situation to an affine test scheme is quasi-separated. -/
theorem isAbsolutelyQuasiSeparated_space (hZ : B.Contains (⊤_ Scheme.{u})) (T : SchemesOver D.Y)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T.left)) :
    IsAbsolutelyQuasiSeparated B S hS hZ (D.space T).1 :=
  isAbsolutelyQuasiSeparated_of_isFinitePresentation B S hS hZ (D.space T).2
    (isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS _ hZ
      ⟨T.left, inferInstance, ⟨Functor.RepresentableBy.yoneda T.left⟩⟩)
    (D.isFinitePresentation_projection T)

/-! ### The system of test schemes above a stage -/

section Stage

variable {I : Type u} [Category.{u} I] (E : I ⥤ BigAffineFppf B S hS) (c : Cone E) {i : I}
  (g : (schemeSpaceFunctor B S hS).obj ((BigAffineFppf.inclusion B S hS).obj (E.obj i)) ⟶ D.Y)

/-- The test scheme over `Y` attached to a scheme over the stage `T_i`. -/
abbrev stageTest {U : BigFppfOver B S hS}
    (h : U ⟶ (BigAffineFppf.inclusion B S hS).obj (E.obj i)) : SchemesOver D.Y :=
  CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map h ≫ g)

/-- **The test schemes `T_k` over `Y`** for the stages `k ⟶ i` above the stage `i`, the
structure morphism of `T_k` being `T_k ⟶ T_i ⟶ Y`. -/
noncomputable def stageTestSystem : Over i ⥤ SchemesOver D.Y where
  obj k := D.stageTest E g ((BigAffineFppf.inclusion B S hS).map (E.map k.hom))
  map {k k'} m := CostructuredArrow.homMk ((BigAffineFppf.inclusion B S hS).map (E.map m.left))
    (by
      dsimp
      rw [← Category.assoc, ← Functor.map_comp, ← ObjectProperty.FullSubcategory.comp_hom,
        ← E.map_comp, Over.w m])
  map_id k := by
    apply CostructuredArrow.hom_ext
    simp
  map_comp m m' := by
    apply CostructuredArrow.hom_ext
    simp

/-- **The limit `T` as a test scheme over `Y`**, with structure morphism `T ⟶ T_i ⟶ Y`, and its
projections to the test schemes `T_k`. -/
noncomputable def stageTestCone : Cone (D.stageTestSystem E g) where
  pt := D.stageTest E g ((BigAffineFppf.inclusion B S hS).map (c.π.app i))
  π :=
    { app k := CostructuredArrow.homMk ((BigAffineFppf.inclusion B S hS).map (c.π.app k.left))
        (by
          dsimp [stageTestSystem]
          rw [← Category.assoc, ← Functor.map_comp, ← ObjectProperty.FullSubcategory.comp_hom,
            c.w])
      naturality k k' m := by
        apply CostructuredArrow.hom_ext
        change 𝟙 _ ≫ (BigAffineFppf.inclusion B S hS).map (c.π.app k'.left) =
          (BigAffineFppf.inclusion B S hS).map (c.π.app k.left) ≫
            (BigAffineFppf.inclusion B S hS).map (E.map m.left)
        rw [Category.id_comp, ← Functor.map_comp, c.w] }

/-- The underlying system of representable presheaves of the test schemes above `i` is the
restriction of the system `E` to the stages above `i`. -/
theorem stageTestSystem_comp_proj :
    D.stageTestSystem E g ⋙ CostructuredArrow.proj _ D.Y ⋙ yoneda =
      (Over.forget i ⋙ E) ⋙ affineYoneda B S hS :=
  rfl

/-- **The limit `T` is the limit of the test schemes `T_k`, as presheaves**, when it is their limit
in schemes. -/
noncomputable def isLimit_stageTestCone [IsCofiltered I]
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    IsLimit ((CostructuredArrow.proj _ D.Y ⋙ yoneda).mapCone (D.stageTestCone E c g)) :=
  isLimit_affineYoneda_mapCone_of_isLimit_toScheme (Over.forget i ⋙ E) (c.whisker (Over.forget i))
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) _).symm hc)

/-- **The test schemes above a stage satisfy the chapter's convention (Stacks 07SD).** -/
theorem siteContainsBaseChangeLimits_stageTestSystem [IsCofiltered I]
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    SiteContainsBaseChangeLimits B S hS
      (D.stageTestSystem E g ⋙ CostructuredArrow.proj _ D.Y ⋙ yoneda) :=
  siteContainsBaseChangeLimits_affineYoneda (Over.forget i ⋙ E) (c.whisker (Over.forget i))
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) _).symm hc)

/-! ### The system of base changes above a stage -/

/-- **The system `X_k = X ×_Y T_k` of base changes** to the test schemes above the stage `i`, as
presheaves on the big fppf site of `S`. -/
noncomputable abbrev stageSpaceSystem : Over i ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  testBaseChangeSystem D.f (D.stageTestSystem E g)

/-- The cone of the system of base changes with vertex `X_T = X ×_Y T`, whose projections are the
morphisms `X_T ⟶ X_k` induced by the projections `T ⟶ T_k`. -/
noncomputable abbrev stageSpaceCone : Cone (D.stageSpaceSystem E g) :=
  (baseChangeOver D.f ⋙ Over.forget D.X ⋙ ObjectProperty.ι _).mapCone (D.stageTestCone E c g)

/-- **`X_T = lim_k X_k`.** -/
noncomputable def isLimit_stageSpaceCone [IsCofiltered I]
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    IsLimit (D.stageSpaceCone E c g) :=
  isLimit_testBaseChangeSystem D.f _ _ (D.isLimit_stageTestCone E c g hc)

/-- **The system of base changes satisfies the chapter's convention (Stacks 07SD).** -/
theorem siteContainsBaseChangeLimits_stageSpaceSystem [IsCofiltered I]
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    SiteContainsBaseChangeLimits B S hS (D.stageSpaceSystem E g) :=
  siteContainsBaseChangeLimits_testBaseChangeSystem D.f _
    (D.siteContainsBaseChangeLimits_stageTestSystem E c g hc)

/-- The transition morphisms `X_k ⟶ X_{k'}` of the system of base changes are affine: they are base
changes of the morphisms `T_k ⟶ T_{k'}` of affine schemes. -/
theorem isAffineHom_stageSpaceSystem_map {k k' : Over i} (m : k ⟶ k') :
    IsAffineHom B S hS ((D.stageSpaceSystem E g).map m) := by
  have _ (k : Over i) : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((CostructuredArrow.proj _ D.Y).obj ((D.stageTestSystem E g).obj k))) :=
    (E.obj k.left).property
  exact IsAffineHom.of_isPullback (isPullback_testBaseChangeSystem D.f _ m).flip
    (isAffineHom_yoneda_map B S hS _)

/-- The stages of the system of base changes are algebraic spaces. -/
theorem isAlgebraicSpace_stageSpaceSystem (k : Over i) :
    IsAlgebraicSpace B S hS ((D.stageSpaceSystem E g).obj k) :=
  (D.space ((D.stageTestSystem E g).obj k)).2

/-- The stages of the system of base changes are quasi-compact. -/
theorem isQuasiCompactSpace_stageSpaceSystem (k : Over i) :
    IsQuasiCompactSpace B S hS ((D.stageSpaceSystem E g).obj k) :=
  D.isQuasiCompactSpace_space _ (E.obj k.left).property

/-- The stages of the system of base changes are quasi-separated. -/
theorem isAbsolutelyQuasiSeparated_stageSpaceSystem (hZ : B.Contains (⊤_ Scheme.{u}))
    (k : Over i) :
    IsAbsolutelyQuasiSeparated B S hS hZ ((D.stageSpaceSystem E g).obj k) :=
  D.isAbsolutelyQuasiSeparated_space hZ _ (E.obj k.left).property


end Stage

end AlgebraicGeometry.Space.CoherentSituation

end
