module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.MayerVietorisSquare
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.CategoryTheory.Subterminal
public import StacksFrontier.AlgebraicGeometry.Full.Square
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraicityOnBaseCover
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSlice
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfOverTypeSheafification

/-!
# Glueing presheaves along a two-element covering of a terminal object

Let `C` be a category with binary products, let `Z` be a terminal object of `C` and let
`jU : U ⟶ Z` and `jW : W ⟶ Z` be monomorphisms whose intersection `V = U ×_Z W` is given by a
cartesian square. Being subobjects of a terminal object, `U`, `W` and `V` are *subterminal*: any
two morphisms into them from a common source agree. Because `Z` is terminal, the fibre product of
`X` and `U` over `Z` is the binary product `U ⨯ X`, so the restriction of a presheaf `F` to `U`
is the presheaf `X ↦ F (U ⨯ X)`.

Two consequences of subterminality organise the glueing of presheaves along `{U, W}`. First, for
a presheaf `A` over the representable presheaf of `U`, the base change of `A` along the Yoneda
image of `f : V ⟶ U` has the same sections as `A` over every object lying over `V`: the
compatibility condition defining the fibre product is automatic and the second coordinate is
forced. Second, the two projections `U ⨯ X ⟶ X` and `W ⨯ X ⟶ X` are monomorphisms and generate a
covering sieve of `X`, so they form a Mayer--Vietoris square with vertices `V ⨯ X`, `U ⨯ X`,
`W ⨯ X` and `X`; evaluating a sheaf on it exhibits its sections over `X` as the fibre product of
its sections over `U ⨯ X` and over `W ⨯ X` above its sections over `V ⨯ X`.

The glueing construction itself takes a presheaf `A` over the representable presheaf of `U`, a
presheaf `B` over that of `W`, and an isomorphism of their base changes to `V`, and produces the
presheaf whose sections over `X` are the pairs of a section of `A` over `U ⨯ X` and a section of
`B` over `W ⨯ X` agreeing over `V ⨯ X`. It is a sheaf whenever `A` and `B` are: the restriction of
a sheaf along `V ⨯ -` is a sheaf, because `V ⨯ -` is the composite of the right adjoint of
`CategoryTheory.Over.forget V` with `CategoryTheory.Over.forget V` and both are continuous for the
localization of the topology at `V`. The construction is functorial in the glueing datum.

Over an object lying over `U` the restriction of the glued presheaf is the first of the two
presheaves glued, since `U ⨯ X ≅ X` and `V ⨯ X ≅ W ⨯ X` there; and symmetrically over `W`.

All of this is applied to the big fppf site of a scheme `S`, whose terminal object is the base
itself, in order to glue algebraic spaces of finite presentation along a covering of the base by
two opens: the glueing functor takes a triple consisting of such a space over `U`, such a space
over `W` and an identification of their base changes to `V` — that is, an object of the
`2`-fibre product `FP_U ×_{FP_V} FP_W` — to the glued space over the base. That the glued space
is an algebraic space over `S` is the criterion of Stacks 0E8Z applied to its two restrictions,
and that its structure morphism is of finite presentation is the Zariski locality of finite
presentation on the target applied to the two-member Zariski covering of the base by `U` and
`W`.

**The comparison functor from the algebraic spaces of finite presentation over the base to the
`2`-fibre product is an equivalence**, which is the content of Stacks 0E8Z. It is faithful and
full because the two projections `U ⨯ T ⟶ T` and `W ⨯ T ⟶ T` form a Mayer--Vietoris square, so a
morphism into an fppf sheaf is determined by, and can be glued from, its restrictions along them;
the two restrictions of a glued pair of morphisms agree over `V ⨯ T` because the given pair of
base-changed morphisms commutes with the comparison isomorphism of the square. It is essentially
surjective because the two restrictions of the glued space are the two spaces glued, compatibly
with the identification over `V`.

## Main definitions

* `CategoryTheory.prodSquare`: the commuting square with vertices `V ⨯ X`, `U ⨯ X`, `W ⨯ X` and
  `X` attached to `iU : V ⟶ U`, `iW : V ⟶ W` and `X`.
* `CategoryTheory.GrothendieckTopology.mayerVietorisSquareProd`: that square, as a
  Mayer--Vietoris square.
* `CategoryTheory.GrothendieckTopology.mayerVietorisSectionsEquiv`: the sections of a sheaf over
  `X` as the compatible pairs of sections over `U ⨯ X` and over `W ⨯ X`.
* `CategoryTheory.prodRestrictMap`: the restriction map `F (U ⨯ -) ⟶ F (V ⨯ -)` along
  `f : V ⟶ U`.
* `CategoryTheory.prodRestrictPullbackIso`: the identification of the restriction along `V ⨯ -`
  of a base change to `V` with the restriction of the presheaf itself.
* `CategoryTheory.SubterminalGlueing.gluedPresheaf` and
  `CategoryTheory.SubterminalGlueing.gluedPresheafMap`: the glued presheaf and its functoriality
  in the glueing datum.
* `AlgebraicGeometry.FinitePresentationSpacesOver.mayerVietorisSquare`: the Mayer--Vietoris
  square of an object of the big fppf site of `S` relative to a two-element covering of the base.
* `CategoryTheory.SubterminalGlueing.gluedRestrictLeftIso` and
  `CategoryTheory.SubterminalGlueing.gluedRestrictRightIso`: the identifications of the two
  restrictions of the glued presheaf with the two presheaves glued.
* `AlgebraicGeometry.Space.rangePair`: the two-member family of subfunctors of the base cut out
  by `U` and `W`.
* `AlgebraicGeometry.FinitePresentationSpacesOver.gluedPresheafFunctor` and
  `AlgebraicGeometry.FinitePresentationSpacesOver.glueingQuasiInverse`: the glueing functor out
  of the `2`-fibre product `FP_U ×_{FP_V} FP_W`, as a functor to presheaves and as a functor to
  `FP_Z`.
* `CategoryTheory.Over.pullbackSectionsEquiv` and `CategoryTheory.Over.pullbackSectionsMap`: the
  sections of a base change to a subterminal `U` over an object lying over `U`, and the map on
  them induced by a morphism of base changes.
* `AlgebraicGeometry.FinitePresentationSpacesOver.glueProd`: the section of an fppf sheaf over
  `T` glued from sections over `U ⨯ T` and over `W ⨯ T` agreeing over `V ⨯ T`.
* `AlgebraicGeometry.FinitePresentationSpacesOver.glueingFullHom` and
  `AlgebraicGeometry.FinitePresentationSpacesOver.glueingFullOverHom`: the morphism over the base
  glued from two compatible base-changed morphisms.
* `CategoryTheory.SubterminalGlueing.gluedOverMap`: the morphism of glued presheaves over the
  terminal object induced by a morphism of glueing data.
* `AlgebraicGeometry.FinitePresentationSpacesOver.counitIso` and
  `AlgebraicGeometry.FinitePresentationSpacesOver.unitIso`: the counit and the unit of the
  equivalence of Stacks 0E8Z.

## Main results

* `CategoryTheory.isSubterminal_of_mono_isTerminal`: a subobject of a terminal object is
  subterminal.
* `CategoryTheory.IsPullback.prod_map_snd`: the square `CategoryTheory.prodSquare` is cartesian.
* `CategoryTheory.isIso_prod_snd_of_hom` and `CategoryTheory.isIso_prod_map_of_hom`: over an
  object lying over `U`, the projection from the product with `U` and the map from the product
  with `V` to the product with `W` are isomorphisms.
* `CategoryTheory.isContinuous_prod_functor_obj` and
  `CategoryTheory.Presheaf.isSheaf_prod_functor_op_comp`: the functor `V ⨯ -` is continuous, so
  the restriction of a sheaf along it is a sheaf.
* `CategoryTheory.bijective_pullback_fst_app`: over an object lying over `V`, the base change
  along the Yoneda image of `V ⟶ U` of a presheaf over the representable presheaf of a
  subterminal `U` has the same sections as that presheaf.
* `CategoryTheory.SubterminalGlueing.isSheaf_gluedPresheaf`: the glued presheaf is a sheaf.
* `AlgebraicGeometry.FinitePresentationSpacesOver.ofTwoArrows_mem_topology`: two jointly
  surjective open immersions onto the base generate a covering sieve of the big fppf topology.
* `AlgebraicGeometry.Space.isZariskiCover_rangePair`: and they form a Zariski covering of the
  representable presheaf of the base.
* `AlgebraicGeometry.Space.isFinitePresentation_of_arrowIso`: finite presentation depends only
  on the arrow up to isomorphism.
* `AlgebraicGeometry.FinitePresentationSpacesOver.isAlgebraicSpace_gluedPresheaf` and
  `AlgebraicGeometry.FinitePresentationSpacesOver.isFinitePresentation_gluedOver`: the glued
  presheaf is an algebraic space over `S` and its structure morphism is of finite
  presentation.
* `AlgebraicGeometry.FinitePresentationSpacesOver.natTrans_ext_of_prod_app` and
  `AlgebraicGeometry.FinitePresentationSpacesOver.over_hom_ext_of_pullback_map_eq`: a morphism
  into an fppf sheaf over the base is determined by its base changes to `U` and to `W`.
* `AlgebraicGeometry.FinitePresentationSpacesOver.faithful_glueingFunctor`: the comparison
  functor into the `2`-fibre product is faithful.
* `AlgebraicGeometry.FinitePresentationSpacesOver.baseChangeSquareIso_hom_app_left` and
  `CategoryTheory.Over.pullbackSquare_map_left_fst`: the comparison isomorphism of the square,
  and the compatibility of a pair of base-changed morphisms with it, read through the iterated
  projections.
* `CategoryTheory.Over.pullbackSectionsMap_eq_of_comm`: a pair of base-changed morphisms
  commuting with the comparison isomorphism of the square induces the same map on sections over
  an object lying over `V`.
* `AlgebraicGeometry.FinitePresentationSpacesOver.full_glueingFunctor`: the comparison functor
  into the `2`-fibre product is full.
* `CategoryTheory.SubterminalGlueing.gluedRestrict_comm`: the two comparison isomorphisms of the
  restrictions of the glued presheaf agree over `V`.
* `AlgebraicGeometry.FinitePresentationSpacesOver.essSurj_glueingFunctor` and
  `AlgebraicGeometry.FinitePresentationSpacesOver.isEquivalence_glueingFunctor`: the comparison
  functor is essentially surjective, hence an equivalence.

## Implementation notes

The glued presheaf is defined by the explicit fibre product of types
`CategoryTheory.Limits.Types.PullbackObj` rather than as a fibre product in the presheaf
category, so that its sections are literally compatible pairs. That it is a sheaf is then
obtained by exhibiting it as a limit of sheaves: the explicit cone is shown to be a limit cone,
and sheaves are closed under limits computed in presheaves.

The hypotheses are stated as subterminality of `U`, `W` and `V` in `C` rather than of their
representable presheaves, since that is all the sheaf-theoretic arguments use and it is what the
cartesian square over a terminal object provides. Subterminality is a proposition, so the glued
presheaf does not depend on which proof of it is supplied.

The covering hypotheses of
`AlgebraicGeometry.FinitePresentationSpacesOver.glueingQuasiInverse` are stated twice, once for
the structure morphisms of `U` and `W` to the terminal object of the site — which is what the
covering sieve and the Zariski covering are read from — and once for their structure morphisms
to `S`, which is what the algebraicity criterion consumes. At the canonical terminal object
`Over.mk (𝟙 (B.obj hS))` the two forms are the same statement, by
`AlgebraicGeometry.toScheme_map_mkIdTerminal_from`.

## What is not proved

The equivalence is established in the generalised setting of an arbitrary terminal object `Z` of
the site, which is what applications to further coverings need; the identification of the
`2`-fibre product `FP_U ×_{FP_V} FP_W` with a `2`-fibre product of the categories of all
algebraic spaces over `S`, and the variants of Stacks 0E8Z for coverings by more than two opens,
are not treated.

## References

* [Stacks Project, Tag 0E8Z](https://stacks.math.columbia.edu/tag/0E8Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-! ### Subterminal objects -/

/-- An object admitting a monomorphism to a terminal object is subterminal: any two morphisms
into it from a common source agree. -/
theorem isSubterminal_of_mono_isTerminal {Z U : C} (hZ : IsTerminal Z) (j : U ⟶ Z) [Mono j] :
    IsSubterminal U := by
  intro T f g
  rw [← cancel_mono j]
  exact hZ.hom_ext _ _

/-- The vertex of a cartesian square whose two upper-right corners are subterminal is
subterminal. -/
theorem IsPullback.isSubterminal {Z U W V : C} {iU : V ⟶ U} {iW : V ⟶ W} {jU : U ⟶ Z}
    {jW : W ⟶ Z} (hV : IsPullback iU iW jU jW) (hU : IsSubterminal U) (hW : IsSubterminal W) :
    IsSubterminal V :=
  fun _ _ _ => hV.hom_ext (hU _ _) (hW _ _)

/-- The projection onto the second factor of a product with a subterminal object is a
monomorphism. -/
theorem IsSubterminal.mono_prod_snd {U : C} (hU : IsSubterminal U) (X : C)
    [HasBinaryProduct U X] : Mono (prod.snd : U ⨯ X ⟶ X) :=
  ⟨fun _ _ h => prod.hom_ext (hU _ _) h⟩

/-! ### Mayer--Vietoris squares from a two-element covering of a terminal object -/

section Square

variable [HasBinaryProducts C]

/-- The commuting square with vertices `V ⨯ X`, `U ⨯ X`, `W ⨯ X` and `X` attached to a pair of
morphisms `iU : V ⟶ U`, `iW : V ⟶ W` and an object `X`, whose two lower edges are the second
projections. -/
@[simps]
noncomputable def prodSquare {V U W : C} (iU : V ⟶ U) (iW : V ⟶ W) (X : C) : Square C where
  X₁ := V ⨯ X
  X₂ := U ⨯ X
  X₃ := W ⨯ X
  X₄ := X
  f₁₂ := prod.map iU (𝟙 X)
  f₁₃ := prod.map iW (𝟙 X)
  f₂₄ := prod.snd
  f₃₄ := prod.snd
  fac := by simp

/-- If `Z` is terminal and `V` is a fibre product of `U` and `W` over `Z`, then for every object
`X` the square `CategoryTheory.prodSquare` is cartesian: fibre products over `Z` are binary
products, and binary products commute with fibre products. -/
theorem IsPullback.prod_map_snd {Z U W V : C} {jU : U ⟶ Z} {jW : W ⟶ Z} {iU : V ⟶ U}
    {iW : V ⟶ W} (hV : IsPullback iU iW jU jW) (hZ : IsTerminal Z) (X : C) :
    IsPullback (prod.map iU (𝟙 X)) (prod.map iW (𝟙 X))
      (prod.snd : U ⨯ X ⟶ X) (prod.snd : W ⨯ X ⟶ X) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (by simp)
    (fun s => prod.lift (hV.lift (s.fst ≫ prod.fst) (s.snd ≫ prod.fst) (hZ.hom_ext _ _))
      (s.fst ≫ prod.snd)) (fun s => ?_) (fun s => ?_) (fun s m h₁ h₂ => ?_))
  · refine prod.hom_ext ?_ ?_ <;> simp
  · refine prod.hom_ext ?_ ?_ <;> simp [s.condition]
  · refine prod.hom_ext (hV.hom_ext ?_ ?_) ?_
    · simpa using congrArg (· ≫ prod.fst) h₁
    · simpa using congrArg (· ≫ prod.fst) h₂
    · simpa using congrArg (· ≫ prod.snd) h₁

/-- For an object `X` lying over a subterminal `U`, the second projection `U ⨯ X ⟶ X` is an
isomorphism, the inverse being the graph of the given morphism `X ⟶ U`. -/
theorem isIso_prod_snd_of_hom {U : C} (hU : IsSubterminal U) {X : C} (p : X ⟶ U) :
    IsIso (prod.snd : U ⨯ X ⟶ X) :=
  ⟨prod.lift p (𝟙 X), prod.hom_ext (hU _ _) (by simp), by simp⟩

/-- For an object `X` lying over `U`, and `V` the intersection of `U` and `W` inside a terminal
object `Z`, the map `V ⨯ X ⟶ W ⨯ X` is an isomorphism: the first coordinate of a point of
`W ⨯ X` already lies over `U` through `X`. -/
theorem isIso_prod_map_of_hom {Z U W V : C} (hZ : IsTerminal Z) (hU : IsSubterminal U)
    {jU : U ⟶ Z} {jW : W ⟶ Z} {iU : V ⟶ U} {iW : V ⟶ W} (hV : IsPullback iU iW jU jW)
    {X : C} (p : X ⟶ U) : IsIso (prod.map iW (𝟙 X) : V ⨯ X ⟶ W ⨯ X) :=
  haveI := isIso_prod_snd_of_hom hU p
  (hV.prod_map_snd hZ X).isIso_snd_of_isIso

/-- The graph of a morphism to a subterminal object is an isomorphism: it is a section of the
second projection, which is itself a monomorphism. -/
theorem isIso_prod_lift_id_of_hom {U : C} (hU : IsSubterminal U) {X : C} (p : X ⟶ U) :
    IsIso (prod.lift p (𝟙 X)) :=
  ⟨prod.snd, by simp, prod.hom_ext (hU _ _) (by simp)⟩


namespace GrothendieckTopology

variable (J : GrothendieckTopology C)

/-- If the two monomorphisms `jU : U ⟶ Z` and `jW : W ⟶ Z` onto a terminal object generate a
covering sieve, then for every object `X` the two projections `U ⨯ X ⟶ X` and `W ⨯ X ⟶ X`
generate a covering sieve of `X`: the sieve they generate contains the base change of the given
one. -/
theorem ofTwoArrows_prod_snd_mem {Z U W : C} (hZ : IsTerminal Z) {jU : U ⟶ Z} {jW : W ⟶ Z}
    (hcov : Sieve.ofTwoArrows jU jW ∈ J Z) (X : C) :
    Sieve.ofTwoArrows (prod.snd : U ⨯ X ⟶ X) (prod.snd : W ⨯ X ⟶ X) ∈ J X := by
  refine J.superset_covering ?_ (J.pullback_stable (hZ.from X) hcov)
  rintro T g hg
  obtain ⟨(_ | _), a, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
  · exact (Sieve.mem_ofArrows_iff _ _ _).2
      ⟨WalkingPair.left, prod.lift a g, (prod.lift_snd a g).symm⟩
  · exact (Sieve.mem_ofArrows_iff _ _ _).2
      ⟨WalkingPair.right, prod.lift a g, (prod.lift_snd a g).symm⟩

variable [HasWeakSheafify J (Type v)]

/-- **The Mayer--Vietoris square attached to an object and a two-element covering of a terminal
object.** If `jU : U ⟶ Z` and `jW : W ⟶ Z` are monomorphisms onto a terminal object which
generate a covering sieve and whose intersection is given by a cartesian square, then for every
object `X` the square with vertices `V ⨯ X`, `U ⨯ X`, `W ⨯ X` and `X` is a Mayer--Vietoris
square. -/
noncomputable def mayerVietorisSquareProd {Z U W V : C} (hZ : IsTerminal Z) {jU : U ⟶ Z}
    {jW : W ⟶ Z} [Mono jU] [Mono jW] {iU : V ⟶ U} {iW : V ⟶ W} (hV : IsPullback iU iW jU jW)
    (hcov : Sieve.ofTwoArrows jU jW ∈ J Z) (X : C) : J.MayerVietorisSquare :=
  haveI : Mono (prodSquare iU iW X).f₂₄ :=
    (isSubterminal_of_mono_isTerminal hZ jU).mono_prod_snd X
  haveI : Mono (prodSquare iU iW X).f₃₄ :=
    (isSubterminal_of_mono_isTerminal hZ jW).mono_prod_snd X
  MayerVietorisSquare.mk_of_isPullback (J := J) (prodSquare iU iW X)
    (hV.prod_map_snd hZ X) (J.ofTwoArrows_prod_snd_mem hZ hcov X)

/-- The underlying square of `CategoryTheory.GrothendieckTopology.mayerVietorisSquareProd` is
`CategoryTheory.prodSquare`. -/
@[simp]
theorem mayerVietorisSquareProd_toSquare {Z U W V : C} (hZ : IsTerminal Z) {jU : U ⟶ Z}
    {jW : W ⟶ Z} [Mono jU] [Mono jW] {iU : V ⟶ U} {iW : V ⟶ W} (hV : IsPullback iU iW jU jW)
    (hcov : Sieve.ofTwoArrows jU jW ∈ J Z) (X : C) :
    (J.mayerVietorisSquareProd hZ hV hcov X).toSquare = prodSquare iU iW X :=
  rfl

/-- **The sections of a sheaf over `X` are the compatible pairs of sections over `U ⨯ X` and over
`W ⨯ X`.** This is the sheaf condition of `CategoryTheory.GrothendieckTopology.MayerVietorisSquare`
at the square `CategoryTheory.prodSquare`. -/
noncomputable def mayerVietorisSectionsEquiv {Z U W V : C} (hZ : IsTerminal Z) {jU : U ⟶ Z}
    {jW : W ⟶ Z} [Mono jU] [Mono jW] {iU : V ⟶ U} {iW : V ⟶ W} (hV : IsPullback iU iW jU jW)
    (hcov : Sieve.ofTwoArrows jU jW ∈ J Z) (X : C) {F : Cᵒᵖ ⥤ Type v}
    (hF : Presheaf.IsSheaf J F) :
    F.obj (op X) ≃
      Types.PullbackObj (F.map (prod.map iU (𝟙 X)).op) (F.map (prod.map iW (𝟙 X)).op) :=
  Equiv.ofBijective _
    (((J.mayerVietorisSquareProd hZ hV hcov X).sheafCondition_iff_bijective_toPullbackObj F).1
      (MayerVietorisSquare.sheafCondition_of_sheaf _ ⟨F, hF⟩))

end GrothendieckTopology

end Square

/-! ### Restriction of a presheaf along a product -/

section Restrict

variable [HasBinaryProducts C]

/-- The functor `X ↦ V ⨯ X` is continuous for every topology on `C`: it is the composite of the
right adjoint of `CategoryTheory.Over.forget V` with `CategoryTheory.Over.forget V`, and both are
continuous for the localization of the topology at `V`. -/
theorem isContinuous_prod_functor_obj (J : GrothendieckTopology C) (V : C) :
    Functor.IsContinuous (prod.functor.obj V : C ⥤ C) J J :=
  Functor.isContinuous_comp (Over.star V) (Over.forget V) J (J.over V) J

/-- The restriction `X ↦ F (V ⨯ X)` of a sheaf along the product with a fixed object is again a
sheaf. -/
theorem Presheaf.isSheaf_prod_functor_op_comp (J : GrothendieckTopology C) (V : C)
    {F : Cᵒᵖ ⥤ Type v} (hF : Presheaf.IsSheaf J F) :
    Presheaf.IsSheaf J ((prod.functor.obj V).op ⋙ F) :=
  have := isContinuous_prod_functor_obj J V
  (prod.functor.obj V).op_comp_isSheaf_of_isSheaf J J F hF

/-- The restriction map `F (U ⨯ -) ⟶ F (V ⨯ -)` induced by a morphism `f : V ⟶ U`. -/
noncomputable def prodRestrictMap {V U : C} (f : V ⟶ U) (F : Cᵒᵖ ⥤ Type v) :
    (prod.functor.obj U).op ⋙ F ⟶ (prod.functor.obj V).op ⋙ F :=
  Functor.whiskerRight (NatTrans.op (prod.functor.map f)) F

/-- The component of `CategoryTheory.prodRestrictMap f F` at `X` is the map of `F` along
`prod.map f (𝟙 X)`. -/
@[simp]
theorem prodRestrictMap_app {V U : C} (f : V ⟶ U) (F : Cᵒᵖ ⥤ Type v) (X : Cᵒᵖ) :
    (prodRestrictMap f F).app X = F.map (prod.map f (𝟙 X.unop)).op :=
  rfl

/-- The restriction maps `CategoryTheory.prodRestrictMap` are natural in the presheaf. -/
theorem prodRestrictMap_naturality {V U : C} (f : V ⟶ U) {F F' : Cᵒᵖ ⥤ Type v} (α : F ⟶ F') :
    Functor.whiskerLeft (prod.functor.obj U).op α ≫ prodRestrictMap f F' =
      prodRestrictMap f F ≫ Functor.whiskerLeft (prod.functor.obj V).op α := by
  ext X x
  exact (NatTrans.naturality_apply α (prod.map f (𝟙 X.unop)).op x).symm

end Restrict

/-! ### Base change to a subterminal object -/

/-- **Base change to a subterminal object does not change the sections over it.** For `f : V ⟶ U`
with `U` and `V` subterminal and `A` a presheaf over the representable presheaf of `U`, the first
projection from the base change of `A` along the Yoneda image of `f` is bijective on sections
over any object admitting a morphism to `V`: the compatibility condition is automatic because `U`
is subterminal, and the second coordinate is unique because `V` is. -/
theorem bijective_pullback_fst_app {V U : C} (f : V ⟶ U) (hU : IsSubterminal U)
    (hV : IsSubterminal V) (A : Over (yoneda.obj U : Cᵒᵖ ⥤ Type v)) {Y : C} (p : Y ⟶ V) :
    Function.Bijective ((pullback.fst A.hom (yoneda.map f)).app (op Y)) := by
  have h : IsPullback ((pullback.fst A.hom (yoneda.map f)).app (op Y))
      ((pullback.snd A.hom (yoneda.map f)).app (op Y)) (A.hom.app (op Y))
      ((yoneda.map f).app (op Y)) :=
    (IsPullback.of_hasPullback A.hom (yoneda.map f)).map
      ((evaluation Cᵒᵖ (Type v)).obj (op Y))
  refine ⟨fun x y hxy => Types.ext_of_isPullback h hxy (hV _ _), fun a => ?_⟩
  obtain ⟨x, hx, -⟩ := Types.exists_of_isPullback h a p (hU _ _)
  exact ⟨x, hx⟩

/-- A morphism of a slice category into a base change along `g` is determined by its composite
with the first projection: the composite with the second projection is the structure
morphism. -/
theorem Over.hom_ext_pullback_fst [HasPullbacks C] {M N : C} (g : N ⟶ M) {Bb : Over M}
    {P : Over N} {α β : P ⟶ (Over.pullback g).obj Bb}
    (h : α.left ≫ pullback.fst Bb.hom g = β.left ≫ pullback.fst Bb.hom g) : α = β :=
  Over.OverMorphism.ext (pullback.hom_ext h ((Over.w α).trans (Over.w β).symm))

/-- For `Z` terminal in `C` and `g : F ⟶ yoneda.obj Z` the structure morphism of a presheaf, the
two projections exhibit `yoneda.obj U ⨯ F` as the base change of `yoneda.map j` along `g`. This
is `AlgebraicGeometry.Space.isPullback_prod_fst_snd_yoneda_obj` for an arbitrary terminal
object and an arbitrary morphism to it. -/
theorem isPullback_prod_fst_snd_of_isTerminal {Z U : C} (hZ : IsTerminal Z) (j : U ⟶ Z)
    {F : Cᵒᵖ ⥤ Type v} (g : F ⟶ yoneda.obj Z) :
    IsPullback (prod.fst : (yoneda.obj U : Cᵒᵖ ⥤ Type v) ⨯ F ⟶ yoneda.obj U) prod.snd
      (yoneda.map j) g := by
  have hT : IsTerminal (yoneda.obj Z : Cᵒᵖ ⥤ Type v) := hZ.isTerminalObj yoneda Z
  have h := hT.isPullback_prod (yoneda.obj U : Cᵒᵖ ⥤ Type v) F
  rwa [hT.hom_ext (hT.from (yoneda.obj U)) (yoneda.map j), hT.hom_ext (hT.from F) g] at h

/-- The Yoneda image of a commuting square commutes. -/
theorem yoneda_map_comm {V U W Z : C} {iU : V ⟶ U} {iW : V ⟶ W} {jU : U ⟶ Z} {jW : W ⟶ Z}
    (w : iU ≫ jU = iW ≫ jW) :
    (yoneda.map iU ≫ yoneda.map jU : (yoneda.obj V : Cᵒᵖ ⥤ Type v) ⟶ yoneda.obj Z) =
      yoneda.map iW ≫ yoneda.map jW := by
  rw [← Functor.map_comp, ← Functor.map_comp, w]

/-- Over a terminal object the restriction of a presheaf to `U` is the product with the
representable presheaf of `U`. -/
noncomputable def prodIsoPullbackOfIsTerminal {Z U : C} (hZ : IsTerminal Z) (j : U ⟶ Z)
    {F : Cᵒᵖ ⥤ Type v} (g : F ⟶ yoneda.obj Z) :
    (yoneda.obj U : Cᵒᵖ ⥤ Type v) ⨯ F ≅ pullback g (yoneda.map j) :=
  (isPullback_prod_fst_snd_of_isTerminal hZ j g).flip.isoPullback


section Restrict

variable [HasBinaryProducts C]

/-- The identification, given by the first projection, of the restriction along `V ⨯ -` of the
base change along the Yoneda image of `f : V ⟶ U` of a presheaf `A` over the representable
presheaf of a subterminal `U` with the restriction of `A` itself. -/
noncomputable def prodRestrictPullbackIso {V U : C} (f : V ⟶ U) (hU : IsSubterminal U)
    (hV : IsSubterminal V) (A : Over (yoneda.obj U : Cᵒᵖ ⥤ Type v)) :
    (prod.functor.obj V).op ⋙ ((Over.pullback (yoneda.map f)).obj A).left ≅
      (prod.functor.obj V).op ⋙ A.left :=
  haveI : ∀ X : Cᵒᵖ, IsIso ((Functor.whiskerLeft (prod.functor.obj V).op
      (pullback.fst A.hom (yoneda.map f))).app X) := fun X =>
    (isIso_iff_bijective _).2
      (bijective_pullback_fst_app f hU hV A (prod.fst : V ⨯ X.unop ⟶ V))
  haveI := NatIso.isIso_of_isIso_app (Functor.whiskerLeft (prod.functor.obj V).op
    (pullback.fst A.hom (yoneda.map f)))
  asIso (Functor.whiskerLeft (prod.functor.obj V).op (pullback.fst A.hom (yoneda.map f)))

/-- `CategoryTheory.prodRestrictPullbackIso` is the restriction of the first projection. -/
theorem prodRestrictPullbackIso_hom {V U : C} (f : V ⟶ U) (hU : IsSubterminal U)
    (hV : IsSubterminal V) (A : Over (yoneda.obj U : Cᵒᵖ ⥤ Type v)) :
    (prodRestrictPullbackIso f hU hV A).hom =
      Functor.whiskerLeft (prod.functor.obj V).op (pullback.fst A.hom (yoneda.map f)) :=
  rfl

/-- The component of `CategoryTheory.prodRestrictPullbackIso` at `X` is the component of the
first projection at `V ⨯ X`. -/
@[simp]
theorem prodRestrictPullbackIso_hom_app {V U : C} (f : V ⟶ U) (hU : IsSubterminal U)
    (hV : IsSubterminal V) (A : Over (yoneda.obj U : Cᵒᵖ ⥤ Type v)) (X : Cᵒᵖ) :
    (prodRestrictPullbackIso f hU hV A).hom.app X =
      (pullback.fst A.hom (yoneda.map f)).app (op (V ⨯ X.unop)) :=
  rfl

/-- `CategoryTheory.prodRestrictPullbackIso` is natural in the presheaf over the representable
presheaf of `U`. -/
theorem prodRestrictPullbackIso_naturality {V U : C} (f : V ⟶ U) (hU : IsSubterminal U)
    (hV : IsSubterminal V) {A A' : Over (yoneda.obj U : Cᵒᵖ ⥤ Type v)} (a : A ⟶ A') :
    Functor.whiskerLeft (prod.functor.obj V).op ((Over.pullback (yoneda.map f)).map a).left ≫
        (prodRestrictPullbackIso f hU hV A').hom =
      (prodRestrictPullbackIso f hU hV A).hom ≫
        Functor.whiskerLeft (prod.functor.obj V).op a.left := by
  rw [prodRestrictPullbackIso_hom, prodRestrictPullbackIso_hom,
    ← Functor.whiskerLeft_comp, ← Functor.whiskerLeft_comp,
    Over.pullback_map_left_comp_fst]

end Restrict

/-- A pair of base-changed morphisms commuting with the comparison isomorphism of a square
induces, through the two iterated projections, the same morphism to the object base changed.
This is the only place the comparison isomorphism of
`CategoryTheory.Over.pullbackSquareIso` has to be unwound: its characterising property
`CategoryTheory.Over.pullbackSquareObjIso_hom_left_fst` does it in one step. -/
theorem Over.pullbackSquare_map_left_fst [HasPullbacks C] {S U L V' : C} {u : U ⟶ S} {p : L ⟶ S}
    {v : V' ⟶ L} {q : V' ⟶ U} (w : q ≫ u = v ≫ p) {X Y : Over S}
    {mU : (Over.pullback u).obj X ⟶ (Over.pullback u).obj Y}
    {mW : (Over.pullback p).obj X ⟶ (Over.pullback p).obj Y}
    (hcomm : (Over.pullback q).map mU ≫ (Over.pullbackSquareObjIso w Y).hom =
      (Over.pullbackSquareObjIso w X).hom ≫ (Over.pullback v).map mW) :
    ((Over.pullback q).map mU).left ≫
        pullback.fst (pullback.snd Y.hom u) q ≫ pullback.fst Y.hom u =
      (Over.pullbackSquareObjIso w X).hom.left ≫ ((Over.pullback v).map mW).left ≫
        pullback.fst (pullback.snd Y.hom p) v ≫ pullback.fst Y.hom p := by
  have h : ((Over.pullback q).map mU).left ≫ (Over.pullbackSquareObjIso w Y).hom.left =
      (Over.pullbackSquareObjIso w X).hom.left ≫ ((Over.pullback v).map mW).left := by
    rw [← Over.comp_left, ← Over.comp_left, hcomm]
  rw [← Over.pullbackSquareObjIso_hom_left_fst w Y, ← Category.assoc, h, Category.assoc]

/-- Two morphisms of the slice over the representable presheaf of a terminal object which have
the same base change to a subterminal `U` agree on sections over `U ⨯ T`: the first projection
from the base change is bijective on those sections. -/
theorem Over.app_prod_eq_of_pullback_map_eq [HasBinaryProducts C] {Z U : C} (hZ : IsTerminal Z)
    (j : U ⟶ Z) (hU : IsSubterminal U) {X Y : Over (yoneda.obj Z : Cᵒᵖ ⥤ Type v)} {f g : X ⟶ Y}
    (h : (Over.pullback (yoneda.map j)).map f = (Over.pullback (yoneda.map j)).map g) (T : C) :
    f.left.app (op (U ⨯ T)) = g.left.app (op (U ⨯ T)) := by
  have h1 : pullback.fst X.hom (yoneda.map j) ≫ f.left =
      pullback.fst X.hom (yoneda.map j) ≫ g.left := by
    rw [← Over.pullback_map_left_comp_fst, ← Over.pullback_map_left_comp_fst, h]
  have hb := bijective_pullback_fst_app j (isSubterminal_of_isTerminal hZ) hU X
    (prod.fst : U ⨯ T ⟶ U)
  refine ConcreteCategory.hom_ext _ _ fun y => ?_
  obtain ⟨z, hz⟩ := hb.surjective y
  rw [← hz]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h1 (op (U ⨯ T))) z

/-! ### Sections of a base change over an object lying over a subterminal object -/

section PullbackSections

variable {Z U : C} (hZ : IsTerminal Z) (j : U ⟶ Z) (hU : IsSubterminal U)

/-- **Over an object lying over a subterminal `U`, the base change along the Yoneda image of
`j : U ⟶ Z` has the same sections as the presheaf itself**, the bijection being the first
projection. Only the existence of a morphism to `U` is used. -/
noncomputable def Over.pullbackSectionsEquiv (X : Over (yoneda.obj Z : Cᵒᵖ ⥤ Type v)) {T : C}
    (hT : Nonempty (T ⟶ U)) :
    ((Over.pullback (yoneda.map j)).obj X).left.obj (op T) ≃ X.left.obj (op T) :=
  Equiv.ofBijective _ (hT.elim fun p =>
    bijective_pullback_fst_app j (isSubterminal_of_isTerminal hZ) hU X p)

/-- `CategoryTheory.Over.pullbackSectionsEquiv` is the component of the first projection. -/
@[simp]
theorem Over.pullbackSectionsEquiv_apply (X : Over (yoneda.obj Z : Cᵒᵖ ⥤ Type v)) {T : C}
    (hT : Nonempty (T ⟶ U)) (z : ((Over.pullback (yoneda.map j)).obj X).left.obj (op T)) :
    Over.pullbackSectionsEquiv hZ j hU X hT z =
      (pullback.fst X.hom (yoneda.map j)).app (op T) z :=
  rfl

/-- The map on sections over an object lying over a subterminal `U` induced by a morphism of the
base changes along the Yoneda image of `j : U ⟶ Z`. -/
noncomputable def Over.pullbackSectionsMap {X Y : Over (yoneda.obj Z : Cᵒᵖ ⥤ Type v)}
    (m : (Over.pullback (yoneda.map j)).obj X ⟶ (Over.pullback (yoneda.map j)).obj Y) {T : C}
    (hT : Nonempty (T ⟶ U)) : X.left.obj (op T) → Y.left.obj (op T) :=
  fun x => Over.pullbackSectionsEquiv hZ j hU Y hT
    (m.left.app (op T) ((Over.pullbackSectionsEquiv hZ j hU X hT).symm x))

/-- `CategoryTheory.Over.pullbackSectionsMap` is characterised by its compatibility with the
first projections from the two base changes. -/
theorem Over.pullbackSectionsMap_fst {X Y : Over (yoneda.obj Z : Cᵒᵖ ⥤ Type v)}
    (m : (Over.pullback (yoneda.map j)).obj X ⟶ (Over.pullback (yoneda.map j)).obj Y) {T : C}
    (hT : Nonempty (T ⟶ U)) (z : ((Over.pullback (yoneda.map j)).obj X).left.obj (op T)) :
    Over.pullbackSectionsMap hZ j hU m hT ((pullback.fst X.hom (yoneda.map j)).app (op T) z) =
      (pullback.fst Y.hom (yoneda.map j)).app (op T) (m.left.app (op T) z) :=
  congrArg (fun w => Over.pullbackSectionsEquiv hZ j hU Y hT (m.left.app (op T) w))
    ((Over.pullbackSectionsEquiv hZ j hU X hT).symm_apply_apply z)

/-- `CategoryTheory.Over.pullbackSectionsMap` is natural in the object lying over `U`. -/
theorem Over.pullbackSectionsMap_naturality {X Y : Over (yoneda.obj Z : Cᵒᵖ ⥤ Type v)}
    (m : (Over.pullback (yoneda.map j)).obj X ⟶ (Over.pullback (yoneda.map j)).obj Y) {T T' : C}
    (g : T' ⟶ T) (hT : Nonempty (T ⟶ U)) (hT' : Nonempty (T' ⟶ U)) (x : X.left.obj (op T)) :
    Y.left.map g.op (Over.pullbackSectionsMap hZ j hU m hT x) =
      Over.pullbackSectionsMap hZ j hU m hT' (X.left.map g.op x) := by
  obtain ⟨z, hz⟩ := (Over.pullbackSectionsEquiv hZ j hU X hT).surjective x
  rw [Over.pullbackSectionsEquiv_apply] at hz
  subst hz
  rw [Over.pullbackSectionsMap_fst,
    ← NatTrans.naturality_apply (pullback.fst X.hom (yoneda.map j)) g.op,
    Over.pullbackSectionsMap_fst]
  exact (NatTrans.naturality_apply (pullback.fst Y.hom (yoneda.map j)) g.op _).symm.trans
    (congrArg (fun w => (pullback.fst Y.hom (yoneda.map j)).app (op T') w)
      (NatTrans.naturality_apply m.left g.op z).symm)

/-- **A pair of base-changed morphisms commuting with the comparison isomorphism of a square
induces the same map on sections over an object lying over `V`.** This is
`CategoryTheory.Over.pullbackSquare_map_left_fst` read through the identification of the sections
of a base change over such an object with the sections of the presheaf itself. -/
theorem Over.pullbackSectionsMap_eq_of_comm {W V : C} {jU : U ⟶ Z} {jW : W ⟶ Z} {iU : V ⟶ U}
    {iW : V ⟶ W} (hW : IsSubterminal W) (hVs : IsSubterminal V)
    (w : yoneda.map iU ≫ yoneda.map jU = yoneda.map iW ≫ yoneda.map jW)
    {X Y : Over (yoneda.obj Z : Cᵒᵖ ⥤ Type v)}
    {mU : (Over.pullback (yoneda.map jU)).obj X ⟶ (Over.pullback (yoneda.map jU)).obj Y}
    {mW : (Over.pullback (yoneda.map jW)).obj X ⟶ (Over.pullback (yoneda.map jW)).obj Y}
    (hcomm : (Over.pullback (yoneda.map iU)).map mU ≫ (Over.pullbackSquareObjIso w Y).hom =
      (Over.pullbackSquareObjIso w X).hom ≫ (Over.pullback (yoneda.map iW)).map mW)
    {T : C} (p : T ⟶ V) (x : X.left.obj (op T)) :
    Over.pullbackSectionsMap hZ jU hU mU ⟨p ≫ iU⟩ x =
      Over.pullbackSectionsMap hZ jW hW mW ⟨p ≫ iW⟩ x := by
  obtain ⟨z, hz⟩ := (bijective_pullback_fst_app jU (isSubterminal_of_isTerminal hZ) hU X
    (p ≫ iU)).surjective x
  have hb : Function.Bijective
      ((pullback.fst (pullback.snd X.hom (yoneda.map jU)) (yoneda.map iU)).app (op T)) :=
    bijective_pullback_fst_app iU hU hVs ((Over.pullback (yoneda.map jU)).obj X) p
  obtain ⟨r, hr⟩ := hb.surjective z
  have hsq := ConcreteCategory.congr_hom (NatTrans.congr_app
    (Over.pullbackSquareObjIso_hom_left_fst w X) (op T)) r
  have hmU := ConcreteCategory.congr_hom (NatTrans.congr_app
    (Over.pullback_map_left_comp_fst (yoneda.map iU) mU) (op T)) r
  have hmW := ConcreteCategory.congr_hom (NatTrans.congr_app
    (Over.pullback_map_left_comp_fst (yoneda.map iW) mW) (op T))
    ((Over.pullbackSquareObjIso w X).hom.left.app (op T) r)
  have hkey := ConcreteCategory.congr_hom (NatTrans.congr_app
    (Over.pullbackSquare_map_left_fst w hcomm) (op T)) r
  simp only [NatTrans.comp_app, types_comp_apply, Over.pullback_obj_hom] at hsq hmU hmW hkey
  rw [← hz, ← hr, Over.pullbackSectionsMap_fst, ← hsq, Over.pullbackSectionsMap_fst,
    ← hmU, ← hmW]
  exact hkey

end PullbackSections

/-- A base change along a monomorphism of presheaves of types is a base change along the
inclusion of its range, the comparison being `CategoryTheory.Subfunctor.toRange`. -/
theorem IsPullback.of_toRange {F G H : Cᵒᵖ ⥤ Type v} {f : F ⟶ H} {p : G ⟶ H} [Mono p]
    {P : Cᵒᵖ ⥤ Type v} {a : P ⟶ F} {b : P ⟶ G} (h : IsPullback a b f p) :
    IsPullback a (b ≫ Subfunctor.toRange p) f (Subfunctor.range p).ι :=
  h.of_iso (Iso.refl P) (Iso.refl F) (asIso (Subfunctor.toRange p)) (Iso.refl H)
    (by simp) (by simp) (by simp) (by simp)

namespace Limits.Types

/-- If the second leg of an explicit fibre product of types is bijective, then the first
projection from the fibre product is bijective: the second coordinate of a compatible pair is
determined by the first. -/
theorem bijective_pullbackObj_fst {X Y Z : Type v} (f : X ⟶ Z) {g : Y ⟶ Z}
    (hg : Function.Bijective g) :
    Function.Bijective (fun p : Types.PullbackObj f g => p.1.1) := by
  refine ⟨fun p q h => ?_, fun x => ?_⟩
  · have h' : (p : X × Y).1 = (q : X × Y).1 := h
    refine Subtype.ext (Prod.ext h' (hg.injective ?_))
    rw [← p.2, ← q.2, h']
  · obtain ⟨y, hy⟩ := hg.surjective (f x)
    exact ⟨⟨⟨x, y⟩, hy.symm⟩, rfl⟩

end Limits.Types

end CategoryTheory

end
