module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing

/-!
# Mayer--Vietoris squares from a two-element covering of a subterminal object

The glueing results of
`StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing` are proved for a base `Z`
which is *terminal* in the ambient category. Stacks 0E91 needs Stacks 0E8Z at a base which is a
proper open `U ∪ W` of the base scheme, hence not terminal in the big fppf site, and the
terminality of `Z` is used there in two quite different ways.

The first use is inessential, and this file removes it. Terminality enters the construction of
the Mayer--Vietoris square attached to an object `X` only through
`CategoryTheory.IsTerminal.hom_ext`, to see that two morphisms `X ⟶ Z` agree; that is exactly
`CategoryTheory.IsSubterminal`, which holds of every open of the base scheme. So the cartesian
square `V ⨯ X, U ⨯ X, W ⨯ X, X` and the isomorphisms governing it are available over a
subterminal base.

The second use is essential and is *not* removed here: the covering property of the two
projections `U ⨯ X ⟶ X` and `W ⨯ X ⟶ X` is read off from the covering `jU, jW` of `Z` by
pulling it back along a morphism `X ⟶ Z`, and for terminal `Z` such a morphism exists for every
`X`. Over a subterminal base it must be supplied, so the lemmas below take it as an argument
`p : X ⟶ Z`. This is not a defect of the proof but of the formulation: the sections of an object
of `FP_Z` over `X` all map to `X ⟶ Z`, so the morphism is available wherever the sheaf condition
is actually applied, and the covering statement is false without it.

## Main results

* `CategoryTheory.IsSubterminal.of_mono`: an object admitting a monomorphism to a subterminal
  object is subterminal.
* `CategoryTheory.IsPullback.prod_map_snd_of_isSubterminal`: for a subterminal `Z` and `V` the
  fibre product of `U` and `W` over `Z`, the square `CategoryTheory.prodSquare` is cartesian.
* `CategoryTheory.isIso_prod_map_of_hom_of_isSubterminal`: for an object lying over `U`, the
  comparison `V ⨯ X ⟶ W ⨯ X` is an isomorphism.
* `CategoryTheory.GrothendieckTopology.ofTwoArrows_prod_snd_mem_of_hom`: for an object `X`
  *equipped with a morphism to `Z`*, the two projections generate a covering sieve of `X`.
* `CategoryTheory.GrothendieckTopology.mayerVietorisSquareProdOfHom` and
  `CategoryTheory.GrothendieckTopology.mayerVietorisSectionsEquivOfHom`: the Mayer--Vietoris
  square at such an `X`, and the resulting description of the sections of a sheaf over `X` as
  compatible pairs of sections over `U ⨯ X` and `W ⨯ X`.

Each of these specialises to the corresponding result of
`StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing` on taking `Z` terminal and
`p` the unique morphism; none of them is used to weaken a statement of that file.

## References

* [Stacks Project, Tag 0E8Z](https://stacks.math.columbia.edu/tag/0E8Z)
* [Stacks Project, Tag 0E91](https://stacks.math.columbia.edu/tag/0E91)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- An object admitting a monomorphism to a subterminal object is subterminal. This generalises
`CategoryTheory.isSubterminal_of_mono_isTerminal`, which assumes the target terminal. -/
theorem IsSubterminal.of_mono {Z U : C} (hZ : IsSubterminal Z) (j : U ⟶ Z) [Mono j] :
    IsSubterminal U := by
  intro T f g
  rw [← cancel_mono j]
  exact hZ _ _

section Square

variable [HasBinaryProducts C]

/-- **If `Z` is subterminal and `V` is a fibre product of `U` and `W` over `Z`, then for every
object `X` the square `CategoryTheory.prodSquare` is cartesian.** Terminality of `Z` is not
needed: it is used only to see that the two morphisms to `Z` out of a cone agree, which is
subterminality. -/
theorem IsPullback.prod_map_snd_of_isSubterminal {Z U W V : C} {jU : U ⟶ Z} {jW : W ⟶ Z}
    {iU : V ⟶ U} {iW : V ⟶ W} (hV : IsPullback iU iW jU jW) (hZ : IsSubterminal Z) (X : C) :
    IsPullback (prod.map iU (𝟙 X)) (prod.map iW (𝟙 X))
      (prod.snd : U ⨯ X ⟶ X) (prod.snd : W ⨯ X ⟶ X) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (by simp)
    (fun s => prod.lift (hV.lift (s.fst ≫ prod.fst) (s.snd ≫ prod.fst) (hZ _ _))
      (s.fst ≫ prod.snd)) (fun s => ?_) (fun s => ?_) (fun s m h₁ h₂ => ?_))
  · refine prod.hom_ext ?_ ?_ <;> simp
  · refine prod.hom_ext ?_ ?_ <;> simp [s.condition]
  · refine prod.hom_ext (hV.hom_ext ?_ ?_) ?_
    · simpa using congrArg (· ≫ prod.fst) h₁
    · simpa using congrArg (· ≫ prod.fst) h₂
    · simpa using congrArg (· ≫ prod.snd) h₁

/-- **For an object `X` lying over `U`, and `V` the intersection of `U` and `W` inside a
subterminal `Z`, the comparison `V ⨯ X ⟶ W ⨯ X` is an isomorphism**: the first coordinate of a
point of `W ⨯ X` already lies over `U` through `X`. This generalises
`CategoryTheory.isIso_prod_map_of_hom` from a terminal to a subterminal `Z`. -/
theorem isIso_prod_map_of_hom_of_isSubterminal {Z U W V : C} (hZ : IsSubterminal Z)
    (hU : IsSubterminal U) {jU : U ⟶ Z} {jW : W ⟶ Z} {iU : V ⟶ U} {iW : V ⟶ W}
    (hV : IsPullback iU iW jU jW) {X : C} (p : X ⟶ U) :
    IsIso (prod.map iW (𝟙 X) : V ⨯ X ⟶ W ⨯ X) := by
  refine ⟨prod.lift (hV.lift (prod.snd ≫ p) prod.fst (hZ _ _)) prod.snd,
    prod.hom_ext ?_ (by simp), prod.hom_ext (by simp) (by simp)⟩
  simp only [Category.assoc, prod.lift_fst, Category.id_comp]
  refine hV.hom_ext ?_ ?_
  · simp only [Category.assoc, IsPullback.lift_fst]
    exact hU _ _
  · simp

namespace GrothendieckTopology

variable (J : GrothendieckTopology C)

/-- **If the two morphisms `jU : U ⟶ Z` and `jW : W ⟶ Z` generate a covering sieve, then for
every object `X` equipped with a morphism to `Z` the two projections `U ⨯ X ⟶ X` and
`W ⨯ X ⟶ X` generate a covering sieve of `X`**: the sieve they generate contains the base change
of the given one along that morphism.

The morphism `p` is what replaces terminality of `Z` here, and it cannot be dispensed with: for
`X` admitting no morphism to `Z` the two projections need not cover `X`. -/
theorem ofTwoArrows_prod_snd_mem_of_hom {Z U W : C} {jU : U ⟶ Z} {jW : W ⟶ Z}
    (hcov : Sieve.ofTwoArrows jU jW ∈ J Z) {X : C} (p : X ⟶ Z) :
    Sieve.ofTwoArrows (prod.snd : U ⨯ X ⟶ X) (prod.snd : W ⨯ X ⟶ X) ∈ J X := by
  refine J.superset_covering ?_ (J.pullback_stable p hcov)
  rintro T g hg
  obtain ⟨(_ | _), a, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
  · exact (Sieve.mem_ofArrows_iff _ _ _).2
      ⟨WalkingPair.left, prod.lift a g, (prod.lift_snd a g).symm⟩
  · exact (Sieve.mem_ofArrows_iff _ _ _).2
      ⟨WalkingPair.right, prod.lift a g, (prod.lift_snd a g).symm⟩

variable [HasWeakSheafify J (Type v)]

/-- **The Mayer--Vietoris square attached to an object lying over a subterminal base covered by
two subobjects.** This is `CategoryTheory.GrothendieckTopology.mayerVietorisSquareProd` with
terminality of `Z` weakened to subterminality, at the cost of a morphism `p : X ⟶ Z`. -/
noncomputable def mayerVietorisSquareProdOfHom {Z U W V : C} (hZ : IsSubterminal Z)
    (hU : IsSubterminal U) (hW : IsSubterminal W) {jU : U ⟶ Z} {jW : W ⟶ Z} {iU : V ⟶ U}
    {iW : V ⟶ W} (hV : IsPullback iU iW jU jW) (hcov : Sieve.ofTwoArrows jU jW ∈ J Z) {X : C}
    (p : X ⟶ Z) : J.MayerVietorisSquare :=
  haveI : Mono (prodSquare iU iW X).f₂₄ := hU.mono_prod_snd X
  haveI : Mono (prodSquare iU iW X).f₃₄ := hW.mono_prod_snd X
  MayerVietorisSquare.mk_of_isPullback (J := J) (prodSquare iU iW X)
    (hV.prod_map_snd_of_isSubterminal hZ X) (J.ofTwoArrows_prod_snd_mem_of_hom hcov p)

/-- The underlying square of `mayerVietorisSquareProdOfHom` is `prodSquare iU iW X`, with vertices
`V ⨯ X`, `U ⨯ X`, `W ⨯ X` and `X`. -/
@[simp]
theorem mayerVietorisSquareProdOfHom_toSquare {Z U W V : C} (hZ : IsSubterminal Z)
    (hU : IsSubterminal U) (hW : IsSubterminal W) {jU : U ⟶ Z} {jW : W ⟶ Z} {iU : V ⟶ U}
    {iW : V ⟶ W} (hV : IsPullback iU iW jU jW) (hcov : Sieve.ofTwoArrows jU jW ∈ J Z) {X : C}
    (p : X ⟶ Z) :
    (J.mayerVietorisSquareProdOfHom hZ hU hW hV hcov p).toSquare = prodSquare iU iW X :=
  rfl

/-- **The sections of a sheaf over an object `X` lying over a subterminal base are the
compatible pairs of sections over `U ⨯ X` and over `W ⨯ X`.** This is the sheaf condition at the
Mayer--Vietoris square `CategoryTheory.GrothendieckTopology.mayerVietorisSquareProdOfHom`. -/
noncomputable def mayerVietorisSectionsEquivOfHom {Z U W V : C} (hZ : IsSubterminal Z)
    (hU : IsSubterminal U) (hW : IsSubterminal W) {jU : U ⟶ Z} {jW : W ⟶ Z} {iU : V ⟶ U}
    {iW : V ⟶ W} (hV : IsPullback iU iW jU jW) (hcov : Sieve.ofTwoArrows jU jW ∈ J Z) {X : C}
    (p : X ⟶ Z) {F : Cᵒᵖ ⥤ Type v} (hF : Presheaf.IsSheaf J F) :
    F.obj (op X) ≃
      Types.PullbackObj (F.map (prod.map iU (𝟙 X)).op) (F.map (prod.map iW (𝟙 X)).op) :=
  Equiv.ofBijective _
    (((J.mayerVietorisSquareProdOfHom hZ hU hW hV hcov p).sheafCondition_iff_bijective_toPullbackObj
        F).1
      (MayerVietorisSquare.sheafCondition_of_sheaf _ ⟨F, hF⟩))

end GrothendieckTopology

/-- **Two morphisms of the slice over the representable presheaf of a subterminal base which
have the same base change to a subterminal `U` agree on sections over `U ⨯ T`.** This is
`CategoryTheory.Over.app_prod_eq_of_pullback_map_eq` with terminality of `Z` weakened to
subterminality; terminality was used there only to see that `Z` is subterminal. -/
theorem Over.app_prod_eq_of_pullback_map_eq_of_isSubterminal {Z U : C} (hZ : IsSubterminal Z)
    (j : U ⟶ Z) (hU : IsSubterminal U) {X Y : Over (yoneda.obj Z : Cᵒᵖ ⥤ Type v)} {f g : X ⟶ Y}
    (h : (Over.pullback (yoneda.map j)).map f = (Over.pullback (yoneda.map j)).map g) (T : C) :
    f.left.app (op (U ⨯ T)) = g.left.app (op (U ⨯ T)) := by
  have h1 : pullback.fst X.hom (yoneda.map j) ≫ f.left =
      pullback.fst X.hom (yoneda.map j) ≫ g.left := by
    rw [← Over.pullback_map_left_comp_fst, ← Over.pullback_map_left_comp_fst, h]
  have hb := bijective_pullback_fst_app j hZ hU X (prod.fst : U ⨯ T ⟶ U)
  refine ConcreteCategory.hom_ext _ _ fun y => ?_
  obtain ⟨z, hz⟩ := hb.surjective y
  rw [← hz]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h1 (op (U ⨯ T))) z

end Square

end CategoryTheory

namespace AlgebraicGeometry.FinitePresentationSpacesOver

open CategoryTheory.SubterminalGlueing

attribute [local instance] BigFppfOver.hasSheafify_type

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Z U W V : BigFppfOver B S hS} (hZ : IsSubterminal Z) (hU : IsSubterminal U)
  (hW : IsSubterminal W) {jU : U ⟶ Z} {jW : W ⟶ Z} {iU : V ⟶ U} {iW : V ⟶ W}
  (hV : IsPullback iU iW jU jW)

/-! ### The Mayer--Vietoris square over a subterminal base -/

/-- **The Mayer--Vietoris square of an object of the big fppf site of `S` lying over a
subterminal base covered by two subobjects.** This is
`AlgebraicGeometry.FinitePresentationSpacesOver.mayerVietorisSquare` with terminality of the base
weakened to subterminality, at the cost of a morphism `p : X ⟶ Z`. -/
noncomputable def mayerVietorisSquareOfHom
    (hcov : Sieve.ofTwoArrows jU jW ∈ BigFppfOver.topology B S hS Z)
    {X : BigFppfOver B S hS} (p : X ⟶ Z) :
    (BigFppfOver.topology B S hS).MayerVietorisSquare :=
  (BigFppfOver.topology B S hS).mayerVietorisSquareProdOfHom hZ hU hW hV hcov p

/-- The sheaf condition of an fppf sheaf at the Mayer--Vietoris square of an object lying over a
subterminal base. -/
theorem sheafCondition_mayerVietorisSquareOfHom
    (hcov : Sieve.ofTwoArrows jU jW ∈ BigFppfOver.topology B S hS Z)
    {X : BigFppfOver B S hS} (p : X ⟶ Z) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) :
    (mayerVietorisSquareOfHom B S hS hZ hU hW hV hcov p).SheafCondition F :=
  CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sheafCondition_of_sheaf _ ⟨F, hF⟩

/-! ### Faithfulness of the comparison functor over a subterminal base -/

include hZ hU hW hV in
/-- **A morphism from a presheaf lying over the representable presheaf of a subterminal base
into an fppf sheaf is determined by its restrictions along the products with `U` and with `W`.**

This is `AlgebraicGeometry.FinitePresentationSpacesOver.natTrans_ext_of_prod_app` over a
subterminal base. The morphism `X ⟶ Z` that the Mayer--Vietoris square needs, and which is free
when `Z` is terminal, is produced from the structure morphism `ζ` of the source: a section of `F`
over `X` maps to a morphism `X ⟶ Z`, and that is exactly the object at which the sheaf condition
has to be applied. -/
theorem natTrans_ext_of_prod_app_of_isSubterminal
    (hcov : Sieve.ofTwoArrows jU jW ∈ BigFppfOver.topology B S hS Z)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (ζ : F ⟶ yoneda.obj Z)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G) {α β : F ⟶ G}
    (hαU : ∀ T : BigFppfOver B S hS, α.app (op (U ⨯ T)) = β.app (op (U ⨯ T)))
    (hαW : ∀ T : BigFppfOver B S hS, α.app (op (W ⨯ T)) = β.app (op (W ⨯ T))) : α = β := by
  refine NatTrans.ext (funext fun T => ConcreteCategory.hom_ext _ _ fun x => ?_)
  have key (A : BigFppfOver B S hS) (hA : ∀ T : BigFppfOver B S hS,
      α.app (op (A ⨯ T)) = β.app (op (A ⨯ T))) :
      G.map (prod.snd : A ⨯ T.unop ⟶ T.unop).op (α.app T x) =
        G.map (prod.snd : A ⨯ T.unop ⟶ T.unop).op (β.app T x) := by
    rw [← NatTrans.naturality_apply α, ← NatTrans.naturality_apply β,
      ConcreteCategory.congr_hom (hA T.unop) _]
  refine (sheafCondition_mayerVietorisSquareOfHom B S hS hZ hU hW hV hcov
    (ζ.app T x : T.unop ⟶ Z) hG).ext (key U hαU) (key W hαW)

include hZ hU hW hV in
/-- **A morphism of the slice over the representable presheaf of a subterminal base is
determined by its base changes to `U` and to `W`.** This is
`AlgebraicGeometry.FinitePresentationSpacesOver.over_hom_ext_of_pullback_map_eq` over a
subterminal base; the morphism to `Z` required by the Mayer--Vietoris square is the structure
morphism of the source. -/
theorem over_hom_ext_of_pullback_map_eq_of_isSubterminal
    (hcov : Sieve.ofTwoArrows jU jW ∈ BigFppfOver.topology B S hS Z)
    {X Y : Over (yoneda.obj Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y.left) {f g : X ⟶ Y}
    (hfgU : (Over.pullback (yoneda.map jU)).map f = (Over.pullback (yoneda.map jU)).map g)
    (hfgW : (Over.pullback (yoneda.map jW)).map f = (Over.pullback (yoneda.map jW)).map g) :
    f = g := by
  refine Over.OverMorphism.ext ?_
  refine natTrans_ext_of_prod_app_of_isSubterminal B S hS hZ hU hW hV hcov X.hom hY ?_ ?_
  · exact Over.app_prod_eq_of_pullback_map_eq_of_isSubterminal hZ jU hU hfgU
  · exact Over.app_prod_eq_of_pullback_map_eq_of_isSubterminal hZ jW hW hfgW

include hZ hU hW in
/-- **The comparison functor into the `2`-fibre product is faithful over a subterminal base.**
Two morphisms with the same base changes to `U` and to `W` agree, because the target is a sheaf
and the two projections `U ⨯ T ⟶ T` and `W ⨯ T ⟶ T` form a Mayer--Vietoris square at every
object lying over the base.

This is `AlgebraicGeometry.FinitePresentationSpacesOver.faithful_glueingFunctor` with terminality
of the base weakened to subterminality, which is what Stacks 0E91 needs at a stage
`Z i = U ∪ W i`. -/
theorem faithful_glueingFunctor_of_isSubterminal
    (hcov : Sieve.ofTwoArrows jU jW ∈ BigFppfOver.topology B S hS Z) :
    Functor.Faithful (glueingFunctor B S hS hV.w) where
  map_injective {X Y} {f g} h := by
    refine (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS Z)).map_injective ?_
    refine over_hom_ext_of_pullback_map_eq_of_isSubterminal B S hS hZ hU hW hV hcov
      Y.property.1.isSheaf ?_ ?_
    · exact congrArg (fun m => (ObjectProperty.ι
        (IsFinitePresentationSpaceOver B S hS U)).map m.hom.left) h
    · exact congrArg (fun m => (ObjectProperty.ι
        (IsFinitePresentationSpaceOver B S hS W)).map m.hom.right) h

end AlgebraicGeometry.FinitePresentationSpacesOver

end
