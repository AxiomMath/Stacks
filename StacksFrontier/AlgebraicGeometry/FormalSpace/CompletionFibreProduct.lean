module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Completion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Modifications
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.OpenSubspaces

/-!
# Completion along a set of points commutes with fibre products

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a presheaf on the big fppf
site of `S` and let `T` be a set of points of `X`. For a morphism `h : Y ⟶ X` write
`Y_{/T} = Y_{/|h|⁻¹T}` for the completion of `Y` along the inverse image of `T`.

Completion carries a cartesian square of presheaves over `X` to a cartesian square of
completions: if `P = X' ×_X X₁` and `T₁ = |X₁ → X|⁻¹T`, then
`P_{/T} = X'_{/T} ×_{X_{/T}} X_{1, /T_1}`. Equivalently the completion of a base change is the
base change of the completion along `X_{1, /T_1} ⟶ X_{/T}`.

Base change along a morphism `X₁ ⟶ X` of algebraic spaces also carries the category of
algebraic spaces locally of finite type over `X` which are isomorphisms over a subspace
`W₀ ⊂ X` to the corresponding category over `X₁` and the inverse image of `W₀`; for
`W₀ = U` the open subspace with `|U| = |X| ∖ T` the inverse image is the open subspace with
point set the complement of `T₁`.

## Main results

* `AlgebraicGeometry.Space.isPullback_completionSheafMap_of_isPullback`: the completion of a
  cartesian square of presheaves is a cartesian square of completions.
* `AlgebraicGeometry.Space.completionBaseChangeIso`: the completion of the base change
  `X' ×_X X₁ ⟶ X₁` is the base change of `X'_{/T} ⟶ X_{/T}` along `X_{1, /T_1} ⟶ X_{/T}`.
* `AlgebraicGeometry.Space.finiteTypeBaseChangeFunctor`: base change on the categories of
  finite-type modifications, with
  `AlgebraicGeometry.Space.preimage_openSubspaceOfPoints_compl` identifying the subspace
  outside of which the target category is taken.
* `AlgebraicGeometry.Space.completionFiniteTypeBaseChangeIso`: the two preceding results
  combined, for a finite-type modification of `X` outside the open subspace with point set
  `Tᶜ`.
* `AlgebraicGeometry.Space.finiteTypeBaseChangePointsFunctor`: base change on the finite-type
  modifications outside the open subspaces cut out by `Tᶜ` and `T₁ᶜ`, with
  `AlgebraicGeometry.Space.finiteTypeBaseChangePointsFunctorCompιIso` identifying it with the
  pullback functor on the ambient slices.

## References

* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
* [Stacks Project, Tag 0APV](https://stacks.math.columbia.edu/tag/0APV)
* [Stacks Project, Tag 0AS2](https://stacks.math.columbia.edu/tag/0AS2)
* [Stacks Project, Tag 03XH](https://stacks.math.columbia.edu/tag/03XH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/- Instance search for pullbacks of presheaves on the big fppf site times out under
Lean v4.35.0, so use the shortcut instances declared in `Spaces.Morphisms.Unramified`. -/
/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search for
them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_CompletionFibreProduct :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  CategoryTheory.Limits.functorCategoryHasLimitsOfShape

/-- The pullback of two morphisms of presheaves on the big fppf site over `S`. -/
local instance (priority := high) hasPullback_presheaf_CompletionFibreProduct
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### The two descriptions of the points of a fibre product lying over `T` -/

/-- For a commutative square the two inverse images of a set of points of the corner along the
two routes through the square agree. -/
theorem preimage_pointsMap_eq_of_comm {P X' X₁ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : P ⟶ X'} {q : P ⟶ X₁} {f : X' ⟶ X} {g : X₁ ⟶ X} (hw : p ≫ f = q ≫ g)
    (T : Set (points B S hS X)) :
    pointsMap B S hS P p ⁻¹' (pointsMap B S hS X' f ⁻¹' T) =
      pointsMap B S hS P q ⁻¹' (pointsMap B S hS X₁ g ⁻¹' T) := by
  rw [← Set.preimage_comp, ← Set.preimage_comp, ← pointsMap_comp, ← pointsMap_comp, hw]

/-! ### The ambient sheaves of a cartesian square -/

/-- The sheafified universe lift of a cartesian square of presheaves is cartesian. -/
theorem isPullback_sheafifiedULiftMap_of_isPullback {P X' X₁ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : P ⟶ X'} {q : P ⟶ X₁} {f : X' ⟶ X} {g : X₁ ⟶ X} (hp : IsPullback p q f g) :
    IsPullback (sheafifiedULiftMap B S hS p) (sheafifiedULiftMap B S hS q)
      (sheafifiedULiftMap B S hS f) (sheafifiedULiftMap B S hS g) :=
  (hp.map ((Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u)
      (Type (u + 1))).obj uliftFunctor.{u + 1})).map
    (plusPlusSheaf (BigFppfOver.topology B S hS) (Type (u + 1)))

/-- Transporting a completion along an equality of the sets of points it is taken along is
compatible with the inclusion into the ambient sheaf. -/
theorem completionSheafInclusion_transport (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {A A' : Set (points B S hS X)} (h : A = A') :
    eqToHom (congrArg (completionSheaf B S hS X) h) ≫ completionSheafInclusion B S hS X A' =
      completionSheafInclusion B S hS X A := by
  subst h
  simp

/-! ### Completion of a cartesian square -/

/-- For a cartesian square of presheaves on the big fppf site of `S` exhibiting `P` as
`X' ×_X X₁`, and a set `T` of points of `X`, the induced square of completions is cartesian:
`P_{/T} = X'_{/T} ×_{X_{/T}} X_{1, /T_1}`. -/
theorem isPullback_completionSheafMap_of_isPullback
    {P X' X₁ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : P ⟶ X'} {q : P ⟶ X₁} {f : X' ⟶ X} {g : X₁ ⟶ X} (hp : IsPullback p q f g)
    (T : Set (points B S hS X)) :
    IsPullback (completionSheafMap B S hS p (pointsMap B S hS X' f ⁻¹' T))
      (eqToHom (congrArg (completionSheaf B S hS P)
          (preimage_pointsMap_eq_of_comm B S hS hp.w T)) ≫
        completionSheafMap B S hS q (pointsMap B S hS X₁ g ⁻¹' T))
      (completionSheafMap B S hS f T) (completionSheafMap B S hS g T) := by
  have hT := preimage_pointsMap_eq_of_comm B S hS hp.w T
  set jA := completionSheafInclusion B S hS P
    (pointsMap B S hS P p ⁻¹' (pointsMap B S hS X' f ⁻¹' T))
  set jA' := completionSheafInclusion B S hS P
    (pointsMap B S hS P q ⁻¹' (pointsMap B S hS X₁ g ⁻¹' T))
  set jX' := completionSheafInclusion B S hS X' (pointsMap B S hS X' f ⁻¹' T)
  set jX₁ := completionSheafInclusion B S hS X₁ (pointsMap B S hS X₁ g ⁻¹' T)
  set jX := completionSheafInclusion B S hS X T
  set u := completionSheafMap B S hS p (pointsMap B S hS X' f ⁻¹' T)
  set v₀ := completionSheafMap B S hS q (pointsMap B S hS X₁ g ⁻¹' T)
  set r := completionSheafMap B S hS f T
  set s := completionSheafMap B S hS g T
  set α := sheafifiedULiftMap B S hS p
  set β := sheafifiedULiftMap B S hS q
  set γ := sheafifiedULiftMap B S hS f
  set δ := sheafifiedULiftMap B S hS g
  set e := eqToHom (congrArg (completionSheaf B S hS P) hT)
  have hA : IsPullback jA u α jX' := isPullback_completionSheafMap B S hS p _
  have hA' : IsPullback jA' v₀ β jX₁ := isPullback_completionSheafMap B S hS q _
  have hX' : IsPullback jX' r γ jX := isPullback_completionSheafMap B S hS f T
  have hX₁ : IsPullback jX₁ s δ jX := isPullback_completionSheafMap B S hS g T
  have hU : IsPullback α β γ δ := isPullback_sheafifiedULiftMap_of_isPullback B S hS hp
  have he : e ≫ jA' = jA := completionSheafInclusion_transport B S hS P hT
  have : Mono jX := mono_completionSheafInclusion B S hS X T
  have hleft : (e ≫ v₀) ≫ jX₁ = jA ≫ β := by
    rw [Category.assoc, ← hA'.w, ← Category.assoc, he]
  have hstep : IsPullback u ((e ≫ v₀) ≫ jX₁) (r ≫ jX) δ := by
    rw [hleft, ← hX'.w]
    exact hA.flip.paste_vert hU
  have hcomm : u ≫ r = (e ≫ v₀) ≫ s := by
    refine (cancel_mono jX).1 ?_
    simpa only [Category.assoc, ← hX₁.w] using hstep.w
  exact hstep.of_bot hcomm hX₁.flip

/-- The completion along `T₁ = |X₁ → X|⁻¹T` of the projection `X' ×_X X₁ ⟶ X₁` is the base
change of `X'_{/T} ⟶ X_{/T}` along `X_{1, /T_1} ⟶ X_{/T}`, as objects over `X_{1, /T_1}`. -/
def completionBaseChangeIso {X' X₁ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X)
    (g : X₁ ⟶ X) (T : Set (points B S hS X)) :
    Over.mk (completionSheafMap B S hS (pullback.snd f g)
        (pointsMap B S hS X₁ g ⁻¹' T)) ≅
      (Over.pullback (completionSheafMap B S hS g T)).obj
        (Over.mk (completionSheafMap B S hS f T)) :=
  let hCart := isPullback_completionSheafMap_of_isPullback B S hS
    (IsPullback.of_hasPullback f g) T
  Over.isoMk ((eqToIso (congrArg (completionSheaf B S hS (pullback f g))
      (preimage_pointsMap_eq_of_comm B S hS (IsPullback.of_hasPullback f g).w T))).symm ≪≫
    hCart.isoPullback) (by simp [hCart.isoPullback_hom_snd])

/-! ### Base change of the finite-type modifications -/

variable {B S hS}

/-- Base change of a finite-type modification of `W` outside `W₀` along a morphism `V ⟶ W` of
algebraic spaces is a finite-type modification of `V` outside the inverse image of `W₀`. -/
theorem isFiniteTypeModification_pullback {V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) (hW : IsAlgebraicSpace B S hS W) (g : V ⟶ W)
    (W₀ : Subfunctor W) {M : Over W} (hM : IsFiniteTypeModification B S hS W₀ M) :
    IsFiniteTypeModification B S hS (W₀.preimage g) ((Over.pullback g).obj M) :=
  ⟨⟨isAlgebraicSpace_pullback B S hS M.hom g hM.1.1 hV hW,
      isIso_pullback_snd_preimage B S hS M.hom g W₀ hM.1.2⟩,
    IsLocallyOfFiniteType.of_isPullback B S hS (IsPullback.of_hasPullback M.hom g).flip
      hM.1.1 hW hM.2⟩

/-- Base change along a morphism `V ⟶ W` of algebraic spaces, as a functor from the
finite-type modifications of `W` outside `W₀` to those of `V` outside the inverse image of
`W₀`. -/
def finiteTypeBaseChangeFunctor {V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) (hW : IsAlgebraicSpace B S hS W) (g : V ⟶ W)
    (W₀ : Subfunctor W) :
    FiniteTypeModification B S hS W₀ ⥤ FiniteTypeModification B S hS (W₀.preimage g) :=
  ObjectProperty.lift _
    (ObjectProperty.ι (IsFiniteTypeModification B S hS W₀) ⋙ Over.pullback g)
    fun M ↦ isFiniteTypeModification_pullback hV hW g W₀ M.property

/-- The base-change functor on finite-type modifications is the pullback functor on the
ambient slice categories. -/
def finiteTypeBaseChangeFunctorCompιIso {V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) (hW : IsAlgebraicSpace B S hS W) (g : V ⟶ W)
    (W₀ : Subfunctor W) :
    finiteTypeBaseChangeFunctor hV hW g W₀ ⋙
        ObjectProperty.ι (IsFiniteTypeModification B S hS (W₀.preimage g)) ≅
      ObjectProperty.ι (IsFiniteTypeModification B S hS W₀) ⋙ Over.pullback g :=
  ObjectProperty.liftCompιIso _ _ _

/-- The inverse image of the open subspace with point set `Tᶜ` is the open subspace with point
set the complement of the inverse image of `T`. -/
theorem preimage_openSubspaceOfPoints_compl {X₁ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : X₁ ⟶ X) (T : Set (points B S hS X)) :
    (openSubspaceOfPoints B S hS X Tᶜ).preimage g =
      openSubspaceOfPoints B S hS X₁ (pointsMap B S hS X₁ g ⁻¹' T)ᶜ := by
  rw [preimage_openSubspaceOfPoints, Set.preimage_compl]

/-- For a finite-type modification `M` of `X` outside the open subspace with point set `Tᶜ`,
the completion along `T₁ = |g|⁻¹T` of the base change of `M` along `g : X₁ ⟶ X` is the base
change along `X_{1, /T_1} ⟶ X_{/T}` of the completion of `M` along `T`. -/
def completionFiniteTypeBaseChangeIso {X₁ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX₁ : IsAlgebraicSpace B S hS X₁) (hX : IsAlgebraicSpace B S hS X) (g : X₁ ⟶ X)
    (T : Set (points B S hS X))
    (M : FiniteTypeModification B S hS (openSubspaceOfPoints B S hS X Tᶜ)) :
    Over.mk (completionSheafMap B S hS
        (((finiteTypeBaseChangeFunctor hX₁ hX g
          (openSubspaceOfPoints B S hS X Tᶜ)).obj M).obj.hom)
        (pointsMap B S hS X₁ g ⁻¹' T)) ≅
      (Over.pullback (completionSheafMap B S hS g T)).obj
        (Over.mk (completionSheafMap B S hS M.obj.hom T)) :=
  completionBaseChangeIso B S hS M.obj.hom g T

/-! ### Base change read through a presentation of the target subfunctor -/

/-- Base change of the finite-type modifications of `W` outside `W₀` along a morphism
`g : V ⟶ W` of algebraic spaces, landing in the modifications of `V` outside a subfunctor `V₀`
presented as the inverse image of `W₀`. -/
def finiteTypeBaseChangeFunctorOfEq {V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) (hW : IsAlgebraicSpace B S hS W) (g : V ⟶ W)
    (W₀ : Subfunctor W) (V₀ : Subfunctor V) (h : W₀.preimage g = V₀) :
    FiniteTypeModification B S hS W₀ ⥤ FiniteTypeModification B S hS V₀ :=
  h ▸ finiteTypeBaseChangeFunctor hV hW g W₀

/-- Base change on finite-type modifications, read through a presentation of the target
subfunctor as an inverse image, is the pullback functor on the ambient slice categories. -/
def finiteTypeBaseChangeFunctorOfEqCompιIso {V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) (hW : IsAlgebraicSpace B S hS W) (g : V ⟶ W)
    (W₀ : Subfunctor W) (V₀ : Subfunctor V) (h : W₀.preimage g = V₀) :
    finiteTypeBaseChangeFunctorOfEq hV hW g W₀ V₀ h ⋙
        ObjectProperty.ι (IsFiniteTypeModification B S hS V₀) ≅
      ObjectProperty.ι (IsFiniteTypeModification B S hS W₀) ⋙ Over.pullback g := by
  subst h
  exact finiteTypeBaseChangeFunctorCompιIso hV hW g W₀

/-- Base change along `g : X₁ ⟶ X` of the finite-type modifications of `X` outside the open
subspace with point set `Tᶜ`, as a functor to the modifications of `X₁` outside the open
subspace with point set the complement of `T₁ = |g|⁻¹T`. -/
def finiteTypeBaseChangePointsFunctor {X₁ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX₁ : IsAlgebraicSpace B S hS X₁) (hX : IsAlgebraicSpace B S hS X) (g : X₁ ⟶ X)
    (T : Set (points B S hS X)) :
    FiniteTypeModification B S hS (openSubspaceOfPoints B S hS X Tᶜ) ⥤
      FiniteTypeModification B S hS
        (openSubspaceOfPoints B S hS X₁ (pointsMap B S hS X₁ g ⁻¹' T)ᶜ) :=
  finiteTypeBaseChangeFunctorOfEq hX₁ hX g _ _ (preimage_openSubspaceOfPoints_compl g T)

/-- Base change on the finite-type modifications outside the open subspaces with point sets
`Tᶜ` and `T₁ᶜ` is the pullback functor on the ambient slice categories. -/
def finiteTypeBaseChangePointsFunctorCompιIso {X₁ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX₁ : IsAlgebraicSpace B S hS X₁) (hX : IsAlgebraicSpace B S hS X) (g : X₁ ⟶ X)
    (T : Set (points B S hS X)) :
    finiteTypeBaseChangePointsFunctor hX₁ hX g T ⋙
        ObjectProperty.ι (IsFiniteTypeModification B S hS
          (openSubspaceOfPoints B S hS X₁ (pointsMap B S hS X₁ g ⁻¹' T)ᶜ)) ≅
      ObjectProperty.ι (IsFiniteTypeModification B S hS
          (openSubspaceOfPoints B S hS X Tᶜ)) ⋙ Over.pullback g :=
  finiteTypeBaseChangeFunctorOfEqCompιIso hX₁ hX g _ _
    (preimage_openSubspaceOfPoints_compl g T)

end AlgebraicGeometry.Space

end
