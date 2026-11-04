module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRepresentableLimits
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraicityOnBaseCover
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleStructureSheaf

/-!
# Systems of equations in global functions are affine of finite presentation over the base

Let `Y` be an algebraic space over `S`.  The last step of the proof of Stacks 0DLC presents the
functor `F(V) = Hom(K_V, E_V)`, over an affine base, as the kernel of a map
`Γ(V, 𝒪_V)^{m₀} ⟶ Γ(V, 𝒪_V)^{m₁}`, that is as the fibre product
`Y ×_{0, 𝔸^{m₁}_Y} 𝔸^{m₀}_Y`, "which proves what we want".  This file proves what that
sentence uses: the functor `T ↦ Γ(T, 𝒪_T)ⁿ` on the test schemes over `Y` is an algebraic space
affine and of finite presentation over `Y` (it is `𝔸ⁿ_Y`), and so is the kernel of any morphism
`Γ(-, 𝒪)^m ⟶ Γ(-, 𝒪)^{m'}` of functors on the test schemes, natural in the test scheme.

## Main definitions

* `CategoryTheory.FunctorToTypes.pow`: the pointwise `n`-th power of a functor to types.
* `CategoryTheory.FunctorToTypes.fibre`: the fibre of a morphism of functors to types over a
  section of its target.
* `AlgebraicGeometry.Space.yonedaProdSpace` and `AlgebraicGeometry.Space.yonedaProdProjection`:
  the restriction `h_a × Y` of `Y` to an object `a` of the site, and its projection to `Y`.
* `AlgebraicGeometry.Space.structureFunctionsFunctor`: `T ↦ Γ(T, 𝒪_T)` on the test schemes
  over `Y`.
* `AlgebraicGeometry.Space.coordinateFunctor`: `T ↦ Γ(T, 𝒪_T)ⁿ`, and
  `AlgebraicGeometry.Space.coordinateKernel`: the kernel of a morphism of coordinate functors.

## Main results

* `AlgebraicGeometry.Space.yonedaProdPointsIso`: the points of `h_a × Y` over `Y` are the
  points of `a`.
* `AlgebraicGeometry.Space.isAffineFinitePresentationAlgebraicSpaceOver_yoneda`: the points of an
  object of the site affine and of finite presentation over `S` are an algebraic space affine and
  of finite presentation over `Y`.
* `AlgebraicGeometry.Space.isAffineFinitePresentationAlgebraicSpaceOver_structureFunctionsFunctor`
  and `AlgebraicGeometry.Space.isAffineFinitePresentationAlgebraicSpaceOver_coordinateFunctor`:
  `𝔸¹_Y` and `𝔸ⁿ_Y`.
* `AlgebraicGeometry.Space.IsAffineFinitePresentationAlgebraicSpaceOver.pow` and
  `AlgebraicGeometry.Space.IsAffineFinitePresentationAlgebraicSpaceOver.fibre`: pointwise powers,
  and fibres over sections, of algebraic spaces affine and of finite presentation over `Y`.
* `AlgebraicGeometry.Space.isAffineFinitePresentationAlgebraicSpaceOver_coordinateKernel`: the
  kernel of a morphism `Γ(-, 𝒪)^m ⟶ Γ(-, 𝒪)^{m'}` is affine and of finite presentation over `Y`.

## Implementation notes

`𝔸¹_Y` is the restriction `h_{𝔸¹_S} × Y`; its projection to `Y` is the base change of
`𝔸¹_S ⟶ S` along `Y ⟶ S` (`AlgebraicGeometry.Space.isPullback_prod_fst_snd_yoneda_obj`), so it
is affine (Stacks 03WI) and of finite presentation (Stacks 03XR) because `𝔸¹_S ⟶ S` is.  Its
points over `Y` at a test scheme `T` are the morphisms `T ⟶ 𝔸¹_S`, which are the global functions
on `T` by `AlgebraicGeometry.Space.gammaAffineLineIso`.  Powers and kernels are fibre products,
handled by `AlgebraicGeometry.Space.IsAffineFinitePresentationAlgebraicSpaceOver.of_isPullback`.

## References

* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
* [Stacks Project, Tag 03WI](https://stacks.math.columbia.edu/tag/03WI)
* [Stacks Project, Tag 03XR](https://stacks.math.columbia.edu/tag/03XR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.FunctorToTypes

universe v w t

variable {C : Type w} [Category.{t} C]

/-- **The pointwise `n`-th power of a functor to types**, `X ↦ Rⁿ(X) = (Fin n → R(X))`. -/
def pow (R : C ⥤ Type v) (n : ℕ) : C ⥤ Type v where
  obj X := Fin n → R.obj X
  map f := ↾fun x i => R.map f (x i)
  map_id X := congrArg TypeCat.ofHom (funext fun x => funext fun i => R.map_id_apply X (x i))
  map_comp f g :=
    congrArg TypeCat.ofHom (funext fun x => funext fun i => R.map_comp_apply f g (x i))

/-- The `(n + 1)`-st pointwise power of a functor to types is its pointwise product with the
`n`-th: a tuple is its first entry together with its tail. -/
def powSuccIso (R : C ⥤ Type v) (n : ℕ) : pow R (n + 1) ≅ prod R (pow R n) :=
  NatIso.ofComponents (fun X => (Fin.consEquiv fun _ => R.obj X).symm.toIso) (fun _ => rfl)

/-- The zeroth pointwise power of a functor to types is terminal. -/
def isTerminalPowZero (R : C ⥤ Type v) : IsTerminal (pow R 0) :=
  IsTerminal.ofUniqueHom
    (fun _ => { app := fun _ => ↾fun _ => finZeroElim
                naturality := fun _ _ _ => congrArg TypeCat.ofHom
                  (funext fun _ => funext fun i => i.elim0) })
    (fun _ _ => NatTrans.ext (funext fun _ => congrArg TypeCat.ofHom
      (funext fun _ => funext fun i => i.elim0)))

/-- **The fibre of a morphism of functors to types over a section**: for `c : P ⟶ Q` and a
section `σ` of `Q`, the functor `X ↦ {x ∈ P(X) | c(x) = σ(X)}`.  For `σ` a zero section this is
the kernel of `c`. -/
def fibre {P Q : C ⥤ Type v} (c : P ⟶ Q) (σ : (Functor.const C).obj PUnit.{v + 1} ⟶ Q) :
    C ⥤ Type v where
  obj X := {x : P.obj X // c.app X x = σ.app X PUnit.unit}
  map {X Y} f := ↾fun x => ⟨P.map f x.1, by
    rw [NatTrans.naturality_apply, x.2, ← NatTrans.naturality_apply]
    rfl⟩
  map_id X := congrArg TypeCat.ofHom (funext fun x => Subtype.ext (P.map_id_apply X x.1))
  map_comp f g := congrArg TypeCat.ofHom (funext fun x => Subtype.ext (P.map_comp_apply f g x.1))

/-- The inclusion of the fibre of `c` over `σ` into the source of `c`. -/
def fibreι {P Q : C ⥤ Type v} (c : P ⟶ Q) (σ : (Functor.const C).obj PUnit.{v + 1} ⟶ Q) :
    fibre c σ ⟶ P where
  app _ := ↾fun x => x.1

/-- The morphism from the fibre of `c` over `σ` to the terminal functor. -/
def fibreToPUnit {P Q : C ⥤ Type v} (c : P ⟶ Q) (σ : (Functor.const C).obj PUnit.{v + 1} ⟶ Q) :
    fibre c σ ⟶ (Functor.const C).obj PUnit.{v + 1} where
  app _ := ↾fun _ => PUnit.unit

/-- **The fibre of `c` over `σ` is the fibre product of `c` and `σ`.** -/
theorem isPullback_fibre {P Q : C ⥤ Type v} (c : P ⟶ Q)
    (σ : (Functor.const C).obj PUnit.{v + 1} ⟶ Q) :
    IsPullback (fibreι c σ) (fibreToPUnit c σ) c σ :=
  IsPullback.of_forall_isPullback_app fun _ => (Types.isPullback_iff _ _ _ _).2
    ⟨congrArg TypeCat.ofHom (funext fun x => x.2),
      fun _ _ h => Subtype.ext h.1,
      fun x _ hx => ⟨⟨x, hx⟩, rfl, rfl⟩⟩

end CategoryTheory.FunctorToTypes

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section ProdPoints

variable {Y : AlgebraicSpaces B S hS} (a : BigFppfOver B S hS)

/-- The restriction `h_a × Y` of an algebraic space `Y` to an object `a` of the site, as an
algebraic space. -/
abbrev yonedaProdSpace : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj a ⨯ Y.obj, isAlgebraicSpace_prod_yoneda_obj a Y.property⟩

/-- The projection `h_a × Y ⟶ Y`. -/
abbrev yonedaProdProjection : yonedaProdSpace (Y := Y) a ⟶ Y :=
  ObjectProperty.homMk prod.snd

/-- The structure morphism of a test scheme over `Y`, as a morphism of presheaves out of the
representable presheaf of its underlying object of the site. -/
abbrev testHom (T : SchemesOver Y) : yoneda.obj T.left ⟶ Y.obj := T.hom.hom

/-- The points over `Y` of the restriction `h_a × Y` at a test scheme `T` are the morphisms
`T ⟶ a` of the site. -/
def yonedaProdPointsEquiv (T : SchemesOver Y) :
    spacePointsOverObj (yonedaProdProjection (Y := Y) a) T ≃ (T.left ⟶ a) where
  toFun x := (prod.fst : yoneda.obj a ⨯ Y.obj ⟶ _).app (Opposite.op T.left) x.1
  invFun φ := ⟨yonedaEquiv (prod.lift (yoneda.map φ) (testHom T)), by
    change (prod.snd : yoneda.obj a ⨯ Y.obj ⟶ _).app _ (yonedaEquiv _) = yonedaEquiv (testHom T)
    rw [← yonedaEquiv_comp, prod.lift_snd]⟩
  left_inv x := by
    refine Subtype.ext (yonedaEquiv.symm.injective ?_)
    rw [Equiv.symm_apply_apply]
    apply prod.hom_ext
    · rw [prod.lift_fst, yonedaEquiv_symm_naturality_right]
      exact (yonedaEquiv.eq_symm_apply.2 (yonedaEquiv_yoneda_map _)).symm
    · rw [prod.lift_snd, yonedaEquiv_symm_naturality_right]
      exact ((congrArg yonedaEquiv.symm x.2).trans (yonedaEquiv_symm_testPoint T)).symm
  right_inv φ := by
    change (prod.fst : yoneda.obj a ⨯ Y.obj ⟶ _).app _ (yonedaEquiv _) = φ
    rw [← yonedaEquiv_comp, prod.lift_fst]
    exact yonedaEquiv_yoneda_map φ

/-- **The points over `Y` of the restriction `h_a × Y` are the points of `a`**, naturally in the
test scheme. -/
def yonedaProdPointsIso :
    spacePointsOver (yonedaProdProjection (Y := Y) a) ≅
      (CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y).op ⋙ yoneda.obj a :=
  NatIso.ofComponents (fun T => (yonedaProdPointsEquiv a T.unop).toIso) (by
    intro T T' g
    ext x
    exact NatTrans.naturality_apply (prod.fst : yoneda.obj a ⨯ Y.obj ⟶ _) g.unop.left.op x.1)

/-- The projection `h_a × Y ⟶ Y` is affine when the structure morphism of `a` is. -/
theorem isAffineHom_yonedaProdProjection
    (ha : _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from a))) :
    IsAffineHom B S hS (yonedaProdProjection (Y := Y) a).hom :=
  isAffineHom_of_isPullback (isPullback_prod_fst_snd_yoneda_obj a Y.obj)
    (isAffineHom_of_presheaf (presheaf_yoneda_map_of_inverseImage B S hS inferInstance _ ha))

/-- The projection `h_a × Y ⟶ Y` is of finite presentation when the structure morphism of `a`
is. -/
theorem isFinitePresentation_yonedaProdProjection
    (ha : FinitePresentation ((BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from a))) :
    IsFinitePresentation B S hS (yonedaProdProjection (Y := Y) a).hom :=
  IsFinitePresentation.of_isPullback B S hS (isAlgebraicSpace_prod_yoneda_obj a Y.property)
    (isAlgebraicSpace_yoneda B S hS a) Y.property (isAlgebraicSpace_yoneda B S hS _)
    (isPullback_prod_fst_snd_yoneda_obj a Y.obj) (isFinitePresentation_yoneda_map B S hS _ ha)

/-- **The points of an object of the site affine and of finite presentation over `S` form an
algebraic space affine and of finite presentation over every `Y`**: the functor
`T ↦ Hom(T, a)` on the test schemes over `Y` is represented by `h_a × Y`. -/
theorem isAffineFinitePresentationAlgebraicSpaceOver_yoneda
    (ha : _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from a)))
    (ha' : FinitePresentation ((BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from a))) :
    IsAffineFinitePresentationAlgebraicSpaceOver Y
      ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y).op ⋙ yoneda.obj a ⋙
        uliftFunctor.{u + 1, u}) :=
  ⟨yonedaProdSpace (Y := Y) a, yonedaProdProjection a,
    isAffineHom_yonedaProdProjection a ha, isFinitePresentation_yonedaProdProjection a ha',
    ⟨Functor.isoWhiskerRight (yonedaProdPointsIso a) _⟩⟩

end ProdPoints

section StructureFunctions

variable (Y : AlgebraicSpaces B S hS)

/-- **The functor of global functions on the test schemes over `Y`**, `T ↦ Γ(T, 𝒪_T)`, lifted to
the value universe of the relative Hom functors.  It is the functor of points over `Y` of the
affine line `𝔸¹_Y`. -/
def structureFunctionsFunctor : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1) :=
  (CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y).op ⋙
    ((BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ ⋙ forget CommRingCat) ⋙
      uliftFunctor.{u + 1, u}

/-- **The affine line `𝔸¹_Y` is an algebraic space affine and of finite presentation over
`Y`**: the functor of global functions on the test schemes over `Y` is represented by the
restriction of the affine line over `S` to `Y`. -/
theorem isAffineFinitePresentationAlgebraicSpaceOver_structureFunctionsFunctor :
    IsAffineFinitePresentationAlgebraicSpaceOver Y (structureFunctionsFunctor Y) := by
  have hA : (BigFppfOver.toScheme B S hS).map
      (Over.mkIdTerminal.from (affineLineBigFppfOver B S hS)) = AffineSpace PUnit.{u + 1} S ↘ S :=
    (toScheme_map_mkIdTerminal_from B S hS _).trans rfl
  have h₁ : _root_.AlgebraicGeometry.IsAffineHom (AffineSpace PUnit.{u + 1} S ↘ S) :=
    inferInstance
  have h₂ : FinitePresentation (AffineSpace PUnit.{u + 1} S ↘ S) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  exact IsAffineFinitePresentationAlgebraicSpaceOver.of_iso
    (Functor.isoWhiskerRight (Functor.isoWhiskerLeft
      (CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y).op (gammaAffineLineIso B S hS).symm)
      uliftFunctor.{u + 1, u})
    (isAffineFinitePresentationAlgebraicSpaceOver_yoneda (Y := Y) (affineLineBigFppfOver B S hS)
      (by rwa [hA]) (by rwa [hA]))

end StructureFunctions

section Powers

variable {Y : AlgebraicSpaces B S hS}

/-- The terminal functor on the test schemes over `Y`, in the value universe of the relative Hom
functors, is terminal. -/
def isTerminalConstPUnitOnSchemesOver :
    IsTerminal ((Functor.const (SchemesOver Y)ᵒᵖ).obj PUnit.{u + 2}) :=
  IsTerminal.ofUniqueHom (fun K => { app := fun X => Types.isTerminalPUnit.from (K.obj X) })
    (fun _ _ => NatTrans.ext (funext fun _ => Types.isTerminalPUnit.hom_ext _ _))

/-- **Pointwise powers of an algebraic space affine and of finite presentation over `Y` are
again such**: `Rⁿ` is the `n`-fold fibre product of `R` over `Y`. -/
theorem IsAffineFinitePresentationAlgebraicSpaceOver.pow
    {R : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1)} (hR : IsAffineFinitePresentationAlgebraicSpaceOver Y R) :
    ∀ n : ℕ, IsAffineFinitePresentationAlgebraicSpaceOver Y (FunctorToTypes.pow R n)
  | 0 => .of_isTerminal (FunctorToTypes.isTerminalPowZero R)
  | n + 1 => (hR.prod (IsAffineFinitePresentationAlgebraicSpaceOver.pow hR n)).of_iso
      (FunctorToTypes.powSuccIso R n).symm

/-- **The fibre over a section of a morphism between algebraic spaces affine and of finite
presentation over `Y` is again one.** -/
theorem IsAffineFinitePresentationAlgebraicSpaceOver.fibre
    {P Q : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1)} (c : P ⟶ Q)
    (σ : (Functor.const (SchemesOver Y)ᵒᵖ).obj PUnit.{u + 2} ⟶ Q)
    (hP : IsAffineFinitePresentationAlgebraicSpaceOver Y P)
    (hQ : IsAffineFinitePresentationAlgebraicSpaceOver Y Q) :
    IsAffineFinitePresentationAlgebraicSpaceOver Y (FunctorToTypes.fibre c σ) :=
  .of_isPullback (FunctorToTypes.isPullback_fibre c σ) hP hQ
    (.of_isTerminal isTerminalConstPUnitOnSchemesOver)

end Powers

section Coordinates

variable (Y : AlgebraicSpaces B S hS)

/-- **The coordinate functor `T ↦ Γ(T, 𝒪_T)ⁿ`** on the test schemes over `Y`: the functor of
points over `Y` of affine `n`-space `𝔸ⁿ_Y`. -/
abbrev coordinateFunctor (n : ℕ) : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1) :=
  FunctorToTypes.pow (structureFunctionsFunctor Y) n

/-- **Affine `n`-space `𝔸ⁿ_Y` is an algebraic space affine and of finite presentation over
`Y`.** -/
theorem isAffineFinitePresentationAlgebraicSpaceOver_coordinateFunctor (n : ℕ) :
    IsAffineFinitePresentationAlgebraicSpaceOver Y (coordinateFunctor Y n) :=
  IsAffineFinitePresentationAlgebraicSpaceOver.pow
    (isAffineFinitePresentationAlgebraicSpaceOver_structureFunctionsFunctor Y) n

/-- The zero section of the coordinate functor: the tuple of zero functions. -/
def coordinateZero (n : ℕ) :
    (Functor.const (SchemesOver Y)ᵒᵖ).obj PUnit.{u + 2} ⟶ coordinateFunctor Y n where
  app T := ↾fun _ _ => ULift.up (0 : Γ((BigFppfOver.toScheme B S hS).obj T.unop.left, ⊤))
  naturality _ _ g := congrArg TypeCat.ofHom (funext fun _ => funext fun _ =>
    congrArg ULift.up
      (map_zero (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g.unop.left).op).hom).symm)

/-- **The kernel of a morphism of coordinate functors**, `T ↦ {v ∈ Γ(T, 𝒪_T)ᵐ | c(v) = 0}`. -/
abbrev coordinateKernel {m m' : ℕ} (c : coordinateFunctor Y m ⟶ coordinateFunctor Y m') :
    (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1) :=
  FunctorToTypes.fibre c (coordinateZero Y m')

/-- **The solutions of a system of equations in `m` functions with values in `m'` functions,
natural in the test scheme, form an algebraic space affine and of finite presentation over
`Y`.**  For `c` the linear map `Γ(T, 𝒪_T)^{m₀} ⟶ Γ(T, 𝒪_T)^{m₁}` dual to a map
`𝒪^{m₁} ⟶ 𝒪^{m₀}` this is the fibre product `Y ×_{0, 𝔸^{m₁}_Y} 𝔸^{m₀}_Y` at the end of the
proof of Stacks 0DLC. -/
theorem isAffineFinitePresentationAlgebraicSpaceOver_coordinateKernel {m m' : ℕ}
    (c : coordinateFunctor Y m ⟶ coordinateFunctor Y m') :
    IsAffineFinitePresentationAlgebraicSpaceOver Y (coordinateKernel Y c) :=
  .fibre c _ (isAffineFinitePresentationAlgebraicSpaceOver_coordinateFunctor Y m)
    (isAffineFinitePresentationAlgebraicSpaceOver_coordinateFunctor Y m')

end Coordinates

end AlgebraicGeometry.Space

end

