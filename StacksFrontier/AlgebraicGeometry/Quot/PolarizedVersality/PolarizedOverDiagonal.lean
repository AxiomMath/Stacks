module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedVersality.PolarizedOverLimit
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedDiagonal
public import StacksFrontier.CategoryTheory.Sites.Stack.MorPresheafOfLifts

/-!
# The diagonal of `S-𝒫olarized` is representable by algebraic spaces

For an object `U` of the big fppf site of `S` and two objects `x`, `y` of `S-𝒫olarized` over `U`,
the presheaf `Isom(x, y)` on `(Sch/U)_{fppf}` is the presheaf `Isom(x, y)` of the underlying
polarized families, read over a terminal base. Consequently the diagonal of `S-𝒫olarized` is
representable by algebraic spaces.

## Main results

* `AlgebraicGeometry.PolarizedVersality.PolarizedOver.isomPresheafIso`: the isomorphism presheaf
  of two objects of `S-𝒫olarized` is that of the underlying polarized families.
* `AlgebraicGeometry.PolarizedVersality.PolarizedOver.hasRepresentableDiagonal_stack`: the
  diagonal of `S-𝒫olarized` is representable by algebraic spaces.

## References

* [Stacks Project, Tag 0D42](https://stacks.math.columbia.edu/tag/0D42)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 02ZB](https://stacks.math.columbia.edu/tag/02ZB)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

namespace AlgebraicGeometry.PolarizedVersality.PolarizedOver

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T : Scheme.{u}}
  {hT' : B.Contains T} (hT : IsTerminal (B.obj hT'))

/-- The fibres of a category fibred in groupoids are groupoids. -/
theorem isGroupoid_fiber {𝒳 C : Type*} [Category 𝒳] [Category C] (p : 𝒳 ⥤ C)
    [p.IsFibered] (hp : p.IsFiberedInGroupoids) (V : C) : IsGroupoid (p.Fiber V) where
  all_isIso {a b} φ := by
    have : p.IsHomLift (𝟙 V) φ.1 := φ.2
    have := hp.isStronglyCartesian_homLift (𝟙 V) φ.1
    have : IsIso φ.1 := IsStronglyCartesian.isIso_of_base_isIso p (𝟙 V) φ.1
    have hinv : p.IsHomLift (𝟙 V) (inv φ.1) := by
      simpa using (inferInstance : p.IsHomLift (inv (𝟙 V)) (inv φ.1))
    exact ⟨⟨inv φ.1, hinv⟩, Fiber.hom_ext (IsIso.hom_inv_id φ.1),
      Fiber.hom_ext (IsIso.inv_hom_id φ.1)⟩

/-- The chosen pullbacks of a fibred category form a system of cartesian lifts. -/
abbrev chosenLiftSystem {𝒳 C : Type*} [Category 𝒳] [Category C] (p : 𝒳 ⥤ C)
    [p.IsFibered] {U : C} (x : p.Fiber U) : CartesianLiftSystem p x where
  obj f := (pullbackFiber p x f.hom).1
  hom f := IsPreFibered.pullbackMap x.2 f.hom
  isStronglyCartesian f := IsFibered.isStronglyCartesian_of_isCartesian p f.hom _
  trans h := pullbackFiberMap p x h
  trans_isHomLift _ := inferInstance
  trans_hom h := pullbackFiberMap_fac p x h

variable {U : BigFppfOver B S hS} (x : (projection B S hS).Fiber U)

/-- The chosen pullbacks of the polarized family of `x` along the morphisms of the site of `S`
into `U`, lifted to `S-𝒫olarized`: a system of cartesian lifts of `x`. -/
abbrev liftSystem : CartesianLiftSystem (projection B S hS) x where
  obj f := ofBase (pullbackFiber (polarizedSliceProjection B hT' hT) (toSliceFiber hT x)
      ((toTerminal hT).map f.hom)).1 f.left (congrArg Comma.left (pullbackFiber
        (polarizedSliceProjection B hT' hT) (toSliceFiber hT x) ((toTerminal hT).map f.hom)).2)
  hom f := liftHom (projection_obj_ofBase _ _ _) x.2 f.hom
    (IsPreFibered.pullbackMap (toSliceFiber hT x).2 ((toTerminal hT).map f.hom))
    (isHomLift_left_of_sliceAtTerminal (polarizedProjection B) hT ((toTerminal hT).map f.hom) _
      (inferInstance : (polarizedSliceProjection B hT' hT).IsHomLift ((toTerminal hT).map f.hom)
        (IsPreFibered.pullbackMap (toSliceFiber hT x).2 ((toTerminal hT).map f.hom))))
  isStronglyCartesian f :=
    @Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift _ _ _ _ _
      (isFiberedInGroupoids_projection B S hS) _ _ _ _ f.hom _ <|
      isHomLift_liftHom (projection_obj_ofBase _ _ _) x.2 f.hom
        (IsPreFibered.pullbackMap (toSliceFiber hT x).2 ((toTerminal hT).map f.hom))
        (isHomLift_left_of_sliceAtTerminal (polarizedProjection B) hT ((toTerminal hT).map f.hom) _
          (inferInstance : (polarizedSliceProjection B hT' hT).IsHomLift ((toTerminal hT).map f.hom)
            (IsPreFibered.pullbackMap (toSliceFiber hT x).2 ((toTerminal hT).map f.hom))))
  trans h := liftHom (projection_obj_ofBase _ _ _) (projection_obj_ofBase _ _ _) h.left
    (pullbackFiberMap (polarizedSliceProjection B hT' hT) (toSliceFiber hT x)
      ((Over.post (toTerminal hT)).map h))
    (isHomLift_left_of_sliceAtTerminal (polarizedProjection B) hT ((toTerminal hT).map h.left) _
      (pullbackFiberMap_isHomLift (polarizedSliceProjection B hT' hT) (toSliceFiber hT x)
        ((Over.post (toTerminal hT)).map h)))
  trans_isHomLift _ := isHomLift_liftHom _ _ _ _ _
  trans_hom h := PolarizedFamilyOver.Hom.ext
    (pullbackFiberMap_fac (polarizedSliceProjection B hT' hT) (toSliceFiber hT x)
      ((Over.post (toTerminal hT)).map h))

variable (y : (projection B S hS).Fiber U)

/-- The morphisms of `S-𝒫olarized` out of the lift of `x` along `f` into `y`, over `f`, are the
morphisms of polarized families over the underlying morphism. -/
def homOverEquiv (f : Over U) :
    (liftSystem hT x).homOver y.1 f ≃
      (chosenLiftSystem (polarizedSliceProjection B hT' hT) (toSliceFiber hT x)).homOver
        y.1.polarized ((Over.post (toTerminal hT)).obj f) where
  toFun φ := ⟨φ.1.polarizedHom, isHomLift_slice hT _ φ.1.polarizedHom
    (projection_obj_ofBase _ _ _) y.2 (isHomLift_polarizedProjection f.hom φ.1 φ.2)⟩
  invFun φ := ⟨liftHom (projection_obj_ofBase _ _ _) y.2 f.hom φ.1
      (isHomLift_left_of_sliceAtTerminal (polarizedProjection B) hT _ φ.1 φ.2),
    isHomLift_liftHom _ _ _ _ _⟩
  left_inv _ := Subtype.ext (PolarizedFamilyOver.Hom.ext rfl)
  right_inv _ := rfl

/-- **The presheaf of morphisms of `S-𝒫olarized` is that of the underlying polarized families**,
read through the functor `Over U ⥤ Over U'` of the site over a terminal base. -/
def morPresheafIso :
    (Over.post (toTerminal hT)).op ⋙
        morPresheaf (polarizedSliceProjection B hT' hT) (toSliceFiber hT x) (toSliceFiber hT y) ≅
      morPresheaf (projection B S hS) x y :=
  (liftSystem hT x).morPresheafIso y _
    (fun f => ((chosenLiftSystem (polarizedSliceProjection B hT' hT)
      (toSliceFiber hT x)).morPresheafEquiv (toSliceFiber hT y)
        ((Over.post (toTerminal hT)).obj f)).trans (homOverEquiv hT x y f).symm)
    (fun {_ _} h q => PolarizedFamilyOver.Hom.ext
      ((chosenLiftSystem (polarizedSliceProjection B hT' hT)
        (toSliceFiber hT x)).morPresheafEquiv_morRestrict
          (toSliceFiber hT y) ((Over.post (toTerminal hT)).map h) q))

/-- The iterated slice of the site of `S` at `U`, read over the terminal base, is the iterated
slice of the site of the terminal base at `U` read there. -/
def iteratedSliceIso :
    Over.iteratedSliceBackward U ⋙ Over.post (toTerminal hT) ≅
      Over.iteratedSliceBackward ((toTerminal hT).obj U) :=
  NatIso.ofComponents
    (fun _ => Over.isoMk (Over.isoMk (Iso.refl _) (hT.hom_ext _ _))
      (Over.OverMorphism.ext (Category.id_comp _)))
    (fun {_ _} _ => Over.OverMorphism.ext (Over.OverMorphism.ext
      ((Category.comp_id _).trans (Category.id_comp _).symm)))

/-- **`Isom(x, y)` for `S-𝒫olarized` is `Isom(x, y)` for the underlying polarized families**, on
the big fppf site of the base of `x` and `y`. -/
def isomPresheafIso :
    (Over.iteratedSliceBackward U).op ⋙ (projection B S hS).isomPresheaf x y ≅
      (Over.iteratedSliceBackward ((toTerminal hT).obj U)).op ⋙
        (polarizedSliceProjection B hT' hT).isomPresheaf (toSliceFiber hT x) (toSliceFiber hT y) :=
  letI : (polarizedSliceProjection B hT' hT).IsFibered :=
    (polarizedProjection_isFiberedInGroupoids_unconditional.sliceAtTerminal hT).isFibered
  isoWhiskerLeft _ (isomPresheafIsoMorPresheafOfGroupoid (projection B S hS)
      (isGroupoid_fiber _ (isFiberedInGroupoids_projection B S hS)) x y ≪≫
      (morPresheafIso hT x y).symm) ≪≫
    isoWhiskerRight (NatIso.op (iteratedSliceIso (U := U) hT)).symm
      (morPresheaf (polarizedSliceProjection B hT' hT) (toSliceFiber hT x) (toSliceFiber hT y)) ≪≫
    isoWhiskerLeft _ (isomPresheafIsoMorPresheafOfGroupoid (polarizedSliceProjection B hT' hT)
      (isGroupoid_fiber _ (polarizedProjection_isFiberedInGroupoids_unconditional.sliceAtTerminal
        hT)) (toSliceFiber hT x) (toSliceFiber hT y)).symm

variable (B S hS) in
/-- **The diagonal of `S-𝒫olarized` is representable by algebraic spaces.** -/
theorem hasRepresentableDiagonal_stack : Stack.HasRepresentableDiagonal B S hS (stack B S hS) := by
  refine (Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS _).2 ?_
  intro U x y
  have hZ : B.Contains (Spec (CommRingCat.of (ULift.{u} ℤ))) := by
    show (Spec (CommRingCat.of (ULift.{u} ℤ))).size < B.cutoff
    rw [Scheme.size_Spec]
    simpa using B.aleph0_lt_cutoff
  let hT := isTerminal_obj_specULiftZ B hZ
  obtain ⟨F, hF, ⟨e⟩⟩ := (Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B _ hZ
    _).1 (hasRepresentableDiagonal_polarizedStackUnconditional B hZ hT) ((toTerminal hT).obj U)
    (toSliceFiber hT x) (toSliceFiber hT y)
  exact ⟨F, hF, ⟨e ≪≫ isoWhiskerRight (isomPresheafIso hT x y).symm uliftFunctor⟩⟩

end AlgebraicGeometry.PolarizedVersality.PolarizedOver

end
