module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRepresentableLimits
public import StacksFrontier.AlgebraicGeometry.Spaces.OverSchemeLocus

/-!
# Extending an algebraic space over an open to the whole base

Let `ι : W ⟶ Y` be a monomorphism of algebraic spaces over `S` of finite presentation, for
instance the inclusion of a quasi-compact open subspace.  Composing with `ι` sends the test
schemes over `W` to test schemes over `Y` (`CategoryTheory.CostructuredArrow.map ι`).  If a
functor `R` on the test schemes over `Y` is empty at every test scheme not factoring through `W`,
and its restriction to the test schemes over `W` is an algebraic space affine and of finite
presentation over `W`, represented by `q : H ⟶ W`, then `R` is an algebraic space of finite
presentation over `Y`, represented by `q ≫ ι`.

The restriction in the other direction is
`AlgebraicGeometry.Space.IsAffineFinitePresentationAlgebraicSpaceOver.baseChange`, and the
analogous statement on `(Sch/Z)` for a scheme `Z`, without finite presentation, is
`AlgebraicGeometry.Space.exists_iso_yoneda_overSchemeTest`.

## Main definitions

* `AlgebraicGeometry.Space.IsFinitePresentationAlgebraicSpaceOver`: a functor on the test
  schemes over `Y` *is an algebraic space of finite presentation over `Y`*.

## Main results

* `AlgebraicGeometry.Space.IsFinitePresentationAlgebraicSpaceOver.of_restrict`: a functor on the
  test schemes over `Y`, empty off `W`, whose restriction to `W` is an algebraic space affine and
  of finite presentation over `W`, is an algebraic space of finite presentation over `Y`.

## References

* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
* [Stacks Project, Tag 0DPW](https://stacks.math.columbia.edu/tag/0DPW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {W Y : AlgebraicSpaces B S hS} (ι : W ⟶ Y)

section Extension

variable (Y) in
/-- **A functor on the test schemes over `Y` is an algebraic space of finite presentation over
`Y`**: it is isomorphic to the universe lift of the functor of points over `Y` of an algebraic
space `H` whose morphism `H ⟶ Y` is of finite presentation in the sense of Stacks 03XP. -/
def IsFinitePresentationAlgebraicSpaceOver (R : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1)) : Prop :=
  ∃ (H : AlgebraicSpaces B S hS) (p : H ⟶ Y), IsFinitePresentation B S hS p.hom ∧
    Nonempty (spacePointsOver p ⋙ uliftFunctor.{u + 1, u} ≅ R)

/-- The test scheme over `W` of a test scheme `T` over `Y` together with a section `w` of `W`
over `T` lying over the section of `Y` that `T` is. -/
abbrev liftTest (T : SchemesOver Y) (w : W.obj.obj (op T.left)) : SchemesOver W :=
  CostructuredArrow.mk (S := schemeSpaceFunctor B S hS) (Y := T.left)
    (ObjectProperty.homMk (yonedaEquiv.symm w))

/-- The section of `W` that `liftTest T w` is, is `w`. -/
theorem testPoint_liftTest (T : SchemesOver Y) (w : W.obj.obj (op T.left)) :
    testPoint (liftTest T w) = w :=
  yonedaEquiv.apply_symm_apply w

/-- The image in the test schemes over `Y` of `liftTest T w` has the structure morphism of `T`,
when `w` lies over the section of `Y` that `T` is. -/
theorem liftTest_map_hom (T : SchemesOver Y) (w : W.obj.obj (op T.left))
    (hw : ι.hom.app (op T.left) w = testPoint T) :
    ((CostructuredArrow.map ι).obj (liftTest T w)).hom = T.hom := by
  apply ObjectProperty.hom_ext
  apply yonedaEquiv.injective
  show yonedaEquiv (yonedaEquiv.symm w ≫ ι.hom) = testPoint T
  rwa [yonedaEquiv_comp, Equiv.apply_symm_apply]

/-- The image in the test schemes over `Y` of `liftTest T w` is `T`, when `w` lies over the
section of `Y` that `T` is. -/
def liftTestIso (T : SchemesOver Y) (w : W.obj.obj (op T.left))
    (hw : ι.hom.app (op T.left) w = testPoint T) :
    (CostructuredArrow.map ι).obj (liftTest T w) ≅ T :=
  CostructuredArrow.isoMk (f := (CostructuredArrow.map ι).obj (liftTest T w)) (f' := T)
    (Iso.refl _) (by
      rw [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.id_comp]
      exact (liftTest_map_hom ι T w hw).symm)

/-- The underlying morphism of schemes of the inverse of `liftTestIso` is the identity. -/
theorem liftTestIso_inv_left (T : SchemesOver Y) (w : W.obj.obj (op T.left))
    (hw : ι.hom.app (op T.left) w = testPoint T) :
    (liftTestIso ι T w hw).inv.left = 𝟙 T.left :=
  rfl

variable {ι} {H : AlgebraicSpaces B S hS} {q : H ⟶ W} {R : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1)}
  (e : spacePointsOver q ⋙ uliftFunctor.{u + 1, u} ≅ (CostructuredArrow.map ι).op ⋙ R)

/-- The value in `R` at `T` of a section of `H` over `T` with a prescribed image `w` in `W`. -/
def supportedExtensionValue (T : SchemesOver Y) (w : W.obj.obj (op T.left))
    (hw : ι.hom.app (op T.left) w = testPoint T)
    (z : {x : H.obj.obj (op T.left) // q.hom.app (op T.left) x = w}) : R.obj (op T) :=
  R.map (liftTestIso ι T w hw).inv.op
    (e.hom.app (op (liftTest T w)) ⟨⟨z.1, z.2.trans (testPoint_liftTest T w).symm⟩⟩)

/-- `supportedExtensionValue` only depends on the prescribed image through its value. -/
theorem supportedExtensionValue_congr (T : SchemesOver Y) {w w' : W.obj.obj (op T.left)}
    (h : w = w')
    (hw : ι.hom.app (op T.left) w = testPoint T) (hw' : ι.hom.app (op T.left) w' = testPoint T)
    (z : {x : H.obj.obj (op T.left) // q.hom.app (op T.left) x = w}) :
    supportedExtensionValue e T w hw z = supportedExtensionValue e T w' hw' ⟨z.1, z.2.trans h⟩ := by
  subst h
  rfl

/-- `supportedExtensionValue` is injective. -/
theorem supportedExtensionValue_injective (T : SchemesOver Y) (w : W.obj.obj (op T.left))
    (hw : ι.hom.app (op T.left) w = testPoint T) :
    Function.Injective (supportedExtensionValue e T w hw) := by
  intro z z' h
  have h₁ := (mono_iff_injective (R.map (liftTestIso ι T w hw).inv.op)).1 inferInstance h
  have h₂ := (mono_iff_injective (e.hom.app (op (liftTest T w)))).1 inferInstance h₁
  exact Subtype.ext (congrArg (fun a => a.down.1) h₂)

/-- `supportedExtensionValue` is natural in the test scheme. -/
theorem supportedExtensionValue_naturality {T' T : SchemesOver Y} (g : T' ⟶ T)
    (w : W.obj.obj (op T.left)) (hw : ι.hom.app (op T.left) w = testPoint T)
    (hw' : ι.hom.app (op T'.left) (W.obj.map g.left.op w) = testPoint T')
    (z : {x : H.obj.obj (op T.left) // q.hom.app (op T.left) x = w}) :
    supportedExtensionValue e T' (W.obj.map g.left.op w) hw'
        ⟨H.obj.map g.left.op z.1, by rw [NatTrans.naturality_apply, z.2]⟩ =
      R.map g.op (supportedExtensionValue e T w hw z) := by
  let gW : liftTest T' (W.obj.map g.left.op w) ⟶ liftTest T w :=
    CostructuredArrow.homMk g.left (by
      refine ObjectProperty.hom_ext _ (yonedaEquiv.injective ?_)
      show yonedaEquiv (yoneda.map g.left ≫ yonedaEquiv.symm w) =
        yonedaEquiv (yonedaEquiv.symm (W.obj.map g.left.op w))
      rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply, Equiv.apply_symm_apply])
  have hsq : (liftTestIso ι T' _ hw').inv ≫ (CostructuredArrow.map ι).map gW =
      g ≫ (liftTestIso ι T w hw).inv :=
    CostructuredArrow.hom_ext _ _ (by
      rw [CostructuredArrow.comp_left, CostructuredArrow.comp_left, liftTestIso_inv_left,
        liftTestIso_inv_left]
      exact (Category.id_comp _).trans (Category.comp_id _).symm)
  have hnat := NatTrans.naturality_apply e.hom gW.op
    (⟨⟨z.1, z.2.trans (testPoint_liftTest T w).symm⟩⟩ :
      (spacePointsOver q ⋙ uliftFunctor.{u + 1, u}).obj (op (liftTest T w)))
  unfold supportedExtensionValue
  refine (congrArg _ hnat).trans ?_
  rw [Functor.comp_map, ← Functor.map_comp_apply, Functor.op_map, Quiver.Hom.unop_op, ← op_comp,
    hsq, op_comp, Functor.map_comp_apply]

/-- The comparison from the points of `H` over `Y`, through `q ≫ ι`, to `R`. -/
def supportedExtensionHom : spacePointsOver (q ≫ ι) ⋙ uliftFunctor.{u + 1, u} ⟶ R where
  app T := ↾fun x =>
    supportedExtensionValue e T.unop (q.hom.app _ x.down.1) x.down.2 ⟨x.down.1, rfl⟩
  naturality T T' g := by
    ext x
    obtain ⟨⟨x, hx⟩⟩ := x
    have hq : W.obj.map g.unop.left.op (q.hom.app _ x) = q.hom.app _ (H.obj.map g.unop.left.op x) :=
      (NatTrans.naturality_apply q.hom g.unop.left.op x).symm
    have hw' : ι.hom.app _ (W.obj.map g.unop.left.op (q.hom.app _ x)) = testPoint T'.unop :=
      (congrArg (ι.hom.app _) hq).trans (spacePointsOver_restrict (p := q ≫ ι) g.unop ⟨x, hx⟩)
    refine (supportedExtensionValue_congr e T'.unop hq.symm _ hw' _).trans ?_
    exact supportedExtensionValue_naturality e g.unop _ hx hw' ⟨x, rfl⟩

/-- Each component of the comparison is bijective, when `ι` is a monomorphism and `R` is empty
at the test schemes not factoring through `W`. -/
theorem supportedExtensionHom_app_bijective (hι : Mono ι.hom)
    (hR : ∀ T : SchemesOver Y, Nonempty (R.obj (op T)) →
      ∃ t : (schemeSpaceFunctor B S hS).obj T.left ⟶ W, t ≫ ι = T.hom)
    (T : (SchemesOver Y)ᵒᵖ) : Function.Bijective ((supportedExtensionHom e).app T) := by
  have hinj : Function.Injective (ι.hom.app (op T.unop.left)) := by
    have := hι
    exact (mono_iff_injective _).1 inferInstance
  constructor
  · rintro ⟨⟨x, hx⟩⟩ ⟨⟨y, hy⟩⟩ h
    have hq : q.hom.app _ x = q.hom.app _ y := hinj (hx.trans hy.symm)
    change supportedExtensionValue e T.unop _ hx ⟨x, rfl⟩ =
      supportedExtensionValue e T.unop _ hy ⟨y, rfl⟩ at h
    have h' := (supportedExtensionValue_congr e T.unop hq hx hy ⟨x, rfl⟩).symm.trans h
    have hxy : x = y := congrArg Subtype.val (supportedExtensionValue_injective e T.unop _ hy h')
    subst hxy
    rfl
  · intro r
    obtain ⟨t, ht⟩ := hR T.unop ⟨r⟩
    let w := testPoint (CostructuredArrow.mk (Y := T.unop.left) t)
    have hw : ι.hom.app _ w = testPoint T.unop := by
      rw [← testPoint_map]
      exact congrArg (fun m : (schemeSpaceFunctor B S hS).obj T.unop.left ⟶ Y =>
        yonedaEquiv m.hom) ht
    let z := (e.inv.app (op (liftTest T.unop w))
      (R.map (liftTestIso ι T.unop w hw).hom.op r)).down
    have hz : q.hom.app _ z.1 = w := z.2.trans (testPoint_liftTest T.unop w)
    refine ⟨⟨⟨z.1, (congrArg (ι.hom.app _) hz).trans hw⟩⟩, ?_⟩
    show supportedExtensionValue e T.unop _ _ ⟨z.1, rfl⟩ = r
    refine (supportedExtensionValue_congr e T.unop hz _ hw _).trans ?_
    show R.map (liftTestIso ι T.unop w hw).inv.op
      (e.hom.app _ (e.inv.app _ (R.map (liftTestIso ι T.unop w hw).hom.op r))) = r
    exact (congrArg _ ((e.app (op (liftTest T.unop w))).inv_hom_id_apply
      (R.map (liftTestIso ι T.unop w hw).hom.op r))).trans
      ((R.mapIso (liftTestIso ι T.unop w hw).op).hom_inv_id_apply r)

/-- **Extension of an algebraic space over `W` to one over `Y`.**  Let `ι : W ⟶ Y` be a
monomorphism of finite presentation, and let `R` be a functor on the test schemes over `Y` which
is empty at every test scheme not factoring through `W`.  If the restriction of `R` to the test
schemes over `W` is an algebraic space affine and of finite presentation over `W`, represented by
`q : H ⟶ W`, then `R` is an algebraic space of finite presentation over `Y`, represented by
`q ≫ ι`. -/
theorem IsFinitePresentationAlgebraicSpaceOver.of_restrict (hι : Mono ι.hom)
    (hιfp : IsFinitePresentation B S hS ι.hom)
    (hR : ∀ T : SchemesOver Y, Nonempty (R.obj (op T)) →
      ∃ t : (schemeSpaceFunctor B S hS).obj T.left ⟶ W, t ≫ ι = T.hom)
    (hW : IsAffineFinitePresentationAlgebraicSpaceOver W ((CostructuredArrow.map ι).op ⋙ R)) :
    IsFinitePresentationAlgebraicSpaceOver Y R := by
  obtain ⟨H, q, -, hf, ⟨e⟩⟩ := hW
  have : ∀ T, IsIso ((supportedExtensionHom e).app T) := fun T =>
    (isIso_iff_bijective _).2 (supportedExtensionHom_app_bijective e hι hR T)
  have : IsIso (supportedExtensionHom e) := NatIso.isIso_of_isIso_app _
  exact ⟨H, q ≫ ι, isFinitePresentation_comp B S hS H.property W.property Y.property _ _ hf hιfp,
    ⟨asIso (supportedExtensionHom e)⟩⟩

end Extension

end AlgebraicGeometry.Space

end
