module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.ConstantGerm
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkIsomorphismCriterion
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs

/-!
# A sheaf of sets with bijective germ maps is constant on an étale neighbourhood

Let `U` be an object of the small étale site of a scheme `S`, let `F` be a sheaf of sets on that
site and let `z : A → F(U)` be a family of sections of `F` over `U`. If for every geometric point
of `S` with a lift to `U` the resulting map from `A` to the stalk of `F` is bijective, then the
comparison map from the constant presheaf with value `A` on the localized site is locally
bijective, so the restriction of `F` to `U` is a constant sheaf with value `A`.

## Main definitions

* `AlgebraicGeometry.constantPresheafHomOfSections` — the comparison map from the constant
  presheaf with value `A` on the localized site attached to a family of sections over `U`.

## Main results

* `AlgebraicGeometry.isLocallyInjective_constantPresheafHomOfSections` and
  `AlgebraicGeometry.isLocallySurjective_constantPresheafHomOfSections` — injectivity,
  respectively surjectivity, of all germ maps makes the comparison map locally injective,
  respectively locally surjective.
* `AlgebraicGeometry.isConstant_overPullback_of_bijective_germ` — bijectivity of all germ maps
  identifies the restriction of `F` to `U` with the constant sheaf on `A`.

## References

* [Stacks Project, Tag 040R](https://stacks.math.columbia.edu/tag/040R)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : Sheaf (SmallEtale.topology B S hS) (Type (u + 1))) (U : SmallEtale B S hS)
  {A : Type (u + 1)} (z : A → F.obj.obj (op U))

/-- The comparison map attached to a family `z` of sections of `F` over `U`: on an object `V` of
the localized site it sends an index to the restriction along `V ⟶ U` of the corresponding
section. -/
public def constantPresheafHomOfSections :
    (Functor.const (Over U)ᵒᵖ).obj A ⟶ (Over.forget U).op ⋙ F.obj where
  app V := ↾ fun a => F.obj.map V.unop.hom.op (z a)
  naturality V W f := by
    ext a
    change F.obj.map W.unop.hom.op (z a) =
      F.obj.map f.unop.left.op (F.obj.map V.unop.hom.op (z a))
    rw [← Functor.map_comp_apply, ← op_comp, Over.w]

/-- The comparison map restricts a section of the family along the structure morphism. -/
public theorem constantPresheafHomOfSections_app (V : (Over U)ᵒᵖ) (a : A) :
    (constantPresheafHomOfSections B S hS F U z).app V a =
      F.obj.map V.unop.hom.op (z a) :=
  rfl

/-- The germ at a geometric point of `S` lifted to `V` of a restricted section of the family is
the germ at the image lift to `U` of the section itself. -/
public theorem toPresheafFiber_constantPresheafHomOfSections {r : GeometricPoint S}
    (V : Over U) (y : (geometricPointFiber B S hS r).obj V.left) (a : A) :
    (geometricPointSitePoint B S hS r).toPresheafFiber V.left y F.obj
        ((constantPresheafHomOfSections B S hS F U z).app (op V) a) =
      (geometricPointSitePoint B S hS r).toPresheafFiber U
        ((geometricPointFiber B S hS r).map V.hom y) F.obj (z a) :=
  (geometricPointSitePoint B S hS r).toPresheafFiber_w_apply V.hom y F.obj (z a)

/-- If every germ map of the family is injective, the comparison map from the constant presheaf
is locally injective for the localized topology. -/
public theorem isLocallyInjective_constantPresheafHomOfSections
    (hz : ∀ (r : GeometricPoint S) (x : (geometricPointFiber B S hS r).obj U),
      Function.Injective fun a : A =>
        (geometricPointSitePoint B S hS r).toPresheafFiber U x F.obj (z a)) :
    Presheaf.IsLocallyInjective ((SmallEtale.topology B S hS).over U)
      (constantPresheafHomOfSections B S hS F U z) := by
  constructor
  intro V a b hab
  rw [GrothendieckTopology.mem_over_iff]
  apply SmallEtale.mem_topology_of_jointlySurjective
  intro x
  set r := geometricPointOfEtalePoint B S hS V.unop.left x
  set p := geometricPointOfEtalePointLift B S hS V.unop.left x
  have hgerm : (geometricPointSitePoint B S hS r).toPresheafFiber U
        ((geometricPointFiber B S hS r).map V.unop.hom p) F.obj (z a) =
      (geometricPointSitePoint B S hS r).toPresheafFiber U
        ((geometricPointFiber B S hS r).map V.unop.hom p) F.obj (z b) := by
    rw [← toPresheafFiber_constantPresheafHomOfSections B S hS F U z V.unop p a,
      ← toPresheafFiber_constantPresheafHomOfSections B S hS F U z V.unop p b]
    exact congrArg ((geometricPointSitePoint B S hS r).toPresheafFiber V.unop.left p F.obj) hab
  obtain rfl : a = b := hz _ _ hgerm
  refine ⟨V.unop.left, 𝟙 _, ?_, ⟨x, by simp⟩⟩
  simp

/-- If every germ map of the family is surjective, the comparison map from the constant presheaf
is locally surjective for the localized topology. -/
public theorem isLocallySurjective_constantPresheafHomOfSections
    (hz : ∀ (r : GeometricPoint S) (x : (geometricPointFiber B S hS r).obj U),
      Function.Surjective fun a : A =>
        (geometricPointSitePoint B S hS r).toPresheafFiber U x F.obj (z a)) :
    Presheaf.IsLocallySurjective ((SmallEtale.topology B S hS).over U)
      (constantPresheafHomOfSections B S hS F U z) := by
  constructor
  intro V c
  rw [GrothendieckTopology.mem_over_iff]
  apply SmallEtale.mem_topology_of_jointlySurjective
  intro x
  set r := geometricPointOfEtalePoint B S hS V.left x
  set p := geometricPointOfEtalePointLift B S hS V.left x
  obtain ⟨e, he⟩ := hz r ((geometricPointFiber B S hS r).map V.hom p)
    ((geometricPointSitePoint B S hS r).toPresheafFiber V.left p F.obj c)
  have he' : (geometricPointSitePoint B S hS r).toPresheafFiber V.left p F.obj
        ((constantPresheafHomOfSections B S hS F U z).app (op V) e) =
      (geometricPointSitePoint B S hS r).toPresheafFiber V.left p F.obj c :=
    (toPresheafFiber_constantPresheafHomOfSections B S hS F U z V p e).trans he
  obtain ⟨W, g, y, hy, heq⟩ :=
    ((geometricPointSitePoint B S hS r).toPresheafFiber_eq_iff' (P := F.obj) V.left p
      ((constantPresheafHomOfSections B S hS F U z).app (op V) e) c).1 he'
  refine ⟨W, g, ?_, ?_⟩
  · rw [Sieve.overEquiv_iff]
    refine ⟨e, ?_⟩
    change F.obj.map (g ≫ V.hom).op (z e) = F.obj.map g.op c
    rwa [op_comp, Functor.map_comp_apply]
  · refine ⟨y.1 default, ?_⟩
    have h1 : y.1 ≫ (SmallEtale.toScheme B S hS).map g = p.1 := congrArg Subtype.val hy
    rw [← geometricPointOfEtalePointLift_base B S hS V.left x, ← h1]
    rfl

/-- If every germ map of the family is bijective, the restriction of `F` to `U` is the constant
sheaf with value `A` on the localized site. -/
public theorem isConstant_overPullback_of_bijective_germ
    (hz : ∀ (r : GeometricPoint S) (x : (geometricPointFiber B S hS r).obj U),
      Function.Bijective fun a : A =>
        (geometricPointSitePoint B S hS r).toPresheafFiber U x F.obj (z a)) :
    Nonempty ((constantSheaf ((SmallEtale.topology B S hS).over U) (Type (u + 1))).obj A ≅
      ((SmallEtale.topology B S hS).overPullback (Type (u + 1)) U).obj F) := by
  have hinj := isLocallyInjective_constantPresheafHomOfSections B S hS F U z
    fun r x => (hz r x).1
  have hsurj := isLocallySurjective_constantPresheafHomOfSections B S hS F U z
    fun r x => (hz r x).2
  let φ : (constantSheaf ((SmallEtale.topology B S hS).over U) (Type (u + 1))).obj A ⟶
      ((SmallEtale.topology B S hS).overPullback (Type (u + 1)) U).obj F :=
    ⟨sheafifyLift ((SmallEtale.topology B S hS).over U)
      (constantPresheafHomOfSections B S hS F U z)
      (((SmallEtale.topology B S hS).overPullback (Type (u + 1)) U).obj F).property⟩
  have hfac : toSheafify ((SmallEtale.topology B S hS).over U)
        ((Functor.const (Over U)ᵒᵖ).obj A) ≫ φ.hom =
      constantPresheafHomOfSections B S hS F U z :=
    toSheafify_sheafifyLift _ _ _
  have h1 : Presheaf.IsLocallyInjective ((SmallEtale.topology B S hS).over U) φ.hom :=
    (Presheaf.comp_isLocallyInjective_iff ((SmallEtale.topology B S hS).over U)
      (toSheafify ((SmallEtale.topology B S hS).over U)
        ((Functor.const (Over U)ᵒᵖ).obj A)) φ.hom).1 (by rwa [hfac])
  have h2 : Presheaf.IsLocallySurjective ((SmallEtale.topology B S hS).over U) φ.hom :=
    (Presheaf.comp_isLocallySurjective_iff ((SmallEtale.topology B S hS).over U)
      (toSheafify ((SmallEtale.topology B S hS).over U)
        ((Functor.const (Over U)ᵒᵖ).obj A)) φ.hom).1 (by rwa [hfac])
  have : IsIso φ := (Sheaf.isLocallyBijective_iff_isIso φ).1 ⟨h1, h2⟩
  exact ⟨asIso φ⟩

end AlgebraicGeometry

end
