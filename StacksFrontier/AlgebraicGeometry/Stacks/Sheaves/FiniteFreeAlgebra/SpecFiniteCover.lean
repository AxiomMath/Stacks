module

public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.Diagram
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.RelativeCover
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Split
public import StacksFrontier.CategoryTheory.FibredOneMorphism

/-!
# The 1-morphism `Spec` from free rank-`d` structures to degree-`d` finite locally free covers

Let `S` be a scheme of a big fppf site. Over the big fppf site over `S`, the free `d`-dimensional
commutative algebra structures on the global sections of an object, together with their
isomorphisms, form a presheaf in groupoids: it is the presheaf `FA_d` of Stacks 05YN restricted
along the forgetful functor from the site over `S` to the ambient site of schemes. The
Grothendieck construction turns that presheaf into a category fibred in groupoids over the site
over `S`, the *pointwise groupoid fibration* of free rank-`d` structures.

Taking the spectrum of the algebra of a structure sends an object of that fibration — an object
`T` of the site together with a structure `m` on `Γ(T, 𝒪_T)` — to a degree-`d` finite locally
free cover of `T`, namely the base change along `T ⟶ Spec Γ(T, 𝒪_T)` of the spectrum of the
algebra of `m`, and sends a morphism to the cartesian square presenting the source cover as a
base change of the target cover. This is the 1-morphism `Spec` of Stacks 05YQ into the category
`ℋ_d` of degree-`d` finite locally free covers.

## Main definitions

* `AlgebraicGeometry.FiniteFreeAlgebra.ffaSitePresheaf`: the presheaf in groupoids of free
  `d`-dimensional structures on the big fppf site over `S`.
* `AlgebraicGeometry.FiniteFreeAlgebra.specCoverObject` and
  `AlgebraicGeometry.FiniteFreeAlgebra.specCoverHom`: the value of `Spec` on an object and on a
  morphism of the pointwise groupoid fibration.
* `AlgebraicGeometry.FiniteFreeAlgebra.specFiniteCover`: the 1-morphism `Spec`
  from the pointwise groupoid fibration of free rank-`d` structures into `ℋ_d`.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.contains_cover`: the cover attached to a structure on an
  object of the site is itself an object of the site.
* `AlgebraicGeometry.FiniteFreeAlgebra.isPullback_of_isPullback_toScheme`: a square of the big
  fppf site over `S` is cartesian as soon as its square of underlying schemes is.
* `AlgebraicGeometry.FiniteFreeAlgebra.isFibredOneMorphism_specFiniteCover`: `Spec` is a
  1-morphism of categories fibred in groupoids over the big fppf site over `S`.

## Implementation notes

The presheaf in groupoids is not rebuilt: it is `AlgebraicGeometry.FiniteFreeAlgebra.presheaf`,
the construction of Stacks 05YN, restricted along `AlgebraicGeometry.BigFppfOver.forget`, and
`AlgebraicGeometry.FiniteFreeAlgebra.ffaSitePresheaf_obj` and
`AlgebraicGeometry.FiniteFreeAlgebra.ffaSitePresheaf_map` record that its groupoids and its
pullback functors are the expected ones on the nose.

All the geometry is imported from
`StacksFrontier/AlgebraicGeometry/Stacks/Sheaves/FiniteFreeAlgebra/RelativeCover.lean`: the cover
itself, its degree, the morphism of covers attached to a morphism of schemes and an isomorphism
onto an extension of scalars, the cartesian square of that morphism and its functoriality. What
is added here is the passage between the site over `S` and schemes. An object of the site is a
scheme together with a proof that its size is below the cutoff, so the cover has to be seen
inside the site, which is `contains_cover`; the cartesian square required of a morphism of `ℋ_d`
is taken in the site, so it has to be reflected from schemes, which is
`isPullback_of_isPullback_toScheme`, an instance of `CategoryTheory.IsPullback.of_map_of_faithful`
for the faithful functor `AlgebraicGeometry.BigFppfOver.toScheme`, which reflects isomorphisms
and therefore reflects the pullbacks it meets.

The two functor laws reduce to `AlgebraicGeometry.FiniteFreeAlgebra.coverMap_id` and
`AlgebraicGeometry.FiniteFreeAlgebra.coverMap_comp` after the extensionality lemma for morphisms
of `ℋ_d` and the faithfulness of `AlgebraicGeometry.BigFppfOver.toScheme`. For the composition
law the fibre component of a composite in the Grothendieck construction carries the coherence
isomorphism of `CategoryTheory.PresheafOfCategories.comp_fiber`; that isomorphism is an identity
here, because the pullback functors of a presheaf of categories compose strictly, and
`AlgebraicGeometry.FiniteFreeAlgebra.comp_fiber` discharges it once and for all.

## References

* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

attribute [local instance] FiniteFreeAlgebra.groupoid

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S) (d : ℕ) [NeZero d]

/-! ### The presheaf in groupoids over the big fppf site over `S` -/

/-- The presheaf in groupoids of free `d`-dimensional commutative algebra structures on the big
fppf site over `S`: the presheaf `FA_d` of Stacks 05YN, restricted along the functor forgetting
the structure morphism to `S`. -/
noncomputable def ffaSitePresheaf : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Grpd.{u, u} :=
  (BigFppfOver.forget 𝒞 S hS).op ⋙ (FiniteFreeAlgebra.presheaf 𝒞 d).functor

/-- The groupoid at an object of the site over `S` is the groupoid of free `d`-dimensional
structures on its global sections. -/
theorem ffaSitePresheaf_obj (T : (BigFppfOver 𝒞 S hS)ᵒᵖ) :
    (ffaSitePresheaf 𝒞 S hS d).obj T =
      Grpd.of (FiniteFreeAlgebra Γ((BigFppfOver.toScheme 𝒞 S hS).obj T.unop, ⊤) d) := rfl

/-- The pullback functor along a morphism of the site over `S` is extension of scalars along the
induced map on global sections. -/
theorem ffaSitePresheaf_map {T U : (BigFppfOver 𝒞 S hS)ᵒᵖ} (f : T ⟶ U) :
    (ffaSitePresheaf 𝒞 S hS d).map f =
      FiniteFreeAlgebra.baseChange ((BigFppfOver.toScheme 𝒞 S hS).map f.unop).appTop.hom := rfl

variable {𝒞 S hS d}

/-! ### The cover as an object of the site -/

/-- **The cover attached to a free `d`-dimensional structure on an object of the big fppf site is
itself an object of the big fppf site.** The structure morphism of the cover is finite locally
free, hence finite, hence locally of finite type and quasi-compact, so it cannot raise the size
of the base past the cutoff. -/
theorem contains_cover (T : BigFppfOver 𝒞 S hS)
    (m : FiniteFreeAlgebra Γ((BigFppfOver.toScheme 𝒞 S hS).obj T, ⊤) d) :
    𝒞.Contains (cover ((BigFppfOver.toScheme 𝒞 S hS).obj T) m).left := by
  have hlf : Stacks.Morphisms.IsFiniteLocallyFree
      (cover ((BigFppfOver.toScheme 𝒞 S hS).obj T) m).hom :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d
  have hfin : IsFinite (cover ((BigFppfOver.toScheme 𝒞 S hS).obj T) m).hom :=
    Stacks.Morphisms.IsFiniteLocallyFree.isFinite _
  exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
    (cover ((BigFppfOver.toScheme 𝒞 S hS).obj T) m).hom T.left.2

/-- The cover attached to a free `d`-dimensional structure, as an object of the big fppf site. -/
noncomputable def coverSiteObj (T : BigFppfOver 𝒞 S hS)
    (m : FiniteFreeAlgebra Γ((BigFppfOver.toScheme 𝒞 S hS).obj T, ⊤) d) : 𝒞.Schemes :=
  𝒞.obj (contains_cover T m)

/-- The structure morphism of the cover, as a morphism of the big fppf site. -/
noncomputable def coverSiteHom (T : BigFppfOver 𝒞 S hS)
    (m : FiniteFreeAlgebra Γ((BigFppfOver.toScheme 𝒞 S hS).obj T, ⊤) d) :
    coverSiteObj T m ⟶ T.left :=
  ObjectProperty.homMk (cover ((BigFppfOver.toScheme 𝒞 S hS).obj T) m).hom

/-- The degree-`d` finite locally free cover attached to a free `d`-dimensional structure on the
global sections of an object of the big fppf site over `S`: an object of `ℋ_d`. -/
noncomputable def specCoverObject (T : BigFppfOver 𝒞 S hS)
    (m : FiniteFreeAlgebra Γ((BigFppfOver.toScheme 𝒞 S hS).obj T, ⊤) d) :
    AlgebraicGeometry.Stack.FiniteCover 𝒞 S hS d where
  U := T
  Z := Over.mk (coverSiteHom T m ≫ T.hom)
  q := Over.homMk (coverSiteHom T m)
  finiteLocallyFree := by
    change Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (cover ((BigFppfOver.toScheme 𝒞 S hS).obj T) m).hom d
    infer_instance

/-! ### Morphisms of covers over the site -/

/-- **A square of the big fppf site over `S` is cartesian as soon as its square of underlying
schemes is.** The functor to schemes is faithful and reflects isomorphisms, hence reflects the
pullbacks it meets. -/
theorem isPullback_of_isPullback_toScheme {P Q R W : BigFppfOver 𝒞 S hS} {a : P ⟶ Q} {b : P ⟶ R}
    {c : Q ⟶ W} {e : R ⟶ W}
    (h : IsPullback ((BigFppfOver.toScheme 𝒞 S hS).map a) ((BigFppfOver.toScheme 𝒞 S hS).map b)
      ((BigFppfOver.toScheme 𝒞 S hS).map c) ((BigFppfOver.toScheme 𝒞 S hS).map e)) :
    IsPullback a b c e := by
  have _ : ReflectsLimit (cospan c e) (BigFppfOver.toScheme 𝒞 S hS) :=
    reflectsLimit_of_reflectsIsomorphisms _ _
  exact IsPullback.of_map_of_faithful (BigFppfOver.toScheme 𝒞 S hS) h

/-- The naturality of the canonical morphism to the spectrum of the global sections, in the form
that a morphism of covers consumes: the compatibility of `f` with the map it induces on global
sections. -/
theorem toSpecΓ_appTop_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) :
    X.toSpecΓ ≫ Spec.map (ofHom f.appTop.hom) = f ≫ Y.toSpecΓ :=
  (Scheme.toSpecΓ_naturality f).symm

/-- The morphism of covers attached to a morphism `f` of the big fppf site over `S` and an
isomorphism of a structure over the source with the extension of scalars of a structure over the
target, as a morphism of the big fppf site. -/
noncomputable def coverSiteMap {T V : BigFppfOver 𝒞 S hS} (f : V ⟶ T)
    {m : FiniteFreeAlgebra Γ((BigFppfOver.toScheme 𝒞 S hS).obj T, ⊤) d}
    {m' : FiniteFreeAlgebra Γ((BigFppfOver.toScheme 𝒞 S hS).obj V, ⊤) d}
    (e : StructureIso m' (m.map ((BigFppfOver.toScheme 𝒞 S hS).map f).appTop.hom)) :
    coverSiteObj V m' ⟶ coverSiteObj T m :=
  ObjectProperty.homMk (coverMap ((BigFppfOver.toScheme 𝒞 S hS).map f)
    (toSpecΓ_appTop_naturality ((BigFppfOver.toScheme 𝒞 S hS).map f)) e)

/-- The morphism of covers lies over `f`. -/
theorem coverSiteMap_hom {T V : BigFppfOver 𝒞 S hS} (f : V ⟶ T)
    {m : FiniteFreeAlgebra Γ((BigFppfOver.toScheme 𝒞 S hS).obj T, ⊤) d}
    {m' : FiniteFreeAlgebra Γ((BigFppfOver.toScheme 𝒞 S hS).obj V, ⊤) d}
    (e : StructureIso m' (m.map ((BigFppfOver.toScheme 𝒞 S hS).map f).appTop.hom)) :
    coverSiteMap f e ≫ coverSiteHom T m = coverSiteHom V m' ≫ f.left := by
  refine 𝒞.inclusion.map_injective ?_
  rw [Functor.map_comp, Functor.map_comp]
  exact coverMap_hom ((BigFppfOver.toScheme 𝒞 S hS).map f)
    (toSpecΓ_appTop_naturality ((BigFppfOver.toScheme 𝒞 S hS).map f)) e

/-- The morphism of `ℋ_d` attached to a morphism `f` of the big fppf site over `S` and an
isomorphism of a structure over the source with the extension of scalars of a structure over the
target: the base component is `f`, and the cover component is the morphism of covers, which
presents the source cover as the base change of the target cover along `f`. -/
noncomputable def specCoverHom {T V : BigFppfOver 𝒞 S hS} (f : V ⟶ T)
    {m : FiniteFreeAlgebra Γ((BigFppfOver.toScheme 𝒞 S hS).obj T, ⊤) d}
    {m' : FiniteFreeAlgebra Γ((BigFppfOver.toScheme 𝒞 S hS).obj V, ⊤) d}
    (e : StructureIso m' (m.map ((BigFppfOver.toScheme 𝒞 S hS).map f).appTop.hom)) :
    specCoverObject V m' ⟶ specCoverObject T m where
  f := f
  g := Over.homMk (coverSiteMap f e) (by
    change coverSiteMap f e ≫ coverSiteHom T m ≫ T.hom = coverSiteHom V m' ≫ V.hom
    rw [← Category.assoc, coverSiteMap_hom, Category.assoc, Over.w f])
  square := isPullback_of_isPullback_toScheme
    (isPullback_coverMap ((BigFppfOver.toScheme 𝒞 S hS).map f)
      (toSpecΓ_appTop_naturality ((BigFppfOver.toScheme 𝒞 S hS).map f)) e)

/-! ### The 1-morphism `Spec` -/

variable (𝒞 S hS d)

/-- The fibre component of a composite in the pointwise groupoid fibration is the composite of
the fibre components, with no coherence isomorphism left over: the pullback functors of a
presheaf of categories compose strictly, so the coherence isomorphism of
`CategoryTheory.PresheafOfCategories.comp_fiber` is an identity. -/
theorem comp_fiber {X Y Z : (CategoryTheory.presheafOfGroupoids (ffaSitePresheaf 𝒞 S hS d)).obj}
    (u : X ⟶ Y) (v : Y ⟶ Z) :
    (u ≫ v).fiber =
      u.fiber ≫ ((ffaSitePresheaf 𝒞 S hS d ⋙ Grpd.forgetToCat).map u.base.op).toFunctor.map
        v.fiber :=
  (CategoryTheory.PresheafOfCategories.comp_fiber
      (ffaSitePresheaf 𝒞 S hS d ⋙ Grpd.forgetToCat) u v).trans
    ((Category.assoc _ _ _).symm.trans (Category.comp_id _))

/-- **The 1-morphism `Spec` of the proof of Stacks 05YQ.** From the pointwise groupoid
fibration of free rank-`d` algebra structures over the big fppf site over `S` into the
category `ℋ_d` of degree-`d`
finite locally free covers: it sends a structure on the global sections of an object of the site
to the spectrum of its algebra, base changed to that object. -/
noncomputable def specFiniteCover :
    (CategoryTheory.presheafOfGroupoids (ffaSitePresheaf 𝒞 S hS d)).obj ⥤
      AlgebraicGeometry.Stack.FiniteCover 𝒞 S hS d where
  obj X := specCoverObject X.base X.fiber
  map u := specCoverHom u.base u.fiber
  map_id X := by
    refine AlgebraicGeometry.Stack.FiniteCover.Hom.ext rfl ?_
    refine (BigFppfOver.toScheme 𝒞 S hS).map_injective ?_
    exact coverMap_id X.fiber
      (toSpecΓ_appTop_naturality (𝟙 ((BigFppfOver.toScheme 𝒞 S hS).obj X.base)))
  map_comp u v := by
    refine AlgebraicGeometry.Stack.FiniteCover.Hom.ext rfl ?_
    refine (BigFppfOver.toScheme 𝒞 S hS).map_injective ?_
    rw [comp_fiber 𝒞 S hS d u v]
    exact (coverMap_comp ((BigFppfOver.toScheme 𝒞 S hS).map u.base)
      ((BigFppfOver.toScheme 𝒞 S hS).map v.base)
      (toSpecΓ_appTop_naturality ((BigFppfOver.toScheme 𝒞 S hS).map u.base))
      (toSpecΓ_appTop_naturality ((BigFppfOver.toScheme 𝒞 S hS).map v.base))
      (toSpecΓ_appTop_naturality ((BigFppfOver.toScheme 𝒞 S hS).map (u.base ≫ v.base)))
      u.fiber v.fiber).symm

/-- **Part of the proof of Stacks 05YQ.** `Spec` is a 1-morphism of categories fibred in
groupoids over the big fppf site over `S`: it is strictly over the site, since both
projections read off the base component,
and it preserves strongly cartesian morphisms, since `ℋ_d` is fibred in groupoids and in such a
category every morphism lying over a base morphism is strongly cartesian. -/
theorem isFibredOneMorphism_specFiniteCover :
    (CategoryTheory.presheafOfGroupoids (ffaSitePresheaf 𝒞 S hS d)).p.IsFibredOneMorphism
      (AlgebraicGeometry.Stack.finiteCoverProjection (B := 𝒞) (S := S) (hS := hS) (d := d))
      (specFiniteCover 𝒞 S hS d) where
  comp_eq := rfl
  map_isStronglyCartesian := by
    intro R T f a b φ h
    have := h
    have hlift := Functor.isHomLift_map_of_comp_eq
      (show specFiniteCover 𝒞 S hS d ⋙
        AlgebraicGeometry.Stack.finiteCoverProjection (B := 𝒞) (S := S) (hS := hS) (d := d) =
          (CategoryTheory.presheafOfGroupoids (ffaSitePresheaf 𝒞 S hS d)).p from rfl) f φ
    exact (AlgebraicGeometry.Stack.isFiberedInGroupoids_finiteCoverProjection
      (B := 𝒞) (S := S) (hS := hS) (d := d)).isStronglyCartesian_homLift f _

end AlgebraicGeometry.FiniteFreeAlgebra

end
