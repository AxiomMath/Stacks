module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Examples.Geometric.Base
public import StacksFrontier.Deformation.Predeformation.Basic

/-!
# Deformations of an algebraic space (Stacks 0E3Z)

Fix a big fppf site `B` containing `Spec Λ` and the spectrum of every object of `𝒞_Λ`. A
*flat family of algebraic spaces* is an object `A` of `𝒞_Λ` together with an algebraic space
over `Spec A`, flat over it, both presented on `B` over `Spec Λ`. A morphism
`(B', Y) ⟶ (A, X)` is a morphism `A ⟶ B'` of `𝒞_Λ` — note the direction: the family is
covariant in the coefficient algebra — together with a morphism `X ⟶ Y` of spaces making the
square over `Spec A ⟶ Spec B'` cartesian. Forgetting the space gives a functor to `𝒞_Λ`, and
that functor is cofibered in groupoids, the cocartesian lift being the base change.

For an algebraic space `X` over the residue field `k`, the pair `(k, X)` is a flat family —
every algebraic space over a field is flat over it — and the *deformation category* of `X` is
the category of flat families over `(k, X)`.

## Main definitions

* `AlgebraicGeometry.BigFppfSite.homOfContains`: a morphism of schemes contained in the site,
  read as a morphism of the site.
* `Deformation.Examples.spaceBaseOver`: the spectrum of an object of `𝒞_Λ`, as an object of
  the big fppf site over `Spec Λ`.
* `Deformation.Examples.FlatAlgebraicSpaceFamily` and its `Hom`, category structure and
  projection `flatAlgebraicSpaceFamilyFunctor`: **Stacks 0E3Z**, the category `ℱ`.
* `Deformation.Examples.spaceSpecialFiber`: the family `(k, X)`.
* `Deformation.Examples.spaceDeformationProjection`: the structure functor of the deformation
  category of `X`.

## Main results

* `Deformation.Examples.flatAlgebraicSpaceFamilyFunctor_isCofiberedInGroupoids`:
  **Stacks 0E3Z**, the projection is cofibered in groupoids.
* `Deformation.Examples.isFlat_of_over_residueField`: an algebraic space over `Spec k` is flat
  over it, which is what makes `(k, X)` a family.

## Implementation notes

All spaces live as presheaves on one big fppf site over `Spec Λ`, so the cartesian condition
on a morphism is a pullback square of presheaves and no comparison of ambient sites is needed.
The containment hypotheses `hΛ` and `hSpec` are explicit arguments rather than instances,
matching the way the representation of algebraic spaces of Stacks 025Y is parameterized.

Flatness of a space over a field is proved from the one-chart form of Stacks 03MJ: the
structure morphism of any étale chart lands in `Spec k`, whose target is a one-point integral
scheme, so flatness of the chart is automatic, and surjectivity of the chart is what the atlas
of Stacks 025Y provides.

The residue-field object is `Deformation.Examples.residueFieldBase`, the object of `𝒞_Λ` whose
carrier is exactly `k`, so that an algebraic space over `Spec k` is literally a space over the
spectrum of the base of the special fibre.

## References

* [Stacks Project, Tag 0E3Z](https://stacks.math.columbia.edu/tag/0E3Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.BigFppfSite

/-- A morphism between two schemes contained in a big fppf site, read as a morphism of the
site's underlying category. The site's inclusion into schemes is fully faithful, so this is
the inverse of applying it. -/
public def homOfContains (B : BigFppfSite.{u}) {X Y : Scheme.{u}} (hX : B.Contains X)
    (hY : B.Contains Y) (f : X ⟶ Y) : B.obj hX ⟶ B.obj hY :=
  B.inclusion.preimage (X := B.obj hX) (Y := B.obj hY) f

/-- `homOfContains` sends the identity of a scheme to the identity in the site. -/
@[simp]
public theorem homOfContains_id (B : BigFppfSite.{u}) {X : Scheme.{u}}
    (hX : B.Contains X) : B.homOfContains hX hX (𝟙 X) = 𝟙 _ := by
  simpa [homOfContains, BigFppfSite.obj, BigFppfSite.inclusion] using
    (Functor.preimage_id (F := B.inclusion) (X := B.obj hX))

/-- `homOfContains` sends a composite of morphisms of schemes to the composite in the site. -/
public theorem homOfContains_comp (B : BigFppfSite.{u}) {X Y Z : Scheme.{u}}
    (hX : B.Contains X) (hY : B.Contains Y) (hZ : B.Contains Z) (f : X ⟶ Y) (g : Y ⟶ Z) :
    B.homOfContains hX hZ (f ≫ g) =
      B.homOfContains hX hY f ≫ B.homOfContains hY hZ g := by
  simpa only [homOfContains] using (Functor.preimage_comp (F := B.inclusion)
    (X := B.obj hX) (Y := B.obj hY) (Z := B.obj hZ) f g)

end AlgebraicGeometry.BigFppfSite

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))

/-- The spectrum of an object of `𝒞_Λ`, as an object of the big fppf site over `Spec Λ`. -/
public abbrev spaceBaseOver (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    BigFppfOver B (Spec (.of Λ)) hΛ :=
  Over.mk (B.homOfContains (hSpec A) hΛ (Spec.map (CommRingCat.ofHom (algebraMap Λ A))))

/-- The morphism of spectra over `Spec Λ` induced by a morphism of `𝒞_Λ`, contravariantly. -/
public def spaceBaseOverMap {A A' : ArtinianLocalAlgCat.{u, u, u} Λ k} (f : A ⟶ A') :
    spaceBaseOver B hΛ hSpec A' ⟶ spaceBaseOver B hΛ hSpec A :=
  Over.homMk (B.homOfContains (hSpec A') (hSpec A)
    (Spec.map (CommRingCat.ofHom f.hom.toRingHom))) (by
      change B.homOfContains (hSpec A') (hSpec A)
          (Spec.map (CommRingCat.ofHom f.hom.toRingHom)) ≫
        B.homOfContains (hSpec A) hΛ (Spec.map (CommRingCat.ofHom (algebraMap Λ A))) =
        B.homOfContains (hSpec A') hΛ (Spec.map (CommRingCat.ofHom (algebraMap Λ A')))
      rw [← BigFppfSite.homOfContains_comp]
      congr 1
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 1
      ext r
      exact f.hom.commutes r)

/-- `spaceBaseOverMap` sends the identity of an object of `𝒞_Λ` to the identity. -/
@[simp]
public theorem spaceBaseOverMap_id (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    spaceBaseOverMap B hΛ hSpec (𝟙 A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change B.homOfContains (hSpec A) (hSpec A)
    (Spec.map (CommRingCat.ofHom (𝟙 A : A ⟶ A).hom.toRingHom)) = 𝟙 _
  rw [ArtinianLocalAlgCat.id_hom]
  change B.homOfContains (hSpec A) (hSpec A)
    (Spec.map (CommRingCat.ofHom (RingHom.id A))) = 𝟙 _
  rw [CommRingCat.ofHom_id, Spec.map_id, BigFppfSite.homOfContains_id]

/-- `spaceBaseOverMap` sends `f ≫ g` to the composite in the opposite order: it is
contravariant. -/
public theorem spaceBaseOverMap_comp {A A' A'' : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (f : A ⟶ A') (g : A' ⟶ A'') :
    spaceBaseOverMap B hΛ hSpec (f ≫ g) =
      spaceBaseOverMap B hΛ hSpec g ≫ spaceBaseOverMap B hΛ hSpec f := by
  apply Over.OverMorphism.ext
  change B.homOfContains (hSpec A'') (hSpec A)
      (Spec.map (CommRingCat.ofHom (f ≫ g).hom.toRingHom)) =
    B.homOfContains (hSpec A'') (hSpec A')
      (Spec.map (CommRingCat.ofHom g.hom.toRingHom)) ≫
      B.homOfContains (hSpec A') (hSpec A)
        (Spec.map (CommRingCat.ofHom f.hom.toRingHom))
  rw [← BigFppfSite.homOfContains_comp]
  simp [ArtinianLocalAlgCat.comp_hom, AlgHom.comp_toRingHom, ← CommRingCat.ofHom_comp,
    ← Spec.map_comp]

/-- **Stacks 0E3Z.** A flat family of algebraic spaces: an object of `𝒞_Λ` together with an
algebraic space over its spectrum, flat over it. -/
@[stacks 0E3Z "the category ℱ: objects"]
public structure FlatAlgebraicSpaceFamily where
  /-- The coefficient algebra. -/
  base : ArtinianLocalAlgCat.{u, u, u} Λ k
  /-- The underlying presheaf on the big fppf site over `Spec Λ`. -/
  space : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u
  /-- The presheaf is an algebraic space. -/
  algebraic : IsAlgebraicSpace B (Spec (.of Λ)) hΛ space
  /-- The structure morphism to the spectrum of the coefficient algebra. -/
  toBase : space ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec base)
  /-- The structure morphism is flat. -/
  flat : Space.IsFlat B (Spec (.of Λ)) hΛ toBase

namespace FlatAlgebraicSpaceFamily

/-- **Stacks 0E3Z.** A morphism of flat families, covariant on coefficient algebras: a
morphism of the coefficient algebras together with a cartesian morphism of spaces over it. -/
@[ext, stacks 0E3Z "the category ℱ: morphisms"]
public structure Hom (P Q : FlatAlgebraicSpaceFamily B hΛ hSpec) where
  /-- The morphism of coefficient algebras. -/
  base : P.base ⟶ Q.base
  /-- The morphism of spaces, in the reverse direction. -/
  map : Q.space ⟶ P.space
  /-- The square over the morphism of spectra is cartesian. -/
  cartesian : IsPullback map Q.toBase P.toBase
    (yoneda.map (spaceBaseOverMap B hΛ hSpec base))

/-- **Stacks 0E3Z.** Flat families of algebraic spaces and their cartesian morphisms form a
category; composition pastes two cartesian squares. -/
@[stacks 0E3Z "the category ℱ"]
public instance instCategory : Category (FlatAlgebraicSpaceFamily B hΛ hSpec) where
  Hom := Hom B hΛ hSpec
  id P :=
    { base := 𝟙 P.base
      map := 𝟙 P.space
      cartesian := by
        rw [spaceBaseOverMap_id]
        exact IsPullback.id_horiz P.toBase }
  comp f g :=
    { base := f.base ≫ g.base
      map := g.map ≫ f.map
      cartesian := by
        rw [spaceBaseOverMap_comp, yoneda.map_comp]
        exact g.cartesian.paste_horiz f.cartesian }
  id_comp := by intros; ext <;> simp
  comp_id := by intros; ext <;> simp
  assoc := by intros; ext <;> simp [Category.assoc]

/-- A morphism `r : P ⟶ R` factors uniquely through `g : P ⟶ Q` over any factorization
`g.base ≫ b = r.base` of its coefficient morphism, since `g` is cartesian. -/
private theorem existsUnique_comp_eq {P Q R : FlatAlgebraicSpaceFamily B hΛ hSpec}
    (g : P ⟶ Q) (r : P ⟶ R) (b : Q.base ⟶ R.base) (hb : g.base ≫ b = r.base) :
    ∃! d : Q ⟶ R, d.base = b ∧ g ≫ d = r := by
  let bmap := yoneda.map (spaceBaseOverMap B hΛ hSpec b)
  let gmap := yoneda.map (spaceBaseOverMap B hΛ hSpec g.base)
  have hbasecomp : bmap ≫ gmap = yoneda.map (spaceBaseOverMap B hΛ hSpec r.base) := by
    rw [← yoneda.map_comp, ← spaceBaseOverMap_comp, hb]
  have hsq : r.map ≫ P.toBase = (R.toBase ≫ bmap) ≫ gmap := by
    simpa only [Category.assoc, hbasecomp] using r.cartesian.w
  let m : R.space ⟶ Q.space :=
    g.cartesian.isLimit.lift (PullbackCone.mk r.map (R.toBase ≫ bmap) hsq)
  have hmleft : m ≫ g.map = r.map := g.cartesian.lift_fst r.map (R.toBase ≫ bmap) hsq
  have hmright : m ≫ Q.toBase = R.toBase ≫ bmap :=
    g.cartesian.lift_snd r.map (R.toBase ≫ bmap) hsq
  have houter : IsPullback (m ≫ g.map) R.toBase P.toBase (bmap ≫ gmap) := by
    simpa only [hmleft, hbasecomp] using r.cartesian
  let d : Q ⟶ R :=
    { base := b
      map := m
      cartesian := IsPullback.of_right houter hmright g.cartesian }
  refine ⟨d, ⟨rfl, Hom.ext hb hmleft⟩, ?_⟩
  rintro d' ⟨rfl, hd'⟩
  have hleft : d'.map ≫ g.map = r.map := congrArg (fun j : P ⟶ R => j.map) hd'
  exact Hom.ext rfl <|
    g.cartesian.hom_ext (hleft.trans hmleft.symm) (d'.cartesian.w.trans hmright.symm)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site goes deep
/-- Pullbacks of presheaves on the big fppf site over `Spec Λ` (instance search times out
without this shortcut). -/
private instance hasPullbacks_presheaf :
    HasPullbacks ((BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf
    {X Y Z : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The base change of a flat family `P` along a morphism `f : P.base ⟶ A` of `𝒞_Λ`: the
fibre product of `P.space` with `Spec A` over `Spec P.base`, flat over `Spec A`. -/
private def baseChange (P : FlatAlgebraicSpaceFamily B hΛ hSpec)
    {A : ArtinianLocalAlgCat.{u, u, u} Λ k} (f : P.base ⟶ A) :
    FlatAlgebraicSpaceFamily B hΛ hSpec :=
  let Pspace : AlgebraicSpaces B (Spec (.of Λ)) hΛ := ⟨P.space, P.algebraic⟩
  let yo (A : ArtinianLocalAlgCat.{u, u, u} Λ k) : AlgebraicSpaces B (Spec (.of Λ)) hΛ :=
    ⟨yoneda.obj (spaceBaseOver B hΛ hSpec A),
      isAlgebraicSpace_yoneda B (Spec (.of Λ)) hΛ (spaceBaseOver B hΛ hSpec A)⟩
  let Pbase := yo P.base
  let Abase := yo A
  let a : Pspace ⟶ Pbase := ObjectProperty.homMk P.toBase
  let b : Abase ⟶ Pbase := ObjectProperty.homMk <| yoneda.map (spaceBaseOverMap B hΛ hSpec f)
  let q := AlgebraicSpaces.fiberProduct B (Spec (.of Λ)) hΛ a b
  { base := A
    space := q.obj
    algebraic := q.property
    toBase := pullback.snd P.toBase (yoneda.map (spaceBaseOverMap B hΛ hSpec f))
    flat := by
      let _ := Space.isFlat_isStableUnderBaseChange B (Spec (.of Λ)) hΛ
      change Space.IsFlat B (Spec (.of Λ)) hΛ
        (pullback.snd P.toBase (yoneda.map (spaceBaseOverMap B hΛ hSpec f)))
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := fun ⦃F G : AlgebraicSpaces B (Spec (.of Λ)) hΛ⦄ (g : F ⟶ G) =>
          Space.IsFlat B (Spec (.of Λ)) hΛ g.hom)
        (AlgebraicSpaces.isPullback_fiberProduct B (Spec (.of Λ)) hΛ a b)
        (show Space.IsFlat B (Spec (.of Λ)) hΛ a.hom from P.flat) }

/-- The cartesian morphism from a flat family to its base change along `f`, lying over `f`. -/
private def toBaseChange (P : FlatAlgebraicSpaceFamily B hΛ hSpec)
    {A : ArtinianLocalAlgCat.{u, u, u} Λ k} (f : P.base ⟶ A) : P ⟶ P.baseChange B hΛ hSpec f where
  base := f
  map := pullback.fst P.toBase (yoneda.map (spaceBaseOverMap B hΛ hSpec f))
  cartesian := IsPullback.of_hasPullback _ _

@[simp]
private theorem toBaseChange_base (P : FlatAlgebraicSpaceFamily B hΛ hSpec)
    {A : ArtinianLocalAlgCat.{u, u, u} Λ k} (f : P.base ⟶ A) :
    (P.toBaseChange B hΛ hSpec f).base = f := rfl

end FlatAlgebraicSpaceFamily

/-- **Stacks 0E3Z.** Forget the space and retain the coefficient algebra. -/
@[stacks 0E3Z "the functor p", implicit_reducible]
public def flatAlgebraicSpaceFamilyFunctor :
    FlatAlgebraicSpaceFamily B hΛ hSpec ⥤ ArtinianLocalAlgCat.{u, u, u} Λ k where
  obj P := P.base
  map f := f.base
  map_id := by intro; rfl
  map_comp := by intros; rfl

/-- The projection sends a flat family to its coefficient algebra. -/
@[simp]
public theorem flatAlgebraicSpaceFamilyFunctor_obj (P : FlatAlgebraicSpaceFamily B hΛ hSpec) :
    (flatAlgebraicSpaceFamilyFunctor B hΛ hSpec).obj P = P.base := rfl

/-- The projection sends a morphism of flat families to its morphism of coefficient
algebras. -/
@[simp]
public theorem flatAlgebraicSpaceFamilyFunctor_map
    {P Q : FlatAlgebraicSpaceFamily B hΛ hSpec} (f : P ⟶ Q) :
    (flatAlgebraicSpaceFamilyFunctor B hΛ hSpec).map f = f.base := rfl

/-- **Stacks 0E3Z.** The projection from flat families of algebraic spaces to their
coefficient algebras is cofibered in groupoids: the cocartesian lift of `A ⟶ A'` is the base
change of the space along `Spec A' ⟶ Spec A`, which is flat because flatness of morphisms of
algebraic spaces is stable under base change. -/
@[stacks 0E3Z "p is cofibred in groupoids"]
public theorem flatAlgebraicSpaceFamilyFunctor_isCofiberedInGroupoids :
    IsCofiberedInGroupoids (flatAlgebraicSpaceFamilyFunctor B hΛ hSpec) := by
  let p := flatAlgebraicSpaceFamilyFunctor B hΛ hSpec
  change p.op.IsFiberedInGroupoids
  refine { exists_lift := ?_, unique_lift := ?_ }
  · intro V U f X hX
    subst U
    refine ⟨.op (X.unop.baseChange B hΛ hSpec f.unop),
      .op (X.unop.toBaseChange B hΛ hSpec f.unop), ?_⟩
    exact IsHomLift.of_fac' (p := p.op) f _ rfl rfl rfl
  · intro x y z φ ψ f h
    obtain ⟨d, ⟨hd₁, hd₂⟩, hd⟩ :=
      FlatAlgebraicSpaceFamily.existsUnique_comp_eq B hΛ hSpec φ.unop ψ.unop f.unop
        (by simpa [p] using congrArg Quiver.Hom.unop h)
    refine ⟨d.op, ⟨Quiver.Hom.unop_inj hd₁, Quiver.Hom.unop_inj hd₂⟩, fun d' hd' => ?_⟩
    exact Quiver.Hom.unop_inj <| hd d'.unop
      ⟨by simpa [p] using congrArg Quiver.Hom.unop hd'.1,
        by simpa using congrArg Quiver.Hom.unop hd'.2⟩

/-! ### The deformation category of an algebraic space over the residue field -/

/-- An algebraic space over the spectrum of the residue field is flat over it: the target of
every étale chart is `Spec k`, over which any morphism is flat, and the atlas of Stacks 025Y
supplies a surjective chart, so the one-chart form of Stacks 03MJ applies. -/
@[stacks 0E3Z "flatness of the special fibre"]
public theorem isFlat_of_over_residueField
    (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
    (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k))) :
    Space.IsFlat B (Spec (.of Λ)) hΛ toK := by
  obtain ⟨U, a, ⟨haSurj, haEtale⟩⟩ := hX.exists_atlas
  let V := spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)
  let h : U ⟶ V := yoneda.preimage (a ≫ toK)
  let T := BigFppfOver.toScheme B (Spec (.of Λ)) hΛ
  let : Subsingleton (T.obj V) := by change Subsingleton (Spec (.of k)); infer_instance
  let : IsIntegral (T.obj V) := by change IsIntegral (Spec (.of k)); infer_instance
  apply (Space.holdsOnEveryEtaleChart_iff_surjectiveChart B (Spec (.of Λ)) hΛ
    (@Flat.{u}) Flat.isEtaleLocalOnSourceAndTarget hX
    (isAlgebraicSpace_yoneda B (Spec (.of Λ)) hΛ V) toK).2
  refine ⟨U, V, a, 𝟙 _, h, haEtale, ?_, haSurj, by simp [h], by infer_instance⟩
  change (MorphismProperty.inverseImage (@Etale.{u}) T).relative yoneda (𝟙 (yoneda.obj V))
  refine ⟨Functor.relativelyRepresentable.of_isIso yoneda (𝟙 (yoneda.obj V)), ?_⟩
  intro A C g fst snd hsquare
  let : IsIso (yoneda.map snd) := hsquare.isIso_snd_of_isIso
  let : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map snd
  exact (inferInstance : Etale (T.map snd))

/-- **Stacks 0E3Z.** An algebraic space `X` over the residue field, as the object `(k, X)` of
the category of flat families. -/
@[stacks 0E3Z "the object x₀"]
public def spaceSpecialFiber (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
    (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k))) :
    FlatAlgebraicSpaceFamily B hΛ hSpec where
  base := residueFieldBase Λ k
  space := X
  algebraic := hX
  toBase := toK
  flat := isFlat_of_over_residueField B hΛ hSpec X hX toK

/-- **Stacks 0E3Z.** The deformation category of an algebraic space `X` over the residue
field, with its structure functor to `𝒞_Λ`: its objects are flat families equipped with a
cartesian morphism to `(k, X)`. -/
@[stacks 0E3Z "the deformation category of X"]
public abbrev spaceDeformationProjection
    (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
    (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k))) :
    Over (spaceSpecialFiber B hΛ hSpec X hX toK) ⥤ ArtinianLocalAlgCat.{u, u, u} Λ k :=
  objectsOverFunctor (flatAlgebraicSpaceFamilyFunctor B hΛ hSpec)
    (spaceSpecialFiber B hΛ hSpec X hX toK)

end Deformation.Examples

end
