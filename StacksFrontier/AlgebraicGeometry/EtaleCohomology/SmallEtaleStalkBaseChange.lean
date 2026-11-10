module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Geometric stalks of inverse images on small étale sites

Mathlib's points of the small étale site of a scheme `S : Scheme.{u}` are the morphisms
`s : Spec Ω ⟶ S` out of the spectrum of a separably closed field, packaged as
`AlgebraicGeometry.Scheme.pointSmallEtale`, and their fibre functors land in `Type u`. Étale
cohomology on this site is written with coefficients in `Type (max (u + 1) v)`, a universe
incomparable to `Type u`. This file supplies the two facts about that pairing which the
base-change theorems need, and which Mathlib states only for coefficients in the point's own
universe:

* the stalk of an inverse image is the stalk of the original sheaf at the image geometric point,
  and
* a family of geometric points covering the scheme detects isomorphisms of sheaves of
  `Type (max (u + 1) v)`.

The first is the geometric content: base change `smallEtaleBaseChange i` along `i : Z ⟶ X`
carries an étale `X`-scheme `U` to `U ×_X Z`, and a lift of `s : Spec Ω ⟶ Z` to `U ×_X Z` is the
same thing as a lift of `s ≫ i` to `U`, because `Over.map i ⊣ Over.pullback i`. That bijection is
natural in `U`, so the fibre functor of `pointSmallEtale (s ≫ i)` is base change followed by the
fibre functor of `pointSmallEtale s`; transporting it through the left Kan extension and
sheafification that define `smallEtaleInverseImage` gives the comparison of stalk functors.

The second is universe bookkeeping done by hand rather than through a universe-lifted point:
`ObjectProperty.IsConservativeFamilyOfPoints` asks the coefficient category to be concrete over
the point's universe, so Mathlib's conservativity of the geometric points says nothing about
sheaves of `Type (max (u + 1) v)`. Local injectivity and local surjectivity of a map of such
sheaves are nevertheless detected by the `Type u`-valued fibres, since both are conditions on
germs; proving them separately and appealing to `Sheaf.isLocallyBijective_iff_isIso` avoids
raising the universe of the points at all.

## Main definitions

* `CategoryTheory.GrothendieckTopology.Point.presheafFiberLanIso` — for sites `(C, J)`, `(D, K)`,
  a functor `G : C ⥤ D` and points whose fibre functors are identified by `G`, the presheaf fibre
  of the left Kan extension along `G.op` is the presheaf fibre of the original.
* `Stacks.EtaleCohomology.pointSmallEtaleBaseChangeFiberIso` — the fibre functor of
  `pointSmallEtale (s ≫ i)` is base change along `i` followed by the fibre functor of
  `pointSmallEtale s`.
* `Stacks.EtaleCohomology.smallEtaleInverseImageStalkIso` — the stalk of `i⁻¹ F` at `s` is the
  stalk of `F` at `s ≫ i`.
* `Stacks.EtaleCohomology.residueGeometricPoint` — the geometric point over `x : X` given by a
  separable closure of the residue field at `x`.

## Main results

* `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.isIso_of_sheafFiber_map` — a
  `w`-small conservative family of points relative to `w` detects isomorphisms of sheaves of
  `Type (max w v)` for any `v`.
* `Stacks.EtaleCohomology.isIso_of_geometricStalk_family` — a map of sheaves of
  `Type (max (u + 1) v)` on the small étale site is an isomorphism as soon as its stalk maps at a
  family of geometric points whose images cover the scheme are.
* `Stacks.EtaleCohomology.isIso_of_forall_geometricStalk` — the same with the family taken to be
  all geometric points, which is how the source states it.
* `Stacks.EtaleCohomology.residueGeometricPoint_apply` — `residueGeometricPoint X x` lies
  over `x`.

## Implementation notes

No declaration here carries a Stacks tag. `smallEtaleInverseImageStalkIso` is one declaration of
the covering set of Tag 03Q1, whose remaining parts (the germ formula, and the corresponding
statement for abelian coefficients) are not proved here, and
`isIso_of_geometricStalk_family` is a fragment of Tag 03PU, which also asserts exactness of the
stalk functors. Tagging either would make the dashboard report the whole tag as formalized.

## References

* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 040R](https://stacks.math.columbia.edu/tag/040R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe w w' v' u' v u

namespace CategoryTheory.GrothendieckTopology.Point

/-- Let `G : C ⥤ D` be a functor between sites `(C, J)` and `(D, K)`, let `Φ` be a point of
`(C, J)` and `Ψ` a point of `(D, K)`, and suppose the fibre functor of `Φ` is `G` followed by
that of `Ψ`. Then the presheaf fibre of `Ψ` applied to a left Kan extension along `G.op` is the
presheaf fibre of `Φ`.

Both functors `(Cᵒᵖ ⥤ Type _) ⥤ Type _` are left adjoints — of `G.op`-precomposition after the
skyscraper functor of `Ψ`, and of the skyscraper functor of `Φ` respectively — and the hypothesis
identifies those two right adjoints, since a skyscraper is a product indexed by the fibre and the
indexing is contravariant. -/
public def presheafFiberLanIso
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (Φ : GrothendieckTopology.Point.{w} J)
    (Ψ : GrothendieckTopology.Point.{w} K) (G : C ⥤ D)
    [∀ (F : Cᵒᵖ ⥤ Type (max w w')), G.op.HasLeftKanExtension F]
    (e : Φ.fiber ≅ G ⋙ Ψ.fiber) :
    G.op.lan ⋙ Ψ.presheafFiber (A := Type (max w w')) ≅
      Φ.presheafFiber (A := Type (max w w')) := by
  have eSky :
      Ψ.skyscraperPresheafFunctor (A := Type (max w w')) ⋙
          (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type (max w w'))).obj G.op ≅
        Φ.skyscraperPresheafFunctor (A := Type (max w w')) := by
    dsimp [GrothendieckTopology.Point.skyscraperPresheafFunctor]
    exact (CategoryTheory.flipFunctor _ _ _).mapIso
      (Functor.isoWhiskerRight (NatIso.op e) piConst.flip)
  exact Adjunction.leftAdjointUniq
    (((G.op.lanAdjunction (Type (max w w'))).comp
      (Ψ.skyscraperPresheafAdjunction (A := Type (max w w')))).ofNatIsoRight eSky)
    (Φ.skyscraperPresheafAdjunction (A := Type (max w w')))

end CategoryTheory.GrothendieckTopology.Point

namespace CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints

/-- A `w`-small conservative family of points of a site, relative to the universe `w`, detects
isomorphisms of sheaves of `Type (max w v)` for an arbitrary `v`.

Mathlib's `ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectIsomorphisms` needs the
coefficient category to be concrete over `w`, which `Type (max w v)` is not. Local injectivity
and local surjectivity are conditions on germs, so the `Type w`-valued fibre functors see them
even at these coefficients; `Sheaf.isLocallyBijective_iff_isIso` then concludes. -/
public lemma isIso_of_sheafFiber_map
    {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
    (P : ObjectProperty (GrothendieckTopology.Point.{w} J))
    [LocallySmall.{w} C] [ObjectProperty.Small.{w} P]
    [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
    (hP : P.IsConservativeFamilyOfPoints)
    {F G : Sheaf J (Type (max w v))} (f : F ⟶ G)
    (hf : ∀ (Φ : P.FullSubcategory), IsIso (Φ.obj.sheafFiber.map f)) : IsIso f := by
  classical
  have cover {X : C} (R : Sieve X)
      (hR : ∀ (Φ : P.FullSubcategory) (x : Φ.obj.fiber.obj X),
        ∃ (Y : C) (g : Y ⟶ X) (_ : R g) (y : Φ.obj.fiber.obj Y),
          Φ.obj.fiber.map g y = x) : R ∈ J X := by
    obtain ⟨α, Y, g, rfl⟩ := R.exists_eq_ofArrows
    refine (hP.jointly_reflect_ofArrows_mem_of_small g).2 fun Φ x => ?_
    obtain ⟨W, a, ha, w, hw⟩ := hR Φ x
    obtain ⟨i, b, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 ha
    exact ⟨i, Φ.obj.fiber.map b w, by simpa using hw⟩
  have hinj : Sheaf.IsLocallyInjective f := ⟨by
    intro X x y h
    refine cover _ fun Φ t => ?_
    have ht : Φ.obj.toPresheafFiber X.unop t F.obj x =
        Φ.obj.toPresheafFiber X.unop t F.obj y := by
      apply ((isIso_iff_bijective _).1 (hf Φ)).1
      change Φ.obj.presheafFiber.map f.hom _ = Φ.obj.presheafFiber.map f.hom _
      simp [h]
    obtain ⟨Y, g, z, hz, heq⟩ := (Φ.obj.toPresheafFiber_eq_iff' _ _ _ _).1 ht
    exact ⟨Y, g, heq, z, hz⟩⟩
  have hsurj : Sheaf.IsLocallySurjective f := ⟨by
    intro X y
    refine cover _ fun Φ t => ?_
    obtain ⟨a, ha⟩ := ((isIso_iff_bijective _).1 (hf Φ)).2
      (Φ.obj.toPresheafFiber X t G.obj y)
    obtain ⟨Y, z, x, rfl⟩ := Φ.obj.toPresheafFiber_jointly_surjective (P := F.obj) a
    let T : Φ.obj.fiber.Elements := Φ.obj.fiber.elementsMk X t
    let V : Φ.obj.fiber.Elements := Φ.obj.fiber.elementsMk Y z
    let W := IsCofiltered.min T V
    let l := IsCofiltered.minToLeft T V
    let r := IsCofiltered.minToRight T V
    have hw : Φ.obj.toPresheafFiber W.obj W.val G.obj (f.hom.app _ (F.obj.map r.hom.op x)) =
        Φ.obj.toPresheafFiber W.obj W.val G.obj (G.obj.map l.hom.op y) := by
      rw [f.hom.naturality_apply, GrothendieckTopology.Point.toPresheafFiber_w_apply,
        GrothendieckTopology.Point.toPresheafFiber_w_apply, l.map_val, r.map_val]
      change Φ.obj.presheafFiber.map f.hom _ = _ at ha
      simpa using ha
    obtain ⟨V', g, z', hz', heq⟩ := (Φ.obj.toPresheafFiber_eq_iff' _ _ _ _).1 hw
    refine ⟨V', g ≫ l.hom, ⟨F.obj.map g.op (F.obj.map r.hom.op x), ?_⟩, z', ?_⟩
    · rw [f.hom.naturality_apply, heq]
      simp only [op_comp, Functor.map_comp]
      rfl
    · simp only [Functor.map_comp, types_comp_apply, hz']
      exact l.map_val⟩
  exact (Sheaf.isLocallyBijective_iff_isIso f).1 ⟨hinj, hsurj⟩

end CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints

namespace Stacks.EtaleCohomology

/-- A lift of the geometric point `s : Spec Ω ⟶ Z` to the base change `U ×_X Z` of an étale
`X`-scheme `U` is the same thing as a lift of `s ≫ i` to `U`, naturally in `U`: the fibre functor
of `pointSmallEtale (s ≫ i)` is base change along `i` followed by the fibre functor of
`pointSmallEtale s`.

The bijection is the adjunction `Over.map i ⊣ Over.pullback i`, under which the two fibres are
`Over.mk (s ≫ i) ⟶ U` and `Over.mk s ⟶ U ×_X Z`; naturality is
`Adjunction.homEquiv_naturality_right`. -/
public def pointSmallEtaleBaseChangeFiberIso
    {Z X : Scheme.{u}} (i : Z ⟶ X) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ Z) :
    (Scheme.pointSmallEtale (s ≫ i)).fiber ≅
      smallEtaleBaseChange i ⋙ (Scheme.pointSmallEtale s).fiber := by
  let adj := Over.mapPullbackAdj i
  let component (U : X.Etale) :
      ((Scheme.pointSmallEtale (s ≫ i)).fiber.obj U) ≃
        ((smallEtaleBaseChange i ⋙ (Scheme.pointSmallEtale s).fiber).obj U) := by
    change ((Over.map i).obj (Over.mk s) ⟶ (Etale.forget X).obj U) ≃ _
    exact adj.homEquiv _ _
  refine NatIso.ofComponents (fun U => (component U).toIso) fun {U V} f => ?_
  ext a
  change ((Over.map i).obj (Over.mk s) ⟶ (Etale.forget X).obj U) at a
  dsimp [component, Scheme.pointSmallEtale_fiber, smallEtaleBaseChange]
  exact adj.homEquiv_naturality_right a ((Etale.forget X).map f)

/-- **Stalks of an inverse image.** For `i : Z ⟶ X` and a geometric point `s : Spec Ω ⟶ Z`, the
stalk at `s` of the inverse image `i⁻¹ F` of a sheaf of sets on the small étale site of `X` is the
stalk of `F` at the image geometric point `s ≫ i`, naturally in `F`.

`smallEtaleInverseImage i` is the left Kan extension along the opposite of base change followed
by sheafification, so the statement is `presheafFiberLanIso` for the fibre identification
`pointSmallEtaleBaseChangeFiberIso`, composed with the fact that the presheaf fibre of a point
factors through sheafification. -/
@[sga "4½ Arcata 2.3.3"]
public def smallEtaleInverseImageStalkIso
    {Z X : Scheme.{u}} (i : Z ⟶ X) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ Z) :
    smallEtaleInverseImage.{u, v} i ⋙ (pointSmallEtale s).sheafFiber ≅
      (pointSmallEtale (s ≫ i)).sheafFiber :=
  Functor.isoWhiskerLeft (sheafToPresheaf (smallEtaleTopology X)
    (Type (max (u + 1) v)))
    ((Functor.associator (smallEtaleBaseChange i).op.lan
        (presheafToSheaf (smallEtaleTopology Z) (Type (max (u + 1) v)))
        (pointSmallEtale s).sheafFiber).symm ≪≫
      Functor.isoWhiskerLeft (smallEtaleBaseChange i).op.lan
        ((pointSmallEtale s).presheafToSheafCompSheafFiberIso (Type (max (u + 1) v))) ≪≫
      GrothendieckTopology.Point.presheafFiberLanIso.{u, max (u + 1) v, u, u + 1, u, u + 1}
        (pointSmallEtale (s ≫ i)) (pointSmallEtale s)
        _ (pointSmallEtaleBaseChangeFiberIso i s))

/-- **Geometric stalks detect isomorphisms.** A map of sheaves of `Type (max (u + 1) v)` on the
small étale site of `X : Scheme.{u}` is an isomorphism as soon as its map on stalks is an
isomorphism at every member of a family of geometric points `s t : Spec (Ω t) ⟶ X`, with `Ω t`
separably closed, whose images cover `X`. -/
public lemma isIso_of_geometricStalk_family
    {X : Scheme.{u}} {ι : Type u} {Ω : ι → Type u}
    [∀ t, Field (Ω t)] [∀ t, IsSepClosed (Ω t)]
    (s : ∀ t, Spec (.of (Ω t)) ⟶ X) (hs : ⋃ t, Set.range (s t) = Set.univ)
    {F G : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v))} (f : F ⟶ G)
    (hf : ∀ t, IsIso ((pointSmallEtale (s t)).sheafFiber.map f)) : IsIso f :=
  ObjectProperty.IsConservativeFamilyOfPoints.isIso_of_sheafFiber_map.{u, u, u + 1,
      max (u + 1) v}
    (ObjectProperty.ofObj (fun t => pointSmallEtale (s t)))
    (Scheme.isConservative_pointSmallEtale s hs) f (by rintro ⟨_, ⟨t⟩⟩; exact hf t)

/-- The geometric point of `X` lying over `x : X`, given by a separable closure of the residue
field at `x`. The family of these, as `x` ranges over `X`, covers `X`. -/
public def residueGeometricPoint (X : Scheme.{u}) (x : X) :
    Spec (.of (SeparableClosure (X.residueField x))) ⟶ X :=
  (SpecToEquivOfField (SeparableClosure (X.residueField x)) X).symm
    ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩

/-- `residueGeometricPoint X x` lies over `x`. -/
public lemma residueGeometricPoint_apply (X : Scheme.{u}) (x : X)
    (t : Spec (.of (SeparableClosure (X.residueField x)))) :
    residueGeometricPoint X x t = x := by
  simp [residueGeometricPoint, SpecToEquivOfField]

/-- **Geometric stalks detect isomorphisms**, in the form the source states it: a map of sheaves
of `Type (max (u + 1) v)` on the small étale site of `X` is an isomorphism as soon as its map on
stalks is an isomorphism at *every* geometric point of `X`.

This is `isIso_of_geometricStalk_family` for the covering family
`residueGeometricPoint`, whose members lie over the points of `X` and therefore have images
covering `X`. -/
public lemma isIso_of_forall_geometricStalk {X : Scheme.{u}}
    {F G : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v))} (f : F ⟶ G)
    (hf : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      IsIso ((pointSmallEtale s).sheafFiber.map f)) : IsIso f :=
  isIso_of_geometricStalk_family (residueGeometricPoint X)
    (Set.eq_univ_of_forall fun x =>
      Set.mem_iUnion.2 ⟨x, default, residueGeometricPoint_apply X x default⟩)
    f fun _ => hf _ _

end Stacks.EtaleCohomology

end
