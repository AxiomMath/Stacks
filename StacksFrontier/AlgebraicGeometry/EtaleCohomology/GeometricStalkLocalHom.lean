module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.FiniteOverStrictHenselization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.BaseChangeFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.Faithful

/-!
# Locality of the map of étale local rings at a geometric point

Let `a : X ⟶ Y` be a morphism of schemes of a big étale site `B`, let `x̄` be a geometric point
of `X` and let `ȳ = a ∘ x̄` be its image in `Y`. Pulling an étale neighborhood `V / Y` of `ȳ`
back along `a` gives an étale neighborhood `X ×_Y V / X` of `x̄`, and pulling global functions
back along the projection `X ×_Y V ⟶ V` therefore induces a ring map of étale local rings

```
  (𝒪_Y)_ȳ ⟶ (𝒪_X)_x̄.
```

This file constructs that map and proves that it is **local**: it carries the maximal ideal of
`(𝒪_Y)_ȳ` into the maximal ideal of `(𝒪_X)_x̄`.

The proof is the one of the source. Both étale local rings carry the geometric evaluation map
`AlgebraicGeometry.structureSheafStalkToGeometricField` to the algebraically closed field of the
geometric point — the two geometric points have the *same* field, `ȳ` being `x̄` composed with
`a` — and evaluation is itself local by
`AlgebraicGeometry.structureSheafStalkToGeometricField_isLocalHom`, because the étale local ring
is strictly henselian. The triangle

```
  (𝒪_Y)_ȳ ⟶ (𝒪_X)_x̄ ⟶ κ(x̄)   =   (𝒪_Y)_ȳ ⟶ κ(ȳ) = κ(x̄)
```

commutes, since evaluating a germ is evaluating a representing section at the chosen lift and
the lift of `x̄` to `X ×_Y V` projects to the lift of `ȳ` to `V`. A germ over `Y` whose image in
`(𝒪_X)_x̄` is a unit therefore has nonzero value at `x̄`, hence nonzero value at `ȳ`, hence is
already a unit. That is exactly locality of the map of stalks.

## Main definitions

* `AlgebraicGeometry.structureSharpRing` — the structure map of a morphism of schemes on the
  structure presheaves of rings of the small étale sites.
* `AlgebraicGeometry.baseChangeEtaleNeighborhood` — base change of pointed étale neighborhoods
  along `a`, from the neighborhoods of `ȳ` to those of `x̄`.
* `AlgebraicGeometry.etaleLocalRingMap` — the map of étale local rings induced by a morphism of
  schemes at a geometric point of the source and its image.

## Main results

* `AlgebraicGeometry.etaleLocalRingMap_ι` — the map on germs: the germ of a section over an
  étale neighborhood of the image point goes to the germ of its pullback over the base-changed
  neighborhood.
* `AlgebraicGeometry.structureSheafStalkToGeometricField_etaleLocalRingMap` — the triangle of
  geometric evaluation maps commutes.
* `AlgebraicGeometry.etaleLocalRingMap_isLocalHom` — the map of étale local rings is a local
  ring homomorphism.

## Implementation notes

No declaration here carries a Stacks tag. The Stacks project does not state this locality as a
numbered lemma: it occurs only as the one step with mathematical content inside the proof of
Tag 04I5, whose own statement is that the morphism of ringed sites `(a_small, a_small^♯)` is a
morphism of *locally* ringed sites. That statement is not proved in the library — see the
discussion in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/RingedSiteHom.lean` — so
tagging anything here would mark Tag 04I5 as formalized.

The map of stalks is a `CategoryTheory.Limits.colimit.desc` out of the colimit over the étale
neighborhoods of `ȳ` which computes `(𝒪_Y)_ȳ`. Its cocone is assembled by whiskering the colimit
cocone of `(𝒪_X)_x̄` along base change of neighborhoods and precomposing with the structure map,
so the naturality of the cocone is inherited from the natural transformation
`AlgebraicGeometry.smallEtaleProjection` of base-change projections and the natural
isomorphism `AlgebraicGeometry.geometricPointFiberBaseChangeIso` identifying the lifts of `ȳ` to
`V` with the lifts of `x̄` to `X ×_Y V`; nothing has to be checked by hand.

## References

* [Stacks Project, Tag 04I5](https://stacks.math.columbia.edu/tag/04I5)
* [Stacks Project, Tag 03PS](https://stacks.math.columbia.edu/tag/03PS)
* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

/-- A ring map is local as soon as it is compatible with ring maps out of its source and target
which agree on the source: if `ε' ∘ φ = ε` and `ε` is a local homomorphism, then so is `φ`,
because a unit in the target of `φ` has unit image under `ε'`. -/
private theorem isLocalHom_of_comp_eq {R R' K : Type*} [CommRing R] [CommRing R'] [CommRing K]
    (φ : R →+* R') (ε : R →+* K) (ε' : R' →+* K) [IsLocalHom ε]
    (h : ε'.comp φ = ε) : IsLocalHom φ :=
  ⟨fun b hb => IsLocalHom.map_nonunit (f := ε) b (by rw [← h]; exact hb.map ε')⟩

section StalkMap

variable {X Y : B.Scheme} (a : X ⟶ Y) (x : GeometricPoint X.obj)

/-- The structure map `a_small^♯` of a morphism of schemes `a : X ⟶ Y`, read on the structure
presheaves of rings of the small étale sites: at an étale `V / Y` it pulls a global function on
`V` back along the projection `X ×_Y V ⟶ V`.

This is `AlgebraicGeometry.structureSharp` with the commutativity of the sections forgotten;
the forgetful form is the one the étale local ring of Stacks 03PS is a colimit of. -/
public def structureSharpRing :
    (SmallEtale.structureSheaf B Y.obj Y.property).obj ⟶
      (smallEtaleBaseChange B a).op ⋙ (SmallEtale.structureSheaf B X.obj X.property).obj :=
  Functor.whiskerRight (NatTrans.op (smallEtaleProjection B a))
    (Scheme.Γ ⋙ forget₂ CommRingCat RingCat)

/-- Base change of pointed étale neighborhoods along `a : X ⟶ Y`: an étale neighborhood
`(V, v̄)` of the image point `ȳ = a ∘ x̄` goes to the étale neighborhood `(X ×_Y V, x̄ × v̄)`
of `x̄`.

On underlying objects this is `AlgebraicGeometry.smallEtaleBaseChange`, and on chosen lifts it
is the correspondence `AlgebraicGeometry.geometricPointFiberBaseChangeIso`. -/
public def baseChangeEtaleNeighborhood :
    (geometricPointFiber B Y.obj Y.property (x.map (B.inclusion.map a))).Elements ⥤
      (geometricPointFiber B X.obj X.property x).Elements where
  obj V := ⟨(smallEtaleBaseChange B a).obj V.1,
    (geometricPointFiberBaseChangeIso B a x).hom.app V.1 V.2⟩
  map {V W} g := ⟨(smallEtaleBaseChange B a).map g.1, by
    have h := NatTrans.naturality_apply
      (geometricPointFiberBaseChangeIso B a x).hom g.1 V.2
    rw [g.2] at h
    exact h.symm⟩
  map_id V := Subtype.ext ((smallEtaleBaseChange B a).map_id V.1)
  map_comp g h := Subtype.ext ((smallEtaleBaseChange B a).map_comp g.1 h.1)

/-- The cocone on the diagram of sections over the étale neighborhoods of `ȳ`, whose colimit is
`(𝒪_Y)_ȳ`, with vertex `(𝒪_X)_x̄`: a global function on an étale neighborhood of `ȳ` is pulled
back along the base-change projection and then taken to its germ at `x̄`.

It is the colimit cocone of `(𝒪_X)_x̄`, whiskered along base change of neighborhoods and
precomposed with the structure map, so its naturality needs no separate argument. -/
public def etaleLocalRingCocone :
    Cocone ((CategoryOfElements.π
      (geometricPointFiber B Y.obj Y.property (x.map (B.inclusion.map a)))).op ⋙
        (SmallEtale.structureSheaf B Y.obj Y.property).obj) where
  pt := etaleLocalRing B X.obj X.property x
  ι := Functor.whiskerLeft (CategoryOfElements.π
      (geometricPointFiber B Y.obj Y.property (x.map (B.inclusion.map a)))).op
      (structureSharpRing B a) ≫
    ((colimit.cocone ((CategoryOfElements.π
        (geometricPointFiber B X.obj X.property x)).op ⋙
      (SmallEtale.structureSheaf B X.obj X.property).obj)).whisker
      (baseChangeEtaleNeighborhood B a x).op).ι

/-- The map of étale local rings induced by a morphism of schemes `a : X ⟶ Y` at a geometric
point `x̄` of `X` and its image `ȳ = a ∘ x̄`:

```
  (𝒪_Y)_ȳ ⟶ (𝒪_X)_x̄.
```

It sends the germ at `(V, v̄)` of a global function on an étale neighborhood `V / Y` of `ȳ` to
the germ at `(X ×_Y V, x̄ × v̄)` of its pullback along the projection `X ×_Y V ⟶ V`. -/
public def etaleLocalRingMap :
    etaleLocalRing B Y.obj Y.property (x.map (B.inclusion.map a)) ⟶
      etaleLocalRing B X.obj X.property x :=
  colimit.desc _ (etaleLocalRingCocone B a x)

/-- On germs, the map of étale local rings pulls a section back along the base-change
projection and takes its germ at the base-changed neighborhood. -/
public theorem etaleLocalRingMap_ι
    (V : (geometricPointFiber B Y.obj Y.property (x.map (B.inclusion.map a))).Elementsᵒᵖ) :
    colimit.ι ((CategoryOfElements.π
        (geometricPointFiber B Y.obj Y.property (x.map (B.inclusion.map a)))).op ⋙
      (SmallEtale.structureSheaf B Y.obj Y.property).obj) V ≫ etaleLocalRingMap B a x =
      (structureSharpRing B a).app (op (unop V).1) ≫
        colimit.ι ((CategoryOfElements.π (geometricPointFiber B X.obj X.property x)).op ⋙
          (SmallEtale.structureSheaf B X.obj X.property).obj)
          (op ((baseChangeEtaleNeighborhood B a x).obj (unop V))) :=
  colimit.ι_desc (etaleLocalRingCocone B a x) V

/-- The lift of `x̄` to the base change `X ×_Y V` projects to the lift of `ȳ` to `V`. -/
private theorem baseChangeEtaleNeighborhood_point_comp_projection
    (V : (geometricPointFiber B Y.obj Y.property (x.map (B.inclusion.map a))).Elements) :
    ((baseChangeEtaleNeighborhood B a x).obj V).2.1 ≫
        (smallEtaleProjection B a).app V.1 = V.2.1 := by
  obtain ⟨V, p⟩ := V
  let := hasPullbacks_bigEtaleSite B
  let := preservesPullbacks_bigEtaleSiteInclusion B
  have hpb := (IsPullback.of_hasPullback (Over.hom V.obj) a).map B.inclusion
  have hw : p.1 ≫ B.inclusion.map (Over.hom V.obj) = x.hom ≫ B.inclusion.map a := by
    simpa [GeometricPoint.map] using p.2
  calc ((baseChangeEtaleNeighborhood B a x).obj ⟨V, p⟩).2.1 ≫
        (smallEtaleProjection B a).app V
      = (hpb.lift p.1 x.hom hw ≫ 𝟙 (B.inclusion.obj (pullback (Over.hom V.obj) a))) ≫
            B.inclusion.map (pullback.fst (Over.hom V.obj) a) := rfl
    _ = hpb.lift p.1 x.hom hw ≫ B.inclusion.map (pullback.fst (Over.hom V.obj) a) := by
        rw [Category.comp_id]
    _ = p.1 := hpb.lift_fst _ _ _

/-- Evaluation of germs of the structure sheaf at a geometric point, as a morphism of the
category of rings out of the étale local ring there.

This is `AlgebraicGeometry.structureSheafStalkToGeometricField`; naming the étale local ring as
the source keeps the composite with a map of étale local rings typeable without a cast. -/
private def geometricEval (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S) :
    etaleLocalRing B S hS s ⟶ RingCat.of s.residueField :=
  RingCat.ofHom (structureSheafStalkToGeometricField B S hS s)

/-- The triangle of geometric evaluation maps commutes, as a triangle of maps of rings. -/
private theorem etaleLocalRingMap_comp_geometricEval :
    etaleLocalRingMap B a x ≫ geometricEval B X.obj X.property x =
      geometricEval B Y.obj Y.property (x.map (B.inclusion.map a)) := by
  refine colimit.hom_ext fun V => ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => k ≫ geometricEval B X.obj X.property x)
    (etaleLocalRingMap_ι B a x V)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  apply RingCat.hom_ext
  refine RingHom.ext fun s => ?_
  have hX := DFunLike.congr_fun
    (structureSheafStalkToGeometricField_ι B X.obj X.property x
      (op ((baseChangeEtaleNeighborhood B a x).obj (unop V))))
    (((smallEtaleProjection B a).app (unop V).1).appTop.hom s)
  have hY := DFunLike.congr_fun
    (structureSheafStalkToGeometricField_ι B Y.obj Y.property
      (x.map (B.inclusion.map a)) V) s
  refine Eq.trans ?_ hY.symm
  refine Eq.trans hX ?_
  exact congrArg (fun k => (Scheme.ΓSpecIso (CommRingCat.of x.residueField)).hom.hom
      (CommRingCat.Hom.hom (Scheme.Hom.appTop k) s))
    (baseChangeEtaleNeighborhood_point_comp_projection B a x (unop V))

/-- The triangle of geometric evaluation maps commutes: evaluating a germ of `(𝒪_Y)_ȳ` at `ȳ` is
evaluating its image in `(𝒪_X)_x̄` at `x̄`.

Both evaluations land in the same algebraically closed field, the geometric point `ȳ` being `x̄`
composed with `a`. -/
public theorem structureSheafStalkToGeometricField_etaleLocalRingMap :
    (structureSheafStalkToGeometricField B X.obj X.property x).comp
        (etaleLocalRingMap B a x).hom =
      structureSheafStalkToGeometricField B Y.obj Y.property (x.map (B.inclusion.map a)) :=
  congrArg RingCat.Hom.hom (etaleLocalRingMap_comp_geometricEval B a x)

/-- **The step with content in the proof of Stacks 04I5.** The map of étale local rings

```
  (𝒪_Y)_ȳ ⟶ (𝒪_X)_x̄
```

induced by a morphism of schemes `a : X ⟶ Y` at a geometric point `x̄` of `X` with image
`ȳ = a ∘ x̄` is a local ring homomorphism.

Evaluation of germs at `ȳ` is a local homomorphism onto the algebraically closed field of the
geometric point, because `(𝒪_Y)_ȳ` is strictly henselian. Since the triangle of evaluations
commutes, a germ over `Y` whose image over `X` is a unit has a unit value at `ȳ`, and is
therefore already a unit. -/
public instance etaleLocalRingMap_isLocalHom : IsLocalHom (etaleLocalRingMap B a x).hom := by
  have : IsLocalHom (structureSheafStalkToGeometricField B Y.obj Y.property
      (x.map (B.inclusion.map a))) :=
    structureSheafStalkToGeometricField_isLocalHom B Y.obj Y.property
      (x.map (B.inclusion.map a))
  exact isLocalHom_of_comp_eq (etaleLocalRingMap B a x).hom
    (structureSheafStalkToGeometricField B Y.obj Y.property (x.map (B.inclusion.map a)))
    (structureSheafStalkToGeometricField B X.obj X.property x)
    (structureSheafStalkToGeometricField_etaleLocalRingMap B a x)

end StalkMap

end AlgebraicGeometry

end
