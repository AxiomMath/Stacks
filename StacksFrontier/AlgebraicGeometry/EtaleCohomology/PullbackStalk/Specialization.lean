module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Basic
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.GeometricPointStalk

/-!
# Specialization maps on étale stalks and inverse images

Let `s` be a geometric point of a scheme `S` and let `t` be a geometric point of the strict
henselization of `S` at `s`, with image `t̄` in `S`. Every étale neighborhood `(U, u)` of `s`
receives a unique morphism from the strict henselization over `S` carrying the canonical
geometric point to `u`; the image of `t` under that morphism makes `U` an étale neighborhood
of `t̄`, and the induced map of neighborhood colimits is the specialization map
`sp : F_s ⟶ F_t̄` of a (pre)sheaf `F` on the small étale site of `S`.

For a morphism `g : S' ⟶ S`, a geometric point `s'` of `S'` and a geometric point `t'` of the
strict henselization of `S'` at `s'`, the specialization map of an inverse image `g⁻¹F` from
`s'` to `t'` is the specialization map of `F` from the image of `s'` to the image of `t'` under
the canonical morphism of strict henselizations, via the identification of the stalks of an
inverse image with the stalks of the original sheaf.

## Main definitions

* `AlgebraicGeometry.GeometricSpecialization` — a geometric point of the strict henselization
  at a geometric point, carried together with its image in the base scheme.
* `AlgebraicGeometry.strictHenselizationEtaleFactor` — the factorization of the structure
  morphism of the strict henselization through a pointed étale neighborhood.
* `AlgebraicGeometry.specializationFiberHom` — the morphism of geometric-point fiber functors
  underlying the specialization map.
* `AlgebraicGeometry.specializationMapOnStalks` — the specialization map on étale stalks.

## Main results

* `AlgebraicGeometry.specializationMapOnStalks_smallEtalePullback` — the specialization map of
  an inverse image is the specialization map of the original sheaf, under the identification of
  stalks of inverse images.

## Implementation notes

The factorization through an étale neighborhood is Olivier's theorem in the form
`AlgebraicGeometry.isInitial_strictHenselizationPoint`: an étale neighborhood of `s` is a
pro-étale neighborhood, and the strict henselization with its canonical geometric point is an
initial one. Following the source's convention that `F_t` abbreviates the stalk at the image of
`t` in `S`, a geometric specialization carries that image as part of its data, so that the
target of a specialization map is literally a stalk on the base scheme and transporting a
specialization along a morphism of strict henselizations needs no comparison of stalks.

The canonical morphism of strict henselizations is characterized by lying over the given
morphism of schemes and carrying the canonical geometric point of its source to the canonical
geometric point of its target; the commuting square is stated for every morphism with these two
properties, hence in particular for the canonical one.

## References

* [Stacks Project, Tag 0GJ6](https://stacks.math.columbia.edu/tag/0GJ6)
* [Stacks Project, Section 0GJ2](https://stacks.math.columbia.edu/tag/0GJ2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- A geometric specialization of a geometric point `s` of `S`: a geometric point of the strict
henselization of `S` at `s`, recorded by its image in `S` together with the lift. The source
writes `F_t` for the stalk at the image in `S` of such a geometric point `t`, so carrying that
image as part of the datum is what makes the target of a specialization map a stalk on `S`. -/
public structure GeometricSpecialization where
  /-- The image in `S` of the geometric point of the strict henselization. -/
  target : GeometricPoint S
  /-- The geometric point of the strict henselization, as a lift of `target`. -/
  lift : target.source ⟶ strictHenselization B S hS s
  /-- The lift lies over the geometric point `target` of `S`. -/
  lift_comp : lift ≫ strictHenselizationToBase B S hS s = target.hom

namespace GeometricSpecialization

/-- The geometric point of the strict henselization underlying a geometric specialization. -/
public def point {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {s : GeometricPoint S} (σ : GeometricSpecialization B S hS s) :
    GeometricPoint (strictHenselization B S hS s) where
  residueField := σ.target.residueField
  hom := σ.lift

/-- Every geometric point of the strict henselization is a geometric specialization, with image
its composite with the structure morphism. -/
public def ofPoint (t : GeometricPoint (strictHenselization B S hS s)) :
    GeometricSpecialization B S hS s where
  target := t.map (strictHenselizationToBase B S hS s)
  lift := t.hom
  lift_comp := rfl

/-- A geometric specialization carries the same information as a geometric point of the strict
henselization. -/
@[simp]
public theorem point_ofPoint (t : GeometricPoint (strictHenselization B S hS s)) :
    (ofPoint B S hS s t).point = t :=
  rfl

end GeometricSpecialization

/-! ### Factoring the strict henselization through an étale neighborhood -/

/-- A pointed étale neighborhood of a geometric point, viewed as a pointed pro-étale
neighborhood. -/
public def etaleNeighborhoodProEt (U : SmallEtale B S hS)
    (u : (geometricPointFiber B S hS s).obj U) :
    (proetalePointFiber S s).Elements :=
  (proetalePointFiber S s).elementsMk (Scheme.ProEt.mk (B.inclusion.map U.obj.hom))
    (Over.homMk u.1 u.2)

/-- The factorization of the structure morphism of the strict henselization at `s` through a
pointed étale neighborhood `(U, u)` of `s`, carrying the canonical geometric point of the
strict henselization to `u`. -/
public def strictHenselizationEtaleFactor (U : SmallEtale B S hS)
    (u : (geometricPointFiber B S hS s).obj U) :
    strictHenselization B S hS s ⟶ (SmallEtale.toScheme B S hS).obj U :=
  ((isInitial_strictHenselizationPoint B S hS s).to
    (etaleNeighborhoodProEt B S hS s U u)).1.left

/-- The factorization through a pointed étale neighborhood lies over the base scheme. -/
public theorem strictHenselizationEtaleFactor_comp (U : SmallEtale B S hS)
    (u : (geometricPointFiber B S hS s).obj U) :
    strictHenselizationEtaleFactor B S hS s U u ≫ B.inclusion.map U.obj.hom =
      strictHenselizationToBase B S hS s :=
  MorphismProperty.Over.w
    ((isInitial_strictHenselizationPoint B S hS s).to
      (etaleNeighborhoodProEt B S hS s U u)).1

/-- The factorization through a pointed étale neighborhood carries the canonical geometric point
of the strict henselization to the chosen lift. -/
public theorem geometricPointToStrictHenselization_comp_strictHenselizationEtaleFactor
    (U : SmallEtale B S hS) (u : (geometricPointFiber B S hS s).obj U) :
    geometricPointToStrictHenselization B S hS s ≫
      strictHenselizationEtaleFactor B S hS s U u = u.1 :=
  congrArg Over.Hom.left
    ((isInitial_strictHenselizationPoint B S hS s).to
      (etaleNeighborhoodProEt B S hS s U u)).2

/-- The factorization through a pointed étale neighborhood is the only morphism over the base
scheme carrying the canonical geometric point of the strict henselization to the chosen lift. -/
public theorem strictHenselizationEtaleFactor_unique (U : SmallEtale B S hS)
    (u : (geometricPointFiber B S hS s).obj U)
    (f : strictHenselization B S hS s ⟶ (SmallEtale.toScheme B S hS).obj U)
    (hf : f ≫ B.inclusion.map U.obj.hom = strictHenselizationToBase B S hS s)
    (hu : geometricPointToStrictHenselization B S hS s ≫ f = u.1) :
    f = strictHenselizationEtaleFactor B S hS s U u :=
  congrArg (fun m => m.1.left) ((isInitial_strictHenselizationPoint B S hS s).hom_ext
    (Y := etaleNeighborhoodProEt B S hS s U u)
    ⟨MorphismProperty.Over.homMk f hf, Over.OverMorphism.ext hu⟩
    ((isInitial_strictHenselizationPoint B S hS s).to (etaleNeighborhoodProEt B S hS s U u)))

/-! ### The specialization map -/

variable {B S hS s}

/-- The morphism of geometric-point fiber functors underlying the specialization map: an étale
neighborhood `(U, u)` of `s` is sent to the étale neighborhood of the image of the geometric
specialization obtained by composing its lift with the factorization through `(U, u)`. -/
public def specializationFiberHom (σ : GeometricSpecialization B S hS s) :
    geometricPointFiber B S hS s ⟶ geometricPointFiber B S hS σ.target where
  app U := ↾ fun u => ⟨σ.lift ≫ strictHenselizationEtaleFactor B S hS s U u, by
    rw [Category.assoc, strictHenselizationEtaleFactor_comp, σ.lift_comp]⟩
  naturality U V m := by
    ext u
    apply Subtype.ext
    have hfactor : strictHenselizationEtaleFactor B S hS s U u ≫
        (SmallEtale.toScheme B S hS).map m =
        strictHenselizationEtaleFactor B S hS s V ((geometricPointFiber B S hS s).map m u) := by
      refine strictHenselizationEtaleFactor_unique B S hS s V _ _ ?_ ?_
      · rw [Category.assoc, SmallEtale.toScheme_map_comp,
          strictHenselizationEtaleFactor_comp]
      · rw [← Category.assoc,
          geometricPointToStrictHenselization_comp_strictHenselizationEtaleFactor]
        rfl
    change σ.lift ≫ strictHenselizationEtaleFactor B S hS s V
        ((geometricPointFiber B S hS s).map m u) =
      (σ.lift ≫ strictHenselizationEtaleFactor B S hS s U u) ≫
        (SmallEtale.toScheme B S hS).map m
    rw [Category.assoc, hfactor]

/-- The specialization morphism of fiber functors is the factorization through the étale
neighborhood, composed with the lift of the geometric specialization. -/
public theorem specializationFiberHom_app_val (σ : GeometricSpecialization B S hS s)
    (U : SmallEtale B S hS) (u : (geometricPointFiber B S hS s).obj U) :
    ((specializationFiberHom σ).app U u).1 =
      σ.lift ≫ strictHenselizationEtaleFactor B S hS s U u :=
  rfl

/-- **Stacks Project, Section 0GJ2.** The specialization map on étale stalks: the map of
neighborhood colimits induced by the specialization morphism of geometric-point fiber
functors. -/
public def specializationMapOnStalks (σ : GeometricSpecialization B S hS s)
    {A : Type v} [Category.{w} A] [HasColimitsOfSize.{u, u} A]
    (F : (SmallEtale B S hS)ᵒᵖ ⥤ A) :
    etaleStalk B S hS s F ⟶ etaleStalk B S hS σ.target F :=
  colimit.pre ((CategoryOfElements.π (geometricPointFiber B S hS σ.target)).op ⋙ F)
    (CategoryOfElements.map (specializationFiberHom σ)).op

/-- The colimit insertion at an étale neighborhood of `s`, followed by the specialization map,
is the colimit insertion at the specialized étale neighborhood. -/
public theorem ι_comp_specializationMapOnStalks (σ : GeometricSpecialization B S hS s)
    {A : Type v} [Category.{w} A] [HasColimitsOfSize.{u, u} A]
    (F : (SmallEtale B S hS)ᵒᵖ ⥤ A) (e : (geometricPointFiber B S hS s).Elements) :
    colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙ F) (op e) ≫
        specializationMapOnStalks σ F =
      colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS σ.target)).op ⋙ F)
        (op ((CategoryOfElements.map (specializationFiberHom σ)).obj e)) :=
  colimit.ι_pre ((CategoryOfElements.π (geometricPointFiber B S hS σ.target)).op ⋙ F)
    (CategoryOfElements.map (specializationFiberHom σ)).op (op e)

/-- For sheaves of sets the specialization map sends the germ of a section at an étale
neighborhood of `s` to the germ of the same section at the specialized neighborhood. -/
public theorem specializationMapOnStalks_ι (σ : GeometricSpecialization B S hS s)
    (F : (SmallEtale B S hS)ᵒᵖ ⥤ Type (u + 1))
    (e : (geometricPointFiber B S hS s).Elements) (z : F.obj (op e.1)) :
    specializationMapOnStalks σ F
        (colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙ F) (op e) z) =
      colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS σ.target)).op ⋙ F)
        (op ((CategoryOfElements.map (specializationFiberHom σ)).obj e)) z :=
  congrArg (fun k => k z) (ι_comp_specializationMapOnStalks σ F e)

namespace GeometricSpecialization

/-- Transport a geometric specialization of a geometric point `s'` of `S'` along a morphism of
strict henselizations lying over `g : S' ⟶ S`: its image in `S` is the image of the original
one, and its lift is the composite of the original lift with that morphism. -/
public def map {B : BigEtaleSite.{u}} {S S' : B.Scheme} {s' : GeometricPoint S'.1}
    (σ : GeometricSpecialization B S'.1 S'.property s') (g : S' ⟶ S)
    (h : strictHenselization B S'.1 S'.property s' ⟶
      strictHenselization B S.1 S.property (s'.map (B.inclusion.map g)))
    (hbase : h ≫ strictHenselizationToBase B S.1 S.property (s'.map (B.inclusion.map g)) =
      strictHenselizationToBase B S'.1 S'.property s' ≫ B.inclusion.map g) :
    GeometricSpecialization B S.1 S.property (s'.map (B.inclusion.map g)) where
  target := σ.target.map (B.inclusion.map g)
  lift := σ.lift ≫ h
  lift_comp := by
    rw [GeometricPoint.map_hom, Category.assoc, hbase, ← Category.assoc, σ.lift_comp]

end GeometricSpecialization

/-! ### Compatibility with inverse images -/

/-- The specialization of a lift of `s'` to a base change `V ×_S S'` is the base change of the
specialization of the corresponding lift of the image of `s'` to `V`. -/
private theorem specializationFiberHom_baseChange_val {B : BigEtaleSite.{u}} {S S' : B.Scheme}
    (g : S' ⟶ S) (s' : GeometricPoint S'.1)
    (σ : GeometricSpecialization B S'.1 S'.property s')
    (h : strictHenselization B S'.1 S'.property s' ⟶
      strictHenselization B S.1 S.property (s'.map (B.inclusion.map g)))
    (hbase : h ≫ strictHenselizationToBase B S.1 S.property (s'.map (B.inclusion.map g)) =
      strictHenselizationToBase B S'.1 S'.property s' ≫ B.inclusion.map g)
    (hpoint : geometricPointToStrictHenselization B S'.1 S'.property s' ≫ h =
      geometricPointToStrictHenselization B S.1 S.property (s'.map (B.inclusion.map g)))
    (V : SmallEtale B S.1 S.property)
    (v : (geometricPointFiber B S.1 S.property (s'.map (B.inclusion.map g))).obj V)
    (u : (geometricPointFiber B S'.1 S'.property s').obj ((smallEtaleBaseChange B g).obj V))
    (hu : u.1 ≫ B.inclusion.map (pullback.fst V.obj.hom g) = v.1) :
    ((specializationFiberHom σ).app ((smallEtaleBaseChange B g).obj V) u).1 ≫
        B.inclusion.map (pullback.fst V.obj.hom g) =
      ((specializationFiberHom (σ.map g h hbase)).app V v).1 := by
  have := preservesPullbacks_bigEtaleSiteInclusion B
  have hp := (IsPullback.of_hasPullback V.obj.hom g).map B.inclusion
  have hw : (h ≫ strictHenselizationEtaleFactor B S.1 S.property
        (s'.map (B.inclusion.map g)) V v) ≫ B.inclusion.map V.obj.hom =
      strictHenselizationToBase B S'.1 S'.property s' ≫ B.inclusion.map g := by
    rwa [Category.assoc, strictHenselizationEtaleFactor_comp]
  have hqk : geometricPointToStrictHenselization B S'.1 S'.property s' ≫
      hp.lift (h ≫ strictHenselizationEtaleFactor B S.1 S.property
          (s'.map (B.inclusion.map g)) V v)
        (strictHenselizationToBase B S'.1 S'.property s') hw = u.1 := by
    apply hp.hom_ext
    · rw [Category.assoc, hp.lift_fst, ← Category.assoc, hpoint,
      geometricPointToStrictHenselization_comp_strictHenselizationEtaleFactor]
      exact hu.symm
    · rw [Category.assoc, hp.lift_snd]
      exact (geometricPointToStrictHenselization_comp B S'.1 S'.property s').trans u.2.symm
  have key : strictHenselizationEtaleFactor B S'.1 S'.property s'
        ((smallEtaleBaseChange B g).obj V) u ≫ B.inclusion.map (pullback.fst V.obj.hom g) =
      h ≫ strictHenselizationEtaleFactor B S.1 S.property
        (s'.map (B.inclusion.map g)) V v :=
    ((strictHenselizationEtaleFactor_unique B S'.1 S'.property s'
      ((smallEtaleBaseChange B g).obj V) u _ (hp.lift_snd _ _ _) hqk).symm =≫ _).trans
      (hp.lift_fst _ _ hw)
  rw [specializationFiberHom_app_val, specializationFiberHom_app_val, Category.assoc, key,
    ← Category.assoc]
  rfl

/-- **Stacks Project, Tag 0GJ6.** Let `g : S' ⟶ S` be a morphism of schemes, let `s'` be a
geometric point of `S'` and let `σ` be a geometric specialization of `s'`, and let `h` be the
canonical morphism of strict henselizations, characterized by lying over `g` and carrying the
canonical geometric point of its source to the canonical geometric point of its target. For a
sheaf `F` on the small étale site of `S` the specialization map of the inverse image `g⁻¹F`
from `s'` to `σ` is the specialization map of `F` from the image of `s'` to the image of `σ`,
under the identification of the stalks of an inverse image with the stalks of `F`. -/
@[stacks 0GJ6]
public theorem specializationMapOnStalks_smallEtalePullback (B : BigEtaleSite.{u})
    (S S' : B.Scheme) (g : S' ⟶ S) (s' : GeometricPoint S'.1)
    (σ : GeometricSpecialization B S'.1 S'.property s')
    (h : strictHenselization B S'.1 S'.property s' ⟶
      strictHenselization B S.1 S.property (s'.map (B.inclusion.map g)))
    (hbase : h ≫ strictHenselizationToBase B S.1 S.property (s'.map (B.inclusion.map g)) =
      strictHenselizationToBase B S'.1 S'.property s' ≫ B.inclusion.map g)
    (hpoint : geometricPointToStrictHenselization B S'.1 S'.property s' ≫ h =
      geometricPointToStrictHenselization B S.1 S.property (s'.map (B.inclusion.map g)))
    (F : Sheaf (SmallEtale.topology B S.1 S.property) (Type (u + 1))) :
    specializationMapOnStalks σ
          (((smallEtaleBaseChange B g).sheafPullback (Type (u + 1))
            (SmallEtale.topology B S.1 S.property)
            (SmallEtale.topology B S'.1 S'.property)).obj F).obj ≫
        (smallEtalePullbackStalkIso B g σ.target).hom.app F =
      (smallEtalePullbackStalkIso B g s').hom.app F ≫
        specializationMapOnStalks (σ.map g h hbase) F.obj := by
  have := preservesPullbacks_bigEtaleSiteInclusion B
  ext z
  let I := (smallEtalePullbackStalkIso B g s').app F
  obtain ⟨⟨⟨V, v⟩⟩, t, ht⟩ := Types.jointly_surjective' (I.hom z)
  let hp := (IsPullback.of_hasPullback V.obj.hom g).map B.inclusion
  let u : (geometricPointFiber B S'.1 S'.property s').obj ((smallEtaleBaseChange B g).obj V) :=
    ⟨hp.lift v.1 s'.hom v.2, hp.lift_snd _ _ _⟩
  let U := (geometricPointFiber B S'.1 S'.property s').elementsMk
    ((smallEtaleBaseChange B g).obj V) u
  let W := (geometricPointFiber B S.1 S.property (s'.map (B.inclusion.map g))).elementsMk V v
  let P := (((smallEtaleBaseChange B g).sheafPullback (Type (u + 1))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B S'.1 S'.property)).obj F).obj
  have hu : u.1 ≫ B.inclusion.map (pullback.fst V.obj.hom g) = v.1 := hp.lift_fst _ _ _
  have hU : U.2.1 ≫ (SmallEtale.toScheme B S'.1 S'.property).map (𝟙 U.1) ≫
      B.inclusion.map (pullback.fst W.1.obj.hom g) = W.2.1 := by
    simpa only [CategoryTheory.Functor.map_id, Category.id_comp] using hu
  have hsource := smallEtalePullbackStalkIso_germ B g s' F U W (𝟙 _) hU t
  let z' := colimit.ι ((CategoryOfElements.π (geometricPointFiber B S'.1 S'.property s')).op ⋙ P)
    (op U) (pullbackSectionAlong B g F W.1 U.1 (𝟙 _) t)
  obtain rfl : z = z' := I.toEquiv.injective (ht.symm.trans hsource.symm)
  let Uσ := (CategoryOfElements.map (specializationFiberHom σ)).obj U
  let Wσ := (CategoryOfElements.map (specializationFiberHom (σ.map g h hbase))).obj W
  have hσ : Uσ.2.1 ≫ (SmallEtale.toScheme B S'.1 S'.property).map (𝟙 Uσ.1) ≫
      B.inclusion.map (pullback.fst Wσ.1.obj.hom g) = Wσ.2.1 := by
    show ((specializationFiberHom σ).app ((smallEtaleBaseChange B g).obj V) u).1 ≫
      (SmallEtale.toScheme B S'.1 S'.property).map
        (𝟙 ((smallEtaleBaseChange B g).obj V)) ≫
        B.inclusion.map (pullback.fst V.obj.hom g) = _
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
    exact specializationFiberHom_baseChange_val g s' σ h hbase hpoint V v u hu
  show (smallEtalePullbackStalkIso B g σ.target).hom.app F
      (specializationMapOnStalks σ P z') =
    specializationMapOnStalks (σ.map g h hbase) F.obj (I.hom z')
  rw [specializationMapOnStalks_ι σ P U
    (pullbackSectionAlong B g F W.1 U.1 (𝟙 _) t),
    show I.hom z' = colimit.ι ((CategoryOfElements.π (geometricPointFiber B S.1 S.property
      (s'.map (B.inclusion.map g)))).op ⋙ F.obj) (op W) t from hsource,
    specializationMapOnStalks_ι (σ.map g h hbase) F.obj W t]
  exact smallEtalePullbackStalkIso_germ B g σ.target F Uσ Wσ (𝟙 _) hσ t

end AlgebraicGeometry

end
