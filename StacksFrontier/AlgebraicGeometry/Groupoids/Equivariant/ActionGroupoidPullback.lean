module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.ActionGroupoid
public import StacksFrontier.AlgebraicGeometry.Groupoids.Equivariant.PullbackFunctor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pullback of equivariant quasi-coherent modules

Let `B` be a scheme over `S`, let `G` be a group scheme over `B` acting on two schemes `X` and
`Y` over `B`, and let `f : Y ⟶ X` be an equivariant morphism. Then `f` induces a morphism of the
associated action groupoids over `S` whose map on objects is `f` and whose map on arrows is
`1_G × f`. Pullback along this morphism of groupoid schemes is a functor from quasi-coherent
modules with descent data on the action groupoid of `X` to those on the action groupoid of `Y`,
that is, from `G`-equivariant quasi-coherent modules on `X` to those on `Y`.

## Main definitions

* `AlgebraicGeometry.actionGroupoid` is the groupoid scheme over `S` attached to an action.
* `AlgebraicGeometry.EquivariantGroupoidMorphism` specifies the induced morphism of action
  groupoids by prescribing its two maps.
* `AlgebraicGeometry.equivariantGroupoidMorphism` is the morphism of action groupoids with object
  map `f` and arrow map `1_G × f`.
* `AlgebraicGeometry.equivariantPullback` is pullback of equivariant quasi-coherent modules.

## Main results

* `AlgebraicGeometry.actionGroupoidMap_comp`: the arrow map `1_G × f` is compatible with
  composition of arrows in the two action groupoids.
* `AlgebraicGeometry.eqToHom_comp_conj`: the composite of two morphisms conjugated by `eqToHom`
  transports is the conjugate of their composite.

## Implementation notes

The two action groupoids are produced by `AlgebraicGeometry.groupoidSchemeOfAction`, which
specifies its object and arrow schemes and all its structure morphisms by equalities rather than
identifying them definitionally with the input data. Accordingly the prescribed maps of the
induced morphism are compared by heterogeneous equalities, and the compatibility with
composition is proved after destructuring those identifications.

The functor itself is the general pullback functor for a morphism of groupoid schemes; its
specifications for the underlying module, the equivariant structure and the action on morphisms
are those of that functor.

## References

* [Stacks Project, Tag 03LG](https://stacks.math.columbia.edu/tag/03LG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

/-- The composite of two morphisms conjugated by `eqToHom` transports is the conjugate of their
composite. -/
theorem eqToHom_comp_conj {C : Type*} [Category C] {A A' B B' D D' : C}
    (hA : A = A') (hB : B = B') (hD : D = D')
    (f : A' ⟶ B') (g : B' ⟶ D') :
    (eqToHom hA ≫ f ≫ eqToHom hB.symm) ≫
        (eqToHom hB ≫ g ≫ eqToHom hD.symm) =
      eqToHom hA ≫ (f ≫ g) ≫ eqToHom hD.symm := by
  subst hA hB hD
  simp

variable {S : Scheme.{u}} (B : Over S) (G X Y : Over B.left)
  [GrpObj G] [ModObj G X] [ModObj G Y]

/-- An equivariant morphism intertwines the composition morphisms of the two action
groupoids over the base. -/
private theorem actionComposition_map_compatible (f : Y ⟶ X) [IsModHom G f]
    (m : G ⊗ Y ⟶ G ⊗ X) (hm : m = G ◁ f)
    (hs : m ≫ snd G X = snd G Y ≫ f)
    (ht : m ≫ γ[G,X] = γ[G,Y] ≫ f) :
    pullback.map (snd G Y) γ[G, Y] (snd G X) γ[G, X] m m f hs.symm ht.symm ≫
        Stacks.Groupoids.ActionGroupoid.composition G X =
      Stacks.Groupoids.ActionGroupoid.composition G Y ≫ m := by
  let p := pullback.fst (snd G Y) γ[G, Y]
  let q := pullback.snd (snd G Y) γ[G, Y]
  let j := pullback.map (snd G Y) γ[G, Y] (snd G X) γ[G, X] m m f hs.symm ht.symm
  have hcond : p ≫ snd G Y = q ≫ γ[G, Y] := pullback.condition
  have w : (p ≫ m) ≫ snd G X = (q ≫ m) ≫ γ[G, X] := by
    rw [Category.assoc, Category.assoc, hs, ht, reassoc_of% hcond]
  have hj : j = pullback.lift (p ≫ m) (q ≫ m) w := rfl
  have hid : pullback.lift p q pullback.condition = 𝟙 _ := by
    dsimp [p, q]
    apply pullback.hom_ext <;> simp
  have hf : m ≫ fst G X = fst G Y := by
    rw [hm, CartesianMonoidalCategory.whiskerLeft_fst]
  have hevalX := actionComposition_eval B G X (p ≫ m) (q ≫ m) w
  have hevalY := actionComposition_eval B G Y p q pullback.condition
  have hevalY' : Stacks.Groupoids.ActionGroupoid.composition G Y =
      lift ((p ≫ fst G Y) * (q ≫ fst G Y)) (q ≫ snd G Y) := by
    simpa [hid] using hevalY
  change j ≫ Stacks.Groupoids.ActionGroupoid.composition G X = _
  rw [hj, hevalX, hevalY']
  apply CartesianMonoidalCategory.hom_ext (C := Over B.left)
  · simp [Category.assoc, hf]
  · simp [Category.assoc, hs]

/-- The arrow map `1_G × f` of an equivariant morphism is compatible with composition of arrows
in the two action groupoids. -/
theorem actionGroupoidMap_comp
    (f : Y ⟶ X) [IsModHom G f]
    (AY : ActionGroupoidConstruction B G Y)
    (AX : ActionGroupoidConstruction B G X)
    (m : G ⊗ Y ⟶ G ⊗ X) (hm : m = G ◁ f)
    (hs : m ≫ snd G X = snd G Y ≫ f)
    (ht : m ≫ γ[G,X] = γ[G,Y] ≫ f)
    (arrowMap : AY.groupoid.arrows ⟶ AX.groupoid.arrows)
    (hArrow : HEq arrowMap ((Over.map B.hom).map m)) :
    ∀ (T : Over S) (a b : T ⟶ AY.groupoid.arrows)
      (hab : a ≫ AY.groupoid.source = b ≫ AY.groupoid.target)
      (hab' : (a ≫ arrowMap) ≫ AX.groupoid.source =
        (b ≫ arrowMap) ≫ AX.groupoid.target),
      AY.groupoid.compose a b hab ≫ arrowMap =
        AX.groupoid.compose (a ≫ arrowMap) (b ≫ arrowMap) hab' := by
  cases AY with
  | mk QY hOY hAY hSY hTY isoY isoYfst isoYsnd hcompY _ _ =>
    cases AX with
    | mk QX hOX hAX hSX hTX isoX isoXfst isoXsnd hcompX _ _ =>
      cases QY with
      | mk objY arrY srcY tgtY compY idY invY sidY tidY sinvY tinvY scompY tcompY
          leftY rightY leftInvY rightInvY assocY =>
        cases QX with
        | mk objX arrX srcX tgtX compX idX invX sidX tidX sinvX tinvX scompX tcompX
            leftX rightX leftInvX rightInvX assocX =>
          cases hOY
          cases hAY
          cases hOX
          cases hAX
          obtain rfl := hSY.eq
          obtain rfl := hTY.eq
          obtain rfl := hSX.eq
          obtain rfl := hTX.eq
          obtain rfl := hArrow.eq
          intro T a b hab hab'
          change (pullback.lift a b hab ≫ compY) ≫ (Over.map B.hom).map m =
            pullback.lift (a ≫ (Over.map B.hom).map m)
              (b ≫ (Over.map B.hom).map m) hab' ≫ compX
          obtain rfl : compY = isoY.hom ≫
              (Over.map B.hom).map (Stacks.Groupoids.ActionGroupoid.composition G Y) :=
            hcompY.eq
          obtain rfl : compX = isoX.hom ≫
              (Over.map B.hom).map (Stacks.Groupoids.ActionGroupoid.composition G X) :=
            hcompX.eq
          let j := pullback.map ((Over.map B.hom).map (snd G Y))
            ((Over.map B.hom).map (γ[G, Y])) ((Over.map B.hom).map (snd G X))
            ((Over.map B.hom).map (γ[G, X])) ((Over.map B.hom).map m)
            ((Over.map B.hom).map m) ((Over.map B.hom).map f)
            (by rw [← Functor.map_comp, ← Functor.map_comp, hs])
            (by rw [← Functor.map_comp, ← Functor.map_comp, ht])
          have hLift : pullback.lift a b hab ≫ j =
              pullback.lift (a ≫ (Over.map B.hom).map m)
                (b ≫ (Over.map B.hom).map m) hab' := by
            apply pullback.hom_ext
            · simp only [j, pullback.map, Category.assoc, pullback.lift_fst,
                pullback.lift_fst_assoc]
            · simp only [j, pullback.map, Category.assoc, pullback.lift_snd,
                pullback.lift_snd_assoc]
          let jRaw := pullback.map (snd G Y) γ[G, Y] (snd G X) γ[G, X]
            m m f hs.symm ht.symm
          have hjRawFst : jRaw ≫ pullback.fst (snd G X) γ[G, X] =
              pullback.fst (snd G Y) γ[G, Y] ≫ m :=
            pullback.lift_fst _ _ _
          have hjRawSnd : jRaw ≫ pullback.snd (snd G X) γ[G, X] =
              pullback.snd (snd G Y) γ[G, Y] ≫ m :=
            pullback.lift_snd _ _ _
          have hjRaw : j ≫ isoX.hom = isoY.hom ≫ (Over.map B.hom).map jRaw := by
            have hiXfst : isoX.inv ≫
                pullback.fst ((Over.map B.hom).map (snd G X))
                  ((Over.map B.hom).map (γ[G, X])) =
                (Over.map B.hom).map (pullback.fst (snd G X) γ[G, X]) := by
              rw [← isoXfst, Iso.inv_hom_id_assoc]
            have hiXsnd : isoX.inv ≫
                pullback.snd ((Over.map B.hom).map (snd G X))
                  ((Over.map B.hom).map (γ[G, X])) =
                (Over.map B.hom).map (pullback.snd (snd G X) γ[G, X]) := by
              rw [← isoXsnd, Iso.inv_hom_id_assoc]
            rw [← Iso.eq_comp_inv]
            apply pullback.hom_ext
            · rw [Category.assoc, Category.assoc, hiXfst, ← Functor.map_comp, hjRawFst,
                Functor.map_comp, ← Category.assoc, isoYfst]
              exact pullback.lift_fst _ _ _
            · rw [Category.assoc, Category.assoc, hiXsnd, ← Functor.map_comp, hjRawSnd,
                Functor.map_comp, ← Category.assoc, isoYsnd]
              exact pullback.lift_snd _ _ _
          have hraw : jRaw ≫ Stacks.Groupoids.ActionGroupoid.composition G X =
              Stacks.Groupoids.ActionGroupoid.composition G Y ≫ m :=
            actionComposition_map_compatible B G X Y f m hm hs ht
          rw [← hLift]
          simp only [Category.assoc]
          rw [reassoc_of% hjRaw, ← Functor.map_comp, ← Functor.map_comp, ← hraw]

/-- The action groupoid of the action of `G` on `X`, viewed as a groupoid scheme over `S`. -/
noncomputable abbrev actionGroupoid : Stacks.Groupoids.GroupoidScheme S :=
  (groupoidSchemeOfAction B G X).groupoid

/-- The morphism of action groupoids induced by an equivariant map, with its two maps
specified as `f` and `1_G × f`. -/
structure EquivariantGroupoidMorphism (f : Y ⟶ X) where
  /-- The underlying morphism of groupoid schemes. -/
  hom : Stacks.Groupoids.GroupoidScheme.Hom (actionGroupoid B G Y) (actionGroupoid B G X)
  /-- The map on objects is `f`. -/
  objects_eq : HEq hom.mapObjects ((Over.map B.hom).map f)
  /-- The map on arrows is `1_G × f`. -/
  arrows_eq : HEq hom.mapArrows
    ((Over.map B.hom).map (lift (fst G Y) (snd G Y ≫ f)))

/-- **Stacks Project, Tag 03LG.** An equivariant morphism induces the specified morphism of
action groupoids. -/
@[stacks 03LG "action-groupoid morphism"]
noncomputable def equivariantGroupoidMorphism (f : Y ⟶ X) [IsModHom G f] :
    EquivariantGroupoidMorphism B G X Y f := by
  let AY := groupoidSchemeOfAction B G Y
  let AX := groupoidSchemeOfAction B G X
  let F := Over.map B.hom
  let m : G ⊗ Y ⟶ G ⊗ X := lift (fst G Y) (snd G Y ≫ f)
  let o : AY.groupoid.objects ⟶ AX.groupoid.objects :=
    eqToHom AY.objects_eq ≫ F.map f ≫ eqToHom AX.objects_eq.symm
  let arrowMap : AY.groupoid.arrows ⟶ AX.groupoid.arrows :=
    eqToHom AY.arrows_eq ≫ F.map m ≫ eqToHom AX.arrows_eq.symm
  have hm : m = G ◁ f := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [m, Over.lift_left, Over.fst_left, Over.whiskerLeft_left_fst]
      exact pullback.lift_fst _ _ _
    · simp only [m, Over.lift_left, Over.whiskerLeft_left_snd]
      exact pullback.lift_snd _ _ _
  have hsource : m ≫ snd G X = snd G Y ≫ f := by
    simp [m]
  have htarget : m ≫ γ[G, X] = γ[G, Y] ≫ f := by
    rw [hm]
    exact (IsModHom.smul_hom (A := G) (f := f)).symm
  have hsourceMap : F.map m ≫ F.map (snd G X) = F.map (snd G Y) ≫ F.map f := by
    simpa only [Functor.map_comp] using congrArg F.map hsource
  have htargetMap : F.map m ≫ F.map (γ[G, X]) = F.map (γ[G, Y]) ≫ F.map f := by
    simpa only [Functor.map_comp] using congrArg F.map htarget
  have hsourceY : AY.groupoid.source =
      eqToHom AY.arrows_eq ≫ F.map (snd G Y) ≫ eqToHom AY.objects_eq.symm :=
    (conj_eqToHom_iff_heq _ _ AY.arrows_eq AY.objects_eq).2 AY.source_eq
  have hsourceX : AX.groupoid.source =
      eqToHom AX.arrows_eq ≫ F.map (snd G X) ≫ eqToHom AX.objects_eq.symm :=
    (conj_eqToHom_iff_heq _ _ AX.arrows_eq AX.objects_eq).2 AX.source_eq
  have htargetY : AY.groupoid.target =
      eqToHom AY.arrows_eq ≫ F.map (γ[G, Y]) ≫ eqToHom AY.objects_eq.symm :=
    (conj_eqToHom_iff_heq _ _ AY.arrows_eq AY.objects_eq).2 AY.target_eq
  have htargetX : AX.groupoid.target =
      eqToHom AX.arrows_eq ≫ F.map (γ[G, X]) ≫ eqToHom AX.objects_eq.symm :=
    (conj_eqToHom_iff_heq _ _ AX.arrows_eq AX.objects_eq).2 AX.target_eq
  have hidY : AY.groupoid.identity =
      eqToHom AY.objects_eq ≫ F.map (Stacks.Groupoids.ActionGroupoid.identity G Y) ≫
        eqToHom AY.arrows_eq.symm :=
    (conj_eqToHom_iff_heq _ _ AY.objects_eq AY.arrows_eq).2 AY.identity_eq
  have hidX : AX.groupoid.identity =
      eqToHom AX.objects_eq ≫ F.map (Stacks.Groupoids.ActionGroupoid.identity G X) ≫
        eqToHom AX.arrows_eq.symm :=
    (conj_eqToHom_iff_heq _ _ AX.objects_eq AX.arrows_eq).2 AX.identity_eq
  refine ⟨{
    mapObjects := o
    mapArrows := arrowMap
    map_source := ?_
    map_target := ?_
    map_identity := ?_
    map_comp := ?_ }, ?_, ?_⟩
  · change arrowMap ≫ AX.groupoid.source = AY.groupoid.source ≫ o
    rw [hsourceX, hsourceY]
    dsimp [arrowMap, o]
    rw [eqToHom_comp_conj AY.arrows_eq AX.arrows_eq AX.objects_eq,
      eqToHom_comp_conj AY.arrows_eq AY.objects_eq AX.objects_eq]
    exact congrArg (fun k => eqToHom AY.arrows_eq ≫ k ≫ eqToHom AX.objects_eq.symm)
      hsourceMap
  · change arrowMap ≫ AX.groupoid.target = AY.groupoid.target ≫ o
    rw [htargetX, htargetY]
    dsimp [arrowMap, o]
    rw [eqToHom_comp_conj AY.arrows_eq AX.arrows_eq AX.objects_eq,
      eqToHom_comp_conj AY.arrows_eq AY.objects_eq AX.objects_eq]
    exact congrArg (fun k => eqToHom AY.arrows_eq ≫ k ≫ eqToHom AX.objects_eq.symm)
      htargetMap
  · change o ≫ AX.groupoid.identity = AY.groupoid.identity ≫ arrowMap
    have hid : f ≫ Stacks.Groupoids.ActionGroupoid.identity G X =
        Stacks.Groupoids.ActionGroupoid.identity G Y ≫ m := by
      apply Over.OverMorphism.ext
      simp [m, Stacks.Groupoids.ActionGroupoid.identity]
    rw [hidX, hidY]
    dsimp [o, arrowMap]
    rw [eqToHom_comp_conj AY.objects_eq AX.objects_eq AX.arrows_eq,
      eqToHom_comp_conj AY.objects_eq AY.arrows_eq AX.arrows_eq]
    exact congrArg (fun k => eqToHom AY.objects_eq ≫ k ≫ eqToHom AX.arrows_eq.symm)
      (congrArg F.map hid)
  · exact actionGroupoidMap_comp B G X Y f AY AX m hm hsource htarget
      arrowMap (by simp [arrowMap, F])
  · change o ≍ F.map f
    simp [o]
  · change arrowMap ≍ F.map m
    simp [arrowMap]

/-- **Stacks Project, Tag 03LG.** Pullback of equivariant quasi-coherent modules along an
equivariant morphism `f`. Its action on modules, on equivariant structures and on morphisms is
that of the pullback functor along the induced morphism of action groupoids. -/
@[stacks 03LG "the functor", sga "3 I 6.5.2", sga "3 I 6.3.1"]
noncomputable def equivariantPullback (f : Y ⟶ X) [IsModHom G f] :
    Stacks.Groupoids.GroupoidScheme.QuasicoherentModule (actionGroupoid B G X) ⥤
      Stacks.Groupoids.GroupoidScheme.QuasicoherentModule (actionGroupoid B G Y) :=
  Stacks.Groupoids.GroupoidScheme.pullbackFunctor
    (equivariantGroupoidMorphism B G X Y f).hom

end AlgebraicGeometry

end
