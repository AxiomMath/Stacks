module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.GroupoidInverse
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.OverPullbackLeft
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.SchemeTheoreticImage

/-!
# Groupoid schemes on scheme-theoretic images over a field

Let `F : G₁ ⟶ G₂` be a morphism of groupoid schemes which is the identity on a common object
scheme, and suppose that object scheme is the spectrum of a field. If the map on arrow schemes
is quasi-compact, then its scheme-theoretic image is again the arrow scheme of a groupoid
scheme, and the image inclusion is a morphism of groupoid schemes.

## Main results

* `AlgebraicGeometry.exists_groupoidScheme_image` constructs the groupoid scheme on the
  scheme-theoretic image, together with its canonical morphism into the target groupoid.

## Implementation notes

The image arrow scheme is taken over the original base scheme by composing its image
inclusion with the structure morphism of the target arrow scheme. The canonical inclusion is
required to be a morphism of groupoid schemes which is the identity on objects and the
scheme-theoretic image inclusion on arrows; its source, target, composition, identity and
inverse are therefore the restrictions of the corresponding maps of the target groupoid.

Each of those restrictions exists because the relevant composite kills the kernel ideal sheaf
cutting out the image. For composition this uses that the image of a product of quasi-compact
morphisms over a field is the product of the images, which is where the field hypothesis
enters.

## References

* [Stacks Project, Tag 04QA](https://stacks.math.columbia.edu/tag/04QA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The identity section of the target groupoid factors through the scheme-theoretic image of the
arrow map, when that map is the identity on objects. -/
private theorem exists_identity_lift_to_image
    {S : Scheme.{u}}
    {G₁ G₂ : GroupoidScheme S} (F : GroupoidScheme.Hom G₁ G₂)
    (hobjects : G₁.objects = G₂.objects)
    (hmapObjects : F.mapObjects = eqToHom hobjects) :
    ∃ e : G₂.objects.left ⟶ F.mapArrows.left.image,
      e ≫ F.mapArrows.left.imageι = G₂.identity.left := by
  have hmap : F.mapObjects.left = eqToHom (congrArg Over.left hobjects) := by
    simpa using congrArg Over.Hom.left hmapObjects
  refine ⟨eqToHom (congrArg Over.left hobjects.symm) ≫ G₁.identity.left ≫
    F.mapArrows.left.toImage, ?_⟩
  have hid : F.mapObjects.left ≫ G₂.identity.left = G₁.identity.left ≫ F.mapArrows.left :=
    congrArg Over.Hom.left F.map_identity
  simp only [Category.assoc, Scheme.Hom.toImage_imageι]
  rw [← hid, hmap]
  simp

/-- Transport of the first projection of a fibre product along equalities of the two maps. -/
private theorem congrHom_hom_fst {X Y S : Scheme} {f₁ f₂ : X ⟶ S} {g₁ g₂ : Y ⟶ S}
    (h₁ : f₁ = f₂) (h₂ : g₁ = g₂) :
    (pullback.congrHom h₁ h₂).hom ≫ pullback.fst f₂ g₂ = pullback.fst f₁ g₁ := by
  subst h₁ h₂
  simp

/-- Transport of the second projection of a fibre product along equalities of the two maps. -/
private theorem congrHom_hom_snd {X Y S : Scheme} {f₁ f₂ : X ⟶ S} {g₁ g₂ : Y ⟶ S}
    (h₁ : f₁ = f₂) (h₂ : g₁ = g₂) :
    (pullback.congrHom h₁ h₂).hom ≫ pullback.snd f₂ g₂ = pullback.snd f₁ g₁ := by
  subst h₁ h₂
  simp

/-- The morphism induced on fibre products by two quasi-compact morphisms over a common base is
quasi-compact. -/
private theorem productMap_quasiCompact
    {S A B X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)
    (f : A ⟶ X) (g : B ⟶ Y) [QuasiCompact f] [QuasiCompact g] :
    QuasiCompact (AlgebraicGeometry.productMap pX pY f g) :=
  MorphismProperty.pullbackMap (P := @QuasiCompact)
    (f := f ≫ pX) (g := g ≫ pY) (f' := pX) (g' := pY)
    (i₁ := f) (i₂ := g) inferInstance inferInstance rfl rfl

/-- Over a field, the comparison from the fibre product of two morphisms to the fibre product of
their scheme-theoretic images is scheme-theoretically dominant. -/
private theorem imageToImage_isSchemeTheoreticallyDominant
    {k : Type u} [Field k] {A B X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (f : A ⟶ X) (g : B ⟶ Y) [QuasiCompact f] [QuasiCompact g] :
    IsSchemeTheoreticallyDominant
      (pullback.map (f ≫ pX) (g ≫ pY) (f.imageι ≫ pX) (g.imageι ≫ pY)
        f.toImage g.toImage (𝟙 _) (by simp) (by simp)) := by
  let h := AlgebraicGeometry.productMap pX pY f g
  let j := AlgebraicGeometry.productMap pX pY f.imageι g.imageι
  let d := pullback.map (f ≫ pX) (g ≫ pY) (f.imageι ≫ pX) (g.imageι ≫ pY)
    f.toImage g.toImage (𝟙 _) (by simp) (by simp)
  have : QuasiCompact h := productMap_quasiCompact pX pY f g
  obtain ⟨e, he, _⟩ := AlgebraicGeometry.existsUnique_imageProductMapIso pX pY f g
  have : IsClosedImmersion j := by
    dsimp [j, AlgebraicGeometry.productMap]
    let : MorphismProperty.IsStableUnderComposition (@IsClosedImmersion :
        MorphismProperty Scheme.{u}) :=
      ⟨fun _ _ _ _ => inferInstance⟩
    exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
      (f := f.imageι ≫ pX) (g := g.imageι ≫ pY) (f' := pX) (g' := pY)
      (i₁ := f.imageι) (i₂ := g.imageι) inferInstance inferInstance rfl rfl
  have hfac : d = h.toImage ≫ e.hom := by
    apply (cancel_mono j).1
    dsimp [d, j, h, AlgebraicGeometry.productMap]
    rw [pullback.map_comp]
    simp [Category.assoc, Scheme.Hom.toImage_imageι, he]
  have : IsSchemeTheoreticallyDominant h.toImage :=
    AlgebraicGeometry.toImage_isSchemeTheoreticallyDominant h
  change IsSchemeTheoreticallyDominant d
  rw [hfac]
  infer_instance

/-- Postcomposing both legs of a fibre product with an isomorphism of the base does not change the
fibre product. -/
private noncomputable abbrev pullbackPostcomposeIso
    {X Y S T : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (e : S ≅ T) :
    pullback f g ≅ pullback (f ≫ e.hom) (g ≫ e.hom) :=
  asIso (pullback.map f g (f ≫ e.hom) (g ≫ e.hom)
    (𝟙 X) (𝟙 Y) e.hom (by simp) (by simp))

/-- `pullbackPostcomposeIso` is compatible with the first projections. -/
private theorem pullbackPostcomposeIso_hom_fst
    {X Y S T : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (e : S ≅ T) :
    (pullbackPostcomposeIso f g e).hom ≫ pullback.fst (f ≫ e.hom) (g ≫ e.hom) =
      pullback.fst f g := by
  simp [pullbackPostcomposeIso, pullback.map]

/-- `pullbackPostcomposeIso` is compatible with the second projections. -/
private theorem pullbackPostcomposeIso_hom_snd
    {X Y S T : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (e : S ≅ T) :
    (pullbackPostcomposeIso f g e).hom ≫ pullback.snd (f ≫ e.hom) (g ≫ e.hom) =
      pullback.snd f g := by
  simp [pullbackPostcomposeIso, pullback.map]

/-- A morphism whose precomposition with a scheme-theoretically dominant morphism factors through
`f` factors through the scheme-theoretic image of `f`. -/
private theorem exists_lift_to_image_of_dominant {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (m : Z ⟶ Y)
    (d : W ⟶ Z) [IsSchemeTheoreticallyDominant d] (g : W ⟶ X) (h : d ≫ m = g ≫ f) :
    ∃ e : Z ⟶ f.image, e ≫ f.imageι = m := by
  have hker : f.ker ≤ m.ker := by
    have hd : (d ≫ m).ker = m.ker := by
      rw [Scheme.Hom.ker_comp, d.ker_eq_bot, Scheme.IdealSheafData.map_bot]
    rw [← hd, h]
    exact Scheme.Hom.le_ker_comp _ _
  exact ⟨IsClosedImmersion.lift f.ker.subschemeι m (by simpa [f.ker.ker_subschemeι] using hker),
    IsClosedImmersion.lift_fac _ _ _⟩

/-- Over a field, composition of arrows of the target groupoid restricts to the scheme-theoretic
image of the arrow map. -/
private theorem exists_comp_lift_to_image
    {S : Scheme.{u}} {k : Type u} [Field k]
    {G₁ G₂ : GroupoidScheme S} (F : GroupoidScheme.Hom G₁ G₂)
    (hobjects : G₁.objects = G₂.objects)
    (hfield : G₁.objects.left = Spec (.of k))
    (hmapObjects : F.mapObjects = eqToHom hobjects)
    [QuasiCompact F.mapArrows.left] :
    let A := F.mapArrows.left.ker
    let HArrows := Over.mk (A.subschemeι ≫ G₂.arrows.hom)
    let i : HArrows ⟶ G₂.arrows := Over.homMk A.subschemeι
    let src : HArrows ⟶ G₂.objects := Over.homMk (A.subschemeι ≫ G₂.source.left)
    let tgt : HArrows ⟶ G₂.objects := Over.homMk (A.subschemeι ≫ G₂.target.left)
    ∃ e : (pullback src tgt).left ⟶ A.subscheme,
      e ≫ A.subschemeι = (pullback.lift
        (pullback.fst src tgt ≫ i) (pullback.snd src tgt ≫ i)
        (by
          apply Over.OverMorphism.ext
          simpa [Category.assoc, src, tgt, i] using
            congrArg Over.Hom.left
              (pullback.condition : pullback.fst src tgt ≫ src =
                pullback.snd src tgt ≫ tgt)) ≫ G₂.comp).left := by
  classical
  let A := F.mapArrows.left.ker
  let HArrows := Over.mk (A.subschemeι ≫ G₂.arrows.hom)
  let i : HArrows ⟶ G₂.arrows := Over.homMk A.subschemeι
  let src : HArrows ⟶ G₂.objects := Over.homMk (A.subschemeι ≫ G₂.source.left)
  let tgt : HArrows ⟶ G₂.objects := Over.homMk (A.subschemeι ≫ G₂.target.left)
  let f := F.mapArrows.left
  let ho : G₁.objects.left = G₂.objects.left := congrArg Over.left hobjects
  let hfield₂ : G₂.objects.left = Spec (.of k) :=
    (congrArg Over.left hobjects.symm).trans hfield
  let e₁ : G₁.objects.left ≅ Spec (.of k) := eqToIso hfield
  let e₂ : G₂.objects.left ≅ Spec (.of k) := eqToIso hfield₂
  let pX : G₂.arrows.left ⟶ Spec (.of k) := G₂.source.left ≫ e₂.hom
  let pY : G₂.arrows.left ⟶ Spec (.of k) := G₂.target.left ≫ e₂.hom
  have hmap : F.mapObjects.left = eqToHom ho := by
    simpa using congrArg Over.Hom.left hmapObjects
  have hs : f ≫ G₂.source.left = G₁.source.left ≫ F.mapObjects.left :=
    congrArg Over.Hom.left F.map_source
  have ht : f ≫ G₂.target.left = G₁.target.left ≫ F.mapObjects.left :=
    congrArg Over.Hom.left F.map_target
  have hs' : G₁.source.left ≫ e₁.hom = f ≫ pX := by
    dsimp [pX, e₁, e₂, f]
    rw [← Category.assoc, hs, hmap]
    simp [Category.assoc]
  have ht' : G₁.target.left ≫ e₁.hom = f ≫ pY := by
    dsimp [pX, pY, e₁, e₂, f]
    rw [← Category.assoc, ht, hmap]
    simp [Category.assoc]
  let α₀ := overPullbackLeftIso G₁.source G₁.target
  let α₁ := pullbackPostcomposeIso G₁.source.left G₁.target.left e₁
  let α₂ := pullback.congrHom hs' ht'
  let α : (pullback G₁.source G₁.target).left ≅
      pullback (f ≫ pX) (f ≫ pY) := α₀ ≪≫ α₁ ≪≫ α₂
  have hsImage : src.left ≫ e₂.hom = f.imageι ≫ pX := by
    simp [src, f, pX, e₂, A, Category.assoc]
  have htImage : tgt.left ≫ e₂.hom = f.imageι ≫ pY := by
    simp [tgt, f, pY, e₂, A, Category.assoc]
  let β₀ := pullbackPostcomposeIso src.left tgt.left e₂
  let β₁ := pullback.congrHom hsImage htImage
  let β : (pullback src tgt).left ≅ pullback (f.imageι ≫ pX) (f.imageι ≫ pY) :=
    overPullbackLeftIso src tgt ≪≫ β₀ ≪≫ β₁
  let q := pullback.map (f ≫ pX) (f ≫ pY) (f.imageι ≫ pX) (f.imageι ≫ pY)
    f.toImage f.toImage (𝟙 _) (by simp) (by simp)
  let d := α.hom ≫ q ≫ β.inv
  let q₂ : pullback src tgt ⟶ pullback G₂.source G₂.target :=
    pullback.lift (pullback.fst src tgt ≫ i) (pullback.snd src tgt ≫ i) (by
      apply Over.OverMorphism.ext
      simpa [Category.assoc, src, tgt, i] using
        congrArg Over.Hom.left
          (pullback.condition : pullback.fst src tgt ≫ src =
            pullback.snd src tgt ≫ tgt))
  let m : (pullback src tgt).left ⟶ G₂.arrows.left := (q₂ ≫ G₂.comp).left
  have : IsSchemeTheoreticallyDominant q :=
    imageToImage_isSchemeTheoreticallyDominant pX pY f f
  have hdomd : IsSchemeTheoreticallyDominant d := by
    dsimp [d]
    infer_instance
  have hαfst : α.hom ≫ pullback.fst (f ≫ pX) (f ≫ pY) =
      (pullback.fst G₁.source G₁.target).left := by
    simp only [α, α₀, α₁, α₂, Iso.trans_hom, Category.assoc,
      overPullbackLeftIso_hom_fst, pullbackPostcomposeIso_hom_fst,
      congrHom_hom_fst]
  have hαsnd : α.hom ≫ pullback.snd (f ≫ pX) (f ≫ pY) =
      (pullback.snd G₁.source G₁.target).left := by
    simp only [α, α₀, α₁, α₂, Iso.trans_hom, Category.assoc,
      overPullbackLeftIso_hom_snd, pullbackPostcomposeIso_hom_snd,
      congrHom_hom_snd]
  have hβfst : β.hom ≫ pullback.fst (f.imageι ≫ pX) (f.imageι ≫ pY) =
      (pullback.fst src tgt).left := by
    simp only [β, β₀, β₁, Iso.trans_hom, Category.assoc,
      overPullbackLeftIso_hom_fst, pullbackPostcomposeIso_hom_fst,
      congrHom_hom_fst]
  have hβsnd : β.hom ≫ pullback.snd (f.imageι ≫ pX) (f.imageι ≫ pY) =
      (pullback.snd src tgt).left := by
    simp only [β, β₀, β₁, Iso.trans_hom, Category.assoc,
      overPullbackLeftIso_hom_snd, pullbackPostcomposeIso_hom_snd,
      congrHom_hom_snd]
  have hβinvfst : β.inv ≫ (pullback.fst src tgt).left =
      pullback.fst (f.imageι ≫ pX) (f.imageι ≫ pY) := by
    rw [← hβfst, Iso.inv_hom_id_assoc]
  have hβinvsnd : β.inv ≫ (pullback.snd src tgt).left =
      pullback.snd (f.imageι ≫ pX) (f.imageι ≫ pY) := by
    rw [← hβsnd, Iso.inv_hom_id_assoc]
  have hqfst : q ≫ pullback.fst (f.imageι ≫ pX) (f.imageι ≫ pY) =
      pullback.fst (f ≫ pX) (f ≫ pY) ≫ f.toImage := by
    dsimp [q, pullback.map]
    rw [pullback.lift_fst]
  have hqsnd : q ≫ pullback.snd (f.imageι ≫ pX) (f.imageι ≫ pY) =
      pullback.snd (f ≫ pX) (f ≫ pY) ≫ f.toImage := by
    dsimp [q, pullback.map]
    rw [pullback.lift_snd]
  have hfst : d ≫ (pullback.fst src tgt).left ≫ i.left =
      (pullback.fst G₁.source G₁.target).left ≫ f := by
    calc
      d ≫ (pullback.fst src tgt).left ≫ i.left =
          α.hom ≫ q ≫ (β.inv ≫ (pullback.fst src tgt).left) ≫ i.left := by
        simp [d, Category.assoc]
      _ = α.hom ≫ q ≫ pullback.fst (f.imageι ≫ pX) (f.imageι ≫ pY) ≫ i.left := by
        rw [hβinvfst]
      _ = α.hom ≫ (q ≫ pullback.fst (f.imageι ≫ pX) (f.imageι ≫ pY)) ≫ i.left := by
        simp [Category.assoc]
      _ = α.hom ≫ (pullback.fst (f ≫ pX) (f ≫ pY) ≫ f.toImage) ≫ f.imageι := by
        rw [hqfst]
        simp [i, A, f, Scheme.Hom.imageι]
      _ = α.hom ≫ pullback.fst (f ≫ pX) (f ≫ pY) ≫ f.toImage ≫ f.imageι := by
        simp [Category.assoc]
      _ = (pullback.fst G₁.source G₁.target).left ≫ f := by
        rw [f.toImage_imageι, ← Category.assoc, hαfst]
  have hsnd : d ≫ (pullback.snd src tgt).left ≫ i.left =
      (pullback.snd G₁.source G₁.target).left ≫ f := by
    calc
      d ≫ (pullback.snd src tgt).left ≫ i.left =
          α.hom ≫ q ≫ (β.inv ≫ (pullback.snd src tgt).left) ≫ i.left := by
        simp [d, Category.assoc]
      _ = α.hom ≫ q ≫ pullback.snd (f.imageι ≫ pX) (f.imageι ≫ pY) ≫ i.left := by
        rw [hβinvsnd]
      _ = α.hom ≫ (q ≫ pullback.snd (f.imageι ≫ pX) (f.imageι ≫ pY)) ≫ i.left := by
        simp [Category.assoc]
      _ = α.hom ≫ (pullback.snd (f ≫ pX) (f ≫ pY) ≫ f.toImage) ≫ f.imageι := by
        rw [hqsnd]
        simp [i, A, f, Scheme.Hom.imageι]
      _ = α.hom ≫ pullback.snd (f ≫ pX) (f ≫ pY) ≫ f.toImage ≫ f.imageι := by
        simp [Category.assoc]
      _ = (pullback.snd G₁.source G₁.target).left ≫ f := by
        rw [f.toImage_imageι, ← Category.assoc, hαsnd]
  have hq₂fst : q₂ ≫ pullback.fst G₂.source G₂.target = pullback.fst src tgt ≫ i :=
    pullback.lift_fst _ _ _
  have hq₂snd : q₂ ≫ pullback.snd G₂.source G₂.target = pullback.snd src tgt ≫ i :=
    pullback.lift_snd _ _ _
  let u := pullback.fst G₁.source G₁.target
  let v := pullback.snd G₁.source G₁.target
  have w : u ≫ G₁.source = v ≫ G₁.target := pullback.condition
  have w' : (u ≫ F.mapArrows) ≫ G₂.source = (v ≫ F.mapArrows) ≫ G₂.target := by
    simpa only [Category.assoc, F.map_source, F.map_target] using
      congrArg (fun z => z ≫ F.mapObjects) w
  let l : pullback G₁.source G₁.target ⟶ pullback G₂.source G₂.target :=
    pullback.lift (u ≫ F.mapArrows) (v ≫ F.mapArrows) w'
  have hl_fst : l ≫ pullback.fst G₂.source G₂.target = u ≫ F.mapArrows :=
    pullback.lift_fst _ _ _
  have hl_snd : l ≫ pullback.snd G₂.source G₂.target = v ≫ F.mapArrows :=
    pullback.lift_snd _ _ _
  have hpair : d ≫ q₂.left = l.left := by
    apply (cancel_mono (overPullbackLeftIso G₂.source G₂.target).hom).1
    apply pullback.hom_ext
    · calc
        (d ≫ q₂.left ≫ (overPullbackLeftIso G₂.source G₂.target).hom) ≫
            pullback.fst G₂.source.left G₂.target.left =
          d ≫ (pullback.fst src tgt).left ≫ i.left := by
            simp only [Category.assoc, overPullbackLeftIso_hom_fst]
            change d ≫ (q₂ ≫ pullback.fst G₂.source G₂.target).left = _
            rw [hq₂fst]
            rfl
        _ = u.left ≫ f := hfst
        _ = (l.left ≫ (overPullbackLeftIso G₂.source G₂.target).hom) ≫
              pullback.fst G₂.source.left G₂.target.left := by
            simp only [Category.assoc, overPullbackLeftIso_hom_fst]
            change _ = (l ≫ pullback.fst G₂.source G₂.target).left
            rw [hl_fst]
            rfl
    · calc
        (d ≫ q₂.left ≫ (overPullbackLeftIso G₂.source G₂.target).hom) ≫
            pullback.snd G₂.source.left G₂.target.left =
          d ≫ (pullback.snd src tgt).left ≫ i.left := by
            simp only [Category.assoc, overPullbackLeftIso_hom_snd]
            change d ≫ (q₂ ≫ pullback.snd G₂.source G₂.target).left = _
            rw [hq₂snd]
            rfl
        _ = v.left ≫ f := hsnd
        _ = (l.left ≫ (overPullbackLeftIso G₂.source G₂.target).hom) ≫
              pullback.snd G₂.source.left G₂.target.left := by
            simp only [Category.assoc, overPullbackLeftIso_hom_snd]
            change _ = (l ≫ pullback.snd G₂.source G₂.target).left
            rw [hl_snd]
            rfl
  have hfac : d ≫ m = G₁.comp.left ≫ f := by
    dsimp [m]
    calc
      d ≫ (q₂.left ≫ G₂.comp.left) = l.left ≫ G₂.comp.left := by
        rw [← Category.assoc, hpair]
      _ = G₁.comp.left ≫ f := by
        simpa [l, u, v, w, GroupoidScheme.compose, f, Category.assoc] using
          (congrArg Over.Hom.left (F.map_comp (pullback G₁.source G₁.target) u v w w')).symm
  exact exists_lift_to_image_of_dominant f m d G₁.comp.left hfac

/-- The inverse morphism of the target groupoid restricts to the scheme-theoretic image of the
arrow map. -/
private theorem exists_inverse_lift_to_image
    {S : Scheme.{u}} {G₁ G₂ : GroupoidScheme S}
    (F : GroupoidScheme.Hom G₁ G₂) [QuasiCompact F.mapArrows.left] :
    ∃ e : F.mapArrows.left.image ⟶ F.mapArrows.left.image,
      e ≫ F.mapArrows.left.imageι = F.mapArrows.left.imageι ≫ G₂.inverse.left := by
  let f := F.mapArrows.left
  have hrel : f ≫ G₂.inverse.left = G₁.inverse.left ≫ f := by
    simpa [f] using congrArg Over.Hom.left (groupoidHom_map_inverse F)
  have := toImage_isSchemeTheoreticallyDominant f
  exact exists_lift_to_image_of_dominant f _ f.toImage G₁.inverse.left
    (by rw [Scheme.Hom.toImage_imageι_assoc, hrel])

/-- The groupoid scheme structure on the scheme-theoretic image of the arrow map, together with
the data identifying its objects, arrows and canonical morphism. -/
private noncomputable def imageGroupoidData_construct
    {S : Scheme.{u}} {k : Type u} [Field k]
    {G₁ G₂ : GroupoidScheme S} (F : GroupoidScheme.Hom G₁ G₂)
    (hobjects : G₁.objects = G₂.objects)
    (hfield : G₁.objects.left = Spec (.of k))
    (hmapObjects : F.mapObjects = eqToHom hobjects)
    [QuasiCompact F.mapArrows.left] :
    { H : GroupoidScheme S //
      ∃ (j : GroupoidScheme.Hom H G₂)
        (hHobjects : H.objects = G₂.objects)
        (hHarrows : H.arrows =
          Over.mk ((F.mapArrows.left.ker).subschemeι ≫ G₂.arrows.hom)),
        (j.mapObjects = eqToHom hHobjects) ∧
        (j.mapArrows.left =
            eqToHom (congrArg Over.left hHarrows) ≫
              (F.mapArrows.left.ker).subschemeι) } := by
  classical
  let A := F.mapArrows.left.ker
  let HArrows := Over.mk (A.subschemeι ≫ G₂.arrows.hom)
  let i : HArrows ⟶ G₂.arrows := Over.homMk A.subschemeι
  let src : HArrows ⟶ G₂.objects := Over.homMk (A.subschemeι ≫ G₂.source.left)
  let tgt : HArrows ⟶ G₂.objects := Over.homMk (A.subschemeι ≫ G₂.target.left)
  have hisrc : i ≫ G₂.source = src := Over.OverMorphism.ext rfl
  have hitgt : i ≫ G₂.target = tgt := Over.OverMorphism.ext rfl
  let idLift := Classical.choose (exists_identity_lift_to_image
    F hobjects hmapObjects)
  have hidLift := Classical.choose_spec (exists_identity_lift_to_image
    F hobjects hmapObjects)
  let invLift := Classical.choose (exists_inverse_lift_to_image F)
  have hinvLift := Classical.choose_spec (exists_inverse_lift_to_image F)
  let compLift := Classical.choose (exists_comp_lift_to_image
    (k := k) F hobjects hfield hmapObjects)
  have hcompLift := Classical.choose_spec (exists_comp_lift_to_image
    (k := k) F hobjects hfield hmapObjects)
  let q : pullback src tgt ⟶ pullback G₂.source G₂.target :=
    pullback.lift (pullback.fst src tgt ≫ i) (pullback.snd src tgt ≫ i) (by
      apply Over.OverMorphism.ext
      simpa [Category.assoc, hisrc, hitgt] using
        congrArg Over.Hom.left
          (pullback.condition : pullback.fst src tgt ≫ src =
            pullback.snd src tgt ≫ tgt))
  have hqfst : q ≫ pullback.fst G₂.source G₂.target =
      pullback.fst src tgt ≫ i := by
    dsimp only [q]
    rw [pullback.lift_fst]
  have hqsnd : q ≫ pullback.snd G₂.source G₂.target =
      pullback.snd src tgt ≫ i := by
    dsimp only [q]
    rw [pullback.lift_snd]
  let idH : G₂.objects ⟶ HArrows := Over.homMk idLift (by
    calc
      idLift ≫ HArrows.hom = (idLift ≫ A.subschemeι) ≫ G₂.arrows.hom := by
        simp [HArrows, Category.assoc]
      _ = G₂.identity.left ≫ G₂.arrows.hom := by rw [hidLift]
      _ = G₂.objects.hom := G₂.identity.w)
  let invH : HArrows ⟶ HArrows := Over.homMk invLift (by
    calc
      invLift ≫ HArrows.hom = (invLift ≫ A.subschemeι) ≫ G₂.arrows.hom := by
        simp [HArrows, Category.assoc]
      _ = (A.subschemeι ≫ G₂.inverse.left) ≫ G₂.arrows.hom := by rw [hinvLift]
      _ = HArrows.hom := by simp [HArrows, Category.assoc])
  let compH : pullback src tgt ⟶ HArrows := Over.homMk compLift (by
    calc
      compLift ≫ HArrows.hom = (compLift ≫ A.subschemeι) ≫ G₂.arrows.hom := by
        simp [HArrows, Category.assoc]
      _ = ((q ≫ G₂.comp).left) ≫ G₂.arrows.hom := by rw [hcompLift]
      _ = (pullback src tgt).hom := (q ≫ G₂.comp).w)
  have hIdI : idH ≫ i = G₂.identity := Over.OverMorphism.ext hidLift
  have hInvI : invH ≫ i = i ≫ G₂.inverse := Over.OverMorphism.ext hinvLift
  have hCompI : compH ≫ i = q ≫ G₂.comp := Over.OverMorphism.ext hcompLift
  let : Mono i := inferInstance
  have hcompose {T : Over S} (a b : T ⟶ HArrows)
      (w : a ≫ src = b ≫ tgt)
      (w' : (a ≫ i) ≫ G₂.source = (b ≫ i) ≫ G₂.target) :
      (pullback.lift a b w ≫ compH) ≫ i =
        G₂.compose (a ≫ i) (b ≫ i) w' := by
    have hfac : pullback.lift a b w ≫ q =
        pullback.lift (a ≫ i) (b ≫ i) w' := by
      apply pullback.hom_ext
      · rw [Category.assoc, hqfst, ← Category.assoc, pullback.lift_fst, pullback.lift_fst]
      · rw [Category.assoc, hqsnd, ← Category.assoc, pullback.lift_snd, pullback.lift_snd]
    rw [Category.assoc, hCompI, ← Category.assoc, hfac]
    rfl
  let H : GroupoidScheme S :=
    { objects := G₂.objects
      arrows := HArrows
      source := src
      target := tgt
      comp := compH
      identity := idH
      inverse := invH
      source_identity := by rw [← hisrc, ← Category.assoc, hIdI, G₂.source_identity]
      target_identity := by rw [← hitgt, ← Category.assoc, hIdI, G₂.target_identity]
      source_inverse := by
        apply Over.OverMorphism.ext
        change invLift ≫ A.subschemeι ≫ G₂.source.left =
          A.subschemeι ≫ G₂.target.left
        have hs := congrArg Over.Hom.left G₂.source_inverse
        change G₂.inverse.left ≫ G₂.source.left = G₂.target.left at hs
        rw [← Category.assoc, hinvLift, Category.assoc, hs]
      target_inverse := by
        apply Over.OverMorphism.ext
        change invLift ≫ A.subschemeι ≫ G₂.target.left =
          A.subschemeι ≫ G₂.source.left
        have ht := congrArg Over.Hom.left G₂.target_inverse
        change G₂.inverse.left ≫ G₂.target.left = G₂.source.left at ht
        rw [← Category.assoc, hinvLift, Category.assoc, ht]
      source_comp := by
        calc
          compH ≫ src = compH ≫ (i ≫ G₂.source) := by rw [hisrc]
          _ = (q ≫ G₂.comp) ≫ G₂.source := by rw [← Category.assoc, hCompI]
          _ = (pullback.snd src tgt ≫ i) ≫ G₂.source := by
            rw [Category.assoc, G₂.source_comp, ← Category.assoc, hqsnd]
          _ = pullback.snd src tgt ≫ src := by rw [Category.assoc, hisrc]
      target_comp := by
        calc
          compH ≫ tgt = compH ≫ (i ≫ G₂.target) := by rw [hitgt]
          _ = (q ≫ G₂.comp) ≫ G₂.target := by rw [← Category.assoc, hCompI]
          _ = (pullback.fst src tgt ≫ i) ≫ G₂.target := by
            rw [Category.assoc, G₂.target_comp, ← Category.assoc, hqfst]
          _ = pullback.fst src tgt ≫ tgt := by rw [Category.assoc, hitgt]
      left_identity := by
        intro T f w
        apply (cancel_mono i).1
        rw [hcompose (f ≫ tgt ≫ idH) f w (by
          simp [Category.assoc, hIdI, ← hitgt, G₂.source_identity])]
        simpa [GroupoidScheme.compose, Category.assoc, hIdI, ← hitgt] using
          G₂.left_identity T (f ≫ i) (by simp [Category.assoc, G₂.source_identity])
      right_identity := by
        intro T f w
        apply (cancel_mono i).1
        rw [hcompose f (f ≫ src ≫ idH) w (by
          simp [Category.assoc, hIdI, ← hisrc, G₂.target_identity])]
        simpa [GroupoidScheme.compose, Category.assoc, hIdI, ← hisrc] using
          G₂.right_identity T (f ≫ i) (by simp [Category.assoc, G₂.target_identity])
      left_inverse := by
        intro T f w
        apply (cancel_mono i).1
        rw [hcompose (f ≫ invH) f w (by
          simp [Category.assoc, hInvI, G₂.source_inverse])]
        simpa [GroupoidScheme.compose, Category.assoc, hInvI, hIdI, ← hisrc, ← hitgt] using
          G₂.left_inverse T (f ≫ i) (by simp [Category.assoc, G₂.source_inverse])
      right_inverse := by
        intro T f w
        apply (cancel_mono i).1
        rw [hcompose f (f ≫ invH) w (by
          simp [Category.assoc, hInvI, G₂.target_inverse])]
        simpa [GroupoidScheme.compose, Category.assoc, hInvI, hIdI, ← hisrc, ← hitgt] using
          G₂.right_inverse T (f ≫ i) (by simp [Category.assoc, G₂.target_inverse])
      assoc := by
        intro T f g h wfg wgh w₁ w₂
        apply (cancel_mono i).1
        let f' := f ≫ i
        let g' := g ≫ i
        let h' := h ≫ i
        have wfg' : f' ≫ G₂.source = g' ≫ G₂.target := by
          dsimp [f', g']
          calc
            (f ≫ i) ≫ G₂.source = f ≫ src := by rw [Category.assoc, hisrc]
            _ = g ≫ tgt := wfg
            _ = (g ≫ i) ≫ G₂.target := by rw [Category.assoc, hitgt]
        have wgh' : g' ≫ G₂.source = h' ≫ G₂.target := by
          dsimp [g', h']
          calc
            (g ≫ i) ≫ G₂.source = g ≫ src := by rw [Category.assoc, hisrc]
            _ = h ≫ tgt := wgh
            _ = (h ≫ i) ≫ G₂.target := by rw [Category.assoc, hitgt]
        have w₁' : (G₂.compose f' g' wfg') ≫ G₂.source = h' ≫ G₂.target := by
          calc
            (G₂.compose f' g' wfg') ≫ G₂.source =
                ((pullback.lift f g wfg ≫ compH) ≫ i) ≫ G₂.source :=
                  congrArg (fun z => z ≫ G₂.source) (hcompose f g wfg wfg').symm
            _ = (pullback.lift f g wfg ≫ compH) ≫ src := by
              rw [Category.assoc, hisrc]
            _ = h ≫ tgt := w₁
            _ = h' ≫ G₂.target := by dsimp [h']; rw [Category.assoc, hitgt]
        have w₂' : f' ≫ G₂.source = (G₂.compose g' h' wgh') ≫ G₂.target := by
          calc
            f' ≫ G₂.source = f ≫ src := by dsimp [f']; rw [Category.assoc, hisrc]
            _ = (pullback.lift g h wgh ≫ compH) ≫ tgt := w₂
            _ = (pullback.lift g h wgh ≫ compH) ≫ (i ≫ G₂.target) := by rw [hitgt]
            _ = ((pullback.lift g h wgh ≫ compH) ≫ i) ≫ G₂.target :=
              (Category.assoc _ _ _).symm
            _ = (G₂.compose g' h' wgh') ≫ G₂.target :=
              congrArg (fun z => z ≫ G₂.target) (hcompose g h wgh wgh')
        have w₁'' : ((pullback.lift f g wfg ≫ compH) ≫ i) ≫ G₂.source =
            h' ≫ G₂.target := by
          calc
            ((pullback.lift f g wfg ≫ compH) ≫ i) ≫ G₂.source =
                (pullback.lift f g wfg ≫ compH) ≫ (i ≫ G₂.source) :=
                  Category.assoc _ _ _
            _ = (pullback.lift f g wfg ≫ compH) ≫ src := by rw [hisrc]
            _ = h ≫ tgt := w₁
            _ = h' ≫ G₂.target := by simp [h', ← hitgt, Category.assoc]
        have w₂'' : f' ≫ G₂.source =
            ((pullback.lift g h wgh ≫ compH) ≫ i) ≫ G₂.target := by
          calc
            f' ≫ G₂.source = f ≫ src := by dsimp [f']; rw [Category.assoc, hisrc]
            _ = (pullback.lift g h wgh ≫ compH) ≫ tgt := w₂
            _ = (pullback.lift g h wgh ≫ compH) ≫ (i ≫ G₂.target) := by rw [hitgt]
            _ = ((pullback.lift g h wgh ≫ compH) ≫ i) ≫ G₂.target :=
              (Category.assoc _ _ _).symm
        have hfg := hcompose f g wfg wfg'
        have hgh := hcompose g h wgh wgh'
        have hcompAssocLeft :
            G₂.compose ((pullback.lift f g wfg ≫ compH) ≫ i) h' w₁'' =
              G₂.compose (G₂.compose f' g' wfg') h' w₁' := by
          change pullback.lift ((pullback.lift f g wfg ≫ compH) ≫ i) h' w₁'' ≫ G₂.comp =
            pullback.lift (G₂.compose f' g' wfg') h' w₁' ≫ G₂.comp
          apply congrArg (fun z => z ≫ G₂.comp)
          apply pullback.hom_ext
          · rw [pullback.lift_fst, pullback.lift_fst, hfg]
          · rw [pullback.lift_snd, pullback.lift_snd]
        have hcompAssocRight :
            G₂.compose f' (G₂.compose g' h' wgh') w₂' =
              G₂.compose f' ((pullback.lift g h wgh ≫ compH) ≫ i) w₂'' := by
          change pullback.lift f' (G₂.compose g' h' wgh') w₂' ≫ G₂.comp =
            pullback.lift f' ((pullback.lift g h wgh ≫ compH) ≫ i) w₂'' ≫ G₂.comp
          apply congrArg (fun z => z ≫ G₂.comp)
          apply pullback.hom_ext
          · rw [pullback.lift_fst, pullback.lift_fst]
          · rw [pullback.lift_snd, pullback.lift_snd, hgh]
        calc
          (pullback.lift (pullback.lift f g wfg ≫ compH) h w₁ ≫ compH) ≫ i =
              G₂.compose ((pullback.lift f g wfg ≫ compH) ≫ i) h' w₁'' :=
                hcompose (pullback.lift f g wfg ≫ compH) h w₁ w₁''
          _ = G₂.compose (G₂.compose f' g' wfg') h' w₁' := hcompAssocLeft
          _ = G₂.compose f' (G₂.compose g' h' wgh') _ := G₂.assoc T f' g' h' wfg' wgh' w₁' w₂'
          _ = G₂.compose f' ((pullback.lift g h wgh ≫ compH) ≫ i) w₂'' := hcompAssocRight
          _ = (pullback.lift f (pullback.lift g h wgh ≫ compH) w₂ ≫ compH) ≫ i :=
            (hcompose f (pullback.lift g h wgh ≫ compH) w₂ w₂'').symm }
  let j : GroupoidScheme.Hom H G₂ :=
    { mapObjects := 𝟙 G₂.objects
      mapArrows := i
      map_source := hisrc
      map_target := hitgt
      map_identity := hIdI.symm
      map_comp := fun _ f g w w' => hcompose f g w w' }
  exact ⟨H, j, rfl, rfl, rfl, rfl⟩

/-- **Stacks Project, Tag 04QA.** The scheme-theoretic image of a quasi-compact
arrow map of groupoid schemes over a field has the restricted groupoid structure. -/
@[stacks 04QA]
public theorem exists_groupoidScheme_image
    {S : Scheme.{u}} {k : Type u} [Field k]
    {G₁ G₂ : GroupoidScheme S} (F : GroupoidScheme.Hom G₁ G₂)
    (hobjects : G₁.objects = G₂.objects)
    (hfield : G₁.objects.left = Spec (.of k))
    (hmapObjects : F.mapObjects = eqToHom hobjects)
    [QuasiCompact F.mapArrows.left] :
    ∃ (H : GroupoidScheme S) (j : GroupoidScheme.Hom H G₂)
      (hHobjects : H.objects = G₂.objects)
      (hHarrows : H.arrows = Over.mk
        (F.mapArrows.left.imageι ≫ G₂.arrows.hom)),
        (j.mapObjects = eqToHom hHobjects) ∧
        (j.mapArrows.left =
          eqToHom (congrArg Over.left hHarrows) ≫ F.mapArrows.left.imageι) :=
  ⟨_, (imageGroupoidData_construct F hobjects hfield hmapObjects).property⟩

end AlgebraicGeometry
