module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.OverPullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.RestrictionOverField
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.BaseChange

/-!
# Restricting a morphism of groupoid schemes

A morphism of groupoid schemes which is compatible with two maps to the two object schemes
restricts to a morphism between the two restricted groupoid schemes. When the two object
schemes are spectra of a field and the restricting maps come from one extension of that field,
the canonical morphism from a restricted arrow scheme to the original arrow scheme is a
homeomorphism, because it is surjective, universally open and universally injective.

The restricting map used for this is the spectrum of a purely inseparable extension, for
instance of the perfect closure of the ground field.

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.restrictionArrowsMap` is the induced morphism between the
  iterated fibre products carrying the arrows of the two restrictions.
* `AlgebraicGeometry.GroupoidScheme.restrictHom` is the restricted morphism of groupoid
  schemes, packaged with the identification of its map on objects and the commuting square
  with the two canonical morphisms to the unrestricted groupoids.

## Main results

* `AlgebraicGeometry.isHomeomorph_base_eqToHom`: the underlying map of an identification of
  two schemes is a homeomorphism.
* `AlgebraicGeometry.universallyInjective_specMap_algebraMap`: the spectrum of a purely
  inseparable field extension is universally injective.
* `AlgebraicGeometry.GroupoidScheme.isHomeomorph_mapArrows_restrict`: over a field extension
  the canonical morphism on arrow schemes of a restriction is a homeomorphism.

## Implementation notes

The restricted morphism is produced as a subtype rather than as a bare definition because the
two identifications recorded alongside it are what its consumers use, and because the arrow
scheme of a restriction is only specified up to the equality `arrows_eq` of
`AlgebraicGeometry.GroupoidScheme.Restriction`. Its functoriality axioms are checked after
evaluation on a test scheme, where the canonical functor out of a restriction is fully
faithful.

## References

* [Stacks Project, Tag 02VB](https://stacks.math.columbia.edu/tag/02VB)
* [Stacks Project, Tag 04LQ](https://stacks.math.columbia.edu/tag/04LQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-! ### Identifications of schemes -/

/-- The underlying map of an identification of two schemes is a homeomorphism. -/
theorem isHomeomorph_base_eqToHom {X Y : Scheme.{u}} (e : X = Y) :
    IsHomeomorph (eqToHom e).base := by
  cases e
  exact IsHomeomorph.id

/-! ### Purely inseparable extensions -/

/-- The morphism of spectra induced by a purely inseparable extension of fields is universally
injective. -/
alias universallyInjective_specMap_algebraMap :=
  universallyInjective_specMap_of_isPurelyInseparable

namespace GroupoidScheme

/-! ### Functoriality of restriction -/

variable {S : Scheme.{u}} {G₁ G₂ : GroupoidScheme S}

/-- The morphism between the iterated fibre products carrying the arrows of two restrictions
induced by a morphism of groupoid schemes compatible with the restricting maps. -/
noncomputable def restrictionArrowsMap (F : GroupoidScheme.Hom G₁ G₂) {U' : Over S}
    (g₁ : U' ⟶ G₁.objects) (g₂ : U' ⟶ G₂.objects) (hg : g₁ ≫ F.mapObjects = g₂) :
    restrictionArrows G₁ g₁ ⟶ restrictionArrows G₂ g₂ :=
  pullback.map (pullback.snd g₁ G₁.target) (pullback.fst G₁.source g₁)
    (pullback.snd g₂ G₂.target) (pullback.fst G₂.source g₂)
    (pullback.map g₁ G₁.target g₂ G₂.target (𝟙 U') F.mapArrows F.mapObjects
      (by simpa using hg) F.map_target.symm)
    (pullback.map G₁.source g₁ G₂.source g₂ F.mapArrows (𝟙 U') F.mapObjects
      F.map_source.symm (by simpa using hg))
    F.mapArrows (by dsimp [pullback.map]; rw [pullback.lift_snd])
    (by dsimp [pullback.map]; rw [pullback.lift_fst])

/-- `AlgebraicGeometry.GroupoidScheme.restrictionArrowsMap` is compatible with the source maps
of the two restrictions. -/
theorem restrictionArrowsMap_comp_restrictionSource (F : GroupoidScheme.Hom G₁ G₂) {U' : Over S}
    (g₁ : U' ⟶ G₁.objects) (g₂ : U' ⟶ G₂.objects) (hg : g₁ ≫ F.mapObjects = g₂) :
    restrictionArrowsMap F g₁ g₂ hg ≫ restrictionSource G₂ g₂ = restrictionSource G₁ g₁ := by
  dsimp [restrictionArrowsMap, restrictionSource, restrictionArrows, pullback.map]
  simp only [Category.assoc, pullback.lift_snd_assoc, pullback.lift_snd, Category.comp_id]

/-- `AlgebraicGeometry.GroupoidScheme.restrictionArrowsMap` is compatible with the target maps
of the two restrictions. -/
theorem restrictionArrowsMap_comp_restrictionTarget (F : GroupoidScheme.Hom G₁ G₂) {U' : Over S}
    (g₁ : U' ⟶ G₁.objects) (g₂ : U' ⟶ G₂.objects) (hg : g₁ ≫ F.mapObjects = g₂) :
    restrictionArrowsMap F g₁ g₂ hg ≫ restrictionTarget G₂ g₂ = restrictionTarget G₁ g₁ := by
  dsimp [restrictionArrowsMap, restrictionTarget, restrictionArrows, pullback.map]
  simp only [Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst, Category.comp_id]

/-- `AlgebraicGeometry.GroupoidScheme.restrictionArrowsMap` is compatible with the canonical
maps to the two unrestricted arrow schemes. -/
theorem restrictionArrowsMap_comp_restrictionArrowsToArrows (F : GroupoidScheme.Hom G₁ G₂)
    {U' : Over S} (g₁ : U' ⟶ G₁.objects) (g₂ : U' ⟶ G₂.objects)
    (hg : g₁ ≫ F.mapObjects = g₂) :
    restrictionArrowsMap F g₁ g₂ hg ≫ restrictionArrowsToArrows G₂ g₂ =
      restrictionArrowsToArrows G₁ g₁ ≫ F.mapArrows := by
  dsimp [restrictionArrowsMap, restrictionArrowsToArrows, restrictionArrows, pullback.map]
  simp only [Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd]

/-- The source of the composite of two composable generalized arrows `f` and `g` is the source of
`g`. -/
theorem compose_comp_source (G : GroupoidScheme S) {T : Over S} {f g : T ⟶ G.arrows}
    (w : f ≫ G.source = g ≫ G.target) : G.compose f g w ≫ G.source = g ≫ G.source := by
  show (pullback.lift f g w ≫ G.comp) ≫ G.source = _
  rw [Category.assoc, G.source_comp, ← Category.assoc, pullback.lift_snd]

/-- The target of the composite of two composable generalized arrows `f` and `g` is the target of
`f`. -/
theorem compose_comp_target (G : GroupoidScheme S) {T : Over S} {f g : T ⟶ G.arrows}
    (w : f ≫ G.source = g ≫ G.target) : G.compose f g w ≫ G.target = f ≫ G.target := by
  show (pullback.lift f g w ≫ G.comp) ≫ G.target = _
  rw [Category.assoc, G.target_comp, ← Category.assoc, pullback.lift_fst]

/-- A morphism of groupoid schemes sends composable generalized arrows to composable ones. -/
theorem mapArrows_composable {G H : GroupoidScheme S} (F : GroupoidScheme.Hom G H) {T : Over S}
    {f g : T ⟶ G.arrows} (w : f ≫ G.source = g ≫ G.target) :
    (f ≫ F.mapArrows) ≫ H.source = (g ≫ F.mapArrows) ≫ H.target := by
  rw [Category.assoc, Category.assoc, F.map_source, F.map_target, ← Category.assoc,
    ← Category.assoc, w]

/-- A pair of maps compatible with source and target which lies over a morphism of groupoid
schemes, along a morphism whose evaluations are fully faithful, preserves identities. -/
theorem comp_identity_eq_of_fullyFaithful {H₁ H₂ : GroupoidScheme S} (a : GroupoidScheme.Hom H₁ G₁)
    (b : GroupoidScheme.Hom H₂ G₂) (F : GroupoidScheme.Hom G₁ G₂)
    {mapObj : H₁.objects ⟶ H₂.objects} {mapArr : H₁.arrows ⟶ H₂.arrows}
    (hsource : mapArr ≫ H₂.source = H₁.source ≫ mapObj)
    (htarget : mapArr ≫ H₂.target = H₁.target ≫ mapObj)
    (hobjects : mapObj ≫ b.mapObjects = a.mapObjects ≫ F.mapObjects)
    (harrows : mapArr ≫ b.mapArrows = a.mapArrows ≫ F.mapArrows)
    (hff : ∀ T : Over S, Nonempty (b.evaluation T).FullyFaithful) :
    mapObj ≫ H₂.identity = H₁.identity ≫ mapArr := by
  ext
  apply yoneda.map_injective
  ext T x
  let T' : Over S := Over.mk (x ≫ H₁.objects.hom)
  let x' : T' ⟶ H₁.objects := Over.homMk x (by simp [T'])
  let y : T' ⟶ H₂.objects := x' ≫ mapObj
  let hleft : H₂.EvaluationHom y y :=
    { arrow := y ≫ H₂.identity
      source_eq := by simp [Category.assoc, H₂.source_identity]
      target_eq := by simp [Category.assoc, H₂.target_identity] }
  have hside : ∀ (s : H₂.arrows ⟶ H₂.objects) (s₁ : H₁.arrows ⟶ H₁.objects),
      mapArr ≫ s = s₁ ≫ mapObj → H₁.identity ≫ s₁ = 𝟙 _ → x' ≫ H₁.identity ≫ mapArr ≫ s = y :=
    fun s s₁ h h₁ => by simp [y, h, ← Category.assoc H₁.identity, h₁]
  let hright : H₂.EvaluationHom y y :=
    { arrow := x' ≫ H₁.identity ≫ mapArr
      source_eq := hside _ _ hsource H₁.source_identity
      target_eq := hside _ _ htarget H₁.target_identity }
  have himage : (b.evaluation T').map hleft = (b.evaluation T').map hright := by
    apply GroupoidScheme.EvaluationHom.ext
    show hleft.arrow ≫ b.mapArrows = hright.arrow ≫ b.mapArrows
    dsimp [hleft, hright]
    calc
      y ≫ H₂.identity ≫ b.mapArrows = y ≫ b.mapObjects ≫ G₂.identity := by
        rw [← b.map_identity]
      _ = x' ≫ a.mapObjects ≫ F.mapObjects ≫ G₂.identity := by
        simpa [y, Category.assoc] using congrArg (fun q => x' ≫ q ≫ G₂.identity) hobjects
      _ = x' ≫ a.mapObjects ≫ G₁.identity ≫ F.mapArrows := by
        simpa [Category.assoc] using congrArg (fun q => x' ≫ a.mapObjects ≫ q) F.map_identity
      _ = x' ≫ H₁.identity ≫ a.mapArrows ≫ F.mapArrows := by
        simpa [Category.assoc] using congrArg (fun q => x' ≫ q ≫ F.mapArrows) a.map_identity
      _ = x' ≫ H₁.identity ≫ mapArr ≫ b.mapArrows := by
        simpa [Category.assoc] using congrArg (fun q => x' ≫ H₁.identity ≫ q) harrows.symm
  show x ≫ (mapObj ≫ H₂.identity).left = x ≫ (H₁.identity ≫ mapArr).left
  simpa [T', x', y, hleft, hright, Over.comp_left, Category.assoc] using
    congrArg Over.Hom.left
      (congrArg (fun q => q.arrow) ((Classical.choice (hff T')).map_injective himage))

/-- A pair of maps compatible with source and target which lies over a morphism of groupoid
schemes, along a morphism whose evaluations are fully faithful, preserves composition. -/
theorem compose_comp_eq_of_fullyFaithful {H₁ H₂ : GroupoidScheme S} (a : GroupoidScheme.Hom H₁ G₁)
    (b : GroupoidScheme.Hom H₂ G₂) (F : GroupoidScheme.Hom G₁ G₂)
    {mapObj : H₁.objects ⟶ H₂.objects} {mapArr : H₁.arrows ⟶ H₂.arrows}
    (hsource : mapArr ≫ H₂.source = H₁.source ≫ mapObj)
    (htarget : mapArr ≫ H₂.target = H₁.target ≫ mapObj)
    (harrows : mapArr ≫ b.mapArrows = a.mapArrows ≫ F.mapArrows)
    (hff : ∀ T : Over S, Nonempty (b.evaluation T).FullyFaithful)
    (T : Over S) (f g : T ⟶ H₁.arrows) (w : f ≫ H₁.source = g ≫ H₁.target)
    (w' : (f ≫ mapArr) ≫ H₂.source = (g ≫ mapArr) ≫ H₂.target) :
    H₁.compose f g w ≫ mapArr = H₂.compose (f ≫ mapArr) (g ≫ mapArr) w' := by
  let leftHom : H₂.EvaluationHom ((g ≫ H₁.source) ≫ mapObj) ((f ≫ H₁.target) ≫ mapObj) :=
    { arrow := H₁.compose f g w ≫ mapArr
      source_eq := by rw [Category.assoc, hsource, ← Category.assoc, compose_comp_source H₁ w]
      target_eq := by rw [Category.assoc, htarget, ← Category.assoc, compose_comp_target H₁ w] }
  let rightHom : H₂.EvaluationHom ((g ≫ H₁.source) ≫ mapObj) ((f ≫ H₁.target) ≫ mapObj) :=
    { arrow := H₂.compose (f ≫ mapArr) (g ≫ mapArr) w'
      source_eq := by rw [compose_comp_source H₂ w', Category.assoc, hsource, ← Category.assoc]
      target_eq := by rw [compose_comp_target H₂ w', Category.assoc, htarget, ← Category.assoc] }
  have wA := mapArrows_composable a w
  have heq : ∀ h : T ⟶ H₁.arrows,
      (h ≫ a.mapArrows) ≫ F.mapArrows = (h ≫ mapArr) ≫ b.mapArrows := fun h => by
    simp [harrows]
  have himage : (b.evaluation T).map leftHom = (b.evaluation T).map rightHom := by
    apply GroupoidScheme.EvaluationHom.ext
    show leftHom.arrow ≫ b.mapArrows = rightHom.arrow ≫ b.mapArrows
    dsimp [leftHom, rightHom]
    calc
      H₁.compose f g w ≫ mapArr ≫ b.mapArrows =
          H₁.compose f g w ≫ a.mapArrows ≫ F.mapArrows := by
        simpa [Category.assoc] using congrArg (fun q => H₁.compose f g w ≫ q) harrows
      _ = G₁.compose (f ≫ a.mapArrows) (g ≫ a.mapArrows) wA ≫ F.mapArrows := by
        simpa [Category.assoc] using congrArg (fun q => q ≫ F.mapArrows) (a.map_comp T f g w wA)
      _ = G₂.compose ((f ≫ a.mapArrows) ≫ F.mapArrows) ((g ≫ a.mapArrows) ≫ F.mapArrows)
            (mapArrows_composable F wA) :=
        F.map_comp T _ _ wA _
      _ = G₂.compose ((f ≫ mapArr) ≫ b.mapArrows) ((g ≫ mapArr) ≫ b.mapArrows)
            (mapArrows_composable b w') := by simp only [heq f, heq g]
      _ = H₂.compose (f ≫ mapArr) (g ≫ mapArr) w' ≫ b.mapArrows :=
        (b.map_comp T _ _ w' _).symm
  exact congrArg (fun q => q.arrow) ((Classical.choice (hff T)).map_injective himage)

/-- The restriction of a morphism of groupoid schemes along two compatible maps to the object
schemes, together with the identification of its map on objects and the commuting square with
the canonical morphisms from the two restrictions. -/
noncomputable def restrictHom (F : GroupoidScheme.Hom G₁ G₂) {U' : Over S}
    (g₁ : U' ⟶ G₁.objects) (g₂ : U' ⟶ G₂.objects) (hg : g₁ ≫ F.mapObjects = g₂) :
    { F' : GroupoidScheme.Hom (GroupoidScheme.restrict G₁ g₁).groupoid
        (GroupoidScheme.restrict G₂ g₂).groupoid //
      F'.mapObjects = eqToHom ((GroupoidScheme.restrict G₁ g₁).objects_eq.trans
        (GroupoidScheme.restrict G₂ g₂).objects_eq.symm) ∧
      F'.mapArrows.left ≫ (GroupoidScheme.restrict G₂ g₂).hom.mapArrows.left =
        (GroupoidScheme.restrict G₁ g₁).hom.mapArrows.left ≫ F.mapArrows.left } := by
  classical
  let A := GroupoidScheme.restrict G₁ g₁
  let B := GroupoidScheme.restrict G₂ g₂
  let mapObj := eqToHom A.objects_eq ≫ eqToHom B.objects_eq.symm
  let mapArr := eqToHom A.arrows_eq ≫ restrictionArrowsMap F g₁ g₂ hg ≫ eqToHom B.arrows_eq.symm
  have hsource : mapArr ≫ B.groupoid.source = A.groupoid.source ≫ mapObj := by
    change (eqToHom A.arrows_eq ≫ restrictionArrowsMap F g₁ g₂ hg ≫
      eqToHom B.arrows_eq.symm) ≫ B.groupoid.source =
      A.groupoid.source ≫ eqToHom A.objects_eq ≫ eqToHom B.objects_eq.symm
    rw [A.source_eq, B.source_eq]
    simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
      Category.id_comp] using
      congrArg (fun q => eqToHom A.arrows_eq ≫ q ≫ eqToHom B.objects_eq.symm)
        (restrictionArrowsMap_comp_restrictionSource F g₁ g₂ hg)
  have htarget : mapArr ≫ B.groupoid.target = A.groupoid.target ≫ mapObj := by
    change (eqToHom A.arrows_eq ≫ restrictionArrowsMap F g₁ g₂ hg ≫
      eqToHom B.arrows_eq.symm) ≫ B.groupoid.target =
      A.groupoid.target ≫ eqToHom A.objects_eq ≫ eqToHom B.objects_eq.symm
    rw [A.target_eq, B.target_eq]
    simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
      Category.id_comp] using
      congrArg (fun q => eqToHom A.arrows_eq ≫ q ≫ eqToHom B.objects_eq.symm)
        (restrictionArrowsMap_comp_restrictionTarget F g₁ g₂ hg)
  have hobjects : mapObj ≫ B.hom.mapObjects = A.hom.mapObjects ≫ F.mapObjects := by
    rw [A.mapObjects_eq, B.mapObjects_eq]
    dsimp [mapObj]
    calc
      eqToHom A.objects_eq ≫ eqToHom B.objects_eq.symm ≫ (eqToHom B.objects_eq ≫ g₂) =
          eqToHom A.objects_eq ≫ g₂ := by
            simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      _ = eqToHom A.objects_eq ≫ (g₁ ≫ F.mapObjects) := by rw [hg.symm]
      _ = (eqToHom A.objects_eq ≫ g₁) ≫ F.mapObjects := (Category.assoc _ _ _).symm
  have harrows : mapArr ≫ B.hom.mapArrows = A.hom.mapArrows ≫ F.mapArrows := by
    rw [A.mapArrows_eq, B.mapArrows_eq]
    dsimp [mapArr]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [restrictionArrowsMap_comp_restrictionArrowsToArrows]
  refine ⟨⟨mapObj, mapArr, hsource, htarget,
    comp_identity_eq_of_fullyFaithful A.hom B.hom F hsource htarget hobjects harrows
      B.evaluation_fullyFaithful,
    compose_comp_eq_of_fullyFaithful A.hom B.hom F hsource htarget harrows
      B.evaluation_fullyFaithful⟩, ?_, ?_⟩
  · dsimp [mapObj]
    simp only [eqToHom_trans]
  · simpa using congrArg Over.Hom.left harrows

/-! ### Restriction along a field extension -/

/-- Restricting a groupoid scheme whose object scheme is the spectrum of a field along a
morphism from the spectrum of another field which is universally injective does not change the
underlying topological space of the arrow scheme: the canonical morphism on arrow schemes is
surjective, universally open and universally injective. -/
theorem isHomeomorph_mapArrows_restrict (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) (k k' : Type u) [Field k] [Field k']
    (_ : G.objects.left ≅ Spec (.of k)) (_ : U'.left ≅ Spec (.of k'))
    [UniversallyInjective g.left] :
    IsHomeomorph (GroupoidScheme.restrict G g).hom.mapArrows.left.base := by
  have hobjects := ‹G.objects.left ≅ Spec (.of k)›
  have hU' := ‹U'.left ≅ Spec (.of k')›
  have : UniversallyOpen (restrictionArrowsToArrows G g).left := by
    convert universallyOpen_restrictionDiagramMorphisms G g k k' hobjects hU' (11 : Fin 12)
      using 1 <;> simp [restrictionDiagramMorphisms]
  have : Surjective (restrictionArrowsToArrows G g).left := by
    convert surjective_restrictionDiagramMorphisms G g k k' hobjects hU' (11 : Fin 12)
      using 1 <;> simp [restrictionDiagramMorphisms]
  have : UniversallyInjective (restrictionArrowsToArrows G g).left := by
    have h₁ : UniversallyInjective (pullback.snd g G.target).left :=
      overFibreProduct_snd _ _ inferInstance
    have h₂ : UniversallyInjective (pullback.fst G.source g).left :=
      overFibreProduct_fst _ _ inferInstance
    simpa only [restrictionArrowsToArrows, restrictionArrows] using
      overFibreProduct_comp _ _ (overFibreProduct_fst _ _ h₂) h₁
  have hproj : IsHomeomorph (restrictionArrowsToArrows G g).left.base :=
    ⟨(restrictionArrowsToArrows G g).left.continuous,
      (restrictionArrowsToArrows G g).left.isOpenMap,
      ⟨(restrictionArrowsToArrows G g).left.injective,
        (restrictionArrowsToArrows G g).left.surjective⟩⟩
  have hcast : IsHomeomorph (eqToHom (GroupoidScheme.restrict G g).arrows_eq).left.base := by
    simpa only [Over.eqToHom_left] using
      isHomeomorph_base_eqToHom (congrArg Over.left (GroupoidScheme.restrict G g).arrows_eq)
  have hmap : (GroupoidScheme.restrict G g).hom.mapArrows.left =
      (eqToHom (GroupoidScheme.restrict G g).arrows_eq).left ≫
        (restrictionArrowsToArrows G g).left := by
    simpa only [Over.comp_left] using
      congrArg Over.Hom.left (GroupoidScheme.restrict G g).mapArrows_eq
  rw [hmap]
  exact hproj.comp hcast

end GroupoidScheme

end AlgebraicGeometry

end
