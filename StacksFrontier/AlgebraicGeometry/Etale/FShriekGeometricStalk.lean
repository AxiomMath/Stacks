module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekBaseChangeSupport
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompactSupport
public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportStalkVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.CompGerm

/-!
# Sections over the geometric fibre and the stalk of a direct image

Let `f : X ⟶ Y` be a morphism of a big étale site, let `ȳ : Spec k ⟶ Y` be a geometric point
whose source lies in the site, and let `X_ȳ = X ×_Y Spec k` be the geometric fibre, with
projection `p : X_ȳ ⟶ X`. For an abelian sheaf `F` on the small étale site of `X`, a section of
`f_*F` over an étale neighbourhood `(V, v̄)` of `ȳ` is a section of `F` over `X_V = X ×_Y V`, and
since `X_ȳ = (X_V)_{v̄}` it can be pulled back to a global section of `p⁻¹F` over `X_ȳ`. These
pullbacks are compatible with restriction between neighbourhoods, so they define the canonical
map

`c_ȳ : (f_*F)_ȳ ⟶ H⁰(X_ȳ, F|_{X_ȳ})`

of the proof of [Stacks, Tag 0F76].

## Main definitions

* `AlgebraicGeometry.SmallEtale.geometricFibreLift` — for an étale neighbourhood `(V, v̄)` of `ȳ`,
  the morphism from the final object of the small étale site of `X_ȳ` to the base change of
  `X_V`, given by `X_ȳ ⟶ X_V`.
* `AlgebraicGeometry.SmallEtale.geometricFibreRestriction` — pullback of a section of `F` over
  `X_V` to a global section of `p⁻¹F` over `X_ȳ`.
* `AlgebraicGeometry.SmallEtale.pushforwardStalkToFibreSections` — the map `c_ȳ`.

## Main results

* `AlgebraicGeometry.SmallEtale.pushforwardStalkToFibreSections_germ` — `c_ȳ` sends the germ of
  a section to its pullback to the geometric fibre.

## References

* [Stacks Project, Tag 0F76](https://stacks.math.columbia.edu/tag/0F76)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace AlgebraicGeometry.SmallEtale

/-- Composing with the images of two composable arrows is composing with the image of their
composite, stated for an abstract functor so that it can be applied where the objects are only
definitionally the ones of the composite. -/
private lemma comp_map_comp_eq {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D) {W : D}
    {X₀ Y₀ Z₀ : C} (t : W ⟶ G.obj X₀) {a : X₀ ⟶ Y₀} {b : Y₀ ⟶ Z₀} {c : X₀ ⟶ Z₀}
    (h : a ≫ b = c) : t ≫ G.map a ≫ G.map b = t ≫ G.map c := by
  rw [← G.map_comp, h]

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) (y : GeometricPoint Y.obj)
  (hy : B.Contains y.source)

/-- A geometric point of `Y` whose source lies in the big étale site, as a morphism of the
site. -/
abbrev geometricPointHom : B.obj y.source hy ⟶ Y :=
  ObjectProperty.homMk y.hom

/-- The geometric fibre `X_ȳ = X ×_Y Spec k` of `f`, as an object of the big étale site. -/
abbrev geometricFibreObj : B.Scheme :=
  pullback f (geometricPointHom B y hy)

/-- The projection `p : X_ȳ ⟶ X` of the geometric fibre. -/
abbrev geometricFibreProj : geometricFibreObj B f y hy ⟶ X :=
  pullback.fst f (geometricPointHom B y hy)

/-- The structure morphism `X_ȳ ⟶ Spec k` of the geometric fibre. -/
abbrev geometricFibreStruct : geometricFibreObj B f y hy ⟶ B.obj y.source hy :=
  pullback.snd f (geometricPointHom B y hy)

/-- The lift of the geometric point to an étale neighbourhood, as a morphism of the site. -/
abbrev neighborhoodPointHom (N : (geometricPointFiber B Y.obj Y.property y).Elements) :
    B.obj y.source hy ⟶ N.1.obj.left :=
  ObjectProperty.homMk N.2.1

/-- The lift of the geometric point to an étale neighbourhood `(V, v̄)`, composed with `V ⟶ Y`,
is the geometric point. -/
theorem neighborhoodPointHom_comp (N : (geometricPointFiber B Y.obj Y.property y).Elements) :
    neighborhoodPointHom B y hy N ≫ N.1.obj.hom = geometricPointHom B y hy :=
  ObjectProperty.hom_ext _ N.2.2

/-- The canonical morphism `X_ȳ ⟶ X_V = V ×_Y X` for an étale neighbourhood `(V, v̄)` of `ȳ`:
its components are `X_ȳ ⟶ Spec k ⟶ V` and `p`. -/
def geometricFibreToNeighborhood (N : (geometricPointFiber B Y.obj Y.property y).Elements) :
    geometricFibreObj B f y hy ⟶ ((smallEtaleBaseChange B f).obj N.1).obj.left :=
  pullback.lift (geometricFibreStruct B f y hy ≫ neighborhoodPointHom B y hy N)
    (geometricFibreProj B f y hy)
    ((Category.assoc _ _ _).trans
      ((congrArg (geometricFibreStruct B f y hy ≫ ·) (neighborhoodPointHom_comp B y hy N)).trans
        pullback.condition.symm))

/-- The second component of `X_ȳ ⟶ X_V` is the projection `p : X_ȳ ⟶ X`. -/
@[reassoc (attr := simp)]
theorem geometricFibreToNeighborhood_snd
    (N : (geometricPointFiber B Y.obj Y.property y).Elements) :
    geometricFibreToNeighborhood B f y hy N ≫ pullback.snd N.1.obj.hom f =
      geometricFibreProj B f y hy :=
  pullback.lift_snd _ _ _

/-- The first component of `X_ȳ ⟶ X_V` is `X_ȳ ⟶ Spec k ⟶ V`. -/
@[reassoc (attr := simp)]
theorem geometricFibreToNeighborhood_fst
    (N : (geometricPointFiber B Y.obj Y.property y).Elements) :
    geometricFibreToNeighborhood B f y hy N ≫ pullback.fst N.1.obj.hom f =
      geometricFibreStruct B f y hy ≫ neighborhoodPointHom B y hy N :=
  pullback.lift_fst _ _ _

/-- For an étale neighbourhood `(V, v̄)` of `ȳ`, the morphism from the final object of the small
étale site of `X_ȳ` to the base change along `p` of `X_V`, given by `X_ȳ ⟶ X_V`. -/
def geometricFibreLift (N : (geometricPointFiber B Y.obj Y.property y).Elements) :
    final B (geometricFibreObj B f y hy).obj (geometricFibreObj B f y hy).property ⟶
      (smallEtaleBaseChange B (geometricFibreProj B f y hy)).obj
        ((smallEtaleBaseChange B f).obj N.1) :=
  baseChangeObjLift B (geometricFibreProj B f y hy) _ _
    (geometricFibreToNeighborhood B f y hy N)
    ((geometricFibreToNeighborhood_snd B f y hy N).trans (Category.id_comp _).symm)

/-- The lift `geometricFibreLift`, followed by the projection of the base change to `X_V`, is the
morphism `X_ȳ ⟶ X_V`. -/
theorem geometricFibreLift_proj (N : (geometricPointFiber B Y.obj Y.property y).Elements) :
    (geometricFibreLift B f y hy N).hom.left ≫
        baseChangeObjProjection B (geometricFibreProj B f y hy)
          ((smallEtaleBaseChange B f).obj N.1) =
      geometricFibreToNeighborhood B f y hy N :=
  baseChangeObjLift_proj _ _ _ _ _ _

/-- The lifts are compatible with morphisms of étale neighbourhoods. -/
theorem geometricFibreLift_naturality
    {N M : (geometricPointFiber B Y.obj Y.property y).Elements} (α : N ⟶ M) :
    geometricFibreLift B f y hy N ≫
        (smallEtaleBaseChange B (geometricFibreProj B f y hy)).map
          ((smallEtaleBaseChange B f).map α.1) =
      geometricFibreLift B f y hy M := by
  have hpt : neighborhoodPointHom B y hy N ≫ α.1.hom.left = neighborhoodPointHom B y hy M :=
    ObjectProperty.hom_ext _ (congrArg Subtype.val α.2)
  have hnat : geometricFibreToNeighborhood B f y hy N ≫
      ((smallEtaleBaseChange B f).map α.1).hom.left = geometricFibreToNeighborhood B f y hy M := by
    have hfst := baseChangeObjProjection_naturality B f α.1
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (geometricFibreToNeighborhood B f y hy N ≫ ·)
        hfst).trans (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ α.1.hom.left)
          (geometricFibreToNeighborhood_fst B f y hy N))).trans ((Category.assoc _ _ _).trans
            ((congrArg (geometricFibreStruct B f y hy ≫ ·) hpt).trans
              (geometricFibreToNeighborhood_fst B f y hy M).symm))))
    · exact (Category.assoc _ _ _).trans ((congrArg (geometricFibreToNeighborhood B f y hy N ≫ ·)
        (Over.w ((smallEtaleBaseChange B f).map α.1).hom)).trans
          ((geometricFibreToNeighborhood_snd B f y hy N).trans
            (geometricFibreToNeighborhood_snd B f y hy M).symm))
  apply baseChangeObj_hom_ext
  show (geometricFibreLift B f y hy N).hom.left ≫
      ((smallEtaleBaseChange B (geometricFibreProj B f y hy)).map
        ((smallEtaleBaseChange B f).map α.1)).hom.left ≫ baseChangeObjProjection B _ _ = _
  rwa [baseChangeObjProjection_naturality, ← Category.assoc, geometricFibreLift_proj,
    geometricFibreLift_proj]

section Restriction

variable (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- The inverse image `p⁻¹F` of `F` to the geometric fibre `X_ȳ`. -/
abbrev geometricFibreSheaf :
    Sheaf (SmallEtale.topology B (geometricFibreObj B f y hy).obj
      (geometricFibreObj B f y hy).property) AddCommGrpCat.{max (u + 1) v} :=
  ((smallEtaleBaseChange B (geometricFibreProj B f y hy)).sheafPullback
    AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B (geometricFibreObj B f y hy).obj
      (geometricFibreObj B f y hy).property)).obj F

/-- The group `H⁰(X_ȳ, F|_{X_ȳ})` of global sections of `p⁻¹F`, the sections over the final
object of the small étale site of `X_ȳ`. -/
abbrev geometricFibreSections : AddCommGrpCat.{max (u + 1) v} :=
  (geometricFibreSheaf B f y hy F).obj.obj
    (op (final B (geometricFibreObj B f y hy).obj (geometricFibreObj B f y hy).property))

/-- The pullback of a section of `F` over `X_V`, for an étale neighbourhood `(V, v̄)` of `ȳ`, to
a global section of `p⁻¹F` over the geometric fibre `X_ȳ = (X_V)_{v̄}`. -/
def geometricFibreRestriction (N : (geometricPointFiber B Y.obj Y.property y).Elements) :
    F.obj.obj (op ((smallEtaleBaseChange B f).obj N.1)) ⟶ geometricFibreSections B f y hy F :=
  pullbackSectionAlongHom B (geometricFibreProj B f y hy) AddCommGrpCat.{max (u + 1) v} F
    ((smallEtaleBaseChange B f).obj N.1) _ (geometricFibreLift B f y hy N)

/-- Pulling back to the geometric fibre is compatible with restriction between étale
neighbourhoods. -/
theorem geometricFibreRestriction_naturality
    {N M : (geometricPointFiber B Y.obj Y.property y).Elements} (α : N ⟶ M) :
    F.obj.map ((smallEtaleBaseChange B f).map α.1).op ≫ geometricFibreRestriction B f y hy F N =
      geometricFibreRestriction B f y hy F M := by
  ext s
  exact (pullbackSectionAlongHom_map B (geometricFibreProj B f y hy) F
      ((smallEtaleBaseChange B f).map α.1) _ (geometricFibreLift B f y hy N) s).trans
    (congrArg (fun a => pullbackSectionAlongHom B (geometricFibreProj B f y hy)
      AddCommGrpCat.{max (u + 1) v} F ((smallEtaleBaseChange B f).obj M.1) _ a s)
      (geometricFibreLift_naturality B f y hy α))

/-- The presheaf `f_*F` on the small étale site of `Y`. -/
abbrev pushforwardPresheaf : (SmallEtale B Y.obj Y.property)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v} :=
  (smallEtaleBaseChange B f).op ⋙ F.obj

/-- **The canonical map `c_ȳ : (f_*F)_ȳ ⟶ H⁰(X_ȳ, F|_{X_ȳ})` of the proof of Stacks 0F76**: a
section of `f_*F` over an étale neighbourhood `(V, v̄)` of `ȳ`, which is a section of `F` over
`X_V`, is sent to its pullback to `X_ȳ = (X_V)_{v̄}`. -/
def pushforwardStalkToFibreSections :
    etaleStalk B Y.obj Y.property y (pushforwardPresheaf B f F) ⟶
      geometricFibreSections B f y hy F :=
  colimit.desc (etaleStalkDiagram B Y.obj Y.property y (pushforwardPresheaf B f F))
    { pt := geometricFibreSections B f y hy F
      ι :=
        { app N := geometricFibreRestriction B f y hy F N.unop
          naturality _ _ α :=
            (geometricFibreRestriction_naturality B f y hy F α.unop).trans
              (Category.comp_id _).symm } }

/-- `c_ȳ` sends the germ of a section over an étale neighbourhood to its pullback to the
geometric fibre. -/
@[reassoc (attr := simp)]
theorem colimit_ι_pushforwardStalkToFibreSections
    (N : (geometricPointFiber B Y.obj Y.property y).Elements) :
    colimit.ι (etaleStalkDiagram B Y.obj Y.property y (pushforwardPresheaf B f F)) (op N) ≫
        pushforwardStalkToFibreSections B f y hy F =
      geometricFibreRestriction B f y hy F N :=
  colimit.ι_desc _ _

/-- **The support of the pullback to the geometric fibre.** A point `z` of `X_ȳ` lies in the
maximal zero open of the pullback of a section `s` of `F` over `X_V` exactly when its image in
`X_V` lies in the maximal zero open of `s`. This is Stacks 03Q1 on germs: the germ of the
pullback at a geometric point over `z` is the germ of `s` at its image. -/
theorem mem_zeroOpen_geometricFibreRestriction_iff
    (N : (geometricPointFiber B Y.obj Y.property y).Elements)
    (s : F.obj.obj (op ((smallEtaleBaseChange B f).obj N.1)))
    (z : (geometricFibreObj B f y hy).obj) :
    z ∈ (↑(zeroOpen B (geometricFibreObj B f y hy).obj (geometricFibreObj B f y hy).property
        (geometricFibreSheaf B f y hy F) _ (geometricFibreRestriction B f y hy F N s)) :
          Set ((SmallEtale.toScheme B (geometricFibreObj B f y hy).obj
            (geometricFibreObj B f y hy).property).obj (final B _ _))) ↔
      (B.inclusion.map (geometricFibreToNeighborhood B f y hy N)).base z ∈
        (↑(zeroOpen B X.obj X.property F ((smallEtaleBaseChange B f).obj N.1) s) :
          Set ((SmallEtale.toScheme B X.obj X.property).obj
            ((smallEtaleBaseChange B f).obj N.1))) := by
  let t := GeometricPoint.ofPoint (geometricFibreObj B f y hy).obj z
  have ht : t.hom.base default = z :=
    GeometricPoint.ofPoint_liesOver (geometricFibreObj B f y hy).obj z
  let w : (geometricPointFiber B X.obj X.property
      (t.map (B.inclusion.map (geometricFibreProj B f y hy)))).obj
        ((smallEtaleBaseChange B f).obj N.1) :=
    ⟨t.hom ≫ B.inclusion.map (geometricFibreToNeighborhood B f y hy N),
      (Category.assoc _ _ _).trans (comp_map_comp_eq B.inclusion t.hom
        (geometricFibreToNeighborhood_snd B f y hy N))⟩
  have hgerm := etaleGerm_pullbackSectionAlongHom B (geometricFibreProj B f y hy) t F
    (final B _ _) (finalLift B (geometricFibreObj B f y hy).obj _ t)
    ((smallEtaleBaseChange B f).obj N.1) w (geometricFibreLift B f y hy N)
    (comp_map_comp_eq B.inclusion t.hom (geometricFibreLift_proj B f y hy N)) s
  have h1 := etaleGerm_final_eq_zero_iff B (geometricFibreObj B f y hy).obj
    (geometricFibreObj B f y hy).property (geometricFibreSheaf B f y hy F) t
    (geometricFibreRestriction B f y hy F N s)
  have h2 := etaleGerm_eq_zero_iff_mem_zeroOpen B X.obj X.property
    (t.map (B.inclusion.map (geometricFibreProj B f y hy))) F
    ((smallEtaleBaseChange B f).obj N.1) w s
  have hinj : Function.Injective (etaleStalkSmallEtalePullObjIso B
      (geometricFibreProj B f y hy) t AddCommGrpCat.{max (u + 1) v} F).hom :=
    ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).1
  have hfin : (finalLift B (geometricFibreObj B f y hy).obj
      (geometricFibreObj B f y hy).property t).1.base default = z := ht
  have hw : w.1.base default =
      (B.inclusion.map (geometricFibreToNeighborhood B f y hy N)).base z := by
    show (t.hom ≫ B.inclusion.map (geometricFibreToNeighborhood B f y hy N)).base default = _
    rw [Scheme.Hom.comp_base, TopCat.comp_app, ht]
  have key : etaleGerm B (geometricFibreObj B f y hy).obj (geometricFibreObj B f y hy).property t
        (geometricFibreSheaf B f y hy F).obj _ (finalLift B _ _ t)
        (geometricFibreRestriction B f y hy F N s) = 0 ↔
      etaleGerm B X.obj X.property (t.map (B.inclusion.map (geometricFibreProj B f y hy))) F.obj
        ((smallEtaleBaseChange B f).obj N.1) w s = 0 :=
    ⟨fun h => hgerm.symm.trans ((congrArg _ h).trans (map_zero _)),
      fun h => hinj ((hgerm.trans h).trans (map_zero _).symm)⟩
  have hall := h1.symm.trans (key.trans h2)
  rwa [hfin, hw] at hall

end Restriction

/-- **The geometric fibre of `f` at `ȳ` is the fibre of `X_V ⟶ V` at the lift `v̄`.** For an
étale neighbourhood `(V, v̄)` of `ȳ` the square formed by `X_ȳ ⟶ X_V`, `X_ȳ ⟶ Spec k`,
`X_V ⟶ V` and `v̄` is cartesian, by pasting with the cartesian square defining `X_V`. -/
theorem isPullback_geometricFibreToNeighborhood
    (N : (geometricPointFiber B Y.obj Y.property y).Elements) :
    IsPullback (geometricFibreToNeighborhood B f y hy N) (geometricFibreStruct B f y hy)
      (pullback.fst N.1.obj.hom f) (neighborhoodPointHom B y hy N) := by
  refine IsPullback.of_right ?_ (geometricFibreToNeighborhood_fst B f y hy N)
    (IsPullback.of_hasPullback N.1.obj.hom f).flip
  rw [geometricFibreToNeighborhood_snd, neighborhoodPointHom_comp]
  exact IsPullback.of_hasPullback f (geometricPointHom B y hy)

section FShriek

variable (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
  [LocallyOfFiniteType (B.inclusion.map f)]

/-- The structure morphism of the geometric fibre is locally of finite type, being a base change
of `f`. -/
instance locallyOfFiniteType_geometricFibreStruct :
    LocallyOfFiniteType (B.inclusion.map (geometricFibreStruct B f y hy)) :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback f (geometricPointHom B y hy)).map B.inclusion) inferInstance

/-- The first projection of the base change of `f` along a morphism `g` is locally of finite
type. -/
private lemma locallyOfFiniteType_fst {V : B.Scheme} (g : V ⟶ Y) :
    LocallyOfFiniteType (B.inclusion.map (pullback.fst g f)) :=
  MorphismProperty.of_isPullback ((IsPullback.of_hasPullback g f).flip.map B.inclusion)
    inferInstance

/-- **The pullback to the geometric fibre of a section with proper support has compact
support.** If the support of a section `s` of `F` over `X_V` is proper over `V`, then the support
of its pullback to `X_ȳ` is proper over `Spec k`: it lies in the inverse image of the support of
`s` (Stacks 03Q1 on germs), which is proper over `Spec k` by base change of properness of a
closed subset (Stacks 0CYP) along the cartesian square
`AlgebraicGeometry.SmallEtale.isPullback_geometricFibreToNeighborhood`. -/
theorem isProperOver_geometricFibreRestriction
    (N : (geometricPointFiber B Y.obj Y.property y).Elements)
    (s : F.obj.obj (op ((smallEtaleBaseChange B f).obj N.1)))
    (hs : properSupportSections B f F N.1 s) :
    IsProperOver (B.inclusion.map (geometricFibreStruct B f y hy))
      (zeroOpen B (geometricFibreObj B f y hy).obj (geometricFibreObj B f y hy).property
        (geometricFibreSheaf B f y hy F) _ (geometricFibreRestriction B f y hy F N s)).compl := by
  have sq := (isPullback_geometricFibreToNeighborhood B f y hy N).map B.inclusion
  have hlft := locallyOfFiniteType_fst B f N.1.obj.hom
  have hZ : IsProperOver (B.inclusion.map (pullback.fst N.1.obj.hom f))
      (zeroOpen B X.obj X.property F ((smallEtaleBaseChange B f).obj N.1) s).compl := hs
  have hbc := @isProperOver_preimage_baseChange _ _ _ _ _ _ _ _ sq hlft _ hZ
  refine isProperOver_of_le _ (fun z hz => ?_) hbc
  intro hz'
  exact hz ((mem_zeroOpen_geometricFibreRestriction_iff B f y hy F N s z).mpr hz')

/-- The stalk at `ȳ` of the inclusion `f_!F ⟶ f_*F`. -/
def fShriekStalkToPushforwardStalk :
    etaleStalk B Y.obj Y.property y (properSupportSheaf B f F).obj ⟶
      etaleStalk B Y.obj Y.property y (pushforwardPresheaf B f F) :=
  colim.map (Functor.whiskerLeft
    (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property y)).op
    (properSupportSheafInclusion B f F).hom)

/-- On the colimit injection at an étale neighbourhood `(V, v̄)`, the stalk of `f_!F ⟶ f_*F` is
the inclusion of sections over `V` followed by the colimit injection. -/
@[reassoc (attr := simp)]
theorem colimit_ι_fShriekStalkToPushforwardStalk
    (N : (geometricPointFiber B Y.obj Y.property y).Elements) :
    colimit.ι (etaleStalkDiagram B Y.obj Y.property y (properSupportSheaf B f F).obj)
        (op N) ≫ fShriekStalkToPushforwardStalk B f y F =
      (properSupportSheafInclusion B f F).hom.app (op N.1) ≫
        colimit.ι (etaleStalkDiagram B Y.obj Y.property y (pushforwardPresheaf B f F)) (op N) :=
  ι_colimMap _ _

/-- The group `H⁰_c(X_ȳ, F|_{X_ȳ})` of compactly supported sections of `p⁻¹F` on the geometric
fibre, over the algebraically closed field of the geometric point (Stacks 0F72). -/
abbrev geometricFibreCompactSections : AddSubgroup (geometricFibreSections B f y hy F) :=
  compactlySupportedSections y.residueField (geometricFibreObj B f y hy).obj
    (B.inclusion.map (geometricFibreStruct B f y hy)) B (geometricFibreObj B f y hy).property
    (geometricFibreSheaf B f y hy F)

/-- `c_ȳ` composed with the stalk of the inclusion `f_!F ⟶ f_*F`, on a germ. -/
theorem fShriekStalk_comp_pushforwardStalkToFibreSections_germ
    (N : (geometricPointFiber B Y.obj Y.property y).Elements)
    (a : (properSupportSheaf B f F).obj.obj (op N.1)) :
    (fShriekStalkToPushforwardStalk B f y F ≫ pushforwardStalkToFibreSections B f y hy F)
        (etaleGerm B Y.obj Y.property y _ N.1 N.2 a) =
      geometricFibreRestriction B f y hy F N
        ((properSupportSheafInclusion B f F).hom.app (op N.1) a) := by
  have hm : colimit.ι (etaleStalkDiagram B Y.obj Y.property y
        (properSupportSheaf B f F).obj) (op N) ≫
        (fShriekStalkToPushforwardStalk B f y F ≫ pushforwardStalkToFibreSections B f y hy F) =
      (properSupportSheafInclusion B f F).hom.app (op N.1) ≫
        geometricFibreRestriction B f y hy F N :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ pushforwardStalkToFibreSections B f y hy F)
        (colimit_ι_fShriekStalkToPushforwardStalk B f y F N)).trans
        ((Category.assoc _ _ _).trans
          (congrArg ((properSupportSheafInclusion B f F).hom.app (op N.1) ≫ ·)
            (colimit_ι_pushforwardStalkToFibreSections B f y hy F N))))
  have h := ConcreteCategory.congr_hom hm a
  simp only [ConcreteCategory.comp_apply] at h
  exact h

/-- `c_ȳ` carries the image of the stalk of `f_!F` into the compactly supported sections. -/
theorem fShriekStalk_mem_geometricFibreCompactSections
    (g : ↑(etaleStalk B Y.obj Y.property y (properSupportSheaf B f F).obj)) :
    (fShriekStalkToPushforwardStalk B f y F ≫ pushforwardStalkToFibreSections B f y hy F) g ∈
      geometricFibreCompactSections B f y hy F := by
  obtain ⟨W, q, a, rfl⟩ := exists_etaleGerm_eq B Y.obj Y.property y _ g
  have hp : properSupportSections B f F W ((properSupportSheafInclusion B f F).hom.app (op W) a) :=
    a.2
  exact (congrArg (· ∈ geometricFibreCompactSections B f y hy F)
    (fShriekStalk_comp_pushforwardStalkToFibreSections_germ B f y hy F ⟨W, q⟩ a)).mpr
    (isProperOver_geometricFibreRestriction B f y hy F ⟨W, q⟩ _ hp)

/-- **The map `(f_!F)_ȳ ⟶ H⁰_c(X_ȳ, F|_{X_ȳ})` of Stacks 0F76**: the restriction of
`c_ȳ : (f_*F)_ȳ ⟶ H⁰(X_ȳ, F|_{X_ȳ})` to the stalk of the subsheaf `f_!F`, which lands in the
compactly supported sections. -/
def fShriekStalkToCompactSections :
    ↑(etaleStalk B Y.obj Y.property y (properSupportSheaf B f F).obj) →+
      geometricFibreCompactSections B f y hy F :=
  AddMonoidHom.codRestrict
    (fShriekStalkToPushforwardStalk B f y F ≫ pushforwardStalkToFibreSections B f y hy F).hom
    _ (fShriekStalk_mem_geometricFibreCompactSections B f y hy F)

/-- **The map of Stacks 0F76 on germs**: the germ at `ȳ` of a section of `f_!F` over an étale
neighbourhood `(V, v̄)`, which is a section of `F` over `X_V` with support proper over `V`, is
sent to its pullback to the geometric fibre `X_ȳ = (X_V)_{v̄}`. -/
theorem fShriekStalkToCompactSections_germ
    (N : (geometricPointFiber B Y.obj Y.property y).Elements)
    (a : (properSupportSheaf B f F).obj.obj (op N.1)) :
    (fShriekStalkToCompactSections B f y hy F
        (etaleGerm B Y.obj Y.property y _ N.1 N.2 a) : geometricFibreSections B f y hy F) =
      geometricFibreRestriction B f y hy F N
        ((properSupportSheafInclusion B f F).hom.app (op N.1) a) :=
  fShriekStalk_comp_pushforwardStalkToFibreSections_germ B f y hy F N a

/-- The image of a closed subset proper over the base is closed. -/
private theorem isClosed_image_of_isProperOver {T S : Scheme.{u}} (g : T ⟶ S)
    [LocallyOfFiniteType g] (Z : Closeds T) (hZ : IsProperOver g Z) :
    IsClosed (g.base '' (Z : Set T)) := by
  have : IsProper ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ g) := hZ
  have h := ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ g).isClosedMap.isClosed_range
  rwa [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal] at h

/-- **Injectivity in Stacks 0F76.** The map `(f_!F)_ȳ ⟶ H⁰_c(X_ȳ, F|_{X_ȳ})` is injective. A
germ at `ȳ` of a section `s` of `F` over `X_V` with support `Z` proper over `V`, whose pullback to
`X_ȳ` vanishes, has `Z` disjoint from the image of `X_ȳ` (Stacks 03Q1 on germs); since `Z` is
proper over `V` its image there is closed, and it misses the point of `V` under `ȳ`, because
`X_ȳ` is the fibre of `X_V ⟶ V` over that point. So `s` vanishes over the complement of that
image, which is an étale neighbourhood of `ȳ`. -/
theorem fShriekStalkToCompactSections_injective :
    Function.Injective (fShriekStalkToCompactSections B f y hy F) := by
  rw [injective_iff_map_eq_zero]
  intro g hg
  obtain ⟨W, q, a, rfl⟩ := exists_etaleGerm_eq B Y.obj Y.property y _ g
  let N : (geometricPointFiber B Y.obj Y.property y).Elements := ⟨W, q⟩
  let s : F.obj.obj (op ((smallEtaleBaseChange B f).obj W)) :=
    (properSupportSheafInclusion B f F).hom.app (op W) a
  have h0 : geometricFibreRestriction B f y hy F N s = 0 := by
    have h := congrArg Subtype.val hg
    rwa [fShriekStalkToCompactSections_germ B f y hy F N a] at h
  have hP : ∀ z, (B.inclusion.map (geometricFibreToNeighborhood B f y hy N)).base z ∈
      (↑(zeroOpen B X.obj X.property F ((smallEtaleBaseChange B f).obj W) s) :
        Set ((SmallEtale.toScheme B X.obj X.property).obj ((smallEtaleBaseChange B f).obj W))) := by
    intro z
    refine (mem_zeroOpen_geometricFibreRestriction_iff B f y hy F N s z).mp ?_
    rw [h0, zeroOpen_zero]
    trivial
  have hlft := locallyOfFiniteType_fst B f W.obj.hom
  let Z := (zeroOpen B X.obj X.property F ((smallEtaleBaseChange B f).obj W) s).compl
  have hZ : IsProperOver (B.inclusion.map (pullback.fst W.obj.hom f)) Z := a.2
  let C := (B.inclusion.map (pullback.fst W.obj.hom f)).base ''
    (↑Z : Set ((SmallEtale.toScheme B X.obj X.property).obj ((smallEtaleBaseChange B f).obj W)))
  have hC : IsClosed C := @isClosed_image_of_isProperOver _ _ _ hlft Z hZ
  have hv : q.1.base default ∉ C := by
    rintro ⟨x, hxZ, hx⟩
    have sq := (isPullback_geometricFibreToNeighborhood B f y hy N).map B.inclusion
    obtain ⟨z₀, hz₀, -⟩ := Scheme.Pullback.exists_preimage_pullback x (default : y.source) hx
    have hz : (B.inclusion.map (geometricFibreToNeighborhood B f y hy N)).base
        (sq.isoPullback.inv.base z₀) = x :=
      ((Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun m => m.base z₀)
        sq.isoPullback_inv_fst)).trans hz₀
    exact hxZ (hz ▸ hP _)
  let U : ((SmallEtale.toScheme B Y.obj Y.property).obj W).Opens := ⟨Cᶜ, hC.isOpen_compl⟩
  rw [← etaleGerm_openObjectLift B Y.obj Y.property y _ W q U hv]
  have hres : (properSupportSheaf B f F).obj.map (openObjectι B Y.obj Y.property W U).op a = 0 := by
    apply Subtype.ext
    show F.obj.map ((smallEtaleBaseChange B f).map (openObjectι B Y.obj Y.property W U)).op s = 0
    rw [map_eq_zero_iff_range_subset_zeroOpen, range_baseChangeObjMap, openObjectι_range]
    intro x hx
    by_contra hxZ
    exact hx ⟨x, hxZ, rfl⟩
  rw [hres, etaleGerm_zero]

end FShriek

end AlgebraicGeometry.SmallEtale
