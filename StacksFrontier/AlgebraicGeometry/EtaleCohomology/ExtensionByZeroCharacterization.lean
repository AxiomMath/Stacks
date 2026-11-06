module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkIsomorphismCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import Mathlib.CategoryTheory.Filtered.Final
public import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero along an open immersion is characterised by its stalks

Let `j : U ⟶ X` be an open immersion, viewed as an object of the small étale site of `X`, and
let `F` be an abelian sheaf on the small étale site of `U`. The extension by zero `j_!F` has
zero stalks at the geometric points of `X` outside `U`, and it is the only abelian sheaf on `X`
with that property restricting to `F`: if `G` restricts to `F` and has zero stalks outside `U`,
the map `j_!F ⟶ G` adjoint to the given identification of `j^{-1}G` with `F` is an
isomorphism.

The uniqueness assertion is proved on stalks. The adjoint map restricts to an isomorphism on
`U`, because the unit of the extension-by-zero adjunction is an isomorphism along an open
immersion; so its stalks at the geometric points of `X` lifting to `U` are isomorphisms, the
stalk of a restriction being the stalk at the image point. At a geometric point outside `U`
both stalks vanish. Stalks at geometric points detect isomorphisms, which finishes the proof.

## Main definitions

* `AlgebraicGeometry.liftNeighborhoods` — the functor from the étale neighbourhoods of a
  geometric point of `U` to those of its image in `X`, given by composition with `j`.

## Main results

* `AlgebraicGeometry.nonempty_geometricPointLifts_of_mem_range` — a geometric point of `X`
  whose image lies in `U` lifts to `U`.
* `AlgebraicGeometry.liftNeighborhoods_initial` — that functor is initial, for `j` an open
  immersion.
* `AlgebraicGeometry.postcomposeStalkIso` — the stalk at a geometric point of `U` of a
  restricted presheaf is the stalk of the presheaf at the image point.
* `AlgebraicGeometry.abelianExtensionByZeroAdjunction_hom_isIso_of_stalk_isZero` — the
  uniqueness characterisation of extension by zero.

## Implementation notes

Initiality of `AlgebraicGeometry.liftNeighborhoods` is where the open immersion is used twice:
composition with `j` is fully faithful because the structure morphism of `U` is then a
monomorphism, and an étale neighbourhood of a geometric point of `X` lifting to `U` is refined
by its base change to `U`, which carries the lift. Cofilteredness of the target category of
neighbourhoods is the general fact for a geometric point.

The uniqueness statement compares the extension by zero with a sheaf `G` given by its own
properties — a restriction isomorphic to `F` and vanishing stalks off `U` — through the
canonical adjoint of that isomorphism, so neither side is the definition of the other.

## References

* [Stacks Project, Tag 0F70](https://stacks.math.columbia.edu/tag/0F70)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)

/-- The image of a geometric point of `X` whose image lies in the open subscheme `U` is
contained in the image of the open immersion: the source of a geometric point has a single
point. -/
public theorem range_subset_of_mem_range (x : GeometricPoint X)
    (hx : x.hom default ∈ Set.range (B.inclusion.map U.obj.hom).base) :
    Set.range x.hom.base ⊆ Set.range (B.inclusion.map U.obj.hom).base := by
  obtain ⟨y, hy⟩ := hx
  rintro z ⟨a, rfl⟩
  rw [Subsingleton.elim a default]
  exact ⟨y, hy⟩

/-- The canonical lift to `U` of a geometric point of `X` whose image lies in the open
subscheme `U`, given by the lifting property of the open immersion. -/
public def geometricPointLiftOfMemRange [IsOpenImmersion (B.inclusion.map U.obj.hom)]
    (x : GeometricPoint X)
    (hx : x.hom default ∈ Set.range (B.inclusion.map U.obj.hom).base) :
    geometricPointLifts B X hX U x :=
  ⟨IsOpenImmersion.lift (B.inclusion.map U.obj.hom) x.hom
      (range_subset_of_mem_range B X hX U x hx),
    IsOpenImmersion.lift_fac _ _ _⟩

/-- A geometric point of `X` whose image lies in the open subscheme `U` lifts to `U`. -/
public theorem nonempty_geometricPointLifts_of_mem_range
    [IsOpenImmersion (B.inclusion.map U.obj.hom)] (x : GeometricPoint X)
    (hx : x.hom default ∈ Set.range (B.inclusion.map U.obj.hom).base) :
    Nonempty (geometricPointLifts B X hX U x) :=
  ⟨geometricPointLiftOfMemRange B X hX U x hx⟩

/-- Composition with `U ⟶ X` carries an étale neighbourhood of a geometric point `p` of `U` to
an étale neighbourhood of the image of `p` in `X`, keeping the lift. -/
public def liftNeighborhoods (p : GeometricPoint U.obj.left.1) :
    (geometricPointFiber B U.obj.left.1 U.obj.left.property p).Elements ⥤
      (geometricPointFiber B X hX (p.map (B.inclusion.map U.obj.hom))).Elements where
  obj W := Functor.elementsMk _ ((smallEtalePostcompose B X hX U).obj W.obj) ⟨W.val.1, by
    change W.val.1 ≫ B.inclusion.map ((smallEtalePostcompose B X hX U).obj W.obj).obj.hom =
      p.hom ≫ B.inclusion.map U.obj.hom
    calc
      _ = W.val.1 ≫ (B.inclusion.map W.obj.obj.hom ≫ B.inclusion.map U.obj.hom) := by
        simp [smallEtalePostcompose]
      _ = (W.val.1 ≫ B.inclusion.map W.obj.obj.hom) ≫ B.inclusion.map U.obj.hom :=
        (Category.assoc _ _ _).symm
      _ = p.hom ≫ B.inclusion.map U.obj.hom := by rw [W.val.2]⟩
  map {W W'} f := Functor.Elements.homMk ((smallEtalePostcompose B X hX U).map f.hom) (by
    apply Subtype.ext
    change W.val.1 ≫ (SmallEtale.toScheme B X hX).map
      ((smallEtalePostcompose B X hX U).map f.hom) = W'.val.1
    exact congrArg Subtype.val f.map_val)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor on neighbourhoods is composition with `U ⟶ X` on underlying objects. -/
public theorem liftNeighborhoods_comp_π (p : GeometricPoint U.obj.left.1) :
    liftNeighborhoods B X hX U p ⋙
        Functor.Elements.π (geometricPointFiber B X hX
          (p.map (B.inclusion.map U.obj.hom))) =
      Functor.Elements.π (geometricPointFiber B U.obj.left.1 U.obj.left.property p) ⋙
        smallEtalePostcompose B X hX U :=
  rfl

private instance liftNeighborhoods_faithful (p : GeometricPoint U.obj.left.1) :
    (liftNeighborhoods B X hX U p).Faithful where
  map_injective {_ _} _ _ h :=
    Functor.Elements.hom_ext ((smallEtalePostcompose B X hX U).map_injective
      (congrArg Functor.Elements.Hom.hom h))

private instance liftNeighborhoods_full [IsOpenImmersion (B.inclusion.map U.obj.hom)]
    (p : GeometricPoint U.obj.left.1) : (liftNeighborhoods B X hX U p).Full where
  map_surjective {W W'} f := by
    have : Mono U.obj.hom := B.inclusion.mono_of_mono_map inferInstance
    obtain ⟨g, hg⟩ := (smallEtalePostcompose B X hX U).map_surjective f.hom
    refine ⟨Functor.Elements.homMk g (Subtype.ext ?_), Functor.Elements.hom_ext hg⟩
    have h := congrArg Subtype.val f.map_val
    rwa [← hg] at h

/-- An étale neighbourhood of a geometric point of `X` which lifts to the open subscheme `U` is
refined by its base change to `U`: the lift and the neighbourhood's own lift agree over `X`, so
they define a lift to the fibre product, which is étale over `U`. -/
private theorem exists_liftNeighborhoods_refinement
    [IsOpenImmersion (B.inclusion.map U.obj.hom)] (p : GeometricPoint U.obj.left.1)
    (V : (geometricPointFiber B X hX (p.map (B.inclusion.map U.obj.hom))).Elements) :
    ∃ W, Nonempty ((liftNeighborhoods B X hX U p).obj W ⟶ V) := by
  let _ := hasPullbacks_bigEtaleSite B
  let _ := preservesPullbacks_bigEtaleSiteInclusion B
  let W := (smallEtaleBaseChange B U.obj.hom).obj V.obj
  let pb := (IsPullback.of_hasPullback V.obj.obj.hom U.obj.hom).map B.inclusion
  have compat : V.val.1 ≫ B.inclusion.map V.obj.obj.hom =
      p.hom ≫ B.inclusion.map U.obj.hom := V.val.2
  let P : (geometricPointFiber B U.obj.left.1 U.obj.left.property p).Elements :=
    Functor.elementsMk _ W ⟨pb.lift V.val.1 p.hom compat, pb.lift_snd V.val.1 p.hom compat⟩
  exact ⟨P, ⟨Functor.Elements.homMk (ObjectProperty.homMk (Over.homMk
    (pullback.fst V.obj.obj.hom U.obj.hom) pullback.condition))
    (Subtype.ext (pb.lift_fst V.val.1 p.hom compat))⟩⟩

/-- Composition with an open immersion is an initial functor on étale neighbourhoods: it is
fully faithful, the neighbourhoods of a geometric point are cofiltered, and every neighbourhood
of the image point is refined by one coming from `U`. -/
public theorem liftNeighborhoods_initial [IsOpenImmersion (B.inclusion.map U.obj.hom)]
    (p : GeometricPoint U.obj.left.1) : (liftNeighborhoods B X hX U p).Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _
    (exists_liftNeighborhoods_refinement B X hX U p)

/-- The stalk at a geometric point `p` of `U` of the restriction of a presheaf on the small
étale site of `X` is the stalk of that presheaf at the image of `p`: restriction is
precomposition with composition by `U ⟶ X`, and that functor is initial on neighbourhoods, so
the two colimits agree. -/
public def postcomposeStalkIso [IsOpenImmersion (B.inclusion.map U.obj.hom)]
    (p : GeometricPoint U.obj.left.1) :
    (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
          (smallEtalePostcompose B X hX U).op ⋙
        etaleStalkPresheafFunctor B U.obj.left.1 U.obj.left.property p AddCommGrpCat.{u + 1} ≅
      etaleStalkPresheafFunctor B X hX (p.map (B.inclusion.map U.obj.hom))
        AddCommGrpCat.{u + 1} :=
  haveI := liftNeighborhoods_initial B X hX U p
  Functor.isoWhiskerLeft
    ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
      (Functor.Elements.π (geometricPointFiber B X hX
        (p.map (B.inclusion.map U.obj.hom)))).op)
    (Functor.Final.colimIso (liftNeighborhoods B X hX U p).op)

/-- The stalk of a restriction, as a natural isomorphism of functors on abelian sheaves. -/
public def abelianRestrictionStalkIso [IsOpenImmersion (B.inclusion.map U.obj.hom)]
    (p : GeometricPoint U.obj.left.1) :
    abelianRestriction B X hX U ⋙
        sheafToPresheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
          AddCommGrpCat.{u + 1} ⋙
        etaleStalkPresheafFunctor B U.obj.left.1 U.obj.left.property p AddCommGrpCat.{u + 1} ≅
      sheafToPresheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1} ⋙
        etaleStalkPresheafFunctor B X hX (p.map (B.inclusion.map U.obj.hom))
          AddCommGrpCat.{u + 1} :=
  Functor.isoWhiskerLeft
    (sheafToPresheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})
    (postcomposeStalkIso B X hX U p)

/-- The map adjoint to an identification of the restriction of `G` with `F` restricts to an
isomorphism: composing it with the unit of the extension-by-zero adjunction returns that
identification, and the unit is an isomorphism along an open immersion. -/
public theorem abelianRestriction_map_homEquiv_symm_isIso
    [IsOpenImmersion (B.inclusion.map U.obj.hom)]
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1})
    (G : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})
    (e : F ≅ (abelianRestriction B X hX U).obj G) :
    IsIso ((abelianRestriction B X hX U).map
      (((abelianExtensionByZeroAdjunction B X hX U).homEquiv F G).symm e.hom)) := by
  have := abelianExtensionByZeroAdjunction_unit_isIso B X hX U F
  have hfactor : (abelianExtensionByZeroAdjunction B X hX U).unit.app F ≫
      (abelianRestriction B X hX U).map
        (((abelianExtensionByZeroAdjunction B X hX U).homEquiv F G).symm e.hom) = e.hom :=
    (Adjunction.homEquiv_apply_eq (abelianExtensionByZeroAdjunction B X hX U) _ e.hom).2 rfl
  have : IsIso e.hom := inferInstance
  exact IsIso.of_isIso_fac_left hfactor

/-- **Stacks 0F70.** An abelian étale sheaf on `X` whose restriction to the open subscheme `U`
is identified with `F` and whose stalks at the geometric points of `X` outside `U` vanish is
canonically the extension by zero of `F`: the map from `j_!F` adjoint to the given
identification is an isomorphism. Together with the vanishing of the stalks of `j_!F` outside
`U` this is the uniqueness assertion of the source. -/
@[stacks 0F70 "extension_by_zero_characterization: uniqueness"]
public theorem abelianExtensionByZeroAdjunction_hom_isIso_of_stalk_isZero
    [IsOpenImmersion (B.inclusion.map U.obj.hom)]
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1})
    (G : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})
    (e : F ≅ (abelianRestriction B X hX U).obj G)
    (hG : ∀ x : GeometricPoint X,
      x.hom default ∉ Set.range (B.inclusion.map U.obj.hom).base →
        IsZero (etaleStalk B X hX x G.obj)) :
    IsIso (((abelianExtensionByZeroAdjunction B X hX U).homEquiv F G).symm e.hom) := by
  set α := ((abelianExtensionByZeroAdjunction B X hX U).homEquiv F G).symm e.hom
  have hrestr : IsIso ((abelianRestriction B X hX U).map α) :=
    abelianRestriction_map_homEquiv_symm_isIso B X hX U F G e
  apply isIso_of_isIso_etaleStalkMap.{u, u + 1} B X hX
  intro s
  by_cases hs : s.hom default ∈ Set.range (B.inclusion.map U.obj.hom).base
  · set q := geometricPointLiftOfMemRange B X hX U s hs
    set p := geometricPointOfLift B X hX U s q
    have hps : p.map (B.inclusion.map U.obj.hom) = s := by
      cases s with
      | mk k f =>
        dsimp [p, geometricPointOfLift, GeometricPoint.map]
        congr 1
        exact q.2
    have hsource : IsIso ((abelianRestrictionStalkIso B X hX U p).hom.app
        ((abelianExtensionByZero B X hX U).obj F)) := inferInstance
    have hrestr' : IsIso ((abelianRestriction B X hX U ⋙
        sheafToPresheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
          AddCommGrpCat.{u + 1} ⋙
        etaleStalkPresheafFunctor B U.obj.left.1 U.obj.left.property p
          AddCommGrpCat.{u + 1}).map α) := by
      have := hrestr
      exact Functor.map_isIso (etaleStalkPresheafFunctor B U.obj.left.1 U.obj.left.property p
        AddCommGrpCat.{u + 1}) ((sheafToPresheaf _ _).map _)
    have htarget' : IsIso ((etaleStalkPresheafFunctor B X hX
        (p.map (B.inclusion.map U.obj.hom)) AddCommGrpCat.{u + 1}).map α.hom) :=
      IsIso.of_isIso_fac_left ((abelianRestrictionStalkIso B X hX U p).hom.naturality α).symm
    rwa [hps] at htarget'
  · exact ⟨⟨0, (abelianExtensionByZero_stalk_isZero_of_not_mem_range B X hX U s F hs).eq_of_src
      _ _, (hG s hs).eq_of_src _ _⟩⟩

end AlgebraicGeometry

end
