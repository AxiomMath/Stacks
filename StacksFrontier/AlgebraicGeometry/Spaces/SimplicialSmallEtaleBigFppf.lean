module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Functor.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleAugmentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleBigFppfInclusion
public import StacksFrontier.CategoryTheory.Sites.Simplicial.OverSimplicialObjectTotalSite

/-!
# From the spaces-étale site of a simplicial algebraic space to its big fppf total site

Let `T` be a big fppf site of algebraic spaces over `S` and `U` a simplicial object of it. The
functor `u : U_{spaces,étale} ⥤ (Spaces/U)_{fppf,total}`, `V/U_n ↦ V/U_n`, of the proof of
Stacks 0DH5 is continuous: in each degree it is the inclusion of `(U_n)_{spaces,étale}` into the
big fppf site `(Spaces/U_n)_{fppf}` followed by the inclusion of that degree into the total site.

## Main definitions

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.toBigFppfTotal`: the functor `u`.

## Main results

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.degreeInclusionCompToBigFppfTotalIso`: in
  degree `n`, `u` is the inclusion of `(U_n)_{spaces,étale}` followed by the component
  inclusion.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.toBigFppfTotal_isContinuous`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CategoryTheory.Limits

universe u

namespace CategoryTheory.SimplicialOver

variable {C : Type*} [Category C] (V : SimplicialObject C)

/-- Two morphisms of the Grothendieck construction of `n ↦ C/V_n` agree as soon as their simplex
maps and the underlying morphisms of `C` of their fibres agree. -/
theorem overMapHom_ext_simplicialSmallEtaleBigFppf {A A' : Grothendieck (V ⋙ Over.mapFunctor C)}
    {f g : A ⟶ A'}
    (hb : Grothendieck.Hom.base f = Grothendieck.Hom.base g)
    (hf : (Grothendieck.Hom.fiber f).left = (Grothendieck.Hom.fiber g).left) : f = g := by
  change Grothendieck.Hom A A' at f g
  cases f with
  | mk b φ =>
    cases g with
    | mk b' ψ =>
      dsimp only at hb
      subst hb
      exact congrArg (Grothendieck.Hom.mk b) (Over.OverMorphism.ext hf)

/-- The underlying morphism of the fibre of an identity is an identity. -/
theorem overMap_id_fiber_left_simplicialSmallEtaleBigFppf
    (A : Grothendieck (V ⋙ Over.mapFunctor C)) :
    (Grothendieck.Hom.fiber (𝟙 A)).left = 𝟙 A.fiber.left := by
  rw [Grothendieck.id_fiber]
  exact Comma.eqToHom_left (H := _)

/-- The underlying morphism of the fibre of a composite is the composite of the underlying
morphisms. -/
theorem overMap_comp_fiber_left_simplicialSmallEtaleBigFppf
    {A A' A'' : Grothendieck (V ⋙ Over.mapFunctor C)} (f : A ⟶ A')
    (g : A' ⟶ A'') : (Grothendieck.Hom.fiber (f ≫ g)).left =
      (Grothendieck.Hom.fiber f).left ≫ (Grothendieck.Hom.fiber g).left := by
  rw [Grothendieck.comp_fiber]
  exact (congrArg (· ≫ (Grothendieck.Hom.fiber f).left ≫ (Grothendieck.Hom.fiber g).left)
    ((Comma.eqToHom_left
      (X := ((V ⋙ Over.mapFunctor C).map (f.base ≫ g.base)).toFunctor.obj A.fiber)
      (Y := ((V ⋙ Over.mapFunctor C).map g.base).toFunctor.obj
        (((V ⋙ Over.mapFunctor C).map f.base).toFunctor.obj A.fiber)) (H := _)).trans
      (eqToHom_refl _ _))).trans (Category.id_comp _)

/-- The inclusion of a degree does not change the underlying morphism of a fibre. -/
theorem overMap_ι_map_fiber_left_simplicialSmallEtaleBigFppf (c : SimplexCategoryᵒᵖ)
    {X Y : Over (V.obj c)} (φ : X ⟶ Y) :
    (Grothendieck.Hom.fiber ((Grothendieck.ι (V ⋙ Over.mapFunctor C) c).map φ)).left =
      φ.left :=
  (congrArg (· ≫ φ.left)
    ((Comma.eqToHom_left (X := ((V ⋙ Over.mapFunctor C).map (𝟙 c)).toFunctor.obj X)
      (Y := X) (H := _)).trans (eqToHom_refl _ _))).trans (Category.id_comp _)

/-- Equal morphisms have equal underlying morphisms of fibres. -/
theorem overMap_fiber_left_congr_simplicialSmallEtaleBigFppf
    {A A' : Grothendieck (V ⋙ Over.mapFunctor C)} {f g : A ⟶ A'}
    (h : f = g) : (Grothendieck.Hom.fiber f).left = (Grothendieck.Hom.fiber g).left := by
  subst h
  rfl

end CategoryTheory.SimplicialOver

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} (U : SimplicialObject T.Spaces)

/-- **The functor `u : U_{spaces,étale} ⥤ (Spaces/U)_{fppf,total}`** of the proof of Stacks 0DH5:
an algebraic space `V` étale over `U_n` goes to `V/U_n` in simplicial degree `n`, and a morphism
`(φ, f)` over `U(φ)` to the morphism `(φ, f)` of the total category. -/
def toBigFppfTotal :
    SimplicialSpacesEtaleSite T.schemeSite S T.scheme_mem U ⥤
      Grothendieck (SimplicialOver.slices U) where
  obj V := ⟨op V.degree, V.obj.1⟩
  map g := ⟨g.base.op, Over.homMk g.hom g.w⟩
  map_id V := SimplicialOver.overMapHom_ext_simplicialSmallEtaleBigFppf U rfl
    (SimplicialOver.overMap_id_fiber_left_simplicialSmallEtaleBigFppf U ⟨op V.degree, V.obj.1⟩).symm
  map_comp {X Y Z} f g := SimplicialOver.overMapHom_ext_simplicialSmallEtaleBigFppf U rfl
    (SimplicialOver.overMap_comp_fiber_left_simplicialSmallEtaleBigFppf U
      (A := ⟨op X.degree, X.obj.1⟩) (A' := ⟨op Y.degree, Y.obj.1⟩) (A'' := ⟨op Z.degree, Z.obj.1⟩)
      ⟨f.base.op, Over.homMk f.hom f.w⟩ ⟨g.base.op, Over.homMk g.hom g.w⟩).symm

/-- The base of the image under `u` of a morphism `g` is the map `g.base` of simplices. -/
theorem toBigFppfTotal_map_base {V W : SimplicialSpacesEtaleSite T.schemeSite S T.scheme_mem U}
    (g : V ⟶ W) : Grothendieck.Hom.base ((toBigFppfTotal U).map g) = g.base.op := rfl

/-- The underlying morphism of algebraic spaces of `u` applied to `g` is `g.hom`. -/
theorem toBigFppfTotal_map_fiber_left
    {V W : SimplicialSpacesEtaleSite T.schemeSite S T.scheme_mem U} (g : V ⟶ W) :
    (Grothendieck.Hom.fiber ((toBigFppfTotal U).map g)).left = g.hom := rfl

/-- The inclusion `(Spaces/U_n)_{fppf} ⥤ (Spaces/U)_{fppf,total}` of the component of degree
`n`. -/
def slicesι (n : SimplexCategory) : Over (U.obj (op n)) ⥤ Grothendieck (SimplicialOver.slices U) :=
  Grothendieck.ι (SimplicialOver.slices U) (op n)

/-- In degree `n`, the functor `u` is the inclusion of `(U_n)_{spaces,étale}` into
`(Spaces/U_n)_{fppf}` followed by the inclusion of the component of degree `n`; the
components of the isomorphism are identities. -/
def degreeInclusionCompToBigFppfTotalIso (n : SimplexCategory) :
    degreeInclusion U n ⋙ toBigFppfTotal U ≅
      SpacesEtale.inclusion T.schemeSite S T.scheme_mem (U.obj (op n)) ⋙ slicesι U n :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {V W} g ↦
    (Category.comp_id _).trans ((SimplicialOver.overMapHom_ext_simplicialSmallEtaleBigFppf U
      (f := (degreeInclusion U n ⋙ toBigFppfTotal U).map g)
      (g := (SpacesEtale.inclusion T.schemeSite S T.scheme_mem (U.obj (op n)) ⋙
        slicesι U n).map g) rfl
      (SimplicialOver.overMap_ι_map_fiber_left_simplicialSmallEtaleBigFppf U (op n) (X := V.1)
        (Y := W.1) g.hom).symm).trans
        (Category.id_comp _).symm))

/-- The component inclusion of degree `n` is continuous for the big fppf topology of `U_n`. -/
theorem slicesι_isContinuous (n : SimplexCategory) :
    (slicesι U n).IsContinuous
      (BigFppfSpaceOver.topology T (U.obj (op n))) (SimplicialOver.totalTopology T.topology U) := by
  have h := SimplicialSiteSituation.componentFunctor_isContinuous
    (SimplicialOver.situation T.topology U) n
  rwa [SimplicialOver.componentTopology_eq] at h

/-- The component inclusion of degree `n` is cocontinuous for the big fppf topology of `U_n`. -/
theorem slicesι_isCocontinuous (n : SimplexCategory) :
    (slicesι U n).IsCocontinuous
      (BigFppfSpaceOver.topology T (U.obj (op n))) (SimplicialOver.totalTopology T.topology U) := by
  have h := SimplicialSiteSituation.componentFunctor_isCocontinuous
    (SimplicialOver.situation T.topology U) n
  rwa [SimplicialOver.componentTopology_eq] at h

/-- **The functor `u` is continuous**: a covering of `U_{spaces,étale}` is an étale covering in a
single degree `n`, which `u` carries to an fppf covering in degree `n` of the total site. -/
instance toBigFppfTotal_isContinuous :
    (toBigFppfTotal U).IsContinuous (topology U) (SimplicialOver.totalTopology T.topology U) where
  op_comp_isSheaf_of_types G := by
    rw [Presieve.isSheaf_coverage]
    rintro V R ⟨E, hE, rfl⟩
    refine Presieve.isSheafFor_ofArrows_map_of_isSheafFor_simplicialSmallEtaleSite
      (degreeInclusion U V.degree) _ E.X E.f ?_
    have := slicesι_isContinuous U V.degree
    have : (SpacesEtale.inclusion T.schemeSite S T.scheme_mem (U.obj (op V.degree)) ⋙
        slicesι U V.degree).IsContinuous
        (SpacesEtale.topology T.schemeSite S T.scheme_mem _)
        (SimplicialOver.totalTopology T.topology U) :=
      Functor.isContinuous_comp _ _ _ (BigFppfSpaceOver.topology T (U.obj (op V.degree))) _
    have : (degreeInclusion U V.degree ⋙ toBigFppfTotal U).IsContinuous
        (SpacesEtale.topology T.schemeSite S T.scheme_mem _)
        (SimplicialOver.totalTopology T.topology U) :=
      Functor.isContinuous_of_iso (degreeInclusionCompToBigFppfTotalIso U V.degree).symm _ _
    have hG := ((isSheaf_iff_isSheaf_of_type _ _).1 ((Functor.sheafPushforwardContinuous
      (degreeInclusion U V.degree ⋙ toBigFppfTotal U) (Type (u + 1))
      (SpacesEtale.topology T.schemeSite S T.scheme_mem _)
      (SimplicialOver.totalTopology T.topology U)).obj G).2) _
      (Precoverage.generate_mem_toGrothendieck
        ((SpacesEtale.mem_precoverage_iff T.schemeSite S T.scheme_mem _).2 ⟨E, rfl, hE⟩))
    exact (Presieve.isSheafFor_iff_generate _).2 hG

/-! ### Representable flatness of `u` -/

/-- On morphisms of a single degree, `u` is the component inclusion of the inclusion of the
spaces-étale site. -/
theorem toBigFppfTotal_map_degreeInclusion {n : SimplexCategory}
    {V W : SpacesEtale T.schemeSite S T.scheme_mem (U.obj (op n))} (f : V ⟶ W) :
    (toBigFppfTotal U).map ((degreeInclusion U n).map f) =
      (slicesι U n).map
        ((SpacesEtale.inclusion T.schemeSite S T.scheme_mem (U.obj (op n))).map f) :=
  SimplicialOver.overMapHom_ext_simplicialSmallEtaleBigFppf U
    (f := (toBigFppfTotal U).map ((degreeInclusion U n).map f))
    (g := (slicesι U n).map
      ((SpacesEtale.inclusion T.schemeSite S T.scheme_mem (U.obj (op n))).map f)) rfl
    (SimplicialOver.overMap_ι_map_fiber_left_simplicialSmallEtaleBigFppf U (op n) (X := V.1)
      (Y := W.1) f.hom).symm

/-- The inclusion of the spaces-étale site of `U_n` into `(Spaces/U_n)_{fppf}` preserves finite
limits, hence is representably flat. -/
instance inclusion_representablyFlat (n : SimplexCategory) :
    RepresentablyFlat (SpacesEtale.inclusion T.schemeSite S T.scheme_mem (U.obj (op n))) := by
  have : HasFiniteLimits (SpacesEtale T.schemeSite S T.scheme_mem (U.obj (op n))) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : PreservesFiniteLimits
      (SpacesEtale.inclusion T.schemeSite S T.scheme_mem (U.obj (op n))) :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks _
  exact flat_of_preservesFiniteLimits _

namespace ToBigFppfTotal

variable {m : SimplexCategory} (W : Over (U.obj (op m)))

/-- The arrows from `W/U_m` to objects of degree `m` of `U_{spaces,étale}`, over the identity of
`[m]`, as arrows to `u`. -/
def structuredArrowInclusion :
    StructuredArrow W (SpacesEtale.inclusion T.schemeSite S T.scheme_mem (U.obj (op m))) ⥤
      StructuredArrow ((slicesι U m).obj W) (toBigFppfTotal U) where
  obj c := StructuredArrow.mk (Y := (degreeInclusion U m).obj c.right)
    ((slicesι U m).map c.hom)
  map {c _} x := StructuredArrow.homMk ((degreeInclusion U m).map x.right)
    ((congrArg ((slicesι U m).map c.hom ≫ ·) (toBigFppfTotal_map_degreeInclusion U x.right)).trans
      (((slicesι U m).map_comp _ _).symm.trans (congrArg (slicesι U m).map (StructuredArrow.w x))))
  map_id _ := StructuredArrow.hom_ext _ _ ((degreeInclusion U m).map_id _)
  map_comp _ _ := StructuredArrow.hom_ext _ _ ((degreeInclusion U m).map_comp _ _)

variable {U W}

/-- The arrow `W/U_m ⟶ V ×_{U_k} U_m` through which an arrow `W/U_m ⟶ V/U_k` over `φ` factors. -/
def reducedHom (d : StructuredArrow ((slicesι U m).obj W) (toBigFppfTotal U)) :
    W ⟶ (SpacesEtale.inclusion T.schemeSite S T.scheme_mem (U.obj (op m))).obj
      (cartesianObj d.right d.hom.base.unop) :=
  Over.homMk (pullback.lift (Grothendieck.Hom.fiber d.hom).left W.hom
    (Over.w (Grothendieck.Hom.fiber d.hom))) (pullback.lift_snd _ _ _)

/-- The reduction of an arrow to degree `m`. -/
abbrev reducedArrow (d : StructuredArrow ((slicesι U m).obj W) (toBigFppfTotal U)) :
    StructuredArrow W (SpacesEtale.inclusion T.schemeSite S T.scheme_mem (U.obj (op m))) :=
  StructuredArrow.mk (reducedHom d)

/-- The arrow `d` factors as `reducedHom d` followed by the image under `u` of the projection
`V ×_{U_k} U_m ⟶ V`. -/
theorem reducedHom_w (d : StructuredArrow ((slicesι U m).obj W) (toBigFppfTotal U)) :
    (slicesι U m).map (reducedHom d) ≫
      (toBigFppfTotal U).map (cartesianFst d.right d.hom.base.unop) = d.hom :=
  SimplicialOver.overMapHom_ext_simplicialSmallEtaleBigFppf U
    (f := (slicesι U m).map (reducedHom d) ≫
      (toBigFppfTotal U).map (cartesianFst d.right d.hom.base.unop)) (g := d.hom)
    (Category.id_comp _)
    ((SimplicialOver.overMap_comp_fiber_left_simplicialSmallEtaleBigFppf U
      (A := (slicesι U m).obj W) (A' := ⟨op m, (cartesianObj d.right d.hom.base.unop).1⟩)
      (A'' := ⟨op d.right.degree, d.right.obj.1⟩)
      ((slicesι U m).map (reducedHom d))
      ((toBigFppfTotal U).map (cartesianFst d.right d.hom.base.unop))).trans
      ((congrArg (· ≫ pullback.fst _ _)
        (SimplicialOver.overMap_ι_map_fiber_left_simplicialSmallEtaleBigFppf U (op m)
          (X := W) (Y := (cartesianObj d.right d.hom.base.unop).1) (reducedHom d))).trans
        (pullback.lift_fst _ _ _)))

/-- The comparison of an arrow with its reduction to degree `m`. -/
def reducedArrowHom (d : StructuredArrow ((slicesι U m).obj W) (toBigFppfTotal U)) :
    (structuredArrowInclusion U W).obj (reducedArrow d) ⟶ d :=
  StructuredArrow.homMk (cartesianFst d.right d.hom.base.unop) (reducedHom_w d)

/-- Every arrow from an arrow of degree `m` over the identity factors through the reduction. -/
theorem exists_eq_map_comp_reducedArrowHom
    (d : StructuredArrow ((slicesι U m).obj W) (toBigFppfTotal U))
    (c : StructuredArrow W (SpacesEtale.inclusion T.schemeSite S T.scheme_mem (U.obj (op m))))
    (s : (structuredArrowInclusion U W).obj c ⟶ d) :
    ∃ x : c ⟶ reducedArrow d, s = (structuredArrowInclusion U W).map x ≫ reducedArrowHom d := by
  have sw : (slicesι U m).map c.hom ≫ (toBigFppfTotal U).map s.right = d.hom :=
    StructuredArrow.w s
  have hk : s.right.base = d.hom.base.unop :=
    congrArg Quiver.Hom.unop ((Category.id_comp _).symm.trans (congrArg Grothendieck.Hom.base sw))
  have sw₁ : c.hom.left ≫ s.right.hom = (Grothendieck.Hom.fiber d.hom).left :=
    ((congrArg (· ≫ s.right.hom)
      (SimplicialOver.overMap_ι_map_fiber_left_simplicialSmallEtaleBigFppf U (op m)
        (X := W) (Y := c.right.1) c.hom)).symm.trans
      (SimplicialOver.overMap_comp_fiber_left_simplicialSmallEtaleBigFppf U
        (A := (slicesι U m).obj W) (A' := ⟨op m, c.right.1⟩)
        (A'' := ⟨op d.right.degree, d.right.obj.1⟩)
        ((slicesι U m).map c.hom) ((toBigFppfTotal U).map s.right)).symm).trans
      (SimplicialOver.overMap_fiber_left_congr_simplicialSmallEtaleBigFppf U sw)
  have l₁ : (cartesianLift s.right hk).hom.left ≫
      pullback.fst d.right.obj.1.hom (U.map d.hom.base.unop.op) = s.right.hom :=
    pullback.lift_fst _ _ _
  have l₂ : (cartesianLift s.right hk).hom.left ≫
      pullback.snd d.right.obj.1.hom (U.map d.hom.base.unop.op) = c.right.1.hom :=
    pullback.lift_snd _ _ _
  refine ⟨StructuredArrow.homMk (cartesianLift s.right hk) (Over.OverMorphism.ext ?_), ?_⟩
  · change c.hom.left ≫ (cartesianLift s.right hk).hom.left = (reducedHom d).left
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((whisker_eq _ l₁).trans
        (sw₁.trans (pullback.lift_fst _ _ _).symm))
    · exact (Category.assoc _ _ _).trans ((whisker_eq _ l₂).trans
        ((Over.w c.hom).trans (pullback.lift_snd _ _ _).symm))
  · exact StructuredArrow.hom_ext _ _ (cartesianLift_fac s.right hk).symm

variable (U W) in
/-- The arrows of degree `m` over the identity form an initial subcategory. -/
instance structuredArrowInclusion_initial : (structuredArrowInclusion U W).Initial := by
  have : IsCofiltered
      (StructuredArrow W (SpacesEtale.inclusion T.schemeSite S T.scheme_mem (U.obj (op m)))) :=
    RepresentablyFlat.cofiltered _
  refine Functor.initial_of_exists_of_isCofiltered _
    (fun d ↦ ⟨reducedArrow d, ⟨reducedArrowHom d⟩⟩) (fun {d c} s s' ↦ ?_)
  obtain ⟨x, rfl⟩ := exists_eq_map_comp_reducedArrowHom d c s
  obtain ⟨x', rfl⟩ := exists_eq_map_comp_reducedArrowHom d c s'
  obtain ⟨c', t, ht⟩ := IsCofilteredOrEmpty.cone_maps x x'
  refine ⟨c', t, ?_⟩
  simp only [← Category.assoc, ← Functor.map_comp, ht]

end ToBigFppfTotal

/-- The fibre of an object `A` of `(Spaces/U)_{fppf,total}`, as an object of `Spaces/U_m` for
`m` the degree of `A`; the object `A` is its image under the component inclusion. -/
def fiberOver (A : Grothendieck (SimplicialOver.slices U)) : Over (U.obj (op A.base.unop)) :=
  A.fiber

/-- **The functor `u` of Stacks 0DH5 is representably flat**: the arrows from `W/U_m` to `u`
contain the arrows of degree `m` over the identity of `[m]` as an initial subcategory, and these
are the arrows to the inclusion of `(U_m)_{spaces,étale}` into `(Spaces/U_m)_{fppf}`, which
preserves finite limits. -/
instance toBigFppfTotal_representablyFlat : RepresentablyFlat (toBigFppfTotal U) where
  cofiltered A := by
    change IsCofiltered (StructuredArrow ((slicesι U A.base.unop).obj (fiberOver U A))
      (toBigFppfTotal U))
    have : IsCofiltered (StructuredArrow (fiberOver U A)
        (SpacesEtale.inclusion T.schemeSite S T.scheme_mem (U.obj (op A.base.unop)))) :=
      RepresentablyFlat.cofiltered _
    exact IsCofiltered.of_initial (ToBigFppfTotal.structuredArrowInclusion U (fiberOver U A))

/-- The functor `u : U_{spaces,étale} ⥤ (Spaces/U)_{fppf,total}` defines a morphism of sites
`(Spaces/U)_{fppf,total} → U_{spaces,étale}`: its inverse image on sheaves of sets is exact. -/
theorem toBigFppfTotal_isMorphismOfSites :
    IsMorphismOfSites.{u + 1} (toBigFppfTotal U) (topology U)
      (SimplicialOver.totalTopology T.topology U) := by
  refine ⟨Functor.sheafPullbackConstruction.sheafPullback (toBigFppfTotal U) (Type (u + 1))
    (topology U) (SimplicialOver.totalTopology T.topology U),
    ⟨Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (toBigFppfTotal U) (Type (u + 1)) (topology U)
      (SimplicialOver.totalTopology T.topology U)⟩, ?_⟩
  let : PreservesFiniteLimits ((toBigFppfTotal U).op.lan :
      ((SimplicialSpacesEtaleSite T.schemeSite S T.scheme_mem U)ᵒᵖ ⥤ Type (u + 1)) ⥤
        (Grothendieck (SimplicialOver.slices U))ᵒᵖ ⥤ Type (u + 1)) :=
    Stacks.Topology.lan_preservesFiniteLimits_of_flat (E := Type (u + 1)) (FE := TypeCat.Fun)
      (toBigFppfTotal U) (fun _ ↦ inferInstance)
  exact inferInstance

/-- **The morphism of topoi `h : Sh((Spaces/U)_{fppf,total}) ⟶ Sh(U_{spaces,étale})`** of the
proof of Stacks 0DH5, given by the morphism of sites of the functor `u`, `V/U_n ↦ V/U_n`. -/
noncomputable def bigFppfTotalToposHom :
    MorphismOfTopoi (Sheaf (SimplicialOver.totalTopology T.topology U) (Type (u + 1)))
      (Sheaf (topology U) (Type (u + 1))) :=
  (toBigFppfTotal_isMorphismOfSites U).morphismOfTopoi

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
