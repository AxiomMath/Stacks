module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Functor.Flat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingImageAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiSite
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.MorphismsGeneral

/-!
# The morphism of small étale topoi of a morphism of simplicial algebraic spaces

A morphism `h : X ⟶ Y` of simplicial algebraic spaces induces, by base change in each
simplicial degree, a continuous functor `Y_{spaces,étale} ⥤ X_{spaces,étale}`
(`AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.pullbackFunctor`). This file shows that it
defines a morphism of sites, hence a morphism of topoi
`h_étale : Sh(X_{spaces,étale}) ⟶ Sh(Y_{spaces,étale})`, and with the structure map `h♯` a
morphism of ringed topoi (Stacks 0DE7).

The total sites have no final object, so exactness of the inverse image is proved through
representable flatness: the category of arrows from an object `W/X_n` to the base change functor
has an initial subcategory, the arrows into objects of degree `n` over the identity of `[n]`,
which is the category of arrows of the degree-`n` base change functor, and the latter preserves
finite limits.

## Main definitions

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.degreePullback`: base change in degree `n`.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.ringedTopos`: the ringed topos
  `(Sh(X_{spaces,étale}), 𝒪_X)`.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.ringedToposHom`: **the morphism of ringed
  topoi `h_étale` of a morphism of simplicial algebraic spaces.**

## Main results

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.pullbackFunctor_representablyFlat` and
  `.pullbackFunctor_isMorphismOfSites`.
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : SimplicialObject (AlgebraicSpaces B S hS)} (h : X ⟶ Y)

/-! ### Base change in a single degree -/

/-- Base change along `h_n : X_n ⟶ Y_n`, as the restriction of `pullbackFunctor h` to the
objects of degree `n` and the morphisms over the identity of `[n]`. -/
noncomputable def degreePullback (n : SimplexCategory) :
    SpacesEtale B S hS (Y.obj (op n)) ⥤ SpacesEtale B S hS (X.obj (op n)) where
  obj V := ((pullbackFunctor h).obj ((degreeInclusion Y n).obj V)).obj
  map f := ObjectProperty.homMk (Over.homMk
    ((pullbackFunctor h).map ((degreeInclusion Y n).map f)).hom
    (((pullbackFunctor h).map ((degreeInclusion Y n).map f)).w.trans (by
      change pullback.snd _ _ ≫ X.map (𝟙 n).op = pullback.snd _ _
      rw [op_id, X.map_id, Category.comp_id])))
  map_id V := ObjectProperty.hom_ext _ (Over.OverMorphism.ext
    (congrArg Hom.hom ((degreeInclusion Y n ⋙ pullbackFunctor h).map_id V)))
  map_comp f g := ObjectProperty.hom_ext _ (Over.OverMorphism.ext
    (congrArg Hom.hom ((degreeInclusion Y n ⋙ pullbackFunctor h).map_comp f g)))

/-- Base change commutes with the inclusion of a degree, on the nose. -/
theorem degreeInclusion_comp_pullbackFunctor (n : SimplexCategory) :
    degreeInclusion Y n ⋙ pullbackFunctor h = degreePullback h n ⋙ degreeInclusion X n := rfl

/-- The degree-`n` base change of a morphism commutes with the projections to `X_n`. -/
private theorem degreePullback_map_hom_left_snd {n : SimplexCategory}
    {V W : SpacesEtale B S hS (Y.obj (op n))} (f : V ⟶ W) :
    ((degreePullback h n).map f).hom.left ≫ pullback.snd W.1.hom (h.app (op n)) =
      pullback.snd V.1.hom (h.app (op n)) := by
  have hX : X.map ((degreeInclusion Y n).map f).base.op = 𝟙 _ := X.map_id (op n)
  exact (pullback.lift_snd _ _ _).trans ((whisker_eq _ hX).trans (Category.comp_id _))

/-- On morphisms, the degree-`n` base change is the base change of the spaces-étale sites. -/
theorem degreePullback_map_hom_left {n : SimplexCategory} {V W : SpacesEtale B S hS (Y.obj (op n))}
    (f : V ⟶ W) : ((degreePullback h n).map f).hom.left =
      ((spacesBaseChange B S hS (h.app (op n))).functor.map f).hom.left := by
  apply pullback.hom_ext
  · exact (pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm
  · exact (degreePullback_map_hom_left_snd h f).trans (pullback.lift_snd _ _ _).symm

/-- The degree-`n` base change is the base change of the spaces-étale sites along `h_n`. -/
noncomputable def spacesBaseChangeIso (n : SimplexCategory) :
    (spacesBaseChange B S hS (h.app (op n))).functor ≅ degreePullback h n :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {_ _} f ↦ ObjectProperty.hom_ext _
    (Over.OverMorphism.ext ((congrArg (fun k ↦ k.hom.left)
      (Category.comp_id ((spacesBaseChange B S hS (h.app (op n))).functor.map f))).trans
      ((degreePullback_map_hom_left h f).symm.trans (congrArg (fun k ↦ k.hom.left)
        (Category.id_comp ((degreePullback h n).map f)).symm)))))

/-- Base change in a single degree preserves finite limits, hence is representably flat. -/
instance degreePullback_representablyFlat (n : SimplexCategory) :
    RepresentablyFlat (degreePullback h n) := by
  let F := (spacesBaseChange B S hS (h.app (op n))).functor
  have hT := SpacesEtale.isTerminal_idObj B S hS (Y.obj (op n))
  have := hT.hasTerminal
  have := Functor.preservesLimitsOfShape_pempty_of_isTerminal F hT
    (isTerminal_spacesBaseChange_idObj B S hS (h.app (op n)))
  have : HasFiniteLimits (SpacesEtale B S hS (Y.obj (op n))) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : PreservesFiniteLimits F := preservesFiniteLimits_of_preservesTerminal_and_pullbacks F
  have : PreservesFiniteLimits (degreePullback h n) :=
    preservesFiniteLimits_of_natIso (spacesBaseChangeIso h n)
  exact flat_of_preservesFiniteLimits _

/-! ### Cartesian lifts in the spaces-étale site of `Y` -/

/-- The base change `V ×_{Y_m} Y_n` of an object `V/Y_m` along `Y(φ) : Y_n ⟶ Y_m`. -/
noncomputable def cartesianObj {n : SimplexCategory} (V : SimplicialSpacesEtaleSite B S hS Y)
    (φ : V.degree ⟶ n) : SpacesEtale B S hS (Y.obj (op n)) :=
  ⟨Over.mk (pullback.snd V.obj.1.hom (Y.map φ.op)),
    isEtale_of_isPullback B S hS _ _ _ _ (IsPullback.of_hasPullback _ _) V.obj.2⟩

/-- The projection `V ×_{Y_m} Y_n ⟶ V`, a morphism over `φ`. -/
noncomputable def cartesianFst {n : SimplexCategory} (V : SimplicialSpacesEtaleSite B S hS Y)
    (φ : V.degree ⟶ n) : (degreeInclusion Y n).obj (cartesianObj V φ) ⟶ V :=
  ⟨φ, pullback.fst _ _, pullback.condition⟩

/-- A morphism over `φ` from an object of degree `n` factors through `V ×_{Y_m} Y_n`. -/
noncomputable def cartesianLift {n : SimplexCategory} {V : SimplicialSpacesEtaleSite B S hS Y}
    {φ : V.degree ⟶ n} {A : SpacesEtale B S hS (Y.obj (op n))}
    (k : (degreeInclusion Y n).obj A ⟶ V) (hk : k.base = φ) : A ⟶ cartesianObj V φ :=
  ObjectProperty.homMk (Over.homMk (pullback.lift k.hom A.1.hom
    (k.w.trans (congrArg (fun t : V.degree ⟶ n ↦ A.1.hom ≫ Y.map t.op) hk)))
    (pullback.lift_snd _ _ _))

/-- The lift `cartesianLift k hk` composed with the projection `cartesianFst V φ` is `k`. -/
theorem cartesianLift_fac {n : SimplexCategory} {V : SimplicialSpacesEtaleSite B S hS Y}
    {φ : V.degree ⟶ n} {A : SpacesEtale B S hS (Y.obj (op n))}
    (k : (degreeInclusion Y n).obj A ⟶ V) (hk : k.base = φ) :
    (degreeInclusion Y n).map (cartesianLift k hk) ≫ cartesianFst V φ = k :=
  Hom.ext ((Category.comp_id φ).trans hk.symm) (pullback.lift_fst _ _ _)

/-! ### Representable flatness of base change -/

variable (W : SimplicialSpacesEtaleSite B S hS X)

/-- The arrows from `W/X_n` to the base change of objects of degree `n`, over the identity of
`[n]`, as arrows to `pullbackFunctor h`. -/
noncomputable def structuredArrowInclusion :
    StructuredArrow W.obj (degreePullback h W.degree) ⥤
      StructuredArrow W (pullbackFunctor h) where
  obj c := StructuredArrow.mk (Y := (degreeInclusion Y W.degree).obj c.right)
    ((degreeInclusion X W.degree).map c.hom)
  map {_ _} x := StructuredArrow.homMk ((degreeInclusion Y W.degree).map x.right)
    (((degreeInclusion X W.degree).map_comp _ _).symm.trans
      (congrArg (degreeInclusion X W.degree).map (StructuredArrow.w x)))
  map_id _ := StructuredArrow.hom_ext _ _ ((degreeInclusion Y W.degree).map_id _)
  map_comp _ _ := StructuredArrow.hom_ext _ _ ((degreeInclusion Y W.degree).map_comp _ _)

variable {W}

/-- For an arrow `d : W ⟶ V ×_{Y_m} X_m` over `φ`, the composite `W ⟶ V ⟶ Y_m` agrees with
`W ⟶ X_n ⟶ Y_n ⟶ Y_m`. -/
theorem reducedHom_aux (d : StructuredArrow W (pullbackFunctor h)) :
    (d.hom.hom ≫ pullback.fst d.right.obj.1.hom (h.app (op d.right.degree))) ≫
        d.right.obj.1.hom =
      (W.obj.1.hom ≫ h.app (op W.degree)) ≫ Y.map d.hom.base.op :=
  (Category.assoc _ _ _).trans ((whisker_eq _ pullback.condition).trans
    ((Category.assoc _ _ _).symm.trans ((eq_whisker d.hom.w _).trans
      ((Category.assoc _ _ _).trans ((whisker_eq _ (h.naturality d.hom.base.op)).trans
        (Category.assoc _ _ _).symm)))))

/-- The arrow `W/X_n ⟶ (V ×_{Y_m} Y_n) ×_{Y_n} X_n` through which an arrow `W ⟶ V ×_{Y_m} X_m`
over `φ` factors. -/
noncomputable def reducedHom (d : StructuredArrow W (pullbackFunctor h)) :
    W.obj ⟶ (degreePullback h W.degree).obj (cartesianObj d.right d.hom.base) :=
  ObjectProperty.homMk (Over.homMk (pullback.lift (pullback.lift (d.hom.hom ≫ pullback.fst _ _)
      (W.obj.1.hom ≫ h.app (op W.degree)) (reducedHom_aux h d))
    W.obj.1.hom (pullback.lift_snd _ _ _)) (pullback.lift_snd _ _ _))

/-- The reduction of an arrow to degree `n`. -/
noncomputable abbrev reducedArrow (d : StructuredArrow W (pullbackFunctor h)) :
    StructuredArrow W.obj (degreePullback h W.degree) :=
  StructuredArrow.mk (reducedHom h d)

/-- The arrow `reducedHom h d` followed by the base change of the projection
`V ×_{Y_m} Y_n ⟶ V` is the arrow `d`. -/
theorem reducedHom_w (d : StructuredArrow W (pullbackFunctor h)) :
    (degreeInclusion X W.degree).map (reducedHom h d) ≫
      (pullbackFunctor h).map (cartesianFst d.right d.hom.base) = d.hom :=
  Hom.ext (Category.comp_id _) (pullback.hom_ext
    ((Category.assoc _ _ _).trans ((whisker_eq _ (pullback.lift_fst _ _ _)).trans
      ((Category.assoc _ _ _).symm.trans ((eq_whisker (pullback.lift_fst _ _ _) _).trans
        (pullback.lift_fst _ _ _)))))
    ((Category.assoc _ _ _).trans ((whisker_eq _ (pullback.lift_snd _ _ _)).trans
      ((Category.assoc _ _ _).symm.trans ((eq_whisker (pullback.lift_snd _ _ _) _).trans
        d.hom.w.symm)))))

/-- The comparison of an arrow with its reduction to degree `n`. -/
noncomputable def reducedArrowHom (d : StructuredArrow W (pullbackFunctor h)) :
    (structuredArrowInclusion h W).obj (reducedArrow h d) ⟶ d :=
  StructuredArrow.homMk (cartesianFst d.right d.hom.base) (reducedHom_w h d)

/-- The first component of `comp_degreePullback_map_cartesianLift`. -/
theorem comp_degreePullback_map_cartesianLift_fst (d : StructuredArrow W (pullbackFunctor h))
    (c : StructuredArrow W.obj (degreePullback h W.degree))
    (s : (structuredArrowInclusion h W).obj c ⟶ d) (hk : s.right.base = d.hom.base) :
    (c.hom.hom.left ≫ ((degreePullback h W.degree).map (cartesianLift s.right hk)).hom.left) ≫
      pullback.fst (cartesianObj d.right d.hom.base).1.hom (h.app (op W.degree)) =
        (reducedHom h d).hom.left ≫
          pullback.fst (cartesianObj d.right d.hom.base).1.hom (h.app (op W.degree)) := by
  have m₁ : ((pullbackFunctor h).map s.right).hom ≫
      pullback.fst d.right.obj.1.hom (h.app (op d.right.degree)) =
        pullback.fst c.right.1.hom (h.app (op W.degree)) ≫ s.right.hom := pullback.lift_fst _ _ _
  have sw₁ : c.hom.hom.left ≫ pullback.fst c.right.1.hom (h.app (op W.degree)) ≫ s.right.hom =
      d.hom.hom ≫ pullback.fst d.right.obj.1.hom (h.app (op d.right.degree)) :=
    (whisker_eq _ m₁).symm.trans
      ((Category.assoc _ _ _).symm.trans (eq_whisker (congrArg Hom.hom (StructuredArrow.w s)) _))
  have l₁ : (cartesianLift s.right hk).hom.left ≫
      pullback.fst d.right.obj.1.hom (Y.map d.hom.base.op) = s.right.hom := pullback.lift_fst _ _ _
  have l₂ : (cartesianLift s.right hk).hom.left ≫
      pullback.snd d.right.obj.1.hom (Y.map d.hom.base.op) = c.right.1.hom :=
    pullback.lift_snd _ _ _
  have p₁ : ((degreePullback h W.degree).map (cartesianLift s.right hk)).hom.left ≫
      pullback.fst (cartesianObj d.right d.hom.base).1.hom (h.app (op W.degree)) =
        pullback.fst c.right.1.hom (h.app (op W.degree)) ≫ (cartesianLift s.right hk).hom.left :=
    pullback.lift_fst _ _ _
  have r₁₁ : ((reducedHom h d).hom.left ≫
      pullback.fst (cartesianObj d.right d.hom.base).1.hom (h.app (op W.degree))) ≫
        pullback.fst d.right.obj.1.hom (Y.map d.hom.base.op) =
          d.hom.hom ≫ pullback.fst d.right.obj.1.hom (h.app (op d.right.degree)) :=
    (eq_whisker (pullback.lift_fst _ _ _) _).trans (pullback.lift_fst _ _ _)
  have r₁₂ : ((reducedHom h d).hom.left ≫
      pullback.fst (cartesianObj d.right d.hom.base).1.hom (h.app (op W.degree))) ≫
        pullback.snd d.right.obj.1.hom (Y.map d.hom.base.op) =
          W.obj.1.hom ≫ h.app (op W.degree) :=
    (eq_whisker (pullback.lift_fst _ _ _) _).trans (pullback.lift_snd _ _ _)
  have hA : c.hom.hom.left ≫ pullback.snd c.right.1.hom (h.app (op W.degree)) = W.obj.1.hom :=
    Over.w c.hom.hom
  have pc : pullback.fst c.right.1.hom (h.app (op W.degree)) ≫ c.right.1.hom =
      pullback.snd c.right.1.hom (h.app (op W.degree)) ≫ h.app (op W.degree) :=
    pullback.condition
  apply pullback.hom_ext
  · exact (eq_whisker (Category.assoc _ _ _) _).trans ((eq_whisker (whisker_eq _ p₁) _).trans
      ((Category.assoc _ _ _).trans ((whisker_eq _ (Category.assoc _ _ _)).trans
        ((whisker_eq _ (whisker_eq _ l₁)).trans (sw₁.trans r₁₁.symm)))))
  · exact (eq_whisker (Category.assoc _ _ _) _).trans ((eq_whisker (whisker_eq _ p₁) _).trans
      ((Category.assoc _ _ _).trans ((whisker_eq _ (Category.assoc _ _ _)).trans
        ((whisker_eq _ (whisker_eq _ l₂)).trans ((whisker_eq _ pc).trans
          ((Category.assoc _ _ _).symm.trans ((eq_whisker hA _).trans r₁₂.symm)))))))

/-- The cartesian lift of an arrow from an arrow of degree `n` is compatible with the
reduction. -/
theorem comp_degreePullback_map_cartesianLift (d : StructuredArrow W (pullbackFunctor h))
    (c : StructuredArrow W.obj (degreePullback h W.degree))
    (s : (structuredArrowInclusion h W).obj c ⟶ d) (hk : s.right.base = d.hom.base) :
    c.hom ≫ (degreePullback h W.degree).map (cartesianLift s.right hk) = reducedHom h d := by
  have r₂ : (reducedHom h d).hom.left ≫
      pullback.snd (cartesianObj d.right d.hom.base).1.hom (h.app (op W.degree)) = W.obj.1.hom :=
    pullback.lift_snd _ _ _
  have hA : c.hom.hom.left ≫ pullback.snd c.right.1.hom (h.app (op W.degree)) = W.obj.1.hom :=
    Over.w c.hom.hom
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)
  show c.hom.hom.left ≫ ((degreePullback h W.degree).map (cartesianLift s.right hk)).hom.left =
    (reducedHom h d).hom.left
  apply pullback.hom_ext
  · exact comp_degreePullback_map_cartesianLift_fst h d c s hk
  · exact (Category.assoc _ _ _).trans ((whisker_eq _ (degreePullback_map_hom_left_snd h _)).trans
      (hA.trans r₂.symm))

/-- Every arrow from an arrow of degree `n` over the identity factors through the reduction. -/
theorem exists_eq_map_comp_reducedArrowHom (d : StructuredArrow W (pullbackFunctor h))
    (c : StructuredArrow W.obj (degreePullback h W.degree))
    (s : (structuredArrowInclusion h W).obj c ⟶ d) :
    ∃ x : c ⟶ reducedArrow h d, s = (structuredArrowInclusion h W).map x ≫ reducedArrowHom h d := by
  have sw : (degreeInclusion X W.degree).map c.hom ≫ (pullbackFunctor h).map s.right = d.hom :=
    StructuredArrow.w s
  have hk : s.right.base = d.hom.base :=
    (Category.comp_id _).symm.trans (congrArg Hom.base sw)
  exact ⟨StructuredArrow.homMk (cartesianLift s.right hk)
    (comp_degreePullback_map_cartesianLift h d c s hk),
    StructuredArrow.hom_ext _ _ (cartesianLift_fac s.right hk).symm⟩

variable (W) in
/-- The arrows of degree `n` over the identity form an initial subcategory. -/
instance structuredArrowInclusion_initial : (structuredArrowInclusion h W).Initial := by
  have : IsCofiltered (StructuredArrow W.obj (degreePullback h W.degree)) :=
    RepresentablyFlat.cofiltered _
  refine Functor.initial_of_exists_of_isCofiltered _
    (fun d ↦ ⟨reducedArrow h d, ⟨reducedArrowHom h d⟩⟩) (fun {d c} s s' ↦ ?_)
  obtain ⟨x, rfl⟩ := exists_eq_map_comp_reducedArrowHom h d c s
  obtain ⟨x', rfl⟩ := exists_eq_map_comp_reducedArrowHom h d c s'
  obtain ⟨c', t, ht⟩ := IsCofilteredOrEmpty.cone_maps x x'
  refine ⟨c', t, ?_⟩
  simp only [← Category.assoc, ← Functor.map_comp, ht]

/-- **Stacks 0DE7.** Base change along a morphism of simplicial algebraic spaces is
representably flat. -/
instance pullbackFunctor_representablyFlat : RepresentablyFlat (pullbackFunctor h) where
  cofiltered W :=
    haveI : IsCofiltered (StructuredArrow W.obj (degreePullback h W.degree)) :=
      RepresentablyFlat.cofiltered _
    IsCofiltered.of_initial (structuredArrowInclusion h W)

/-- **Stacks 0DE7.** Base change along a morphism `h : X ⟶ Y` of simplicial algebraic spaces
defines a morphism of sites `X_{spaces,étale} → Y_{spaces,étale}`: its inverse image on sheaves
of sets is exact. -/
theorem pullbackFunctor_isMorphismOfSites :
    IsMorphismOfSites.{u + 1} (pullbackFunctor h) (topology Y) (topology X) := by
  refine ⟨Functor.sheafPullbackConstruction.sheafPullback (pullbackFunctor h) (Type (u + 1))
    (topology Y) (topology X), ⟨Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (pullbackFunctor h) (Type (u + 1)) (topology Y) (topology X)⟩, ?_⟩
  have : PreservesFiniteLimits ((pullbackFunctor h).op.lan :
      ((SimplicialSpacesEtaleSite B S hS Y)ᵒᵖ ⥤ Type (u + 1)) ⥤
        (SimplicialSpacesEtaleSite B S hS X)ᵒᵖ ⥤ Type (u + 1)) :=
    Stacks.Topology.lan_preservesFiniteLimits_of_flat (E := Type (u + 1)) (FE := TypeCat.Fun)
      (pullbackFunctor h) (fun _ ↦ inferInstance)
  exact inferInstance

/-- **Stacks 0DE7.** The morphism of topoi `h_étale : Sh(X_{spaces,étale}) ⟶ Sh(Y_{spaces,étale})`
of a morphism of simplicial algebraic spaces. -/
noncomputable def toposHom :
    MorphismOfTopoi (Sheaf (topology X) (Type (u + 1))) (Sheaf (topology Y) (Type (u + 1))) :=
  (pullbackFunctor_isMorphismOfSites h).morphismOfTopoi

variable (X) in
/-- **Stacks 0DE7.** The ringed topos `(Sh(X_{spaces,étale}), 𝒪_X)` of a simplicial algebraic
space. -/
noncomputable def ringedTopos : RingedTopos.{u + 1, u + 1, u + 1} where
  C := SimplicialSpacesEtaleSite B S hS X
  J := topology X
  O := structureSheaf X

/-- The structure map `h♯ : 𝒪_Y ⟶ h_* 𝒪_X` as a map of sheaves of commutative rings. -/
noncomputable def structureSheafSharp :
    structureSheaf Y ⟶ ((pullbackFunctor h).sheafPushforwardContinuous CommRingCat.{u + 1}
      (topology Y) (topology X)).obj (structureSheaf X) where
  hom := structureSharp h

/-- **Stacks 0DE7.** The morphism of ringed topoi
`h_étale : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)` of a morphism of simplicial algebraic
spaces: the morphism of topoi of base change in each degree, with the structure map `h♯` given
by `h_n♯` in degree `n`. -/
noncomputable def ringedToposHom : RingedToposHom (ringedTopos X) (ringedTopos Y) where
  toToposHom := toposHom h
  fSharp := structureSheafSharp h ≫ (Stacks.Sheaves.ToposPullback.restrictionCommRingIso
    (topology Y) (topology X) (pullbackFunctor h) (structureSheaf X)).inv

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite
