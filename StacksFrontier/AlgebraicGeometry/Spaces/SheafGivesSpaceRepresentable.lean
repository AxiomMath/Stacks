module

public import Mathlib.CategoryTheory.Sites.Canonical
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafGivesSpaceFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleStructureSheaf

/-!
# The functor of Stacks 0GF6 at a representable sheaf

Stacks 0GF6 attaches to a sheaf of sets `𝓕` on the étale site of an algebraic space `Y` the
functor `X(T) = {(y, s) | y : T → Y, s ∈ Γ(T, y⁻¹ 𝓕)}`
(`AlgebraicGeometry.Space.sheafPairsPresheaf`). This file proves the two facts about that
construction which reduce the four assertions of Stacks 0GF6 to the representability of `𝓕`:
the construction is functorial in `𝓕`, and when `𝓕 = h_W` is the sheaf represented by an
algebraic space `W` étale over `Y`, the functor `X` is the functor of points of `W`, over `Y`.
The source records the second fact in its proof ("the construction sends the representable
sheaf `h_V` on `Y_étale` to the representable functor represented by `V`").

## Main definitions

* `AlgebraicGeometry.Space.sheafPairsPresheafMap` and
  `AlgebraicGeometry.Space.sheafPairsPresheafMapIso`: functoriality of `X` in the sheaf.
* `AlgebraicGeometry.Space.sheafPairsPresheafYonedaIso` and
  `AlgebraicGeometry.Space.sheafPairsPresheafRepresentableIso`: the functor `X` of the sheaf
  represented by `W` (resp. of its sheafification) is the functor of points of `W`.
* `CategoryTheory.Adjunction.yonedaIso`: Stacks 04D3 for subcanonical sites, the inverse image
  of a representable sheaf along a continuous functor is representable.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.isSheaf_yoneda_obj` and the instance
  `AlgebraicGeometry.Space.SpacesEtale.subcanonical`: the spaces-étale topology of an algebraic
  space is subcanonical.
* `AlgebraicGeometry.Space.spacesEtaleInverseImage_comp_inv_app_comp_baseChangeYonedaIso_hom`:
  the identification of Stacks 04D3 is compatible with the composition comparison of the
  inverse images.
* `AlgebraicGeometry.Space.sheafPairsPresheafYonedaIso_hom_comp` and
  `AlgebraicGeometry.Space.sheafPairsPresheafRepresentableIso_hom_comp`: these identifications
  lie over `Y`.

## Implementation notes

For `y : T ⟶ Y` the inverse image `y⁻¹ h_W` is `h_{T ×_Y W}` by Stacks 04D3, and since the
spaces-étale topology is subcanonical a global section of `h_{T ×_Y W}` is a section of
`T ×_Y W ⟶ T`, that is a morphism `T ⟶ W` over `y`. This identifies each set `X(T)` with the
morphisms `T ⟶ W` (`AlgebraicGeometry.Space.representablePairsEquiv`). The restriction maps of
`X` are built from the composition comparison of the inverse images, which is only given as an
adjoint mate; the identification is compatible with restriction because the isomorphism of
Stacks 04D3 is compatible with that mate
(`AlgebraicGeometry.Space.spacesEtaleInverseImage_comp_inv_app_comp_baseChangeYonedaIso_hom`),
which is checked through the corepresentability bijections of
`CategoryTheory.Adjunction.yonedaCorepEquiv`.

Subcanonicity is proved from Stacks 04P2: a covering family of the spaces-étale site is an
étale covering of algebraic spaces, along which morphisms into any algebraic space descend.

## References

* [Stacks Project, Tag 0GF6](https://stacks.math.columbia.edu/tag/0GF6)
* [Stacks Project, Tag 04D3](https://stacks.math.columbia.edu/tag/04D3)
* [Stacks Project, Tag 04P2](https://stacks.math.columbia.edu/tag/04P2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Adjunction

universe v u₁ u₂

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} [J.Subcanonical] [K.Subcanonical]
  {u : C ⥤ D} [u.IsContinuous J K] {F : Sheaf J (Type v) ⥤ Sheaf K (Type v)}
  (adj : F ⊣ u.sheafPushforwardContinuous (Type v) J K)

/-- The sections over `U` of the pushforward of a sheaf `H` along `u` are the sections of `H`
over `u(U)`; this is the Yoneda bijection read in those terms. -/
noncomputable def pushforwardYonedaEquiv (U : C) (H : Sheaf K (Type v)) :
    (J.yoneda.obj U ⟶ (u.sheafPushforwardContinuous (Type v) J K).obj H) ≃
      H.obj.obj (Opposite.op (u.obj U)) :=
  J.yonedaEquiv

omit [K.Subcanonical] in
/-- `CategoryTheory.Adjunction.pushforwardYonedaEquiv` is natural in the sheaf. -/
theorem pushforwardYonedaEquiv_comp (U : C) {H H' : Sheaf K (Type v)}
    (f : J.yoneda.obj U ⟶ (u.sheafPushforwardContinuous (Type v) J K).obj H) (α : H ⟶ H') :
    pushforwardYonedaEquiv U H' (f ≫ (u.sheafPushforwardContinuous (Type v) J K).map α) =
      α.hom.app _ (pushforwardYonedaEquiv U H f) :=
  rfl

omit [K.Subcanonical] in
/-- `CategoryTheory.Adjunction.pushforwardYonedaEquiv` is natural in the object. -/
theorem pushforwardYonedaEquiv_yoneda_map_comp {U U' : C} (g : U ⟶ U') {H : Sheaf K (Type v)}
    (f : J.yoneda.obj U' ⟶ (u.sheafPushforwardContinuous (Type v) J K).obj H) :
    pushforwardYonedaEquiv U H (J.yoneda.map g ≫ f) =
      H.obj.map (u.map g).op (pushforwardYonedaEquiv U' H f) :=
  (J.yonedaEquiv_naturality f g).symm

/-- For a left adjoint `F` of the pushforward along a continuous functor `u` between
subcanonical sites, the morphisms out of `F(h_U)` and the morphisms out of `h_{u(U)}` are both
the sections over `u(U)`; this is the resulting bijection. -/
noncomputable def yonedaCorepEquiv (U : C) (H : Sheaf K (Type v)) :
    (F.obj (J.yoneda.obj U) ⟶ H) ≃ (K.yoneda.obj (u.obj U) ⟶ H) :=
  (adj.homEquiv _ _).trans ((pushforwardYonedaEquiv U H).trans K.yonedaEquiv.symm)

/-- `CategoryTheory.Adjunction.yonedaCorepEquiv`, unfolded through the Yoneda bijection of the
target site. -/
theorem yonedaEquiv_yonedaCorepEquiv (U : C) {H : Sheaf K (Type v)}
    (f : F.obj (J.yoneda.obj U) ⟶ H) :
    K.yonedaEquiv (adj.yonedaCorepEquiv U H f) =
      pushforwardYonedaEquiv U H (adj.homEquiv _ _ f) := by
  simp only [yonedaCorepEquiv, Equiv.trans_apply]
  exact K.yonedaEquiv.apply_symm_apply _

/-- `CategoryTheory.Adjunction.yonedaCorepEquiv` is natural in the test sheaf. -/
theorem yonedaCorepEquiv_comp (U : C) {H H' : Sheaf K (Type v)}
    (f : F.obj (J.yoneda.obj U) ⟶ H) (α : H ⟶ H') :
    adj.yonedaCorepEquiv U H' (f ≫ α) = adj.yonedaCorepEquiv U H f ≫ α := by
  apply K.yonedaEquiv.injective
  rw [K.yonedaEquiv_comp, yonedaEquiv_yonedaCorepEquiv, yonedaEquiv_yonedaCorepEquiv,
    homEquiv_naturality_right, pushforwardYonedaEquiv_comp]

/-- **The inverse image of a representable sheaf is representable** (Stacks 04D3 for
subcanonical sites): a left adjoint `F` of the pushforward along a continuous functor `u`
carries the sheaf represented by `U` to the sheaf represented by `u(U)`. -/
noncomputable def yonedaIso (U : C) : F.obj (J.yoneda.obj U) ≅ K.yoneda.obj (u.obj U) where
  hom := (adj.yonedaCorepEquiv U _).symm (𝟙 _)
  inv := adj.yonedaCorepEquiv U _ (𝟙 _)
  hom_inv_id := by
    apply (adj.yonedaCorepEquiv U _).injective
    rw [yonedaCorepEquiv_comp, Equiv.apply_symm_apply, Category.id_comp]
  inv_hom_id := by
    have h := (adj.yonedaCorepEquiv_comp U (𝟙 _) ((adj.yonedaCorepEquiv U _).symm (𝟙 _))).symm
    rwa [Category.id_comp, Equiv.apply_symm_apply] at h

/-- The defining property of `CategoryTheory.Adjunction.yonedaIso`: precomposing with it turns
the bijection of `CategoryTheory.Adjunction.yonedaCorepEquiv` into the identity. -/
theorem yonedaCorepEquiv_yonedaIso_hom_comp (U : C) {H : Sheaf K (Type v)}
    (k : K.yoneda.obj (u.obj U) ⟶ H) :
    adj.yonedaCorepEquiv U H ((adj.yonedaIso U).hom ≫ k) = k := by
  rw [yonedaCorepEquiv_comp]
  change (adj.yonedaCorepEquiv U _) ((adj.yonedaCorepEquiv U _).symm (𝟙 _)) ≫ k = k
  rw [Equiv.apply_symm_apply, Category.id_comp]

/-- The transpose of `CategoryTheory.Adjunction.yonedaIso` followed by a morphism `k` out of
`h_{u(U)}` is, on sections over `U`, the element of `k` given by the Yoneda lemma. -/
theorem pushforwardYonedaEquiv_homEquiv_yonedaIso_hom_comp (U : C) {H : Sheaf K (Type v)}
    (k : K.yoneda.obj (u.obj U) ⟶ H) :
    pushforwardYonedaEquiv U H (adj.homEquiv _ _ ((adj.yonedaIso U).hom ≫ k)) =
      K.yonedaEquiv k := by
  rw [← yonedaEquiv_yonedaCorepEquiv, yonedaCorepEquiv_yonedaIso_hom_comp]

/-- The transpose of `CategoryTheory.Adjunction.yonedaIso` is, on sections over `U`, the
tautological section of `h_{u(U)}`. -/
theorem pushforwardYonedaEquiv_homEquiv_yonedaIso_hom (U : C) :
    pushforwardYonedaEquiv U _ (adj.homEquiv _ _ (adj.yonedaIso U).hom) = 𝟙 (u.obj U) := by
  rw [← Category.comp_id (adj.yonedaIso U).hom, pushforwardYonedaEquiv_homEquiv_yonedaIso_hom_comp]
  rfl

/-- `CategoryTheory.Adjunction.yonedaIso` is natural in the object. -/
@[reassoc]
theorem map_yoneda_map_comp_yonedaIso_hom {U U' : C} (g : U ⟶ U') :
    F.map (J.yoneda.map g) ≫ (adj.yonedaIso U').hom =
      (adj.yonedaIso U).hom ≫ K.yoneda.map (u.map g) := by
  apply (adj.yonedaCorepEquiv U _).injective
  rw [yonedaCorepEquiv_yonedaIso_hom_comp]
  apply K.yonedaEquiv.injective
  rw [yonedaEquiv_yonedaCorepEquiv, homEquiv_naturality_left,
    pushforwardYonedaEquiv_yoneda_map_comp, ← yonedaEquiv_yonedaCorepEquiv,
    ← Category.comp_id (adj.yonedaIso U').hom, yonedaCorepEquiv_yonedaIso_hom_comp,
    K.yonedaEquiv_yoneda_map]
  exact Category.comp_id (u.map g)

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` of presheaves on the big fppf site over `S` is deep
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_SheafGivesSpaceRepresentable :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_SheafGivesSpaceRepresentable
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

namespace SpacesEtale

variable {X : AlgebraicSpaces B S hS}

/-- A presieve of the spaces-étale site whose members jointly cover the points of their
target satisfies the sheaf condition for every presheaf represented by an object of the site.

The members form an étale covering of algebraic spaces, so a compatible family of morphisms
into the represented object descends uniquely by Stacks 04P2, and the descended morphism lies
over `X` because its composite with the structure morphism descends the structure morphisms of
the members, as the structure morphism of the target does. -/
theorem isSheafFor_yoneda_of_jointlySurjective (A : SpacesEtale B S hS X)
    {U : SpacesEtale B S hS X} (P : Presieve U)
    (hP : ∀ x : points B S hS ((toSpaces B S hS X).obj U).1, ∃ (Z : SpacesEtale B S hS X)
      (h : Z ⟶ U), P h ∧ ∃ y : points B S hS ((toSpaces B S hS X).obj Z).1,
        pointsMap B S hS ((toSpaces B S hS X).obj Z).1 ((toSpaces B S hS X).map h).hom y = x) :
    Presieve.IsSheafFor (yoneda.obj A) P := by
  intro x hx
  let I : Type (u + 1) := Σ Z : SpacesEtale B S hS X, {h : Z ⟶ U // P h}
  let Xi : I → AlgebraicSpaces B S hS := fun i => (toSpaces B S hS X).obj i.1
  let fi : ∀ i, Xi i ⟶ (toSpaces B S hS X).obj U := fun i => (toSpaces B S hS X).map i.2.1
  have hfpqc := isFpqcCovering_of_isEtaleCovering B S hS _ _
    (isEtaleCovering_of_isCovering B S hS X (fun i : I => i.1) (fun i => i.2.1) (by
      intro pt
      obtain ⟨Z, h, hh, y, hy⟩ := hP pt
      exact ⟨⟨Z, h, hh⟩, y, hy⟩) :
      IsEtaleCovering B S hS (fun i => (Xi i).1) (fun i => (fi i).hom))
  have hstr : ∀ i : I, fi i ≫ U.obj.hom = i.1.obj.hom := fun i =>
    toSpaces_map_comp_structure B S hS X i.2.1
  let p₁ : ∀ i j : I, AlgebraicSpaces.fiberProduct B S hS (fi i) (fi j) ⟶ Xi i := fun i j =>
    ObjectProperty.homMk (pullback.fst (fi i).hom (fi j).hom)
  let p₂ : ∀ i j : I, AlgebraicSpaces.fiberProduct B S hS (fi i) (fi j) ⟶ Xi j := fun i j =>
    ObjectProperty.homMk (pullback.snd (fi i).hom (fi j).hom)
  have hpair : ∀ i j : I,
      ∀ {Q : AlgebraicSpaces B S hS} (k : (toSpaces B S hS X).obj A ⟶ Q),
        p₁ i j ≫ (toSpaces B S hS X).map (x i.2.1 i.2.2) ≫ k =
          p₂ i j ≫ (toSpaces B S hS X).map (x j.2.1 j.2.2) ≫ k := by
    intro i j Q k
    have hsq := AlgebraicSpaces.isPullback_fiberProduct B S hS (fi i) (fi j)
    have hp₁ : IsEtale B S hS (p₁ i j).hom :=
      isEtale_of_isPullback B S hS _ _ _ _ hsq.flip (isEtale_toSpaces_map B S hS X j.2.1)
    let Pij : SpacesEtale B S hS X :=
      ⟨Over.mk (p₁ i j ≫ i.1.obj.hom), isEtale_comp B S hS hp₁ i.1.property⟩
    have hw : p₂ i j ≫ j.1.obj.hom = p₁ i j ≫ i.1.obj.hom := by
      rw [← hstr i, ← hstr j, ← Category.assoc, ← Category.assoc, hsq.w]
    let q₁ : Pij ⟶ i.1 := ObjectProperty.homMk (Over.homMk (p₁ i j) rfl)
    let q₂ : Pij ⟶ j.1 := ObjectProperty.homMk (Over.homMk (p₂ i j) hw)
    have hc : q₁ ≫ x i.2.1 i.2.2 = q₂ ≫ x j.2.1 j.2.2 :=
      hx q₁ q₂ i.2.2 j.2.2 (ObjectProperty.hom_ext _ (Over.OverMorphism.ext hsq.w))
    have hc' := congrArg (fun m => (toSpaces B S hS X).map m ≫ k) hc
    simp only [Functor.map_comp, Category.assoc] at hc'
    exact hc'
  obtain ⟨t, ht, htu⟩ := existsUnique_desc_of_fpqcCovering B S hS fi hfpqc
    ((toSpaces B S hS X).obj A) (fun i => (toSpaces B S hS X).map (x i.2.1 i.2.2))
    (fun i j => by simpa using hpair i j (𝟙 _))
  have hover : t ≫ A.obj.hom = U.obj.hom := by
    obtain ⟨t', -, hu⟩ := existsUnique_desc_of_fpqcCovering B S hS fi hfpqc X
      (fun i => i.1.obj.hom) (fun i j => by
        have e : ∀ i : I, (toSpaces B S hS X).map (x i.2.1 i.2.2) ≫ A.obj.hom = i.1.obj.hom :=
          fun i => toSpaces_map_comp_structure B S hS X _
        have h := hpair i j A.obj.hom
        rwa [e i, e j] at h)
    rw [hu (t ≫ A.obj.hom) (fun i => by
        rw [← Category.assoc, ht i]; exact toSpaces_map_comp_structure B S hS X _),
      hu U.obj.hom hstr]
  refine ⟨ObjectProperty.homMk (Over.homMk t hover),
    fun Z h hh => ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ht ⟨Z, h, hh⟩)), ?_⟩
  intro t₂ ht₂
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)
  refine htu ((toSpaces B S hS X).map t₂) (fun i => ?_)
  have h : i.2.1 ≫ t₂ = x i.2.1 i.2.2 := ht₂ i.2.1 i.2.2
  rw [← h, Functor.map_comp]

/-- **The spaces-étale topology is subcanonical**: the presheaf represented by any algebraic
space étale over `X` is a sheaf on the spaces-étale site of `X`. Morphisms into an algebraic
space descend along étale coverings by Stacks 04P2. -/
theorem isSheaf_yoneda_obj (A : SpacesEtale B S hS X) :
    Presieve.IsSheaf (topology B S hS X) (yoneda.obj A) := by
  rw [Precoverage.isSheaf_toGrothendieck_iff]
  intro V U f R hR
  obtain ⟨E, rfl, hE⟩ := hR
  apply isSheafFor_yoneda_of_jointlySurjective
  intro pt
  obtain ⟨i, y, hy⟩ := hE (pointsMap B S hS _ ((toSpaces B S hS X).map f).hom pt)
  obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom B S hS
    ((IsPullback.of_hasPullback f (E.f i)).map (toSpaces B S hS X))) pt y hy.symm
  exact ⟨pullback f (E.f i), pullback.fst _ _,
    ⟨_, pullback.snd _ _, E.f i, Presieve.ofArrows.mk i, pullback.condition.symm⟩, w, hw⟩

/-- The spaces-étale topology of an algebraic space is subcanonical. -/
instance subcanonical : (topology B S hS X).Subcanonical :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ (isSheaf_yoneda_obj B S hS)

end SpacesEtale

/-! ### Functoriality in the sheaf -/

variable {Y : AlgebraicSpaces B S hS}

/-- Restricting a section and then pushing it along a morphism of sheaves is pushing it along
the morphism and then restricting: the composition comparison of the inverse images is
natural. -/
theorem pullSection_comp_map {G G' : spacesEtaleSheafCat B S hS Y} (α : G ⟶ G')
    {T' T : AlgebraicSpaces B S hS} (g : T' ⟶ T) (y : T ⟶ Y)
    (s : terminalSpacesEtaleSheaf B S hS T ⟶ (spacesEtaleInverseImage B S hS y).obj G) :
    LocallyDiscrete.pullSection (spacesEtaleSheafCat B S hS)
        (fun {_ _} f => spacesEtaleInverseImage B S hS f)
        (fun X => terminalSpacesEtaleSheaf B S hS X)
        (fun X => terminalSpacesEtaleSheaf_isTerminal B S hS X)
        (fun {_ _} f {_} hA => spacesEtaleInverseImage_isTerminal_obj B S hS f hA)
        (fun {_ _ _} f g => spacesEtaleInverseImage_comp B S hS f g) G' g y
        (s ≫ (spacesEtaleInverseImage B S hS y).map α) =
      LocallyDiscrete.pullSection (spacesEtaleSheafCat B S hS)
          (fun {_ _} f => spacesEtaleInverseImage B S hS f)
          (fun X => terminalSpacesEtaleSheaf B S hS X)
          (fun X => terminalSpacesEtaleSheaf_isTerminal B S hS X)
          (fun {_ _} f {_} hA => spacesEtaleInverseImage_isTerminal_obj B S hS f hA)
          (fun {_ _ _} f g => spacesEtaleInverseImage_comp B S hS f g) G g y s ≫
        (spacesEtaleInverseImage B S hS (g ≫ y)).map α := by
  simp only [LocallyDiscrete.pullSection, Functor.map_comp, Category.assoc]
  congr 2
  exact (spacesEtaleInverseImage_comp B S hS g y).inv.naturality α

/-- **Functoriality of the functor of Stacks 0GF6 in the sheaf.** A morphism of spaces-étale
sheaves `α : G ⟶ G'` sends a pair `(y, s)` to `(y, y⁻¹(α) ∘ s)`. -/
noncomputable def sheafPairsPresheafMap {G G' : spacesEtaleSheafCat B S hS Y} (α : G ⟶ G') :
    sheafPairsPresheaf B S hS G ⟶ sheafPairsPresheaf B S hS G' where
  app T := TypeCat.ofHom fun p => ⟨p.1, p.2 ≫ (spacesEtaleInverseImage B S hS p.1).map α⟩
  naturality T T' g := by
    refine TypeCat.homEquiv.injective (funext fun p => ?_)
    exact (congrArg (Sigma.mk _) (pullSection_comp_map B S hS α g.unop p.1 p.2)).symm

/-- The functoriality of the functor of Stacks 0GF6 in the sheaf leaves the first coordinate
unchanged, i.e. it lies over `Y`. -/
@[reassoc (attr := simp)]
theorem sheafPairsPresheafMap_comp_sheafPairsToBase {G G' : spacesEtaleSheafCat B S hS Y}
    (α : G ⟶ G') :
    sheafPairsPresheafMap B S hS α ≫ sheafPairsToBase B S hS G' = sheafPairsToBase B S hS G :=
  rfl

/-- The functoriality of the functor of Stacks 0GF6 in the sheaf preserves identities. -/
@[simp]
theorem sheafPairsPresheafMap_id (G : spacesEtaleSheafCat B S hS Y) :
    sheafPairsPresheafMap B S hS (𝟙 G) = 𝟙 _ := by
  ext T : 2
  refine TypeCat.homEquiv.injective (funext fun p => ?_)
  change (⟨p.1, p.2 ≫ (spacesEtaleInverseImage B S hS p.1).map (𝟙 G)⟩ :
    (sheafPairsPresheaf B S hS G).obj T) = p
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

/-- The functoriality of the functor of Stacks 0GF6 in the sheaf preserves composition. -/
@[simp]
theorem sheafPairsPresheafMap_comp {G G' G'' : spacesEtaleSheafCat B S hS Y} (α : G ⟶ G')
    (β : G' ⟶ G'') :
    sheafPairsPresheafMap B S hS (α ≫ β) =
      sheafPairsPresheafMap B S hS α ≫ sheafPairsPresheafMap B S hS β := by
  ext T : 2
  refine TypeCat.homEquiv.injective (funext fun p => ?_)
  change (⟨p.1, p.2 ≫ (spacesEtaleInverseImage B S hS p.1).map (α ≫ β)⟩ :
    (sheafPairsPresheaf B S hS G'').obj T) =
      ⟨p.1, (p.2 ≫ (spacesEtaleInverseImage B S hS p.1).map α) ≫
        (spacesEtaleInverseImage B S hS p.1).map β⟩
  rw [CategoryTheory.Functor.map_comp, Category.assoc]

/-- An isomorphism of spaces-étale sheaves induces an isomorphism of the functors of
Stacks 0GF6 attached to them, over `Y`. -/
noncomputable def sheafPairsPresheafMapIso {G G' : spacesEtaleSheafCat B S hS Y} (α : G ≅ G') :
    sheafPairsPresheaf B S hS G ≅ sheafPairsPresheaf B S hS G' where
  hom := sheafPairsPresheafMap B S hS α.hom
  inv := sheafPairsPresheafMap B S hS α.inv
  hom_inv_id := by rw [← sheafPairsPresheafMap_comp, α.hom_inv_id, sheafPairsPresheafMap_id]
  inv_hom_id := by rw [← sheafPairsPresheafMap_comp, α.inv_hom_id, sheafPairsPresheafMap_id]

/-- The isomorphism induced by an isomorphism of sheaves lies over `Y`. -/
@[reassoc (attr := simp)]
theorem sheafPairsPresheafMapIso_hom_comp_sheafPairsToBase
    {G G' : spacesEtaleSheafCat B S hS Y} (α : G ≅ G') :
    (sheafPairsPresheafMapIso B S hS α).hom ≫ sheafPairsToBase B S hS G' =
      sheafPairsToBase B S hS G :=
  rfl

/-! ### The terminal sheaf on the spaces-étale site -/

/-- The terminal sheaf on the spaces-étale site of `T` is the sheaf represented by the
terminal object `T` of that site. -/
noncomputable def terminalSheafIsoYoneda (T : AlgebraicSpaces B S hS) :
    terminalSpacesEtaleSheaf B S hS T ≅
      (SpacesEtale.topology B S hS T).yoneda.obj (SpacesEtale.idObj B S hS T) :=
  (terminalSpacesEtaleSheaf_isTerminal B S hS T).uniqueUpToIso
    ((SpacesEtale.isTerminal_idObj B S hS T).isTerminalObj
      (SpacesEtale.topology B S hS T).yoneda)

/-! ### Inverse images of representable sheaves and the composition comparison -/

section Coherence

/-- The isomorphism of Stacks 04D3 for the spaces-étale inverse image along `y : T ⟶ Z`: the
inverse image of the sheaf represented by `V` is the sheaf represented by `T ×_Z V`. -/
noncomputable abbrev baseChangeYonedaIso {T Z : AlgebraicSpaces B S hS} (y : T ⟶ Z)
    (V : SpacesEtale B S hS Z) :
    (spacesEtaleInverseImage B S hS y).obj ((SpacesEtale.topology B S hS Z).yoneda.obj V) ≅
      (SpacesEtale.topology B S hS T).yoneda.obj ((spacesBaseChange B S hS y).functor.obj V) :=
  (spacesEtaleAdjunction B S hS y).yonedaIso V

/-- **The isomorphism of Stacks 04D3 is compatible with the composition comparison of the
inverse images**: identifying `(k ≫ y)⁻¹ h_V` with `h_{T' ×_Z V}` directly, or through
`k⁻¹ y⁻¹ h_V = k⁻¹ h_{T ×_Z V} = h_{T' ×_T (T ×_Z V)}`, differ by the composition
isomorphism of the base changes of Stacks 03G2, part (2). -/
theorem spacesEtaleInverseImage_comp_inv_app_comp_baseChangeYonedaIso_hom
    {T' T Z : AlgebraicSpaces B S hS} (k : T' ⟶ T) (y : T ⟶ Z) (V : SpacesEtale B S hS Z) :
    (spacesEtaleInverseImage_comp B S hS k y).inv.app
          ((SpacesEtale.topology B S hS Z).yoneda.obj V) ≫
        (baseChangeYonedaIso B S hS (k ≫ y) V).hom =
      (spacesEtaleInverseImage B S hS k).map (baseChangeYonedaIso B S hS y V).hom ≫
        (baseChangeYonedaIso B S hS k ((spacesBaseChange B S hS y).functor.obj V)).hom ≫
          (SpacesEtale.topology B S hS T').yoneda.map
            ((spacesBaseChange_comp B S hS k y).hom.app V) := by
  apply (((spacesEtaleAdjunction B S hS y).comp
    (spacesEtaleAdjunction B S hS k)).homEquiv _ _).injective
  have hinv : (spacesEtaleInverseImage_comp B S hS k y).inv =
      (conjugateEquiv (spacesEtaleAdjunction B S hS (k ≫ y))
        ((spacesEtaleAdjunction B S hS y).comp (spacesEtaleAdjunction B S hS k))).symm
        (spacesEtaleSheafPushforwardComp B S hS k y).hom := rfl
  -- Transposing after precomposing with the mate is transposing and postcomposing.
  have hmate : ∀ {H} (m : (spacesEtaleInverseImage B S hS (k ≫ y)).obj
        ((SpacesEtale.topology B S hS Z).yoneda.obj V) ⟶ H),
      ((spacesEtaleAdjunction B S hS y).comp (spacesEtaleAdjunction B S hS k)).homEquiv _ _
          ((spacesEtaleInverseImage_comp B S hS k y).inv.app _ ≫ m) =
        (spacesEtaleAdjunction B S hS (k ≫ y)).homEquiv _ _ m ≫
          (spacesEtaleSheafPushforwardComp B S hS k y).hom.app H := by
    intro H m
    rw [hinv, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
      CategoryTheory.Functor.map_comp, ← Category.assoc, ← unit_conjugateEquiv_symm,
      Category.assoc, Category.assoc, NatTrans.naturality]
  rw [hmate, Adjunction.comp_homEquiv]
  simp only [Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left]
  apply (Adjunction.pushforwardYonedaEquiv V _).injective
  rw [← Adjunction.yonedaEquiv_yonedaCorepEquiv, Adjunction.yonedaCorepEquiv_yonedaIso_hom_comp]
  change (spacesBaseChange_comp B S hS k y).hom.app V ≫
      Adjunction.pushforwardYonedaEquiv (u := (spacesBaseChange B S hS (k ≫ y)).functor) V _
        ((spacesEtaleAdjunction B S hS (k ≫ y)).homEquiv _ _
          (baseChangeYonedaIso B S hS (k ≫ y) V).hom) =
    Adjunction.pushforwardYonedaEquiv (u := (spacesBaseChange B S hS k).functor)
      ((spacesBaseChange B S hS y).functor.obj V) _
      ((spacesEtaleAdjunction B S hS k).homEquiv _ _
        ((baseChangeYonedaIso B S hS k ((spacesBaseChange B S hS y).functor.obj V)).hom ≫
          (SpacesEtale.topology B S hS T').yoneda.map
            ((spacesBaseChange_comp B S hS k y).hom.app V)))
  rw [Adjunction.pushforwardYonedaEquiv_homEquiv_yonedaIso_hom,
    Adjunction.pushforwardYonedaEquiv_homEquiv_yonedaIso_hom_comp,
    GrothendieckTopology.yonedaEquiv_yoneda_map, Category.comp_id]

end Coherence

/-! ### The representable case -/

section Representable

variable (W : SpacesEtale B S hS Y)

/-- The points of the cartesian base change `T ×_Y W ⟶ T` over `T` are the morphisms
`T ⟶ W` over `Y`. -/
noncomputable def baseChangeSectionEquiv {T : AlgebraicSpaces B S hS} (y : T ⟶ Y) :
    {g : T ⟶ W.obj.left // g ≫ W.obj.hom = y} ≃
      (SpacesEtale.idObj B S hS T ⟶ (spacesBaseChange B S hS y).functor.obj W) where
  toFun g := ObjectProperty.homMk (Over.homMk
    (((spacesBaseChange B S hS y).isPullback W).lift g.1 (𝟙 T)
      (g.2.trans (Category.id_comp y).symm))
    (((spacesBaseChange B S hS y).isPullback W).lift_snd _ _ _))
  invFun m := ⟨m.hom.left ≫ (spacesBaseChange B S hS y).projection.app W, by
    exact (Category.assoc _ _ _).trans ((congrArg (m.hom.left ≫ ·)
      ((spacesBaseChange B S hS y).isPullback W).w).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ y) (Over.w m.hom)).trans (Category.id_comp y))))⟩
  left_inv g := Subtype.ext (((spacesBaseChange B S hS y).isPullback W).lift_fst _ _ _)
  right_inv m := by
    dsimp only
    refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)
    refine ((spacesBaseChange B S hS y).isPullback W).hom_ext ?_ ?_
    · exact ((spacesBaseChange B S hS y).isPullback W).lift_fst _ _ _
    · exact (((spacesBaseChange B S hS y).isPullback W).lift_snd _ _ _).trans
        (Over.w m.hom).symm

/-- The sections over `T` of the inverse image along `y : T ⟶ Y` of the sheaf represented by
`W` are the morphisms `T ⟶ W` over `Y`: through Stacks 04D3 the inverse image is represented
by `T ×_Y W`, the spaces-étale topology is subcanonical, and a section of `T ×_Y W ⟶ T` is a
morphism `T ⟶ W` over `Y`. -/
noncomputable def representableSectionEquiv {T : AlgebraicSpaces B S hS} (y : T ⟶ Y) :
    {g : T ⟶ W.obj.left // g ≫ W.obj.hom = y} ≃
      (terminalSpacesEtaleSheaf B S hS T ⟶ (spacesEtaleInverseImage B S hS y).obj
        ((SpacesEtale.topology B S hS Y).yoneda.obj W)) :=
  (baseChangeSectionEquiv B S hS W y).trans
    ((SpacesEtale.topology B S hS T).yonedaFullyFaithful.homEquiv.trans
      (Iso.homCongr (terminalSheafIsoYoneda B S hS T).symm
        (baseChangeYonedaIso B S hS y W).symm))

/-- The pairs `(y, s)` over `T` attached to the sheaf represented by `W` are the morphisms
`T ⟶ W`. -/
noncomputable def representablePairsEquiv (T : AlgebraicSpaces B S hS) :
    (T ⟶ W.obj.left) ≃
      (sheafPairsPresheaf B S hS ((SpacesEtale.topology B S hS Y).yoneda.obj W)).obj (op T) :=
  (Equiv.sigmaFiberEquiv (fun g : T ⟶ W.obj.left => g ≫ W.obj.hom)).symm.trans
    (Equiv.sigmaCongrRight fun y => representableSectionEquiv B S hS W y)

/-- The section of `y⁻¹ h_W` attached to a morphism `g : T ⟶ W` over `Y`, written out. -/
theorem representableSectionEquiv_apply {T : AlgebraicSpaces B S hS} (y : T ⟶ Y)
    (g : {g : T ⟶ W.obj.left // g ≫ W.obj.hom = y}) :
    representableSectionEquiv B S hS W y g =
      (terminalSheafIsoYoneda B S hS T).hom ≫
        (SpacesEtale.topology B S hS T).yoneda.map (baseChangeSectionEquiv B S hS W y g) ≫
          (baseChangeYonedaIso B S hS y W).inv :=
  rfl

/-- The unique morphism from the terminal object of the spaces-étale site of `T'` to the base
change along `k : T' ⟶ T` of the terminal object of the spaces-étale site of `T` composes with
the projection to `T` to `k`. -/
theorem isTerminal_spacesBaseChange_idObj_from_comp_projection {T' T : AlgebraicSpaces B S hS}
    (k : T' ⟶ T) :
    ((isTerminal_spacesBaseChange_idObj B S hS k).from (SpacesEtale.idObj B S hS T')).hom.left ≫
      (spacesBaseChange B S hS k).projection.app (SpacesEtale.idObj B S hS T) = k :=
  (Category.comp_id _).symm.trans ((congrArg (_ ≫ ·)
    ((spacesBaseChange B S hS k).isPullback (SpacesEtale.idObj B S hS T)).w).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ k)
        (Over.w ((isTerminal_spacesBaseChange_idObj B S hS k).from
          (SpacesEtale.idObj B S hS T')).hom)).trans (Category.id_comp k))))

/-- Base change of the section `T ⟶ T ×_Y W` attached to `g` along `k : T' ⟶ T` is the
section `T' ⟶ T' ×_Y W` attached to `k ≫ g`, through the composition isomorphism of the base
changes of Stacks 03G2, part (2). -/
theorem baseChangeSectionEquiv_comp {T' T : AlgebraicSpaces B S hS} (k : T' ⟶ T) (y : T ⟶ Y)
    (g : T ⟶ W.obj.left) (hg : g ≫ W.obj.hom = y) :
    (isTerminal_spacesBaseChange_idObj B S hS k).from (SpacesEtale.idObj B S hS T') ≫
        (spacesBaseChange B S hS k).functor.map (baseChangeSectionEquiv B S hS W y ⟨g, hg⟩) ≫
          (spacesBaseChange_comp B S hS k y).hom.app W =
      baseChangeSectionEquiv B S hS W (k ≫ y) ⟨k ≫ g, by rw [Category.assoc, hg]⟩ := by
  apply (baseChangeSectionEquiv B S hS W (k ≫ y)).symm.injective
  rw [Equiv.symm_apply_apply]
  refine Subtype.ext ?_
  change ((isTerminal_spacesBaseChange_idObj B S hS k).from
      (SpacesEtale.idObj B S hS T')).hom.left ≫
        ((spacesBaseChange B S hS k).functor.map
          (baseChangeSectionEquiv B S hS W y ⟨g, hg⟩)).hom.left ≫
        ((spacesBaseChange_comp B S hS k y).hom.app W).hom.left ≫
          (spacesBaseChange B S hS (k ≫ y)).projection.app W = k ≫ g
  rw [spacesBaseChange_comp_projection]
  have hnat : ((spacesBaseChange B S hS k).functor.map
      (baseChangeSectionEquiv B S hS W y ⟨g, hg⟩)).hom.left ≫
        (spacesBaseChange B S hS k).projection.app ((spacesBaseChange B S hS y).functor.obj W) =
      (spacesBaseChange B S hS k).projection.app (SpacesEtale.idObj B S hS T) ≫
        (baseChangeSectionEquiv B S hS W y ⟨g, hg⟩).hom.left :=
    (spacesBaseChange B S hS k).projection.naturality
      (baseChangeSectionEquiv B S hS W y ⟨g, hg⟩)
  have hlift : (baseChangeSectionEquiv B S hS W y ⟨g, hg⟩).hom.left ≫
      (spacesBaseChange B S hS y).projection.app W = g :=
    ((spacesBaseChange B S hS y).isPullback W).lift_fst _ _ _
  rw [← Category.assoc (((spacesBaseChange B S hS k).functor.map _).hom.left), hnat,
    Category.assoc, hlift]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ g)
    (isTerminal_spacesBaseChange_idObj_from_comp_projection B S hS k))

/-- Restricting the section of `y⁻¹ h_W` attached to `g : T ⟶ W` along `k : T' ⟶ T` gives
the section of `(k ≫ y)⁻¹ h_W` attached to `k ≫ g`. -/
theorem pullSection_representableSectionEquiv {T' T : AlgebraicSpaces B S hS} (k : T' ⟶ T)
    (y : T ⟶ Y) (g : T ⟶ W.obj.left) (hg : g ≫ W.obj.hom = y) :
    LocallyDiscrete.pullSection (spacesEtaleSheafCat B S hS)
        (fun {_ _} f => spacesEtaleInverseImage B S hS f)
        (fun X => terminalSpacesEtaleSheaf B S hS X)
        (fun X => terminalSpacesEtaleSheaf_isTerminal B S hS X)
        (fun {_ _} f {_} hA => spacesEtaleInverseImage_isTerminal_obj B S hS f hA)
        (fun {_ _ _} f g => spacesEtaleInverseImage_comp B S hS f g)
        ((SpacesEtale.topology B S hS Y).yoneda.obj W) k y
        (representableSectionEquiv B S hS W y ⟨g, hg⟩) =
      representableSectionEquiv B S hS W (k ≫ y) ⟨k ≫ g, by rw [Category.assoc, hg]⟩ := by
  rw [← cancel_mono (baseChangeYonedaIso B S hS (k ≫ y) W).hom,
    representableSectionEquiv_apply, representableSectionEquiv_apply,
    ← baseChangeSectionEquiv_comp B S hS W k y g hg]
  simp only [LocallyDiscrete.pullSection, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [spacesEtaleInverseImage_comp_inv_app_comp_baseChangeYonedaIso_hom]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc, Iso.inv_hom_id_map_assoc]
  rw [Adjunction.map_yoneda_map_comp_yonedaIso_hom_assoc (spacesEtaleAdjunction B S hS k)]
  have hterm : (spacesEtaleInverseImage_isTerminal_obj B S hS k
      (terminalSpacesEtaleSheaf_isTerminal B S hS T)).from (terminalSpacesEtaleSheaf B S hS T') ≫
        (spacesEtaleInverseImage B S hS k).map (terminalSheafIsoYoneda B S hS T).hom ≫
          (baseChangeYonedaIso B S hS k (SpacesEtale.idObj B S hS T)).hom =
      (terminalSheafIsoYoneda B S hS T').hom ≫ (SpacesEtale.topology B S hS T').yoneda.map
        ((isTerminal_spacesBaseChange_idObj B S hS k).from (SpacesEtale.idObj B S hS T')) :=
    ((isTerminal_spacesBaseChange_idObj B S hS k).isTerminalObj
      (SpacesEtale.topology B S hS T').yoneda).hom_ext _ _
  rw [← reassoc_of% hterm]

/-- A pair `(y, s)` whose second coordinate is the section attached to `g` is the pair
attached to `g`. -/
theorem sigma_mk_representableSectionEquiv {T : AlgebraicSpaces B S hS} (y : T ⟶ Y)
    (g : T ⟶ W.obj.left) (hg : g ≫ W.obj.hom = y) :
    (⟨y, representableSectionEquiv B S hS W y ⟨g, hg⟩⟩ :
        (sheafPairsPresheaf B S hS ((SpacesEtale.topology B S hS Y).yoneda.obj W)).obj (op T)) =
      representablePairsEquiv B S hS W T g := by
  subst hg
  rfl

/-- The pairs attached to morphisms into `W` are compatible with restriction. -/
theorem representablePairsEquiv_naturality {T' T : AlgebraicSpaces B S hS} (k : T' ⟶ T)
    (g : T ⟶ W.obj.left) :
    (sheafPairsPresheaf B S hS ((SpacesEtale.topology B S hS Y).yoneda.obj W)).map k.op
        (representablePairsEquiv B S hS W T g) =
      representablePairsEquiv B S hS W T' (k ≫ g) := by
  change (⟨k ≫ g ≫ W.obj.hom, LocallyDiscrete.pullSection (spacesEtaleSheafCat B S hS)
        (fun {_ _} f => spacesEtaleInverseImage B S hS f)
        (fun X => terminalSpacesEtaleSheaf B S hS X)
        (fun X => terminalSpacesEtaleSheaf_isTerminal B S hS X)
        (fun {_ _} f {_} hA => spacesEtaleInverseImage_isTerminal_obj B S hS f hA)
        (fun {_ _ _} f g => spacesEtaleInverseImage_comp B S hS f g)
        ((SpacesEtale.topology B S hS Y).yoneda.obj W) k (g ≫ W.obj.hom)
        (representableSectionEquiv B S hS W (g ≫ W.obj.hom) ⟨g, rfl⟩)⟩ :
      (sheafPairsPresheaf B S hS ((SpacesEtale.topology B S hS Y).yoneda.obj W)).obj (op T')) =
    _
  rw [pullSection_representableSectionEquiv, sigma_mk_representableSectionEquiv]

end Representable

/-- **The functor of Stacks 0GF6 at a representable sheaf.** For an algebraic space `W` étale
over `Y`, the functor `T ↦ {(y, s) | y : T ⟶ Y, s ∈ Γ(T, y⁻¹ h_W)}` attached to the sheaf
`h_W` represented by `W` is the functor of points of `W`: a pair `(y, s)` is a morphism
`T ⟶ W` over `y`. -/
noncomputable def sheafPairsPresheafYonedaIso (W : SpacesEtale B S hS Y) :
    sheafPairsPresheaf B S hS ((SpacesEtale.topology B S hS Y).yoneda.obj W) ≅
      yoneda.obj W.obj.left :=
  (NatIso.ofComponents (fun T => (representablePairsEquiv B S hS W T.unop).toIso)
    (fun {T T'} k => by
      ext g
      exact (representablePairsEquiv_naturality B S hS W k.unop g).symm)).symm

/-- The identification of the functor of Stacks 0GF6 at `h_W` with the functor of points of `W`
lies over `Y`. -/
@[reassoc (attr := simp)]
theorem sheafPairsPresheafYonedaIso_hom_comp (W : SpacesEtale B S hS Y) :
    (sheafPairsPresheafYonedaIso B S hS W).hom ≫ yoneda.map W.obj.hom =
      sheafPairsToBase B S hS _ := by
  rw [sheafPairsPresheafYonedaIso, Iso.symm_hom, Iso.inv_comp_eq]
  ext T g
  rfl

/-- **The functor of Stacks 0GF6 at a representable sheaf**, for the sheafification of the
presheaf represented by an algebraic space `W` étale over `Y`: it is the functor of points of
`W`. -/
noncomputable def sheafPairsPresheafRepresentableIso (W : SpacesEtale B S hS Y) :
    sheafPairsPresheaf B S hS
        ((presheafToSheaf (SpacesEtale.topology B S hS Y) (Type (u + 1))).obj (yoneda.obj W)) ≅
      yoneda.obj W.obj.left :=
  sheafPairsPresheafMapIso B S hS
      (sheafificationIso ((SpacesEtale.topology B S hS Y).yoneda.obj W)).symm ≪≫
    sheafPairsPresheafYonedaIso B S hS W

/-- The identification of `AlgebraicGeometry.Space.sheafPairsPresheafRepresentableIso` lies
over `Y`. -/
@[reassoc (attr := simp)]
theorem sheafPairsPresheafRepresentableIso_hom_comp (W : SpacesEtale B S hS Y) :
    (sheafPairsPresheafRepresentableIso B S hS W).hom ≫ yoneda.map W.obj.hom =
      sheafPairsToBase B S hS _ := by
  rw [sheafPairsPresheafRepresentableIso, Iso.trans_hom, Category.assoc,
    sheafPairsPresheafYonedaIso_hom_comp, sheafPairsPresheafMapIso_hom_comp_sheafPairsToBase]


end AlgebraicGeometry.Space
