module

public import StacksFrontier.Algebra.Homology.HomologyToMapHomologyAdjunction
public import StacksFrontier.CategoryTheory.Abelian.InjectiveResolution.DescHomotopy
public import StacksFrontier.Algebra.Homology.RightDerivedEdge
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.CohomologyOnACofilteredLimit

/-!
# Maps of right derived functors attached to a morphism into a pushforward

Let `P : 𝒳 ⥤ ℬ` and `P' : 𝒳' ⥤ ℬ'` be additive functors, let `H : 𝒳' ⥤ 𝒳` preserve injective
objects, let `K : ℬ' ⥤ ℬ` be left exact, and let `e : H ⋙ P ≅ P' ⋙ K`. In the geometric
situation `P = f_*`, `P' = f'_*`, `H = g'_*`, `K = g_*` for a commutative square of ringed
spaces, and `e` is the identification of the two composite direct images.

A morphism `u : X ⟶ H N`, for `X` in `𝒳` and `N` in `𝒳'`, induces in every degree a morphism

`Rⁿ P (X) ⟶ K (Rⁿ P' (N))`,

computed on injective resolutions `I` of `X` and `J` of `N` by a comparison `c : I ⟶ H J`
extending `u`: it is the map on `n`-th homology of `P(c)`, read through `e`, followed by the
comparison `Hⁿ(K(P' J)) ⟶ K(Hⁿ(P' J))` of the left exact functor `K`. When `K` is the identity
this is the map on cohomology along an `f`-map of [Stacks, Tag 01FA]; when `H` is the identity
and `u` is an identity it is the map `Hⁿ(X, F) ⟶ Γ(Y, Rⁿ f_* F)` of [Stacks, Tag 01F4]; and in
general it is the adjoint form of the base change map of [Stacks, Tag 02N7] in degree `n`.

## Main definitions

* `Stacks.Cohomology.RelativePullback.mapOf`: the map, for given resolutions and comparison.
* `Stacks.Cohomology.RelativePullback.map`: the map, on the chosen injective resolutions.

## Main results

* `Stacks.Cohomology.RelativePullback.mapOf_eq_mapOf`: the map does not depend on the resolutions
  or on the comparison.
* `Stacks.Cohomology.RelativePullback.map_eq_mapOf`: so `map` may be computed on any resolutions.
* `Stacks.Cohomology.RelativePullback.map_comp`: **the composition law** for two stacked
  situations.
* `Stacks.Cohomology.RelativePullback.map_comp_map`: the map is natural in the target object.
* `Stacks.Cohomology.RelativePullback.map_id_eq`: for `H` the identity and `u` an identity, the
  map is the comparison `Hⁿ(P I) ⟶ K (Hⁿ(P' I))` read through `e`.

## References

* [Stacks Project, Tag 01FA](https://stacks.math.columbia.edu/tag/01FA)
* [Stacks Project, Tag 01F4](https://stacks.math.columbia.edu/tag/01F4)
* [Stacks Project, Tag 02N7](https://stacks.math.columbia.edu/tag/02N7)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

namespace Stacks.Cohomology.RelativePullback

open RightDerivedCoEdge HomologyAdjunction

variable {𝒳 : Type u₁} [Category.{v₁} 𝒳] [Abelian 𝒳]
  {𝒳' : Type u₂} [Category.{v₂} 𝒳'] [Abelian 𝒳']
  {ℬ : Type u₃} [Category.{v₃} ℬ] [Abelian ℬ]
  {ℬ' : Type u₄} [Category.{v₄} ℬ'] [Abelian ℬ']
  [HasInjectiveResolutions 𝒳] [HasInjectiveResolutions 𝒳']

/-- The augmentation `X ⟶ I⁰` of an injective resolution, with its source spelled `X`. -/
abbrev aug {𝒞 : Type*} [Category* 𝒞] [Abelian 𝒞] {X : 𝒞} (I : InjectiveResolution X) :
    X ⟶ I.cocomplex.X 0 :=
  I.ι.f 0

/-- `InjectiveResolution.desc` of an identity is compatible with the augmentations. -/
lemma aug_comp_desc_id_f_zero {𝒞 : Type*} [Category* 𝒞] [Abelian 𝒞] {X : 𝒞}
    (I I' : InjectiveResolution X) :
    aug I' ≫ (InjectiveResolution.desc (𝟙 X) I I').f 0 = aug I :=
  (InjectiveResolution.desc_commutes_zero (𝟙 X) I I').trans (Category.id_comp (I.ι.f 0 : X ⟶ _))

/-- `CategoryTheory.InjectiveResolution.isoRightDerivedObj`, with its target spelled as the
homology of the complex, which is the spelling `HomologicalComplex.homologyMap` produces. -/
def rdIso {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] [Abelian 𝒞] [Abelian 𝒟]
    [HasInjectiveResolutions 𝒞] {X : 𝒞} (I : InjectiveResolution X) (F : 𝒞 ⥤ 𝒟) [F.Additive]
    (n : ℕ) :
    (F.rightDerived n).obj X ≅ ((F.mapHomologicalComplex _).obj I.cocomplex).homology n :=
  I.isoRightDerivedObj F n

/-- `rdIso` is natural: for `f : X ⟶ Y` and a morphism `φ : I ⟶ J` of injective resolutions
lying over `f`, the map `Rⁿ F (f)` corresponds under `rdIso` to the map on homology of `F(φ)`. -/
@[reassoc]
lemma rdIso_hom_naturality {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] [Abelian 𝒞] [Abelian 𝒟]
    [HasInjectiveResolutions 𝒞] {X Y : 𝒞} (f : X ⟶ Y) (I : InjectiveResolution X)
    (J : InjectiveResolution Y) (φ : I.cocomplex ⟶ J.cocomplex)
    (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (F : 𝒞 ⥤ 𝒟) [F.Additive] (n : ℕ) :
    (F.rightDerived n).map f ≫ (rdIso J F n).hom =
      (rdIso I F n).hom ≫ HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map φ) n :=
  InjectiveResolution.isoRightDerivedObj_hom_naturality f I J φ comm F n

/-- The inverse of `rdIso` is natural: for `f : X ⟶ Y` and a morphism `φ : I ⟶ J` of
injective resolutions lying over `f`, the map on homology of `F(φ)` corresponds under the
inverse of `rdIso` to `Rⁿ F (f)`. -/
@[reassoc]
lemma rdIso_inv_naturality {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] [Abelian 𝒞] [Abelian 𝒟]
    [HasInjectiveResolutions 𝒞] {X Y : 𝒞} (f : X ⟶ Y) (I : InjectiveResolution X)
    (J : InjectiveResolution Y) (φ : I.cocomplex ⟶ J.cocomplex)
    (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (F : 𝒞 ⥤ 𝒟) [F.Additive] (n : ℕ) :
    (rdIso I F n).inv ≫ (F.rightDerived n).map f =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map φ) n ≫ (rdIso J F n).inv :=
  InjectiveResolution.isoRightDerivedObj_inv_naturality f I J φ comm F n

/-- Two injective resolutions of one object give the same `rdIso` up to the map on homology of
any comparison between them. -/
lemma rdIso_hom_eq {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] [Abelian 𝒞] [Abelian 𝒟]
    [HasInjectiveResolutions 𝒞] {X : 𝒞} (I I' : InjectiveResolution X) (F : 𝒞 ⥤ 𝒟) [F.Additive]
    (n : ℕ) :
    (rdIso I F n).hom = (rdIso I' F n).hom ≫ HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex _).map (InjectiveResolution.desc (𝟙 X) I I')) n := by
  simpa using rdIso_hom_naturality (𝟙 X) I' I _ (InjectiveResolution.desc_commutes_zero (𝟙 X) I I')
    F n

section Def

variable (P : 𝒳 ⥤ ℬ) (P' : 𝒳' ⥤ ℬ') (H : 𝒳' ⥤ 𝒳) (K : ℬ' ⥤ ℬ)
  [P.Additive] [P'.Additive] [H.Additive] [K.Additive] [PreservesFiniteLimits K]
  (e : H ⋙ P ≅ P' ⋙ K)

/-- The morphism of complexes `P I ⟶ K (P' J)` attached to a comparison `c : I ⟶ H J`. -/
def complexMap {I : CochainComplex 𝒳 ℕ} {J : CochainComplex 𝒳' ℕ}
    (c : I ⟶ (H.mapHomologicalComplex _).obj J) :
    (P.mapHomologicalComplex _).obj I ⟶
      (K.mapHomologicalComplex _).obj ((P'.mapHomologicalComplex _).obj J) :=
  (P.mapHomologicalComplex _).map c ≫ (NatTrans.mapHomologicalComplex e.hom _).app J

/-- In degree `n`, `complexMap` is `P (c.f n)` followed by the component of `e` at `J.X n`. -/
lemma complexMap_f {I : CochainComplex 𝒳 ℕ} {J : CochainComplex 𝒳' ℕ}
    (c : I ⟶ (H.mapHomologicalComplex _).obj J) (n : ℕ) :
    (complexMap P P' H K e c).f n = P.map (c.f n) ≫ e.hom.app (J.X n) := rfl

/-- **The map, for given injective resolutions `I` of `X`, `J` of `N` and a comparison
`c : I ⟶ H J`.** -/
def mapOf {X : 𝒳} {N : 𝒳'} (I : InjectiveResolution X) (J : InjectiveResolution N)
    (c : I.cocomplex ⟶ (H.mapHomologicalComplex _).obj J.cocomplex) (n : ℕ) :
    (P.rightDerived n).obj X ⟶ K.obj ((P'.rightDerived n).obj N) :=
  (rdIso I P n).hom ≫
    HomologicalComplex.homologyMap (complexMap P P' H K e c) n ≫
      homologyToMapHomology K ((P'.mapHomologicalComplex _).obj J.cocomplex) n ≫
        K.map (rdIso J P' n).inv

/-- `mapOf` is natural in the source and target objects: for morphisms `α : I' ⟶ I` and
`β : J ⟶ J'` of resolutions lying over `f` and `g`, the comparison `α ≫ c ≫ H β` gives `Rⁿ P (f)`
followed by the map for `c`, followed by `K` of `Rⁿ P' (g)`. -/
private lemma mapOf_naturality {X X' : 𝒳} {N N' : 𝒳'} (f : X' ⟶ X) (g : N ⟶ N')
    (I' : InjectiveResolution X') (I : InjectiveResolution X) (J : InjectiveResolution N)
    (J' : InjectiveResolution N') (α : I'.cocomplex ⟶ I.cocomplex) (β : J.cocomplex ⟶ J'.cocomplex)
    (hα : aug I' ≫ α.f 0 = f ≫ aug I) (hβ : aug J ≫ β.f 0 = g ≫ aug J')
    (c : I.cocomplex ⟶ (H.mapHomologicalComplex _).obj J.cocomplex) (n : ℕ) :
    mapOf P P' H K e I' J' (α ≫ c ≫ (H.mapHomologicalComplex _).map β) n =
      (P.rightDerived n).map f ≫ mapOf P P' H K e I J c n ≫ K.map ((P'.rightDerived n).map g) := by
  have hcx : complexMap P P' H K e (α ≫ c ≫ (H.mapHomologicalComplex _).map β) =
      (P.mapHomologicalComplex _).map α ≫ complexMap P P' H K e c ≫
        (K.mapHomologicalComplex _).map ((P'.mapHomologicalComplex _).map β) := by
    unfold complexMap
    simp only [CategoryTheory.Functor.map_comp, assoc]
    congr 2
    exact NatTrans.mapHomologicalComplex_naturality e.hom β
  unfold mapOf
  simp only [assoc, hcx, HomologicalComplex.homologyMap_comp]
  rw [rdIso_hom_naturality_assoc f I' I α hα P n]
  congr 3
  rw [homologyToMapHomology_naturality_assoc, ← K.map_comp, ← K.map_comp]
  congr 2
  exact (rdIso_inv_naturality g J J' β hβ P' n).symm

variable [H.PreservesInjectiveObjects]

/-- **The map does not depend on the resolutions or on the comparison**, as long as the
comparison extends the given `u : X ⟶ H N`. -/
theorem mapOf_eq_mapOf {X : 𝒳} {N : 𝒳'} (u : X ⟶ H.obj N)
    (I I' : InjectiveResolution X) (J J' : InjectiveResolution N)
    (c : I.cocomplex ⟶ (H.mapHomologicalComplex _).obj J.cocomplex)
    (hc : aug I ≫ c.f 0 = u ≫ H.map (aug J))
    (c' : I'.cocomplex ⟶ (H.mapHomologicalComplex _).obj J'.cocomplex)
    (hc' : aug I' ≫ c'.f 0 = u ≫ H.map (aug J')) (n : ℕ) :
    mapOf P P' H K e I J c n = mapOf P P' H K e I' J' c' n := by
  let α : I'.cocomplex ⟶ I.cocomplex := InjectiveResolution.desc (𝟙 X) I I'
  let β : J.cocomplex ⟶ J'.cocomplex := InjectiveResolution.desc (𝟙 N) J' J
  have hinj : ∀ i, Injective (((H.mapHomologicalComplex _).obj J'.cocomplex).X i) := fun i =>
    RightDerivedEdge.injective_mapHomologicalComplex_obj H J'.cocomplex J'.injective i
  have hhom := InjectiveResolution.homologyMap_mapHomologicalComplex_map_eq
    (I := I') (K := (H.mapHomologicalComplex _).obj J'.cocomplex) P
    (α ≫ c ≫ (H.mapHomologicalComplex _).map β) c' (by
      refine InjectiveResolution.ι_comp_ext _ _ ?_
      show aug I' ≫ α.f 0 ≫ c.f 0 ≫ H.map (β.f 0) = aug I' ≫ c'.f 0
      rw [reassoc_of% aug_comp_desc_id_f_zero I I', reassoc_of% hc, hc', ← H.map_comp,
        aug_comp_desc_id_f_zero J' J]) n
  have key := mapOf_naturality P P' H K e (𝟙 X) (𝟙 N) I' I J J' α β
    ((aug_comp_desc_id_f_zero I I').trans (id_comp _).symm)
    ((aug_comp_desc_id_f_zero J' J).trans (id_comp _).symm) c n
  simp only [CategoryTheory.Functor.map_id, id_comp, comp_id] at key
  rw [← key]
  unfold mapOf complexMap
  rw [HomologicalComplex.homologyMap_comp, hhom, ← HomologicalComplex.homologyMap_comp]

/-- The comparison of chosen injective resolutions extending `u : X ⟶ H N`. -/
def comparison {X : 𝒳} {N : 𝒳'} (u : X ⟶ H.obj N) :
    (injectiveResolution X).cocomplex ⟶
      (H.mapHomologicalComplex _).obj (injectiveResolution N).cocomplex :=
  SpectralLimit.descToComplex (injectiveResolution X) _
    (RightDerivedEdge.injective_mapHomologicalComplex_obj H _ (injectiveResolution N).injective)
    (u ≫ H.map (aug (injectiveResolution N))) (by
      change (u ≫ H.map (aug (injectiveResolution N))) ≫
        H.map ((injectiveResolution N).cocomplex.d 0 1) = 0
      rw [assoc, ← H.map_comp]
      have : aug (injectiveResolution N) ≫ (injectiveResolution N).cocomplex.d 0 1 = 0 :=
        (injectiveResolution N).ι_f_zero_comp_complex_d
      rw [this, H.map_zero, comp_zero])

/-- In degree `0`, the comparison extends `u`: the augmentation of the resolution of `X`
followed by `comparison H u` is `u` followed by `H` of the augmentation of the resolution of
`N`. -/
@[reassoc]
lemma aug_comp_comparison_f_zero {X : 𝒳} {N : 𝒳'} (u : X ⟶ H.obj N) :
    aug (injectiveResolution X) ≫ (comparison H u).f 0 =
      u ≫ H.map (aug (injectiveResolution N)) :=
  SpectralLimit.ι_comp_descToComplex _ _ _ _ _

/-- **The map `Rⁿ P (X) ⟶ K (Rⁿ P' (N))` attached to `u : X ⟶ H N`**, computed on the chosen
injective resolutions. -/
def map {X : 𝒳} {N : 𝒳'} (u : X ⟶ H.obj N) (n : ℕ) :
    (P.rightDerived n).obj X ⟶ K.obj ((P'.rightDerived n).obj N) :=
  mapOf P P' H K e (injectiveResolution X) (injectiveResolution N) (comparison H u) n

/-- `map` may be computed on any injective resolutions and any comparison extending `u`. -/
theorem map_eq_mapOf {X : 𝒳} {N : 𝒳'} (u : X ⟶ H.obj N) (I : InjectiveResolution X)
    (J : InjectiveResolution N)
    (c : I.cocomplex ⟶ (H.mapHomologicalComplex _).obj J.cocomplex)
    (hc : aug I ≫ c.f 0 = u ≫ H.map (aug J)) (n : ℕ) :
    map P P' H K e u n = mapOf P P' H K e I J c n :=
  mapOf_eq_mapOf P P' H K e u _ _ _ _ _ (aug_comp_comparison_f_zero H u) _ hc n

/-- **The map is natural in the target object.** Composing `u : X ⟶ H N` with `H g` for
`g : N ⟶ N'` composes the map with `K` of the morphism `g` induces on `Rⁿ P'`. -/
theorem map_comp_map {X : 𝒳} {N N' : 𝒳'} (u : X ⟶ H.obj N) (g : N ⟶ N') (n : ℕ) :
    map P P' H K e (u ≫ H.map g) n =
      map P P' H K e u n ≫ K.map ((P'.rightDerived n).map g) := by
  let J := injectiveResolution N
  let J' := injectiveResolution N'
  let β : J.cocomplex ⟶ J'.cocomplex := InjectiveResolution.desc g J' J
  have hβ : aug J ≫ β.f 0 = g ≫ aug J' := InjectiveResolution.desc_commutes_zero g J' J
  let c := comparison H u ≫ (H.mapHomologicalComplex _).map β
  have hc : aug (injectiveResolution X) ≫ c.f 0 = (u ≫ H.map g) ≫ H.map (aug J') := by
    show aug (injectiveResolution X) ≫ (comparison H u).f 0 ≫ H.map (β.f 0) = _
    rw [aug_comp_comparison_f_zero_assoc, assoc, ← H.map_comp, hβ, H.map_comp]
  rw [map_eq_mapOf P P' H K e _ _ J' c hc]
  simpa [map, c] using mapOf_naturality P P' H K e (𝟙 X) g _ _ J J' (𝟙 _) β (by simp) hβ
    (comparison H u) n

/-- **The map attached to an identity, for `H` the identity functor**, computed on the chosen
injective resolution: it is the comparison `Hⁿ(P I) ⟶ K(Hⁿ(P' I))` of the left exact functor
`K`, read through `e`. -/
theorem map_id_eq [(𝟭 𝒳).PreservesInjectiveObjects] (P : 𝒳 ⥤ ℬ) (P' : 𝒳 ⥤ ℬ') (K : ℬ' ⥤ ℬ)
    [P.Additive] [P'.Additive] [K.Additive] [PreservesFiniteLimits K] (e : 𝟭 𝒳 ⋙ P ≅ P' ⋙ K)
    (X : 𝒳) (n : ℕ) :
    map P P' (𝟭 𝒳) K e (𝟙 X) n =
      (rdIso (injectiveResolution X) P n).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex e.hom _).app (injectiveResolution X).cocomplex) n ≫
        homologyToMapHomology K ((P'.mapHomologicalComplex _).obj
          (injectiveResolution X).cocomplex) n ≫
        K.map (rdIso (injectiveResolution X) P' n).inv := by
  rw [map_eq_mapOf P P' (𝟭 𝒳) K e (𝟙 X) (injectiveResolution X) (injectiveResolution X)
    (𝟙 (injectiveResolution X).cocomplex) (by simp)]
  unfold mapOf complexMap
  rw [CategoryTheory.Functor.map_id, id_comp]

end Def

/-- The homology comparison of a left exact functor is natural in the functor. -/
@[reassoc]
lemma homologyMap_app_comp_homologyToMapHomology {ι : Type*} {c : ComplexShape ι}
    {Q Q' : ℬ' ⥤ ℬ} [Q.Additive] [Q'.Additive] [PreservesFiniteLimits Q]
    [PreservesFiniteLimits Q'] (α : Q ⟶ Q') (C : HomologicalComplex ℬ' c) (i : ι) :
    HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex α c).app C) i ≫
        homologyToMapHomology Q' C i =
      homologyToMapHomology Q C i ≫ α.app (C.homology i) := by
  rw [← cancel_epi (((Q.mapHomologicalComplex c).obj C).homologyπ i),
    HomologicalComplex.homologyπ_naturality_assoc, homologyπ_comp_homologyToMapHomology,
    homologyπ_comp_homologyToMapHomology_assoc, α.naturality, ← cancel_epi (mapCycles Q C i),
    ← mapCyclesIso_hom, Iso.hom_inv_id_assoc]
  have h : mapCycles Q C i ≫ HomologicalComplex.cyclesMap
      ((NatTrans.mapHomologicalComplex α c).app C) i ≫ (mapCyclesIso Q' C i).inv =
      α.app (C.cycles i) := by
    rw [← cancel_mono (mapCyclesIso Q' C i).hom, assoc, assoc, Iso.inv_hom_id, comp_id,
      mapCyclesIso_hom, ← cancel_mono (((Q'.mapHomologicalComplex c).obj C).iCycles i), assoc,
      HomologicalComplex.cyclesMap_i, mapCycles_i_assoc, assoc, mapCycles_i,
      NatTrans.mapHomologicalComplex_app_f, α.naturality]
  rw [← assoc, ← reassoc_of% h, mapCyclesIso_hom, assoc]

section Comp

variable {𝒳'' : Type u₅} [Category.{v₅} 𝒳''] [Abelian 𝒳''] [HasInjectiveResolutions 𝒳'']
  {ℬ'' : Type u₆} [Category.{v₆} ℬ''] [Abelian ℬ'']
  (P : 𝒳 ⥤ ℬ) (P' : 𝒳' ⥤ ℬ') (P'' : 𝒳'' ⥤ ℬ'')
  (H₁ : 𝒳' ⥤ 𝒳) (K₁ : ℬ' ⥤ ℬ) (H₂ : 𝒳'' ⥤ 𝒳') (K₂ : ℬ'' ⥤ ℬ') (H : 𝒳'' ⥤ 𝒳) (K : ℬ'' ⥤ ℬ)
  [P.Additive] [P'.Additive] [P''.Additive] [H₁.Additive] [H₂.Additive] [H.Additive]
  [K₁.Additive] [K₂.Additive] [K.Additive] [PreservesFiniteLimits K₁]
  [PreservesFiniteLimits K₂] [PreservesFiniteLimits K]
  [H₁.PreservesInjectiveObjects] [H₂.PreservesInjectiveObjects] [H.PreservesInjectiveObjects]
  (e₁ : H₁ ⋙ P ≅ P' ⋙ K₁) (e₂ : H₂ ⋙ P' ≅ P'' ⋙ K₂) (e : H ⋙ P ≅ P'' ⋙ K)
  (ηH : H₂ ⋙ H₁ ≅ H) (ηK : K₂ ⋙ K₁ ≅ K)

/-- **The composition law.** For two stacked situations whose composite is identified with a
third one through `ηH : H₂ ⋙ H₁ ≅ H` and `ηK : K₂ ⋙ K₁ ≅ K`, compatibly with the three
identifications of composite functors, the map attached to the composite morphism
`X ⟶ H₁ N ⟶ H₁ H₂ Z ≅ H Z` is the composite of the two maps. -/
theorem map_comp
    (he : ∀ Z, e.hom.app Z = P.map (ηH.inv.app Z) ≫ e₁.hom.app (H₂.obj Z) ≫
      K₁.map (e₂.hom.app Z) ≫ ηK.hom.app (P''.obj Z))
    {X : 𝒳} {N : 𝒳'} {Z : 𝒳''} (u₁ : X ⟶ H₁.obj N) (u₂ : N ⟶ H₂.obj Z) (n : ℕ) :
    map P P'' H K e (u₁ ≫ H₁.map u₂ ≫ ηH.hom.app Z) n =
      map P P' H₁ K₁ e₁ u₁ n ≫ K₁.map (map P' P'' H₂ K₂ e₂ u₂ n) ≫
        ηK.hom.app ((P''.rightDerived n).obj Z) := by
  let I := injectiveResolution X
  let J := injectiveResolution N
  let L := injectiveResolution Z
  let c₁ := comparison H₁ u₁
  let c₂ := comparison H₂ u₂
  let c : I.cocomplex ⟶ (H.mapHomologicalComplex _).obj L.cocomplex :=
    c₁ ≫ (H₁.mapHomologicalComplex _).map c₂ ≫
      (NatTrans.mapHomologicalComplex ηH.hom _).app L.cocomplex
  have hc : aug I ≫ c.f 0 = (u₁ ≫ H₁.map u₂ ≫ ηH.hom.app Z) ≫ H.map (aug L) := by
    show aug I ≫ c₁.f 0 ≫ H₁.map (c₂.f 0) ≫ ηH.hom.app (L.cocomplex.X 0) = _
    rw [aug_comp_comparison_f_zero_assoc, ← H₁.map_comp_assoc, aug_comp_comparison_f_zero,
      H₁.map_comp, assoc, assoc, assoc]
    congr 2
    exact ηH.hom.naturality (aug L)
  rw [map_eq_mapOf P P'' H K e _ I L c hc]
  have hcx : complexMap P P'' H K e c =
      complexMap P P' H₁ K₁ e₁ c₁ ≫ (K₁.mapHomologicalComplex _).map
        (complexMap P' P'' H₂ K₂ e₂ c₂) ≫
        (NatTrans.mapHomologicalComplex ηK.hom _).app
          ((P''.mapHomologicalComplex _).obj L.cocomplex) := by
    ext m
    simp only [HomologicalComplex.comp_f, complexMap_f, Functor.mapHomologicalComplex_map_f,
      NatTrans.mapHomologicalComplex_app_f, he, K₁.map_comp, c, P.map_comp, assoc]
    rw [← P.map_comp_assoc (ηH.hom.app _), Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      id_comp]
    congr 1
    exact e₁.hom.naturality_assoc (c₂.f m) _
  unfold map mapOf
  rw [hcx, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  simp only [assoc]
  congr 2
  simp only [K₁.map_comp, assoc]
  rw [← K₁.map_comp_assoc (rdIso _ P' n).inv, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    id_comp, ← homologyToMapHomology_naturality_assoc]
  congr 1
  rw [homologyMap_app_comp_homologyToMapHomology_assoc, homologyToMapHomology_comp, assoc]
  congr 2
  exact (ηK.hom.naturality _).symm

end Comp

section Adjoint

variable (P : 𝒳 ⥤ ℬ) (P' : 𝒳' ⥤ ℬ') (H : 𝒳' ⥤ 𝒳) (K : ℬ' ⥤ ℬ) {L : ℬ ⥤ ℬ'} (adj : L ⊣ K)
  [P.Additive] [P'.Additive] [H.Additive] [K.Additive] [L.Additive] [PreservesFiniteLimits K]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (e : H ⋙ P ≅ P' ⋙ K)

/-- **The adjoint of the map**, for `K` a right adjoint with exact left adjoint `L`: on given
resolutions it is `L(Rⁿ P X) ≅ L(Hⁿ(P I)) ≅ Hⁿ(L(P I)) ⟶ Hⁿ(P' J) ≅ Rⁿ P' N`, the middle arrow
induced by the adjoint of the morphism of complexes `P I ⟶ K (P' J)`. -/
theorem homEquiv_symm_mapOf {X : 𝒳} {N : 𝒳'} (I : InjectiveResolution X)
    (J : InjectiveResolution N)
    (c : I.cocomplex ⟶ (H.mapHomologicalComplex _).obj J.cocomplex) (n : ℕ) :
    (adj.homEquiv _ _).symm (mapOf P P' H K e I J c n) =
      L.map (rdIso I P n).hom ≫ inv (homologyToMapHomology L _ n) ≫
        HomologicalComplex.homologyMap (adjointHom adj (complexMap P P' H K e c)) n ≫
          (rdIso J P' n).inv := by
  rw [Equiv.symm_apply_eq, Adjunction.homEquiv_unit]
  unfold mapOf
  rw [← assoc (HomologicalComplex.homologyMap _ n), homologyMap_comp_homologyToMapHomology_eq adj]
  simp only [CategoryTheory.Functor.map_comp, assoc]
  rw [← adj.unit_naturality_assoc]

end Adjoint

end Stacks.Cohomology.RelativePullback

end
