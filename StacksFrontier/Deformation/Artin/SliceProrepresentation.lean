module

public import StacksFrontier.Deformation.Artin.SliceTangentSpace
public import StacksFrontier.Deformation.CofiberedPresentation.SmoothPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteObjectOfFinitePresentation
public import StacksFrontier.Deformation.Artin.ChangeOfField.Equivalence
public import StacksFrontier.Deformation.Completed.CompletionPoints
public import StacksFrontier.Deformation.ResidueField.SeparableExtension

/-!
# The deformations of a point of a scheme are its points in an affine chart

Let `V` be a scheme of the big fppf site over `S`, let `v₀ : Spec k ⟶ V` be a point over a field
`k` lying over an affine open `Spec Λ ⊆ S`, and let `c` be an affine chart `Spec R ⊆ V` at the
image of `v₀` lying over `Spec Λ`. A deformation of `v₀` over an Artinian local `Λ`-algebra `A`
with residue field `k` is a morphism `Spec A ⟶ V` restricting to `v₀`; since `Spec A` has one
point it lands in the chart, so it is a `Λ`-algebra map `R ⟶ A` lifting the ring map `R ⟶ k` of
`v₀`. This file proves that the deformation category `𝓕_{(Sch/V),k,v₀}` is equivalent over `𝒞_Λ`
to the category of elements of the functor `A ↦ {R ⟶ A lifting R ⟶ k}`.

## Main definitions

* `Deformation.Artin.SliceTangent.chartPoints`: the functor `A ↦ {R ⟶ A lifting R ⟶ k}`.
* `Deformation.Artin.SliceTangent.sliceToChartPoints`: the comparison functor.

## Main results

* `Deformation.Artin.SliceTangent.sliceChartPointsEquivalence`: the equivalence over `𝒞_Λ`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Deformation.Artin.SliceTangent

universe u

attribute [local implicit_reducible]
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.mk
  CategoryTheory.Functor.Fiber.fiberInclusion

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {V : BigFppfOver B S hS}
variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
variable {v₀ : Over V}
variable {hv₀ : (Over.forget V ⋙ Over.post B.inclusion).obj v₀ =
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
variable [IsOpenImmersion iΛ] (c : AffineChart iΛ (B.inclusion.map V.hom)
  ((pointMap hv₀).base (closedPt (.of k))))

/-- The ring map out of the chart of the point `v₀`. -/
noncomputable abbrev pointValue : c.ring ⟶ CommRingCat.of k :=
  c.ringMap (pointMap hv₀) (range_pointMap c)

/-- The points of the chart lifting `v₀`: the functor `A ↦ {R ⟶ A lifting R ⟶ k}` on `𝒞_Λ`. -/
noncomputable def chartPoints : ArtinianLocalAlgCat.{u, u, u} Λ k ⥤ Type u where
  obj A := {ψ : c.ring ⟶ CommRingCat.of A //
    c.structureMap ≫ ψ = CommRingCat.ofHom (algebraMap Λ A) ∧
      ψ ≫ CommRingCat.ofHom (residueMap A) = pointValue c}
  map {A A'} β := ↾fun ψ => ⟨ψ.1 ≫ CommRingCat.ofHom β.hom.toRingHom, by
      rw [← Category.assoc, ψ.2.1]
      ext a
      exact β.hom.commutes a, by
      rw [Category.assoc, ← CommRingCat.ofHom_comp, residueMap_comp]; exact ψ.2.2⟩
  map_id A := by
    ext ψ : 3
    apply Subtype.ext
    change (ψ : c.ring ⟶ CommRingCat.of A) ≫ CommRingCat.ofHom (AlgHom.id Λ A).toRingHom = ψ.1
    rw [show (AlgHom.id Λ A).toRingHom = RingHom.id A from rfl, CommRingCat.ofHom_id,
      Category.comp_id]
  map_comp f g := by
    ext ψ : 3
    apply Subtype.ext
    change (ψ : c.ring ⟶ _) ≫ CommRingCat.ofHom (g.hom.comp f.hom).toRingHom =
      ((ψ : c.ring ⟶ _) ≫ CommRingCat.ofHom f.hom.toRingHom) ≫ CommRingCat.ofHom g.hom.toRingHom
    rw [Category.assoc]
    rfl

/-- The point of the chart attached to a deformation. -/
noncomputable def chartPointOf (a : (sliceDeformations iΛ v₀ hv₀).carrier) :
    (chartPoints c).obj ((sliceDeformations iΛ v₀ hv₀).projection.obj a) :=
  ⟨chartValue c ((sliceDeformations iΛ v₀ hv₀).objects a)
      ((sliceDeformations iΛ v₀ hv₀).object_projection a).symm,
    structureMap_chartValue c _ _, chartValue_residue c _ _⟩

/-- The functor `chartPoints c` acts on a point `ψ : R ⟶ A` by composing with the map `A ⟶ A'`. -/
@[simp]
theorem chartPoints_map_val {A A' : ArtinianLocalAlgCat.{u, u, u} Λ k} (β : A ⟶ A')
    (ψ : (chartPoints c).obj A) :
    ((chartPoints c).map β ψ).1 = ψ.1 ≫ CommRingCat.ofHom β.hom.toRingHom := rfl

/-- The point of the chart attached to a deformation is natural in morphisms of deformations. -/
theorem chartPointOf_map {a b : (sliceDeformations iΛ v₀ hv₀).carrier} (f : a ⟶ b) :
    (chartPoints c).map ((sliceDeformations iΛ v₀ hv₀).projection.map f) (chartPointOf c a) =
      chartPointOf c b :=
  Subtype.ext (chartValue_of_morphism c _ _ ((sliceDeformations iΛ v₀ hv₀).morphisms a b f) _
    ((sliceDeformations iΛ v₀ hv₀).morphism_projection f).symm).symm

/-- **The comparison functor** from the deformations of `v₀` to the points of the chart. -/
noncomputable def sliceToChartPoints :
    (sliceDeformations iΛ v₀ hv₀).carrier ⥤ (chartPoints c).Elements where
  obj a := (chartPoints c).elementsMk ((sliceDeformations iΛ v₀ hv₀).projection.obj a)
    (chartPointOf c a)
  map f := Functor.Elements.homMk ((sliceDeformations iΛ v₀ hv₀).projection.map f)
    (chartPointOf_map c f)
  map_id a := Functor.Elements.hom_ext ((sliceDeformations iΛ v₀ hv₀).projection.map_id a)
  map_comp f g :=
    Functor.Elements.hom_ext ((sliceDeformations iΛ v₀ hv₀).projection.map_comp f g)

/-- The comparison functor commutes with the projections to `𝒞_Λ`. -/
theorem sliceToChartPoints_comp_π :
    sliceToChartPoints c ⋙ Functor.Elements.π (chartPoints c) =
      (sliceDeformations iΛ v₀ hv₀).projection := rfl

/-- The comparison functor is faithful. -/
instance : (sliceToChartPoints c).Faithful where
  map_injective {a b} f g h := by
    have h1 : (sliceDeformations iΛ v₀ hv₀).projection.map f =
        (sliceDeformations iΛ v₀ hv₀).projection.map g := congrArg Functor.Elements.Hom.hom h
    apply ((sliceDeformations iΛ v₀ hv₀).morphisms a b).injective
    apply deformationMorphism_ext_of_ringHom
    rw [← (sliceDeformations iΛ v₀ hv₀).morphism_projection f,
      ← (sliceDeformations iΛ v₀ hv₀).morphism_projection g, h1]

omit [IsOpenImmersion iΛ] in
/-- Changing the name of the algebra of a chart value along an equality. -/
theorem chartValue_trans
    (x : DeformationObject iΛ (Over.forget V ⋙ Over.post B.inclusion) v₀ hv₀)
    {A A' : ArtinianLocalAlgCat.{u, u, u} Λ k} (hx : x.algebra = A) (e : A = A') :
    chartValue c x (hx.trans e) =
      chartValue c x hx ≫ CommRingCat.ofHom (eqToHom e).hom.toRingHom := by
  subst e
  rw [eqToHom_refl, ArtinianLocalAlgCat.id_hom]
  rw [show (AlgHom.id Λ A).toRingHom = RingHom.id A from rfl, CommRingCat.ofHom_id,
    Category.comp_id]

/-- Transport along an equality of algebras and back is the identity. -/
theorem comp_ofHom_eqToHom_symm_comp {R : CommRingCat.{u}}
    {A A' : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (e : A = A') (ψ : R ⟶ CommRingCat.of A') :
    (ψ ≫ CommRingCat.ofHom (eqToHom e.symm).hom.toRingHom) ≫
      CommRingCat.ofHom (eqToHom e).hom.toRingHom = ψ := by
  subst e
  rw [eqToHom_refl, ArtinianLocalAlgCat.id_hom]
  rw [show (AlgHom.id Λ A).toRingHom = RingHom.id A from rfl, CommRingCat.ofHom_id,
    Category.comp_id, Category.comp_id]

/-- If the deformation category is cofibered in groupoids, the comparison functor is full. -/
theorem full_sliceToChartPoints
    (hcof : IsCofiberedInGroupoids (sliceDeformations iΛ v₀ hv₀).projection) :
    (sliceToChartPoints c).Full where
  map_surjective {a b} φ := by
    let C := sliceDeformations iΛ v₀ hv₀
    let β : C.projection.obj a ⟶ C.projection.obj b := φ.1
    obtain ⟨a', ι, hι⟩ := exists_pushforward hcof β a rfl
    have ha' : C.projection.obj a' = C.projection.obj b := IsHomLift.codomain_eq _ β ι
    have hιmap : C.projection.map ι = β ≫ eqToHom ha'.symm := by
      simpa using IsHomLift.fac' C.projection β ι
    have hval : (chartPoints c).map (C.projection.map ι) (chartPointOf c a) =
        chartPointOf c a' := chartPointOf_map c ι
    have hφ : (chartPoints c).map β (chartPointOf c a) = chartPointOf c b := φ.2
    rw [hιmap, Functor.map_comp_apply, hφ] at hval
    have hx : (C.objects a').algebra = C.projection.obj b :=
      (C.object_projection a').symm.trans ha'
    have hx' : (C.objects b).algebra = C.projection.obj b := (C.object_projection b).symm
    have heq : chartValue c (C.objects a') hx = chartValue c (C.objects b) hx' := by
      have h1 := congrArg Subtype.val hval
      change chartValue c (C.objects b) hx' ≫
        CommRingCat.ofHom (eqToHom ha'.symm).hom.toRingHom =
          chartValue c (C.objects a') (C.object_projection a').symm at h1
      rw [chartValue_trans c (C.objects a') (C.object_projection a').symm ha', ← h1]
      exact comp_ofHom_eqToHom_symm_comp ha' _
    obtain ⟨m, hm⟩ := exists_morphism_of_chartValue_eq c hx hx' heq
    refine ⟨ι ≫ (C.morphisms a' b).symm m, ?_⟩
    apply Functor.Elements.hom_ext
    change C.projection.map (ι ≫ (C.morphisms a' b).symm m) = β
    have hm' := C.morphism_projection ((C.morphisms a' b).symm m)
    rw [Equiv.apply_symm_apply, hm] at hm'
    have hm'' : C.projection.map ((C.morphisms a' b).symm m) = eqToHom ha' := by
      have := congrArg (fun t => eqToHom (C.object_projection a') ≫ t ≫
        eqToHom (C.object_projection b).symm) hm'
      simpa using this
    rw [Functor.map_comp, hιmap, hm'']
    simp

/-- An equality of objects of a slice category carries the structure map of one to the
structure map of the other. -/
theorem overHom_eq_eqToHom_comp {C : Type*} [Category C] {T : C} {X Y : Over T} (h : X = Y) :
    X.hom = eqToHom (congrArg Over.left h) ≫ Y.hom := by
  subst h; simp

/-- An `eqToHom` of an object with itself composes away. -/
theorem eqToHom_self_comp {C : Type*} [Category C] {a b : C} (h : a = a) (x : a ⟶ b) :
    eqToHom h ≫ x = x := by simp

/-- A conjugate of a morphism by `eqToHom`s cancelling in pairs is the morphism. -/
theorem eqToHom_comp_eqToHom_comp_comp_eqToHom {C : Type*} [Category C] {a b c : C}
    (h₁ : a = b) (h₂ : b = a) (x : a ⟶ c) (h₃ : c = c) :
    eqToHom h₁ ≫ (eqToHom h₂ ≫ x) ≫ eqToHom h₃ = x := by
  subst h₁; simp

omit [IsOpenImmersion iΛ] in
/-- The ring map out of the chart of the restriction of the chart to `Spec A` along `ψ` is
`ψ`. -/
theorem ringMap_specMap_fromSpec {A : CommRingCat.{u}} (ψ : c.ring ⟶ A)
    (hg : Set.range (Spec.map ψ ≫ c.fromSpec).base ⊆ c.U) :
    c.ringMap (Spec.map ψ ≫ c.fromSpec) hg = ψ := by
  apply Spec.map_injective
  apply (cancel_mono c.fromSpec).mp
  rw [c.spec_ringMap]

/-- **The deformation of `v₀` attached to a point of the chart.** -/
noncomputable def chartPointDeformation
    (hfin : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (A : ArtinianLocalAlgCat.{u, u, u} Λ k) (ψ : (chartPoints c).obj A) :
    DeformationObject iΛ (Over.forget V ⋙ Over.post B.inclusion) v₀ hv₀ := by
  have hft := spec_finiteType_of_residueField_point A iΛ hfin hqc
  haveI := hft.1
  haveI := hft.2
  have hA : B.Contains (Spec (.of A)) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
      (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) hS
  let g : Spec (.of A) ⟶ (BigFppfOver.toScheme B S hS).obj V := Spec.map ψ.1 ≫ c.fromSpec
  have hg : g ≫ B.inclusion.map V.hom = Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ := by
    change (Spec.map ψ.1 ≫ c.fromSpec) ≫ B.inclusion.map V.hom = _
    rw [Category.assoc, ← c.spec_structureMap, ← Category.assoc, ← Spec.map_comp, ψ.2.1]
  let W := BigFppfOver.siteObjectOver B S hS V hA g
  have hbase : (Over.forget V ⋙ Over.post B.inclusion).obj
      (Over.mk (BigFppfOver.siteMapOver B S hS V hA g)) =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) := by
    change Over.mk (g ≫ B.inclusion.map V.hom) = _
    rw [hg]
  have hv : B.inclusion.map v₀.left.hom =
      eqToHom (congrArg Over.left hv₀) ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ :=
    overHom_eq_eqToHom_comp hv₀
  let u₀ : v₀.left.left ⟶ W.left :=
    B.inclusion.preimage (eqToHom (congrArg Over.left hv₀) ≫
      Spec.map (CommRingCat.ofHom (residueMap A)))
  have hu₀ : B.inclusion.map u₀ = eqToHom (congrArg Over.left hv₀) ≫
      Spec.map (CommRingCat.ofHom (residueMap A)) := B.inclusion.map_preimage _
  have hres : Spec.map (CommRingCat.ofHom (residueMap A)) ≫ g = pointMap hv₀ := by
    change Spec.map (CommRingCat.ofHom (residueMap A)) ≫ Spec.map ψ.1 ≫ c.fromSpec = _
    rw [← Category.assoc, ← Spec.map_comp, ψ.2.2, c.spec_ringMap]
  have hpt : pointMap hv₀ = eqToHom (congrArg Over.left hv₀).symm ≫
      B.inclusion.map v₀.hom.left := rfl
  have w₁ : u₀ ≫ (BigFppfOver.siteMapOver B S hS V hA g).left = v₀.hom.left := by
    apply B.inclusion.map_injective
    rw [Functor.map_comp, hu₀]
    change (eqToHom (congrArg Over.left hv₀) ≫ Spec.map (CommRingCat.ofHom (residueMap A))) ≫ g =
      B.inclusion.map v₀.hom.left
    rw [Category.assoc, hres, hpt]
    simp
  have w₀ : u₀ ≫ W.hom = v₀.left.hom := by
    have h1 : (BigFppfOver.siteMapOver B S hS V hA g).left ≫ V.hom = W.hom :=
      Over.w (BigFppfOver.siteMapOver B S hS V hA g)
    have h2 : v₀.hom.left ≫ V.hom = v₀.left.hom := Over.w v₀.hom
    rw [← h1, ← Category.assoc, w₁, h2]
  let uo : v₀.left ⟶ W := Over.homMk u₀ w₀
  let arrow : v₀ ⟶ Over.mk (BigFppfOver.siteMapOver B S hS V hA g) :=
    Over.homMk uo (Over.OverMorphism.ext w₁)
  exact
    { algebra := A
      point := Over.mk (BigFppfOver.siteMapOver B S hS V hA g)
      arrow := arrow
      base := hbase
      arrow_base := by
        change eqToHom _ ≫ B.inclusion.map u₀ ≫ eqToHom _ = _
        rw [hu₀]
        exact eqToHom_comp_eqToHom_comp_comp_eqToHom _ _ _ _ }

/-- The chart value of the deformation attached to a point `ψ` of the chart is `ψ`. -/
theorem chartValue_chartPointDeformation
    (hfin : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (A : ArtinianLocalAlgCat.{u, u, u} Λ k) (ψ : (chartPoints c).obj A) :
    chartValue c (chartPointDeformation c hfin hqc A ψ) rfl = ψ.1 := by
  have h : chartPointMap (chartPointDeformation c hfin hqc A ψ) rfl =
      Spec.map ψ.1 ≫ c.fromSpec := by
    rw [chartPointMap, eqToHom_refl, specMap_id, Category.id_comp]
    change eqToHom _ ≫ (Spec.map ψ.1 ≫ c.fromSpec) = _
    exact eqToHom_self_comp _ _
  rw [chartValue, AffineChart.ringMap_congr c _ (h ▸ range_chartPointMap c _ rfl) h]
  exact ringMap_specMap_fromSpec c ψ.1 _

/-- The comparison functor is essentially surjective. -/
theorem essSurj_sliceToChartPoints
    (hfin : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    (sliceToChartPoints c).EssSurj where
  mem_essImage y := by
    let C := sliceDeformations iΛ v₀ hv₀
    obtain @⟨A, ψ⟩ := y
    let d := chartPointDeformation c hfin hqc A ψ
    let a := C.objects.symm d
    have hd : C.objects a = d := Equiv.apply_symm_apply _ _
    have hA : C.projection.obj a = A := (C.object_projection a).trans (congrArg _ hd)
    have hval : (chartPoints c).map (eqToHom hA) (chartPointOf c a) = ψ := by
      apply Subtype.ext
      change chartValue c (C.objects a) (C.object_projection a).symm ≫
        CommRingCat.ofHom (eqToHom hA).hom.toRingHom = ψ.1
      rw [← chartValue_trans]
      have key : ∀ (x : DeformationObject iΛ (Over.forget V ⋙ Over.post B.inclusion) v₀ hv₀)
          (hx : x = d) (h : x.algebra = A), chartValue c x h = ψ.1 := by
        intro x hx h
        subst hx
        exact chartValue_chartPointDeformation c hfin hqc A ψ
      exact key _ hd _
    let m : (sliceToChartPoints c).obj a ⟶ (chartPoints c).elementsMk A ψ := ⟨eqToHom hA, hval⟩
    have : IsIso ((Functor.Elements.π (chartPoints c)).map m) :=
      show IsIso (eqToHom hA) from inferInstance
    have : IsIso m := isIso_of_isCofiberedInGroupoids_of_map_isIso
      (Deformation.isCofiberedInGroupoids_elementsProjection (chartPoints c)) m
    exact ⟨a, ⟨asIso m⟩⟩

/-- **The deformations of a point of a scheme are the points of an affine chart lifting it**:
the comparison functor is an equivalence over `𝒞_Λ`. -/
noncomputable def sliceChartPointsEquivalence
    (hfin : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hcof : IsCofiberedInGroupoids (sliceDeformations iΛ v₀ hv₀).projection) :
    StacksRepresentableCFG.EquivalenceOver (sliceDeformations iΛ v₀ hv₀).projection
      (Functor.Elements.π (chartPoints c)) :=
  haveI := full_sliceToChartPoints c hcof
  haveI := essSurj_sliceToChartPoints c hfin hqc
  equivalenceOverOfCofibered hcof (sliceToChartPoints c) (sliceToChartPoints_comp_π c)

/-! ### The points of the chart are prorepresented by a completion -/

section Completion

variable [IsNoetherianRing Λ] [Module.Finite Λ k]
  {K : Type u} [Field K] [Algebra Λ K] [Algebra K k] [IsScalarTower Λ K k]
  [Module.Finite Λ K] [Module.Finite K k]

/-- The tower `Λ → K → k` of a residue field `K` of the chart below `k`. -/
@[implicit_reducible] noncomputable def chartTower : ChangeOfFieldsSituation.{u, u, u} where
  Λ := Λ
  k := K
  l := k

/-- The chart ring as a `Λ`-algebra. -/
@[implicit_reducible] noncomputable def chartAlgebra : Algebra Λ c.ring :=
  c.structureMap.hom.toAlgebra

attribute [local instance] chartAlgebra

/-- The chart ring as an algebra over the base ring of `chartTower`. -/
noncomputable local instance chartTowerAlgebra :
    Algebra (chartTower (Λ := Λ) (k := k) (K := K)).Λ c.ring :=
  chartAlgebra c

/-- An object of `𝒞` of `chartTower` as a `Λ`-algebra. -/
local instance chartTowerObjAlgebra
    (T : ArtinianLocalAlgCat.{u, u, u} (chartTower (Λ := Λ) (k := k) (K := K)).Λ
      (chartTower (Λ := Λ) (k := k) (K := K)).k) : Algebra Λ T :=
  inferInstanceAs (Algebra (chartTower (Λ := Λ) (k := k) (K := K)).Λ T)

omit [Module.Finite Λ k] in
/-- A point of the chart has residue the image of `q`, when `R → k` factors through `q`. -/
theorem residueMap_chartPoint (q : c.ring →ₐ[Λ] K)
    (hχ : ∀ r : c.ring, algebraMap K k (q r) = (pointValue c).hom r)
    (T : ArtinianLocalAlgCat.{u, u, u} Λ k) (ψ : (chartPoints c).obj T) (x : c.ring) :
    Deformation.residueMap (chartTower (Λ := Λ) (k := k) (K := K)) T (ψ.1.hom x) =
      algebraMap K k (q x) := by
  rw [hχ]
  exact congrArg (fun φ : c.ring ⟶ CommRingCat.of k => φ.hom x) ψ.2.2

/-- A point `ψ` of the chart, paired with `q`, as a ring map into the pullback `T ×_k K`. -/
noncomputable def chartPointPullbackHom (q : c.ring →ₐ[Λ] K)
    (hχ : ∀ r : c.ring, algebraMap K k (q r) = (pointValue c).hom r)
    (T : ArtinianLocalAlgCat.{u, u, u} Λ k) (ψ : (chartPoints c).obj T) :
    c.ring →+* RingHom.pullback
      (Deformation.residueMap (chartTower (Λ := Λ) (k := k) (K := K)) T) (algebraMap K k) :=
  (ψ.1.hom.prod q.toRingHom).codRestrict _ (residueMap_chartPoint c q hχ T ψ)

/-- A point `ψ` of the chart, paired with `q`, as a `Λ`-algebra map into `T ×_k K`. -/
noncomputable def chartPointToPullback (q : c.ring →ₐ[Λ] K)
    (hχ : ∀ r : c.ring, algebraMap K k (q r) = (pointValue c).hom r)
    (T : ArtinianLocalAlgCat.{u, u, u} Λ k) (ψ : (chartPoints c).obj T) :
    c.ring →ₐ[Λ] (comparisonFunctor (chartTower (Λ := Λ) (k := k) (K := K))).functor.obj T where
  toRingHom := ((comparisonFunctor (chartTower (Λ := Λ) (k := k) (K := K))).pullbackEquiv
    T).symm.toRingHom.comp (chartPointPullbackHom c q hχ T ψ)
  commutes' r := by
    let cmp := comparisonFunctor (chartTower (Λ := Λ) (k := k) (K := K))
    have h := RingEquiv.apply_symm_apply (cmp.pullbackEquiv T)
      (chartPointPullbackHom c q hχ T ψ (algebraMap Λ c.ring r))
    apply (cmp.pullbackEquiv T).injective
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · exact (congrArg (fun z => z.val.1) h).trans
        ((congrArg (fun φ : CommRingCat.of Λ ⟶ CommRingCat.of T => φ.hom r) ψ.2.1).trans
          (cmp.algebraMap_fst T r).symm)
    · exact (congrArg (fun z => z.val.2) h).trans
        ((q.commutes r).trans (cmp.algebraMap_snd T r).symm)

omit [Module.Finite Λ k] in
/-- The first component of `chartPointToPullback c q hχ T ψ` in `T ×_k K` is `ψ`. -/
theorem chartPointToPullback_fst (q : c.ring →ₐ[Λ] K)
    (hχ : ∀ r : c.ring, algebraMap K k (q r) = (pointValue c).hom r)
    (T : ArtinianLocalAlgCat.{u, u, u} Λ k) (ψ : (chartPoints c).obj T) (x : c.ring) :
    ((comparisonFunctor (chartTower (Λ := Λ) (k := k) (K := K))).pullbackEquiv T
      (chartPointToPullback c q hχ T ψ x)).val.1 = ψ.1.hom x :=
  congrArg (fun z => z.val.1) (RingEquiv.apply_symm_apply
    ((comparisonFunctor (chartTower (Λ := Λ) (k := k) (K := K))).pullbackEquiv T)
    (chartPointPullbackHom c q hχ T ψ x))

omit [Module.Finite Λ k] in
/-- The second component of `chartPointToPullback c q hχ T ψ` in `T ×_k K` is `q`. -/
theorem chartPointToPullback_snd (q : c.ring →ₐ[Λ] K)
    (hχ : ∀ r : c.ring, algebraMap K k (q r) = (pointValue c).hom r)
    (T : ArtinianLocalAlgCat.{u, u, u} Λ k) (ψ : (chartPoints c).obj T) (x : c.ring) :
    ((comparisonFunctor (chartTower (Λ := Λ) (k := k) (K := K))).pullbackEquiv T
      (chartPointToPullback c q hχ T ψ x)).val.2 = q x :=
  congrArg (fun z => z.val.2) (RingEquiv.apply_symm_apply
    ((comparisonFunctor (chartTower (Λ := Λ) (k := k) (K := K))).pullbackEquiv T)
    (chartPointPullbackHom c q hχ T ψ x))

/-- The point of the chart given by a `Λ`-algebra map into `T ×_k K` with residue `q`. -/
noncomputable def chartPointOfPullback (q : c.ring →ₐ[Λ] K)
    (hχ : ∀ r : c.ring, algebraMap K k (q r) = (pointValue c).hom r)
    (T : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (f : c.ring →ₐ[Λ] (comparisonFunctor (chartTower (Λ := Λ) (k := k) (K := K))).functor.obj T)
    (hf : ∀ x, ((comparisonFunctor (chartTower (Λ := Λ) (k := k) (K := K))).functor.obj
      T).residueEquiv (IsLocalRing.residue _ (f x)) = q x) :
    (chartPoints c).obj T :=
  let cmp := comparisonFunctor (chartTower (Λ := Λ) (k := k) (K := K))
  ⟨CommRingCat.ofHom ((RingHom.pullbackFst
      (Deformation.residueMap (chartTower (Λ := Λ) (k := k) (K := K)) T) (algebraMap K k)).comp
      ((cmp.pullbackEquiv T).toRingHom.comp f.toRingHom)), by
    ext r
    exact (congrArg (fun z => (cmp.pullbackEquiv T z).val.1) (f.commutes r)).trans
      (cmp.algebraMap_fst T r), by
    ext x
    exact (cmp.pullbackEquiv T (f x)).property.trans
      ((congrArg (algebraMap K k) ((cmp.residue_snd T (f x)).symm.trans (hf x))).trans (hχ x))⟩

/-- The points of the chart are the `Λ`-algebra maps into `T ×_k K` with residue `q`. -/
noncomputable def chartPointsEquivPullback (q : c.ring →ₐ[Λ] K)
    (hχ : ∀ r : c.ring, algebraMap K k (q r) = (pointValue c).hom r)
    (T : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    (chartPoints c).obj T ≃
      {f : c.ring →ₐ[Λ] (comparisonFunctor (chartTower (Λ := Λ) (k := k) (K := K))).functor.obj T //
        ∀ x, ((comparisonFunctor (chartTower (Λ := Λ) (k := k) (K := K))).functor.obj
          T).residueEquiv (IsLocalRing.residue _ (f x)) = q x} where
  toFun ψ := ⟨chartPointToPullback c q hχ T ψ, fun x =>
    ((comparisonFunctor (chartTower (Λ := Λ) (k := k) (K := K))).residue_snd T
      (chartPointToPullback c q hχ T ψ x)).trans (chartPointToPullback_snd c q hχ T ψ x)⟩
  invFun f := chartPointOfPullback c q hχ T f.1 f.2
  left_inv ψ := Subtype.ext <| by
    ext x
    exact chartPointToPullback_fst c q hχ T ψ x
  right_inv f := by
    let cmp := comparisonFunctor (chartTower (Λ := Λ) (k := k) (K := K))
    apply Subtype.ext
    refine AlgHom.ext fun x => ?_
    apply (cmp.pullbackEquiv T).injective
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · exact chartPointToPullback_fst c q hχ T _ x
    · exact (chartPointToPullback_snd c q hχ T _ x).trans
        ((f.2 x).symm.trans (cmp.residue_snd T (f.1 x)))

omit [Module.Finite Λ k] in
/-- `chartPointToPullback` is natural in `T`: it commutes with the maps induced by `β`. -/
theorem chartPointToPullback_map (q : c.ring →ₐ[Λ] K)
    (hχ : ∀ r : c.ring, algebraMap K k (q r) = (pointValue c).hom r)
    {T T' : ArtinianLocalAlgCat.{u, u, u} Λ k} (β : T ⟶ T') (ψ : (chartPoints c).obj T) :
    chartPointToPullback c q hχ T' ((chartPoints c).map β ψ) =
      ((comparisonFunctor (chartTower (Λ := Λ) (k := k) (K := K))).functor.map β).hom.comp
        (chartPointToPullback c q hχ T ψ) := by
  let cmp := comparisonFunctor (chartTower (Λ := Λ) (k := k) (K := K))
  refine AlgHom.ext fun x => ?_
  apply (cmp.pullbackEquiv T').injective
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · exact (chartPointToPullback_fst c q hχ T' _ x).trans ((cmp.map_fst β _).trans
      (congrArg β.hom (chartPointToPullback_fst c q hχ T ψ x))).symm
  · exact (chartPointToPullback_snd c q hχ T' _ x).trans ((cmp.map_snd β _).trans
      (chartPointToPullback_snd c q hχ T ψ x)).symm

/-- **The points of the chart are the points of the completion over `T ×_k K`.** Let
`q : R → K` be a surjection onto a field `K` below `k` through which the point `R → k` of `v₀`
factors. Then `A ↦ {R → A lifting R → k}` is the functor `A ↦ Hom(R^∧, A ×_k K)`, where `R^∧`
is the completion of `R` at the kernel of `q`. -/
noncomputable def chartPointsIso
    (q : c.ring →ₐ[Λ] K) (hq : Function.Surjective q)
    (hfg : (RingHom.ker q.toRingHom).FG)
    (hχ : ∀ r : c.ring, algebraMap K k (q r) = (pointValue c).hom r) :
    chartPoints c ≅ (comparisonFunctor (chartTower (Λ := Λ) (k := k) (K := K))).functor ⋙
      restrictedCoyoneda (completionObjectOfSurjection q hq hfg) := by
  let cmp := comparisonFunctor (chartTower (Λ := Λ) (k := k) (K := K))
  let e₁ := chartPointsEquivPullback c q hχ
  let e : ∀ T : ArtinianLocalAlgCat.{u, u, u} Λ k,
      (chartPoints c).obj T ≃
        ((cmp.functor ⋙ restrictedCoyoneda (completionObjectOfSurjection q hq hfg)).obj T) :=
    fun T => (e₁ T).trans (completionPointsEquiv q hq hfg (cmp.functor.obj T)).symm
  refine NatIso.ofComponents (fun T => Equiv.toIso (e T)) ?_
  intro T T' β
  ext ψ : 3
  change e T' ((chartPoints c).map β ψ) =
    e T ψ ≫ artinianToComplete.map (cmp.functor.map β)
  apply (completionPointsEquiv q hq hfg (cmp.functor.obj T')).injective
  apply Subtype.ext
  refine (congrArg Subtype.val (Equiv.apply_symm_apply
    (completionPointsEquiv q hq hfg (cmp.functor.obj T')) (e₁ T' ((chartPoints c).map β ψ)))).trans
    (Eq.trans ?_ (completionPointsEquiv_naturality q hq hfg (cmp.functor.map β) (e T ψ)).symm)
  have he : (completionPointsEquiv q hq hfg (cmp.functor.obj T)) (e T ψ) = e₁ T ψ :=
    Equiv.apply_symm_apply _ _
  rw [he]
  exact chartPointToPullback_map c q hχ β ψ

/-- An isomorphism of set-valued functors is an equivalence over the base of their categories
of elements. -/
noncomputable def elementsEquivalenceOverOfIso {C : Type*} [Category C] {P Q : C ⥤ Type u}
    (e : P ≅ Q) :
    StacksRepresentableCFG.EquivalenceOver (Functor.Elements.π P) (Functor.Elements.π Q) :=
  haveI : (NatTrans.mapElements e.hom).Faithful := ⟨fun {a b} f g h =>
    Functor.Elements.hom_ext <| congrArg (fun m : (NatTrans.mapElements e.hom).obj a ⟶
      (NatTrans.mapElements e.hom).obj b => m.hom) h⟩
  haveI : (NatTrans.mapElements e.hom).Full := ⟨fun {a b} f => by
    refine ⟨⟨f.1, ?_⟩, rfl⟩
    have h : Q.map f.1 (e.hom.app a.1 a.2) = e.hom.app b.1 b.2 := f.2
    exact (e.app b.1).toEquiv.injective ((NatTrans.naturality_apply e.hom f.1 a.2).trans h)⟩
  haveI : (NatTrans.mapElements e.hom).EssSurj := ⟨fun y => by
    refine ⟨P.elementsMk y.1 (e.inv.app y.1 y.2), ⟨eqToIso ?_⟩⟩
    change Q.elementsMk y.1 (e.hom.app y.1 (e.inv.app y.1 y.2)) = y
    rw [Iso.inv_hom_id_app_apply]⟩
  Deformation.equivalenceOverOfCofibered
    (Deformation.isCofiberedInGroupoids_elementsProjection P) (NatTrans.mapElements e.hom) rfl

omit [Module.Finite Λ k] in
/-- **The deformations of a point of a scheme are prorepresented by a completion of a chart.**
Let `q : R → K` be a surjection of the chart ring onto a field `K` below `k`, through which the
point `R → k` of `v₀` factors, with `k/K` finite separable. Then the deformation category of
`v₀` is equivalent over `𝒞_Λ` to the category of elements of `Â|_{𝒞_Λ}` for a Noetherian complete
local `Λ`-algebra `Â` with residue field `k` of the dimension of `R_{ker q}`: the extension
`R^∧[X]/(F)` of the completion of `R` at `ker q` (`Deformation.SeparableExtension`). -/
theorem exists_sliceEquivalence_completion
    [LocallyOfFiniteType (B.inclusion.map V.hom)]
    (hfin : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (q : c.ring →ₐ[Λ] K) (hq : Function.Surjective q)
    (hχ : ∀ r : c.ring, algebraMap K k (q r) = (pointValue c).hom r)
    [Algebra.IsSeparable K k] :
    letI : (RingHom.ker q.toRingHom).IsPrime := RingHom.ker_isPrime _
    ∃ A : CompleteLocalAlgCat.{u, u, u} Λ k,
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (Functor.Elements.π (restrictedCoyoneda A)) (sliceDeformations iΛ v₀ hv₀).projection) ∧
      ringKrullDim A = ringKrullDim (Localization.AtPrime (RingHom.ker q.toRingHom)) := by
  let : (RingHom.ker q.toRingHom).IsPrime := RingHom.ker_isPrime _
  have : Algebra.FiniteType Λ c.ring := RingHom.finiteType_algebraMap.mp c.finiteType_structureMap
  have : IsNoetherianRing c.ring := Algebra.FiniteType.isNoetherianRing Λ c.ring
  have hfg : (RingHom.ker q.toRingHom).FG := IsNoetherian.noetherian _
  let S0 := chartTower (Λ := Λ) (k := k) (K := K)
  have : Algebra.IsSeparable S0.k S0.l := ‹Algebra.IsSeparable K k›
  let RK := completionObjectOfSurjection q hq hfg
  let A := SeparableExtension.obj S0 RK
  have hcof := (isDeformationCategory_sliceDeformations (v₀ := v₀) (hv₀ := hv₀) hfin
    hqc).predeformation.cofibered
  let E₁ := sliceChartPointsEquivalence c hfin hqc hcof
  let E₂ := elementsEquivalenceOverOfIso (chartPointsIso c q hq hfg hχ)
  let E₃ := elementsEquivalenceOverOfIso (SeparableExtension.restrictedCoyonedaIso S0 RK)
  refine ⟨A, ⟨((E₁.trans E₂).trans E₃).symm⟩, ?_⟩
  rw [SeparableExtension.ringKrullDim_obj]
  exact ringKrullDim_completionObjectOfSurjection q hq hfg

end Completion

end Deformation.Artin.SliceTangent

end
