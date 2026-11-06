module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericallyFiniteQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalMorphism.SchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalMorphism.ChartFactorization

/-!
# Birational morphisms of algebraic spaces: local rings at generic points and birationality

The stalk of every schematic chart at a generic point is identified with the local ring
`AlgebraicGeometry.Space.genericLocalRing` by a coherent family of isomorphisms
(`AlgebraicGeometry.Space.exists_coherentChartStalkIso`), the induced map of local rings
`AlgebraicGeometry.Space.genericLocalRingMap` is characterized on compatible charts, and
`AlgebraicGeometry.Space.IsBirational` (Stacks 0ACV) is defined and unpacked.

See `StacksFrontier.AlgebraicGeometry.Spaces.BirationalMorphism` for the overview.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Products of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_IsBirational
    (J : Type) : HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  inferInstance

private noncomputable def chartFactorStalkMap
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hdense : HasDenseRepresentableOpenSubspace B S hS F)
    (hfinite : (letI := pointTopology B S hS F
      (irreducibleComponents (points B S hS F)).Finite))
    {x : points B S hS F}
    (hx : letI := pointTopology B S hS F
      x ∈ genericPoints (points B S hS F))
    (c : GenericChart B S hS x) :
    genericLocalRing B S hS hF hdense hfinite x hx ⟶ c.localRing B S hS := by
  let f := (BigFppfOver.toScheme B S hS).map
    (chartFactorHom B S hS hF c)
  have hp := chartFactorHom_point_eq B S hS hF hdense hfinite hx c
  exact eqToHom (congrArg
      (fun z => ((BigFppfOver.toScheme B S hS).obj
        (schematicScheme B S hS hF)).presheaf.stalk z) hp.symm) ≫
    f.stalkMap (schemePoint B S hS c.U c.point)

private noncomputable def chartFactorStalkIso
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hdense : HasDenseRepresentableOpenSubspace B S hS F)
    (hfinite : (letI := pointTopology B S hS F
      (irreducibleComponents (points B S hS F)).Finite))
    {x : points B S hS F}
    (hx : letI := pointTopology B S hS F
      x ∈ genericPoints (points B S hS F))
    (c : GenericChart B S hS x) :
    c.localRing B S hS ≅ genericLocalRing B S hS hF hdense hfinite x hx := by
  let f := (BigFppfOver.toScheme B S hS).map
    (chartFactorHom B S hS hF c)
  have hp := chartFactorHom_point_eq B S hS hF hdense hfinite hx c
  haveI : IsIso (f.stalkMap (schemePoint B S hS c.U c.point)) :=
    (AlgebraicGeometry.IsOpenImmersion.iff_isIso_stalkMap.mp
      (chartFactorHom_isOpenImmersion_scheme B S hS hF c)).2 _
  haveI : IsIso (chartFactorStalkMap B S hS hF hdense hfinite hx c) := by
    change IsIso (eqToHom (congrArg
      (fun z => ((BigFppfOver.toScheme B S hS).obj
        (schematicScheme B S hS hF)).presheaf.stalk z) hp.symm) ≫
      f.stalkMap (schemePoint B S hS c.U c.point))
    infer_instance
  exact (asIso (chartFactorStalkMap B S hS hF hdense hfinite hx c)).symm

private theorem stalkMap_factor_coherent_local
    {C D T : Scheme.{u}} (γ : C ⟶ D) (φd : D ⟶ T) (φc : C ⟶ T)
    (a : C) (b : D) (z : T)
    (hfac : φc = γ ≫ φd) (hpoint : γ a = b)
    (hpC : φc a = z) (hpD : φd b = z) :
    (eqToHom (congrArg (fun w => T.presheaf.stalk w) hpD.symm) ≫
      φd.stalkMap b) ≫
      eqToHom (congrArg (fun w => D.presheaf.stalk w) hpoint.symm) ≫
      γ.stalkMap a =
    eqToHom (congrArg (fun w => T.presheaf.stalk w) hpC.symm) ≫
      φc.stalkMap a := by
  cases hpoint
  cases hfac
  change φd (γ a) = z at hpC
  have hpoints : hpC = hpD := Subsingleton.elim _ _
  rw [Scheme.Hom.stalkMap_comp, hpoints]
  simp [Category.assoc]

private theorem chartFactorStalkIso_coherent_local
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hdense : HasDenseRepresentableOpenSubspace B S hS F)
    (hfinite : (letI := pointTopology B S hS F
      (irreducibleComponents (points B S hS F)).Finite))
    (x : points B S hS F)
    (hx : letI := pointTopology B S hS F
      x ∈ genericPoints (points B S hS F))
    (c d : GenericChart B S hS x) (g : c.U ⟶ d.U)
    (hcomm : c.immersion = yoneda.map g ≫ d.immersion)
    (hpoint : ((BigFppfOver.toScheme B S hS).map g)
      (schemePoint B S hS c.U c.point) =
      schemePoint B S hS d.U d.point) :
    (chartFactorStalkIso B S hS hF hdense hfinite hx d).inv ≫
      eqToHom (congrArg
        (fun z => ((BigFppfOver.toScheme B S hS).obj d.U).presheaf.stalk z)
        hpoint.symm) ≫
      ((BigFppfOver.toScheme B S hS).map g).stalkMap
        (schemePoint B S hS c.U c.point) ≫
      (chartFactorStalkIso B S hS hF hdense hfinite hx c).hom = 𝟙 _ := by
  let T := BigFppfOver.toScheme B S hS
  let φc := T.map (chartFactorHom B S hS hF c)
  let φd := T.map (chartFactorHom B S hS hF d)
  let γ := T.map g
  have : Mono (schematicChart B S hS hF) :=
    AlgebraicGeometry.Space.mono_of_isOpenImmersion B S hS _
      (isOpenImmersion_schematicChart B S hS hF)
  have hfacYoneda : yoneda.map (chartFactorHom B S hS hF c) =
      yoneda.map g ≫ yoneda.map (chartFactorHom B S hS hF d) := by
    apply (cancel_mono (schematicChart B S hS hF)).1
    calc
      yoneda.map (chartFactorHom B S hS hF c) ≫ schematicChart B S hS hF =
          c.immersion := chartFactorHom_fac B S hS hF c
      _ = yoneda.map g ≫ d.immersion := hcomm
      _ = yoneda.map g ≫
          (yoneda.map (chartFactorHom B S hS hF d) ≫ schematicChart B S hS hF) := by
            rw [chartFactorHom_fac]
      _ = (yoneda.map g ≫ yoneda.map (chartFactorHom B S hS hF d)) ≫
          schematicChart B S hS hF := by simp [Category.assoc]
  have hfac : φc = γ ≫ φd := by
    have hhom : chartFactorHom B S hS hF c =
        g ≫ chartFactorHom B S hS hF d := by
      apply yoneda.map_injective
      simpa only [Functor.map_comp] using hfacYoneda
    calc
      φc = T.map (chartFactorHom B S hS hF c) := rfl
      _ = T.map (g ≫ chartFactorHom B S hS hF d) := congrArg T.map hhom
      _ = γ ≫ φd := by simp [φd, γ, Functor.map_comp]
  have hpC := chartFactorHom_point_eq B S hS hF hdense hfinite hx c
  have hpD := chartFactorHom_point_eq B S hS hF hdense hfinite hx d
  have hstalk := stalkMap_factor_coherent_local γ φd φc
    (schemePoint B S hS c.U c.point)
    (schemePoint B S hS d.U d.point)
    (schemePoint B S hS (schematicScheme B S hS hF)
      (schematicRepresentative B S hS hF hdense hfinite x hx))
    hfac hpoint hpC hpD
  have : IsIso (chartFactorStalkMap B S hS hF hdense hfinite hx c) := by
    show IsIso ((chartFactorStalkIso B S hS hF hdense hfinite hx c).inv)
    infer_instance
  have hcompare :
      chartFactorStalkMap B S hS hF hdense hfinite hx d ≫
        eqToHom (congrArg
          (fun z => ((BigFppfOver.toScheme B S hS).obj d.U).presheaf.stalk z)
          hpoint.symm) ≫
        γ.stalkMap (schemePoint B S hS c.U c.point) =
      chartFactorStalkMap B S hS hF hdense hfinite hx c := by
    show (eqToHom (congrArg
        (fun z => (T.obj (schematicScheme B S hS hF)).presheaf.stalk z) hpD.symm) ≫
        φd.stalkMap (schemePoint B S hS d.U d.point)) ≫
        eqToHom (congrArg
          (fun z => (T.obj d.U).presheaf.stalk z) hpoint.symm) ≫
        γ.stalkMap (schemePoint B S hS c.U c.point) =
      eqToHom (congrArg
        (fun z => (T.obj (schematicScheme B S hS hF)).presheaf.stalk z) hpC.symm) ≫
        φc.stalkMap (schemePoint B S hS c.U c.point)
    exact hstalk
  show (chartFactorStalkMap B S hS hF hdense hfinite hx d ≫
      eqToHom (congrArg
        (fun z => ((BigFppfOver.toScheme B S hS).obj d.U).presheaf.stalk z)
        hpoint.symm) ≫
      γ.stalkMap (schemePoint B S hS c.U c.point) ≫
      (asIso (chartFactorStalkMap B S hS hF hdense hfinite hx c)).inv) =
    𝟙 (genericLocalRing B S hS hF hdense hfinite x hx)
  calc
    (chartFactorStalkMap B S hS hF hdense hfinite hx d ≫
        eqToHom (congrArg
          (fun z => ((BigFppfOver.toScheme B S hS).obj d.U).presheaf.stalk z)
          hpoint.symm) ≫
        γ.stalkMap (schemePoint B S hS c.U c.point)) ≫
        (asIso (chartFactorStalkMap B S hS hF hdense hfinite hx c)).inv =
      chartFactorStalkMap B S hS hF hdense hfinite hx c ≫
        (asIso (chartFactorStalkMap B S hS hF hdense hfinite hx c)).inv :=
      congrArg (fun k => k ≫
        (asIso (chartFactorStalkMap B S hS hF hdense hfinite hx c)).inv) hcompare
    _ = 𝟙 (genericLocalRing B S hS hF hdense hfinite x hx) := by simp

/-- A coherent family of canonical identifications between schematic-chart
stalks and the local ring on the schematic locus. -/
theorem exists_coherentChartStalkIso
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hdense : HasDenseRepresentableOpenSubspace B S hS F)
    (hfinite : (letI := pointTopology B S hS F
      (irreducibleComponents (points B S hS F)).Finite))
    (x : points B S hS F)
    (hx : letI := pointTopology B S hS F
      x ∈ genericPoints (points B S hS F)) :
    ∃ e : ∀ c : GenericChart B S hS x,
        c.localRing B S hS ≅ genericLocalRing B S hS hF hdense hfinite x hx,
      e (schematicGenericChart B S hS hF hdense hfinite x hx) = Iso.refl _ ∧
      ∀ (c d : GenericChart B S hS x) (g : c.U ⟶ d.U)
        (_hcomm : c.immersion = yoneda.map g ≫ d.immersion)
        (hpoint : ((BigFppfOver.toScheme B S hS).map g)
          (schemePoint B S hS c.U c.point) =
          schemePoint B S hS d.U d.point),
        (e d).inv ≫
          eqToHom (congrArg
            (fun z => ((BigFppfOver.toScheme B S hS).obj d.U).presheaf.stalk z)
            hpoint.symm) ≫
          ((BigFppfOver.toScheme B S hS).map g).stalkMap
            (schemePoint B S hS c.U c.point) ≫
          (e c).hom = 𝟙 _ := by
  let c₀ := schematicGenericChart B S hS hF hdense hfinite x hx
  let e₀ := chartFactorStalkIso B S hS hF hdense hfinite hx c₀
  let e := fun c => chartFactorStalkIso B S hS hF hdense hfinite hx c ≪≫ e₀.symm
  refine ⟨e, ?_, ?_⟩
  · simp [e, e₀, c₀]; rfl
  · intro c d g hcomm hpoint
    have hn := chartFactorStalkIso_coherent_local B S hS hF hdense hfinite x hx
      c d g hcomm hpoint
    dsimp [e, e₀, c₀] at hn ⊢
    calc
      _ = (chartFactorStalkIso B S hS hF hdense hfinite hx
            (schematicGenericChart B S hS hF hdense hfinite x hx)).hom ≫
          ((chartFactorStalkIso B S hS hF hdense hfinite hx d).inv ≫
            eqToHom (congrArg
              (fun z => ((BigFppfOver.toScheme B S hS).obj d.U).presheaf.stalk z)
              hpoint.symm) ≫
            ((BigFppfOver.toScheme B S hS).map g).stalkMap
              (schemePoint B S hS c.U c.point) ≫
            (chartFactorStalkIso B S hS hF hdense hfinite hx c).hom) ≫
          (chartFactorStalkIso B S hS hF hdense hfinite hx
            (schematicGenericChart B S hS hF hdense hfinite x hx)).inv := by
        simp only [Category.assoc]; rfl
      _ = (chartFactorStalkIso B S hS hF hdense hfinite hx
            (schematicGenericChart B S hS hF hdense hfinite x hx)).hom ≫
          𝟙 _ ≫
          (chartFactorStalkIso B S hS hF hdense hfinite hx
            (schematicGenericChart B S hS hF hdense hfinite x hx)).inv :=
        congrArg (fun k =>
          (chartFactorStalkIso B S hS hF hdense hfinite hx
            (schematicGenericChart B S hS hF hdense hfinite x hx)).hom ≫
          k ≫
          (chartFactorStalkIso B S hS hF hdense hfinite hx
            (schematicGenericChart B S hS hF hdense hfinite x hx)).inv) hn
      _ = 𝟙 _ := by simp

/-- The canonical identification of a chart's stalk with the local ring
on the schematic locus. -/
noncomputable def chartStalkIso
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hdense : HasDenseRepresentableOpenSubspace B S hS F)
    (hfinite : (letI := pointTopology B S hS F
      (irreducibleComponents (points B S hS F)).Finite))
    (x : points B S hS F)
    (hx : letI := pointTopology B S hS F
      x ∈ genericPoints (points B S hS F))
    (c : GenericChart B S hS x) :
    c.localRing B S hS ≅ genericLocalRing B S hS hF hdense hfinite x hx :=
  (exists_coherentChartStalkIso B S hS hF hdense hfinite x hx).choose c

/-- Chart comparisons agree with the local-ring map of every refinement. -/
theorem chartStalkIso_naturality
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hdense : HasDenseRepresentableOpenSubspace B S hS F)
    (hfinite : (letI := pointTopology B S hS F
      (irreducibleComponents (points B S hS F)).Finite))
    (x : points B S hS F)
    (hx : letI := pointTopology B S hS F
      x ∈ genericPoints (points B S hS F))
    (c d : GenericChart B S hS x) (g : c.U ⟶ d.U)
    (hcomm : c.immersion = yoneda.map g ≫ d.immersion)
    (hpoint : ((BigFppfOver.toScheme B S hS).map g)
      (schemePoint B S hS c.U c.point) =
      schemePoint B S hS d.U d.point) :
    (chartStalkIso B S hS hF hdense hfinite x hx d).inv ≫
      eqToHom (congrArg
        (fun z => ((BigFppfOver.toScheme B S hS).obj d.U).presheaf.stalk z)
        hpoint.symm) ≫
      ((BigFppfOver.toScheme B S hS).map g).stalkMap
        (schemePoint B S hS c.U c.point) ≫
      (chartStalkIso B S hS hF hdense hfinite x hx c).hom = 𝟙 _ :=
  (exists_coherentChartStalkIso B S hS hF hdense hfinite x hx).choose_spec.2
    c d g hcomm hpoint

private theorem chartStalkMap_sourceRefine_local
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hdense : HasDenseRepresentableOpenSubspace B S hS F)
    (hfinite : (letI := pointTopology B S hS F
      (irreducibleComponents (points B S hS F)).Finite))
    {x : points B S hS F}
    (hx : letI := pointTopology B S hS F
      x ∈ genericPoints (points B S hS F))
    (e c : GenericChart B S hS x) (u : e.U ⟶ c.U)
    (hcomm : e.immersion = yoneda.map u ≫ c.immersion)
    (hpoint : ((BigFppfOver.toScheme B S hS).map u)
      (schemePoint B S hS e.U e.point) =
      schemePoint B S hS c.U c.point)
    (V : BigFppfOver B S hS) (H : c.U ⟶ V)
    (z : (BigFppfOver.toScheme B S hS).obj V)
    (hpH : ((BigFppfOver.toScheme B S hS).map H)
      (schemePoint B S hS c.U c.point) = z)
    (hpUH : ((BigFppfOver.toScheme B S hS).map (u ≫ H))
      (schemePoint B S hS e.U e.point) = z) :
    eqToHom (congrArg (fun q =>
      ((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk q) hpH.symm) ≫
      ((BigFppfOver.toScheme B S hS).map H).stalkMap
        (schemePoint B S hS c.U c.point) ≫
      (chartStalkIso B S hS hF hdense hfinite x hx c).hom =
    eqToHom (congrArg (fun q =>
      ((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk q) hpUH.symm) ≫
      ((BigFppfOver.toScheme B S hS).map (u ≫ H)).stalkMap
        (schemePoint B S hS e.U e.point) ≫
      (chartStalkIso B S hS hF hdense hfinite x hx e).hom := by
  let T := BigFppfOver.toScheme B S hS
  let a := schemePoint B S hS e.U e.point
  let b := schemePoint B S hS c.U c.point
  have hfac : T.map (u ≫ H) = T.map u ≫ T.map H := by
    simp [T]
  have hstalk := stalkMap_factor_coherent_local (T.map u) (T.map H)
    (T.map (u ≫ H)) a b z hfac hpoint hpUH hpH
  have hnat := chartStalkIso_naturality B S hS hF hdense hfinite x hx e c u
    hcomm hpoint
  have htail : eqToHom (congrArg (fun q => (T.obj c.U).presheaf.stalk q) hpoint.symm) ≫
      (T.map u).stalkMap a ≫ (chartStalkIso B S hS hF hdense hfinite x hx e).hom =
      (chartStalkIso B S hS hF hdense hfinite x hx c).hom := by
    have ht := congrArg
      (fun k => (chartStalkIso B S hS hF hdense hfinite x hx c).hom ≫ k) hnat
    simpa [T, Category.assoc] using ht
  have hleft :
      (eqToHom (congrArg (fun q => (T.obj V).presheaf.stalk q) hpH.symm) ≫
        (T.map H).stalkMap b) ≫
        (chartStalkIso B S hS hF hdense hfinite x hx c).hom =
      ((eqToHom (congrArg (fun q => (T.obj V).presheaf.stalk q) hpH.symm) ≫
        (T.map H).stalkMap b) ≫
        eqToHom (congrArg (fun q => (T.obj c.U).presheaf.stalk q) hpoint.symm) ≫
        (T.map u).stalkMap a) ≫
        (chartStalkIso B S hS hF hdense hfinite x hx e).hom := by
    rw [← htail]
    simp [Category.assoc]
  calc
    _ = _ := hleft
    _ = (eqToHom (congrArg (fun q => (T.obj V).presheaf.stalk q) hpUH.symm) ≫
        (T.map (u ≫ H)).stalkMap a ≫
        (chartStalkIso B S hS hF hdense hfinite x hx e).hom) :=
          congrArg (fun k => k ≫ (chartStalkIso B S hS hF hdense hfinite x hx e).hom) hstalk

private theorem chartStalkMap_targetFactor_local
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (hdenseX : HasDenseRepresentableOpenSubspace B S hS X)
    (hdenseY : HasDenseRepresentableOpenSubspace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    {x : points B S hS X}
    (hx : letI := pointTopology B S hS X
      x ∈ genericPoints (points B S hS X))
    {y : points B S hS Y}
    (hy : letI := pointTopology B S hS Y
      y ∈ genericPoints (points B S hS Y))
    (c : GenericChart B S hS x) (d : GenericChart B S hS y)
    (g : c.U ⟶ d.U)
    (hpoint : ((BigFppfOver.toScheme B S hS).map g)
      (schemePoint B S hS c.U c.point) =
      schemePoint B S hS d.U d.point)
    (hfactorPoint : ((BigFppfOver.toScheme B S hS).map
        (g ≫ chartFactorHom B S hS hY d))
      (schemePoint B S hS c.U c.point) =
      schemePoint B S hS (schematicScheme B S hS hY)
        (schematicRepresentative B S hS hY hdenseY hfiniteY y hy)) :
    (chartStalkIso B S hS hY hdenseY hfiniteY y hy d).inv ≫
      eqToHom (congrArg
        (fun z => ((BigFppfOver.toScheme B S hS).obj d.U).presheaf.stalk z)
        hpoint.symm) ≫
      ((BigFppfOver.toScheme B S hS).map g).stalkMap
        (schemePoint B S hS c.U c.point) ≫
      (chartStalkIso B S hS hX hdenseX hfiniteX x hx c).hom =
    (chartStalkIso B S hS hY hdenseY hfiniteY y hy
      (schematicGenericChart B S hS hY hdenseY hfiniteY y hy)).inv ≫
      eqToHom (congrArg
        (fun z => ((BigFppfOver.toScheme B S hS).obj
          (schematicScheme B S hS hY)).presheaf.stalk z)
        hfactorPoint.symm)
        ≫ ((BigFppfOver.toScheme B S hS).map
          (g ≫ chartFactorHom B S hS hY d)).stalkMap
            (schemePoint B S hS c.U c.point) ≫
      (chartStalkIso B S hS hX hdenseX hfiniteX x hx c).hom := by
  let T := BigFppfOver.toScheme B S hS
  let β := chartFactorHom B S hS hY d
  let s := schematicGenericChart B S hS hY hdenseY hfiniteY y hy
  let a := schemePoint B S hS c.U c.point
  let b := schemePoint B S hS d.U d.point
  let z := schemePoint B S hS (schematicScheme B S hS hY)
    (schematicRepresentative B S hS hY hdenseY hfiniteY y hy)
  have hcomm : d.immersion = yoneda.map β ≫ s.immersion := by
    simpa [s, schematicGenericChart] using
      (chartFactorHom_fac B S hS hY d).symm
  have hpβ : T.map β b = z :=
    chartFactorHom_point_eq B S hS hY hdenseY hfiniteY hy d
  have hpβs : T.map β b = schemePoint B S hS s.U s.point := by
    simpa [s, schematicGenericChart, z] using hpβ
  have hpH : T.map (g ≫ β) a = z := by
    simpa [T, β, a, z] using hfactorPoint
  have hfac : T.map (g ≫ β) = T.map g ≫ T.map β := by
    simp [T]
  have hstalk := stalkMap_factor_coherent_local (T.map g) (T.map β)
    (T.map (g ≫ β)) a b z hfac hpoint hpH hpβ
  have hnat := chartStalkIso_naturality B S hS hY hdenseY hfiniteY y hy d s β
    hcomm hpβs
  have hInv : (chartStalkIso B S hS hY hdenseY hfiniteY y hy d).inv =
      (chartStalkIso B S hS hY hdenseY hfiniteY y hy s).inv ≫
        eqToHom (congrArg (fun q => (T.obj s.U).presheaf.stalk q) hpβs.symm) ≫
        (T.map β).stalkMap b := by
    let A := (chartStalkIso B S hS hY hdenseY hfiniteY y hy s).inv ≫
      eqToHom (congrArg (fun q => (T.obj s.U).presheaf.stalk q) hpβs.symm) ≫
      (T.map β).stalkMap b
    have hnat' : A ≫ (chartStalkIso B S hS hY hdenseY hfiniteY y hy d).hom = 𝟙 _ := by
      calc
        _ = (chartStalkIso B S hS hY hdenseY hfiniteY y hy s).inv ≫
            eqToHom (congrArg (fun q => (T.obj s.U).presheaf.stalk q) hpβs.symm) ≫
            (T.map β).stalkMap b ≫
            (chartStalkIso B S hS hY hdenseY hfiniteY y hy d).hom := by
              dsimp [A]
              exact Category.assoc _ _ _
        _ = 𝟙 _ := hnat
    calc
      _ = (A ≫ (chartStalkIso B S hS hY hdenseY hfiniteY y hy d).hom) ≫
          (chartStalkIso B S hS hY hdenseY hfiniteY y hy d).inv := by
            rw [hnat']
            simp
      _ = A := by simp [A, Category.assoc]
  rw [hInv]
  exact congrArg (fun k =>
    (chartStalkIso B S hS hY hdenseY hfiniteY y hy s).inv ≫ k ≫
      (chartStalkIso B S hS hX hdenseX hfiniteX x hx c).hom) hstalk

/-- The induced local ring map is characterized by its expression on every
pair of compatible schematic open charts. -/
theorem exists_genericLocalRingMap
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (hdenseX : HasDenseRepresentableOpenSubspace B S hS X)
    (hdenseY : HasDenseRepresentableOpenSubspace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (f : X ⟶ Y) (x : points B S hS X)
    (hx : letI := pointTopology B S hS X
      x ∈ genericPoints (points B S hS X))
    (hy : letI := pointTopology B S hS Y
      pointsMap B S hS X f x ∈ genericPoints (points B S hS Y)) :
    ∃ φ : genericLocalRing B S hS hY hdenseY hfiniteY
        (pointsMap B S hS X f x) hy ⟶
        genericLocalRing B S hS hX hdenseX hfiniteX x hx,
      ∀ (c : GenericChart B S hS x)
        (d : GenericChart B S hS (pointsMap B S hS X f x))
        (g : c.U ⟶ d.U)
        (_hcomm : c.immersion ≫ f = yoneda.map g ≫ d.immersion)
        (hpoint : ((BigFppfOver.toScheme B S hS).map g)
          (schemePoint B S hS c.U c.point) =
          schemePoint B S hS d.U d.point),
        φ = (chartStalkIso B S hS hY hdenseY hfiniteY _ hy d).inv ≫
          eqToHom (congrArg
            (fun z => ((BigFppfOver.toScheme B S hS).obj d.U).presheaf.stalk z)
            hpoint.symm) ≫
          ((BigFppfOver.toScheme B S hS).map g).stalkMap
            (schemePoint B S hS c.U c.point) ≫
          (chartStalkIso B S hS hX hdenseX hfiniteX x hx c).hom := by
  let y := pointsMap B S hS X f x
  let sY := schematicGenericChart B S hS hY hdenseY hfiniteY y hy
  let V := sY.U
  let pY := sY.point
  let z := schemePoint B S hS V pY
  let T := BigFppfOver.toScheme B S hS
  obtain ⟨c₀, d₀, g₀, hcomm₀, hpoint₀⟩ :=
    exists_compatibleGenericCharts_local B S hS hX hY hdenseX hdenseY
      hfiniteX hfiniteY f x hx hy
  let φ := (chartStalkIso B S hS hY hdenseY hfiniteY y hy d₀).inv ≫
    eqToHom (congrArg
      (fun q => ((BigFppfOver.toScheme B S hS).obj d₀.U).presheaf.stalk q)
      hpoint₀.symm) ≫
    ((BigFppfOver.toScheme B S hS).map g₀).stalkMap
      (schemePoint B S hS c₀.U c₀.point) ≫
    (chartStalkIso B S hS hX hdenseX hfiniteX x hx c₀).hom
  refine ⟨φ, ?_⟩
  intro c d g hcomm hpoint
  obtain ⟨e, u, v, heU, heV, hpointU, hpointV⟩ :=
    exists_commonGenericChartRefinement_local B S hS hX c c₀
  have : Mono (schematicChart B S hS hY) :=
    AlgebraicGeometry.Space.mono_of_isOpenImmersion B S hS _
      (isOpenImmersion_schematicChart B S hS hY)
  let W := {q : e.U ⟶ V //
    ((BigFppfOver.toScheme B S hS).map q)
      (schemePoint B S hS e.U e.point) = z}
  let ν (w : W) :=
    (chartStalkIso B S hS hY hdenseY hfiniteY y hy sY).inv ≫
      eqToHom (congrArg
        (fun w => ((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk w)
        w.2.symm) ≫
      ((BigFppfOver.toScheme B S hS).map w.1).stalkMap
        (schemePoint B S hS e.U e.point) ≫
      (chartStalkIso B S hS hX hdenseX hfiniteX x hx e).hom
  -- the comparison along a pair of compatible charts, refined through `e`
  have side : ∀ (c : GenericChart B S hS x) (d : GenericChart B S hS y) (g : c.U ⟶ d.U)
      (hcomm : c.immersion ≫ f = yoneda.map g ≫ d.immersion)
      (hpoint : ((BigFppfOver.toScheme B S hS).map g)
        (schemePoint B S hS c.U c.point) = schemePoint B S hS d.U d.point)
      (w : e.U ⟶ c.U) (hw : e.immersion = yoneda.map w ≫ c.immersion)
      (hpw : ((BigFppfOver.toScheme B S hS).map w)
        (schemePoint B S hS e.U e.point) = schemePoint B S hS c.U c.point),
      ∃ hpK : ((BigFppfOver.toScheme B S hS).map (w ≫ g ≫ chartFactorHom B S hS hY d))
          (schemePoint B S hS e.U e.point) = z,
        (chartStalkIso B S hS hY hdenseY hfiniteY y hy d).inv ≫
          eqToHom (congrArg
            (fun z => ((BigFppfOver.toScheme B S hS).obj d.U).presheaf.stalk z)
            hpoint.symm) ≫
          ((BigFppfOver.toScheme B S hS).map g).stalkMap
            (schemePoint B S hS c.U c.point) ≫
          (chartStalkIso B S hS hX hdenseX hfiniteX x hx c).hom =
          ν ⟨w ≫ g ≫ chartFactorHom B S hS hY d, hpK⟩ ∧
        yoneda.map (w ≫ g ≫ chartFactorHom B S hS hY d) ≫ schematicChart B S hS hY =
          e.immersion ≫ f := by
    intro c d g hcomm hpoint w hw hpw
    have hpβ : ((BigFppfOver.toScheme B S hS).map (chartFactorHom B S hS hY d))
        (schemePoint B S hS d.U d.point) = z :=
      chartFactorHom_point_eq B S hS hY hdenseY hfiniteY hy d
    have hfactorPoint : ((BigFppfOver.toScheme B S hS).map (g ≫ chartFactorHom B S hS hY d))
        (schemePoint B S hS c.U c.point) = z := by
      rw [T.map_comp, Scheme.Hom.comp_apply, hpoint, hpβ]
    have hpK : ((BigFppfOver.toScheme B S hS).map (w ≫ g ≫ chartFactorHom B S hS hY d))
        (schemePoint B S hS e.U e.point) = z := by
      rw [T.map_comp, Scheme.Hom.comp_apply, hpw]
      exact hfactorPoint
    refine ⟨hpK, ?_, ?_⟩
    · have hsource := chartStalkMap_sourceRefine_local B S hS hX
        hdenseX hfiniteX hx e c w hw hpw V (g ≫ chartFactorHom B S hS hY d) z hfactorPoint hpK
      rw [chartStalkMap_targetFactor_local B S hS hX hY
        hdenseX hdenseY hfiniteX hfiniteY hx hy c d g hpoint hfactorPoint]
      exact congrArg (fun q => (chartStalkIso B S hS hY hdenseY hfiniteY y hy sY).inv ≫ q)
        hsource
    · simp only [Functor.map_comp, Category.assoc, chartFactorHom_fac, hw, ← hcomm]
  obtain ⟨hpK, h1, hc1⟩ := side c d g hcomm hpoint u heU hpointU
  obtain ⟨hpK₀, h2, hc2⟩ := side c₀ d₀ g₀ hcomm₀ hpoint₀ v heV hpointV
  have hk := yoneda.map_injective ((cancel_mono (schematicChart B S hS hY)).1 (hc1.trans hc2.symm))
  exact h2.trans ((congrArg ν (Subtype.ext hk.symm)).trans h1.symm)

/-- The induced map from the target's local ring to the source's local ring. -/
noncomputable def genericLocalRingMap
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (hdenseX : HasDenseRepresentableOpenSubspace B S hS X)
    (hdenseY : HasDenseRepresentableOpenSubspace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (f : X ⟶ Y) (x : points B S hS X)
    (hx : letI := pointTopology B S hS X
      x ∈ genericPoints (points B S hS X))
    (hy : letI := pointTopology B S hS Y
      pointsMap B S hS X f x ∈ genericPoints (points B S hS Y)) :
    genericLocalRing B S hS hY hdenseY hfiniteY
      (pointsMap B S hS X f x) hy ⟶
      genericLocalRing B S hS hX hdenseX hfiniteX x hx :=
  (exists_genericLocalRingMap B S hS hX hY hdenseX hdenseY
    hfiniteX hfiniteY f x hx hy).choose

/-- The dense representable open subspace of a decent algebraic space, as supplied by
Stacks 086U. -/
theorem hasDenseRepresentableOpenSubspace_of_isDecentSpace
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hdec : IsDecentSpace B S hS F) :
    HasDenseRepresentableOpenSubspace B S hS F :=
  exists_denseRange_isRepresentable_isOpenSubspace_of_isDecentSpace B S hS hF hdec

/-- **Stacks 0ACV.** A morphism of decent algebraic spaces with finitely many irreducible
components is birational when it bijects the generic points of the irreducible components and
induces isomorphisms on their schematic-locus local rings. -/
@[stacks 0ACV, ega "I 2.2.9" "more general"]
def IsBirational
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (hdecX : IsDecentSpace B S hS X)
    (hdecY : IsDecentSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (f : X ⟶ Y) : Prop :=
  letI : TopologicalSpace (points B S hS X) :=
    pointTopology B S hS X
  letI : TopologicalSpace (points B S hS Y) :=
    pointTopology B S hS Y
  ∃ hbij : Set.BijOn (pointsMap B S hS X f)
      (genericPoints (points B S hS X))
      (genericPoints (points B S hS Y)),
    ∀ (x : points B S hS X)
      (hx : x ∈ genericPoints (points B S hS X)),
      IsIso (genericLocalRingMap B S hS hX hY
        (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hX hdecX)
        (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hY hdecY)
        hfiniteX hfiniteY f x hx (hbij.mapsTo hx))

/-- Birationality is exactly bijectivity on generic points together with
isomorphisms of the induced local-ring maps there. -/
theorem isBirational_iff
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (hdecX : IsDecentSpace B S hS X)
    (hdecY : IsDecentSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (f : X ⟶ Y) :
    IsBirational B S hS hX hY hdecX hdecY hfiniteX hfiniteY f ↔
      letI : TopologicalSpace (points B S hS X) :=
        pointTopology B S hS X
      letI : TopologicalSpace (points B S hS Y) :=
        pointTopology B S hS Y
      ∃ hbij : Set.BijOn (pointsMap B S hS X f)
          (genericPoints (points B S hS X))
          (genericPoints (points B S hS Y)),
        ∀ (x : points B S hS X)
          (hx : x ∈ genericPoints (points B S hS X)),
          IsIso (genericLocalRingMap B S hS hX hY
            (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hX hdecX)
            (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hY hdecY)
            hfiniteX hfiniteY f x hx (hbij.mapsTo hx)) :=
  Iff.rfl

/-- Construct a birationality assertion from its two defining conditions. -/
theorem IsBirational.of_bijOn_isIso_genericLocalRingMap
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (hdecX : IsDecentSpace B S hS X)
    (hdecY : IsDecentSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (f : X ⟶ Y)
    (hbij : letI := pointTopology B S hS X
      letI := pointTopology B S hS Y
      Set.BijOn (pointsMap B S hS X f)
        (genericPoints (points B S hS X))
        (genericPoints (points B S hS Y)))
    (hiso : letI := pointTopology B S hS X
      letI := pointTopology B S hS Y
      ∀ (x : points B S hS X)
        (hx : x ∈ genericPoints (points B S hS X)),
        IsIso (genericLocalRingMap B S hS hX hY
          (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hX hdecX)
          (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hY hdecY)
          hfiniteX hfiniteY f x hx (hbij.mapsTo hx))) :
    IsBirational B S hS hX hY hdecX hdecY hfiniteX hfiniteY f :=
  ⟨hbij, hiso⟩

/-- A birational morphism bijects the generic points of irreducible components. -/
theorem IsBirational.bijOn
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (hdecX : IsDecentSpace B S hS X)
    (hdecY : IsDecentSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    {f : X ⟶ Y}
    (hf : IsBirational B S hS hX hY hdecX hdecY hfiniteX hfiniteY f) :
    letI : TopologicalSpace (points B S hS X) :=
      pointTopology B S hS X
    letI : TopologicalSpace (points B S hS Y) :=
      pointTopology B S hS Y
    Set.BijOn (pointsMap B S hS X f)
      (genericPoints (points B S hS X))
      (genericPoints (points B S hS Y)) :=
  hf.choose

/-- At a generic point, a birational morphism induces an isomorphism on
the local rings of the schematic loci. -/
theorem IsBirational.isIso_genericLocalRingMap
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (hdecX : IsDecentSpace B S hS X)
    (hdecY : IsDecentSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    {f : X ⟶ Y}
    (hf : IsBirational B S hS hX hY hdecX hdecY hfiniteX hfiniteY f)
    (x : points B S hS X)
    (hx : letI := pointTopology B S hS X
      x ∈ genericPoints (points B S hS X)) :
    IsIso (genericLocalRingMap B S hS hX hY
      (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hX hdecX)
      (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hY hdecY)
      hfiniteX hfiniteY f x hx
      ((hf.bijOn B S hS hX hY hdecX hdecY hfiniteX hfiniteY).mapsTo hx)) :=
  hf.choose_spec x hx

end AlgebraicGeometry.Space

end
