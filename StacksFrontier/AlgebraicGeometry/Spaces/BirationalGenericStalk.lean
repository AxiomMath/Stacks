module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.FieldValued
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiCompactMonomorphicPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointsFromEtaleCover
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecializationLift
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Birational morphisms at generic local rings

A birational morphism of decent algebraic spaces with finitely many irreducible components
becomes an isomorphism after base change to the spectrum of the local ring of the target at
a generic point of one of its irreducible components.

## Main definitions

* `AlgebraicGeometry.Space.genericStalkSpec` is the spectrum of the local ring of an
  algebraic space at a generic point, as an object of the big fppf site over the base.
* `AlgebraicGeometry.Space.fromGenericStalk` is its canonical morphism to the space.
* `AlgebraicGeometry.Space.genericStalkInclusion` is its canonical morphism to the schematic
  locus, through which `AlgebraicGeometry.Space.fromGenericStalk` factors.

## Main results

* `AlgebraicGeometry.Space.isIso_pullback_snd_fromGenericStalk_of_isBirational` is
  Stacks 0BBD.

## Implementation notes

The local ring of an algebraic space at a generic point is computed on its schematic locus,
as `AlgebraicGeometry.Space.genericLocalRing`. Its spectrum is small enough to lie in the
chosen big fppf site because the site's cutoff is a strong limit and the stalk is a quotient
of a set of sections indexed by the affine opens through the point. The canonical map is the
composite of `Spec` of the stalk into the schematic locus with the schematic chart.

Birationality is taken in the form of `AlgebraicGeometry.Space.IsBirational`, which is
parameterised by decency of the source and the target, as the source statement is. Decency does
two jobs here: through Stacks 086U it gives the representable open subspace with dense point set
on which the local rings at generic points are computed, and it supplies soberness of the point
spaces, through which a generic point of the target has a unique preimage, together with the
finiteness of étale fibres of Stacks 03JV used to lift specializations.

The proof follows the source: a generic point `y` of the target is hit by a unique generic
point `x` of the source, the two are computed by compatible schematic charts `c ⟶ d` whose
stalk map at `x` is the birational isomorphism of local rings, and that isomorphism both
splits `X ×_Y Spec 𝒪_{Y,y} ⟶ Spec 𝒪_{Y,y}` and makes it a monomorphism, the latter because
every point of a test object maps to `x` and the chart `c` is then a common factorization.

## References

* [Stacks Project, Tag 0BBD](https://stacks.math.columbia.edu/tag/0BBD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hY : IsAlgebraicSpace B S hS Y)
  (hdenseY : HasDenseRepresentableOpenSubspace B S hS Y)
  (hfiniteY : (letI := pointTopology B S hS Y
    (irreducibleComponents (points B S hS Y)).Finite))
  (y : points B S hS Y)
  (hy : letI := pointTopology B S hS Y
    y ∈ genericPoints (points B S hS Y))

/-- The spectrum of the local ring of an algebraic space at a generic point, as an object
over the base scheme. -/
noncomputable def genericStalkSpec : BigFppfOver B S hS := by
  let U := schematicScheme B S hS hY
  let T := (BigFppfOver.toScheme B S hS).obj U
  let z := schemePoint B S hS U
    (schematicRepresentative B S hS hY hdenseY hfiniteY y hy)
  let R := T.presheaf.stalk z
  have hR : B.Contains (Spec R) := by
    have hcard : Cardinal.mk R ≤ T.size := by
      let I : Type u := {V : T.affineOpens // z ∈ V.1}
      let g : (i : I) × T.presheaf.obj (Opposite.op i.1.1) → R :=
        fun i => (ConcreteCategory.hom (T.presheaf.germ i.1.1 z i.1.2)) i.2
      have hg : Function.Surjective g := by
        intro r
        obtain ⟨V, hzV, hV, s, hs⟩ :=
          TopCat.Presheaf.exists_mem_germ_eq_of_isBasis
            T.isBasis_affineOpens T.presheaf z r
        exact ⟨⟨⟨⟨V, hV⟩, hzV⟩, s⟩, hs⟩
      calc
        Cardinal.mk R ≤ Cardinal.mk ((i : I) × T.presheaf.obj (Opposite.op i.1.1)) :=
          Cardinal.mk_le_of_surjective hg
        _ = Cardinal.sum (fun i : I => Cardinal.mk (T.presheaf.obj (Opposite.op i.1.1))) :=
          Cardinal.mk_sigma _
        _ ≤ Cardinal.mk I * ⨆ i : I,
            Cardinal.mk (T.presheaf.obj (Opposite.op i.1.1)) :=
          Cardinal.sum_le_mk_mul_iSup _
        _ ≤ T.size * T.size :=
          mul_le_mul ((Cardinal.mk_subtype_le _).trans T.mk_affineOpens_le_size)
            (ciSup_le' fun i => T.mk_sections_le_size i.1) (by positivity) (by positivity)
        _ = T.size := by rw [Cardinal.mul_eq_self T.aleph0_le_size]
    exact Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff
      B.cutoff_isStrongPrelimit R U.left.property
      (hcard.trans (Cardinal.self_le_power _ Cardinal.one_le_aleph0))
  let q : B.obj hR ⟶ U.left :=
    B.inclusion.preimage (T.fromSpecStalk z)
  exact Over.mk (q ≫ U.hom)

/-- The canonical map from the spectrum of the local ring at a generic point into the
algebraic space. -/
noncomputable def fromGenericStalk :
    yoneda.obj (genericStalkSpec B S hS hY hdenseY hfiniteY y hy) ⟶ Y := by
  let U := schematicScheme B S hS hY
  let q : genericStalkSpec B S hS hY hdenseY hfiniteY y hy ⟶ U :=
    Over.homMk (B.inclusion.preimage
      (((BigFppfOver.toScheme B S hS).obj U).fromSpecStalk
        (schemePoint B S hS U
          (schematicRepresentative B S hS hY hdenseY hfiniteY y hy)))) rfl
  exact yoneda.map q ≫ schematicChart B S hS hY

/-- The canonical map of the generic stalk spectrum into the schematic locus. -/
noncomputable def genericStalkInclusion :
    genericStalkSpec B S hS hY hdenseY hfiniteY y hy ⟶ schematicScheme B S hS hY :=
  Over.homMk (B.inclusion.preimage
    (((BigFppfOver.toScheme B S hS).obj (schematicScheme B S hS hY)).fromSpecStalk
      (schemePoint B S hS (schematicScheme B S hS hY)
        (schematicRepresentative B S hS hY hdenseY hfiniteY y hy)))) rfl

/-- The generic stalk spectrum maps to the schematic locus by `Spec` of the stalk. -/
theorem toScheme_map_genericStalkInclusion :
    (BigFppfOver.toScheme B S hS).map
        (genericStalkInclusion B S hS hY hdenseY hfiniteY y hy) =
      ((BigFppfOver.toScheme B S hS).obj (schematicScheme B S hS hY)).fromSpecStalk
        (schemePoint B S hS (schematicScheme B S hS hY)
          (schematicRepresentative B S hS hY hdenseY hfiniteY y hy)) :=
  B.inclusion.map_preimage _

private theorem algebraic_of_injective_ringHom
    {K L M : Type u} [CommRing K] [CommRing L] [CommRing M]
    (α : K →+* L) (β : L →+* M) (γ : K →+* M)
    (hcomp : γ = β.comp α) (hinj : Function.Injective β)
    (halg : letI : Algebra K M := γ.toAlgebra; Algebra.IsAlgebraic K M) :
    letI : Algebra K L := α.toAlgebra
    Algebra.IsAlgebraic K L := by
  let : Algebra K L := α.toAlgebra
  let : Algebra K M := γ.toAlgebra
  have : Algebra.IsAlgebraic K M := halg
  exact Algebra.IsAlgebraic.of_ringHom_of_comp_eq (RingHom.id K) β
    (fun x => ⟨x, rfl⟩) hinj (by
      show γ.comp (RingHom.id K) = β.comp α
      simpa using hcomp)

private theorem algebraic_trans_of_ringHom
    {K L M : Type u} [CommRing K] [CommRing L] [CommRing M] [NoZeroDivisors L]
    (α : K →+* L) (β : L →+* M) (γ : K →+* M)
    (hcomp : γ = β.comp α)
    (halg₁ : letI : Algebra K L := α.toAlgebra; Algebra.IsAlgebraic K L)
    (halg₂ : letI : Algebra L M := β.toAlgebra; Algebra.IsAlgebraic L M) :
    letI : Algebra K M := γ.toAlgebra
    Algebra.IsAlgebraic K M := by
  let : Algebra K L := α.toAlgebra
  let : Algebra L M := β.toAlgebra
  let : Algebra K M := γ.toAlgebra
  have : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact congrArg (fun f : K →+* M => f x) hcomp)
  have : Algebra.IsAlgebraic K L := halg₁
  have : Algebra.IsAlgebraic L M := halg₂
  exact Algebra.IsAlgebraic.trans K L M

private theorem algebraic_residueField_descends
    {T U S : Scheme.{u}} (f : T ⟶ S) (g : T ⟶ U) (h : U ⟶ S)
    (t : T) (q : U) (hpoint : g t = q) (hcomm : g ≫ h = f)
    (halg : letI := (f.residueFieldMap t).hom.toAlgebra
      Algebra.IsAlgebraic (S.residueField (f t)) (T.residueField t)) :
    letI := (h.residueFieldMap q).hom.toAlgebra
    Algebra.IsAlgebraic (S.residueField (h q)) (U.residueField q) := by
  subst f
  subst q
  let q := g t
  let f := g ≫ h
  let α := (h.residueFieldMap q).hom
  let β := (g.residueFieldMap t).hom
  let γ := (f.residueFieldMap t).hom
  have hcomp : γ = β.comp α := congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp g h t)
  exact @algebraic_of_injective_ringHom
    (S.residueField (h q)) (U.residueField q) (T.residueField t)
    inferInstance inferInstance inferInstance α β γ hcomp (RingHom.injective β) halg

private theorem exists_genericPoint_preimage_of_isBirational
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hdecentX : IsDecentSpace B S hS X)
    (hdecentY : IsDecentSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (f : X ⟶ Y)
    (hf : IsBirational B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY f) :
    ∃ (x : points B S hS X)
      (hx : letI := pointTopology B S hS X
        x ∈ genericPoints (points B S hS X)),
      ∃ hxy : pointsMap B S hS X f x = y,
        IsIso (genericLocalRingMap B S hS hX hY
          (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hX hdecentX)
          (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hY hdecentY)
          hfiniteX hfiniteY f x hx (hxy ▸ hy)) := by
  let : TopologicalSpace (points B S hS X) := pointTopology B S hS X
  let : TopologicalSpace (points B S hS Y) := pointTopology B S hS Y
  obtain ⟨x, hx, hxy⟩ :=
    (hf.bijOn B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY).surjOn hy
  refine ⟨x, hx, hxy, ?_⟩
  simpa [hxy] using
    hf.isIso_genericLocalRingMap B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY x hx

private theorem exists_genericPoint_specializes_of_isDecent
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hdecentX : IsDecentSpace B S hS X)
    (x : points B S hS X) :
    letI := pointTopology B S hS X
    ∃ η : points B S hS X,
      η ∈ genericPoints (points B S hS X) ∧ η ⤳ x := by
  let : TopologicalSpace (points B S hS X) := pointTopology B S hS X
  have : QuasiSober (points B S hS X) :=
    (stacksSober_iff_t0_and_quasiSober.mp
      (stacksSober_points_of_isDecentSpace B S hS hX hdecentX)).2
  obtain ⟨Z, hZ, hxZ⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible (closure {x})
      isIrreducible_singleton.closure
  let η : genericPoints (points B S hS X) := genericPoints.ofComponent ⟨Z, hZ⟩
  refine ⟨η.1, η.2, ?_⟩
  rw [specializes_iff_mem_closure, (genericPoints.isGenericPoint_ofComponent ⟨Z, hZ⟩).def]
  exact hxZ (subset_closure (Set.mem_singleton x))

private theorem eq_of_specializes_genericPoint
    {T : Type*} [TopologicalSpace T] [T0Space T]
    {x y : T} (hy : y ∈ genericPoints T) (hxy : x ⤳ y) : x = y := by
  have hreverse := hy.2 isIrreducible_singleton.closure hxy.closure_subset
  exact (hxy.antisymm (specializes_iff_closure_subset.mpr hreverse)).eq

include hY hy in
private theorem exists_genericPoint_preimage_specializes
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hdecentX : IsDecentSpace B S hS X)
    (hdecentY : IsDecentSpace B S hS Y)
    (f : X ⟶ Y) (x : points B S hS X)
    (hxy : pointsMap B S hS X f x = y) :
    letI := pointTopology B S hS X
    ∃ η : points B S hS X,
      η ∈ genericPoints (points B S hS X) ∧
      pointsMap B S hS X f η = y ∧ η ⤳ x := by
  let := pointTopology B S hS X
  let := pointTopology B S hS Y
  have : T0Space (points B S hS Y) :=
    (stacksSober_iff_t0_and_quasiSober.mp
      (stacksSober_points_of_isDecentSpace B S hS hY hdecentY)).1
  obtain ⟨η, hη, hηx⟩ :=
    exists_genericPoint_specializes_of_isDecent B S hS hX hdecentX x
  refine ⟨η, hη, ?_, hηx⟩
  apply eq_of_specializes_genericPoint hy
  rw [← hxy]
  exact hηx.map ((pointTopologyFamily B S hS).continuous hX hY f)

include hy in
private theorem genericPoint_specializes_every_point_over_generic
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hdecentX : IsDecentSpace B S hS X)
    (hdecentY : IsDecentSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (f : X ⟶ Y)
    (hf : IsBirational B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY f)
    (η : points B S hS X)
    (hη : letI := pointTopology B S hS X
      η ∈ genericPoints (points B S hS X))
    (hηy : pointsMap B S hS X f η = y)
    (x : points B S hS X)
    (hxy : pointsMap B S hS X f x = y) :
    letI := pointTopology B S hS X
    η ⤳ x := by
  obtain ⟨ξ, hξ, hξy, hξx⟩ :=
    exists_genericPoint_preimage_specializes B S hS hY y hy hX hdecentX hdecentY f x hxy
  have hξη : ξ = η :=
    (hf.bijOn B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY).injOn
      hξ hη (hξy.trans hηy.symm)
  exact hξη ▸ hξx

private instance inverseImage_toScheme_isStableUnderBaseChange
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
  ⟨fun sq hf => MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := P)
    (sq.map (BigFppfOver.toScheme B S hS)) hf⟩

private theorem exists_compatibleGenericCharts
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hdenseX : HasDenseRepresentableOpenSubspace B S hS X)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (f : X ⟶ Y) (x : points B S hS X)
    (hx : letI := pointTopology B S hS X
      x ∈ genericPoints (points B S hS X))
    (hfx : letI := pointTopology B S hS Y
      pointsMap B S hS X f x ∈ genericPoints (points B S hS Y)) :
    ∃ (c : GenericChart B S hS x) (g : c.U ⟶ schematicScheme B S hS hY),
      c.immersion ≫ f = yoneda.map g ≫ schematicChart B S hS hY ∧
      ((BigFppfOver.toScheme B S hS).map g) (schemePoint B S hS c.U c.point) =
        schemePoint B S hS (schematicScheme B S hS hY)
          (schematicRepresentative B S hS hY hdenseY hfiniteY _ hfx) := by
  let c₀ := schematicGenericChart B S hS hX hdenseX hfiniteX x hx
  let d := schematicGenericChart B S hS hY hdenseY hfiniteY _ hfx
  let rep := d.isOpen.rep
  let W := rep.pullback (c₀.immersion ≫ f)
  let j : W ⟶ c₀.U := rep.snd (c₀.immersion ≫ f)
  let k : W ⟶ d.U := rep.fst' (c₀.immersion ≫ f)
  have hpb : IsPullback (yoneda.map k) (yoneda.map j) d.immersion
      (c₀.immersion ≫ f) := rep.isPullback' (c₀.immersion ≫ f)
  have hpt : pointsMap B S hS (yoneda.obj d.U) d.immersion d.point.class =
      pointsMap B S hS (yoneda.obj c₀.U) (c₀.immersion ≫ f) c₀.point.class := by
    rw [pointsMap_comp_apply, c₀.mapsTo, d.mapsTo]
  obtain ⟨z, hzk, hzj⟩ :=
    exists_point_of_isPullback_presheaf B S hS hpb d.point.class c₀.point.class hpt
  obtain ⟨p, rfl⟩ := Quot.exists_rep z
  let P := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have hj : P j := d.isOpen.property _ _ j hpb
  have hj' : IsOpenImmersion B S hS (yoneda.map j) := MorphismProperty.relative_map hj
  have hopen : IsOpenImmersion B S hS (yoneda.map j ≫ c₀.immersion) :=
    MorphismProperty.comp_mem P.presheaf _ _ hj' c₀.isOpen
  let c : GenericChart B S hS x := {
    U := W
    immersion := yoneda.map j ≫ c₀.immersion
    isOpen := hopen
    point := p
    mapsTo := by
      rw [pointsMap_comp_apply]
      exact (congrArg (pointsMap B S hS _ c₀.immersion) hzj).trans c₀.mapsTo
  }
  exact ⟨c, k, (Category.assoc _ _ _).trans hpb.w.symm,
    schemePoint_eq_of_class_eq B S hS d.U _ _ hzk⟩

private theorem isIso_stalkMap_of_isBirational
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hdecentX : IsDecentSpace B S hS X)
    (hdecentY : IsDecentSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (f : X ⟶ Y)
    (hf : IsBirational B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY f)
    (x : points B S hS X)
    (hx : letI := pointTopology B S hS X
      x ∈ genericPoints (points B S hS X))
    (c : GenericChart B S hS x)
    (d : GenericChart B S hS (pointsMap B S hS X f x))
    (g : c.U ⟶ d.U)
    (hcomm : c.immersion ≫ f = yoneda.map g ≫ d.immersion)
    (hpoint : ((BigFppfOver.toScheme B S hS).map g)
      (schemePoint B S hS c.U c.point) = schemePoint B S hS d.U d.point) :
    IsIso (((BigFppfOver.toScheme B S hS).map g).stalkMap
      (schemePoint B S hS c.U c.point)) := by
  have hdenseX := hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hX hdecentX
  have hdenseY := hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hY hdecentY
  let hfx := (hf.bijOn B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY).mapsTo hx
  have he := (exists_genericLocalRingMap B S hS hX hY hdenseX hdenseY
    hfiniteX hfiniteY f x hx hfx).choose_spec c d g hcomm hpoint
  have hi := hf.isIso_genericLocalRingMap B S hS hX hY hdecentX hdecentY
    hfiniteX hfiniteY x hx
  change IsIso (genericLocalRingMap B S hS hX hY hdenseX hdenseY
    hfiniteX hfiniteY f x hx hfx) at hi
  change genericLocalRingMap B S hS hX hY hdenseX hdenseY
    hfiniteX hfiniteY f x hx hfx = _ at he
  rw [he] at hi
  let eX := chartStalkIso B S hS hX hdenseX hfiniteX x hx c
  let eY := chartStalkIso B S hS hY hdenseY hfiniteY _ hfx d
  let b := eqToHom (congrArg
    (fun z => ((BigFppfOver.toScheme B S hS).obj d.U).presheaf.stalk z) hpoint.symm)
  let k := ((BigFppfOver.toScheme B S hS).map g).stalkMap
    (schemePoint B S hS c.U c.point)
  have : IsIso (eY.inv ≫ b ≫ k ≫ eX.hom) := hi
  have : IsIso (b ≫ k ≫ eX.hom) := IsIso.of_isIso_comp_left eY.inv _
  have : IsIso (k ≫ eX.hom) := IsIso.of_isIso_comp_left b _
  exact IsIso.of_isIso_comp_right k eX.hom

private lemma exists_section_fromSpecStalk
    {U V : Scheme.{u}} (g : U ⟶ V) (z : U) (w : V) (hzw : g z = w)
    [IsIso (g.stalkMap z)] :
    ∃ s : Spec (V.presheaf.stalk w) ⟶ U, s ≫ g = V.fromSpecStalk w := by
  subst w
  refine ⟨Spec.map (inv (g.stalkMap z)) ≫ U.fromSpecStalk z, ?_⟩
  rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk g (x := z), Spec.map_inv,
    IsIso.inv_hom_id_assoc]

private theorem exists_section_fromGenericStalk_of_isBirational
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hdecentX : IsDecentSpace B S hS X)
    (hdecentY : IsDecentSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (f : X ⟶ Y)
    (hf : IsBirational B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY f) :
    ∃ s : yoneda.obj (genericStalkSpec B S hS hY
        (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hY hdecentY)
        hfiniteY y hy) ⟶ X,
      s ≫ f = fromGenericStalk B S hS hY
        (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hY hdecentY)
        hfiniteY y hy := by
  have hdenseX := hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hX hdecentX
  have hdenseY := hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hY hdecentY
  show ∃ s : yoneda.obj (genericStalkSpec B S hS hY hdenseY hfiniteY y hy) ⟶ X,
    s ≫ f = fromGenericStalk B S hS hY hdenseY hfiniteY y hy
  obtain ⟨x, hx, hxy, _⟩ := exists_genericPoint_preimage_of_isBirational
    B S hS hY hfiniteY y hy hX hdecentX hdecentY hfiniteX f hf
  subst y
  obtain ⟨c, g, hcomm, hpoint⟩ := exists_compatibleGenericCharts
    B S hS hY hdenseY hfiniteY hX hdenseX hfiniteX f x hx hy
  let d := schematicGenericChart B S hS hY hdenseY hfiniteY _ hy
  have : IsIso (((BigFppfOver.toScheme B S hS).map g).stalkMap
      (schemePoint B S hS c.U c.point)) :=
    isIso_stalkMap_of_isBirational B S hS hY hfiniteY
      hX hdecentX hdecentY hfiniteX f hf x hx c d g hcomm hpoint
  let A := genericStalkSpec B S hS hY hdenseY hfiniteY _ hy
  let q := genericStalkInclusion B S hS hY hdenseY hfiniteY _ hy
  obtain ⟨s₀, hs₀⟩ := exists_section_fromSpecStalk
    ((BigFppfOver.toScheme B S hS).map g)
    (schemePoint B S hS c.U c.point)
    (schemePoint B S hS d.U d.point) hpoint
  let sl : A.left ⟶ c.U.left := B.inclusion.preimage s₀
  have hmaps : B.inclusion.map sl = s₀ :=
    B.inclusion.map_preimage (X := A.left) (Y := c.U.left) s₀
  have hsl : sl ≫ g.left = q.left := by
    apply B.inclusion.map_injective
    rw [Functor.map_comp, hmaps]
    exact hs₀.trans
      (toScheme_map_genericStalkInclusion B S hS hY hdenseY hfiniteY _ hy).symm
  let s : A ⟶ c.U := Over.homMk sl (by
    rw [← g.w, ← Category.assoc, hsl, q.w])
  have hsq : s ≫ g = q := Over.OverMorphism.ext hsl
  refine ⟨yoneda.map s ≫ c.immersion, ?_⟩
  rw [Category.assoc, hcomm, ← Category.assoc, ← Functor.map_comp, hsq]
  rfl

private theorem eq_of_specializes_of_algebraic_residueField
    {U V : Scheme.{u}} (g : U ⟶ V) {z t : U} (hst : z ⤳ t)
    (hgt : g t = g z)
    (halg : letI := (g.residueFieldMap z).hom.toAlgebra
      Algebra.IsAlgebraic (V.residueField (g z)) (U.residueField z)) : t = z := by
  let t' := (g.fiberHomeo (g z)).symm ⟨t, hgt⟩
  have hs : g.asFiber z ⤳ t' := by
    apply (g.fiberι (g z)).isEmbedding.isInducing.specializes_iff.mp
    simpa only [Scheme.Hom.fiberι_asFiber, t', Scheme.Hom.fiberι_fiberHomeo_symm] using hst
  have he : t' = g.asFiber z :=
    (AlgebraicGeometry.isClosed_asFiber_of_isAlgebraic_residueField g z
      halg).closure_subset hs.mem_closure
  simpa only [t', Scheme.Hom.fiberι_fiberHomeo_symm, Scheme.Hom.fiberι_asFiber] using
    congrArg (g.fiberι (g z)) he

private instance mono_genericChart_immersion
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {x : points B S hS F} (c : GenericChart B S hS x) :
    Mono c.immersion := by
  apply MorphismProperty.presheaf_monomorphisms_le_monomorphisms
  apply MorphismProperty.relative_monotone _ c.immersion c.isOpen
  intro U V f hf
  have : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map f) := hf
  exact (BigFppfOver.toScheme B S hS).mono_of_mono_map (f := f) inferInstance

private theorem algebraic_residueField_of_isIso_stalkMap
    {U V : Scheme.{u}} (g : U ⟶ V) (z : U) [IsIso (g.stalkMap z)] :
    letI := (g.residueFieldMap z).hom.toAlgebra
    Algebra.IsAlgebraic (V.residueField (g z)) (U.residueField z) := by
  have : IsIso (g.residueFieldMap z) :=
    (IsLocalRing.ResidueField.mapEquiv
      (asIso (g.stalkMap z)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom
  let := (g.residueFieldMap z).hom.toAlgebra
  constructor
  intro a
  obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso (g.residueFieldMap z)).surjective a
  exact (isIntegral_algebraMap (R := V.residueField (g z)) (A := U.residueField z)).isAlgebraic

private theorem algebraic_residueField_of_etale_chart
    {X Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Z) (x : points B S hS X)
    (c : GenericChart B S hS x)
    (d : GenericChart B S hS (pointsMap B S hS X f x))
    (g : c.U ⟶ d.U) (hcomm : c.immersion ≫ f = yoneda.map g ≫ d.immersion)
    (hg : IsIso (((BigFppfOver.toScheme B S hS).map g).stalkMap
      (schemePoint B S hS c.U c.point)))
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (v : U ⟶ d.U) (hv : a ≫ f = yoneda.map v ≫ d.immersion)
    (q : points B S hS (yoneda.obj U))
    (hq : pointsMap B S hS _ a q = x) :
    let z := pointsToScheme B S hS U q
    let vS := (BigFppfOver.toScheme B S hS).map v
    letI := (vS.residueFieldMap z).hom.toAlgebra
    Algebra.IsAlgebraic
      (((BigFppfOver.toScheme B S hS).obj d.U).residueField (vS z))
      (((BigFppfOver.toScheme B S hS).obj U).residueField z) := by
  let T := BigFppfOver.toScheme B S hS
  let rep := c.isOpen.rep
  let W := rep.pullback a
  let j : W ⟶ U := rep.snd a
  let k : W ⟶ c.U := rep.fst' a
  have sq : IsPullback (yoneda.map k) (yoneda.map j) c.immersion a := rep.isPullback' a
  obtain ⟨w, hwc, hwu⟩ :=
    exists_point_of_isPullback_presheaf B S hS sq c.point.class q (c.mapsTo.trans hq.symm)
  let z := pointsToScheme B S hS W w
  have hwc' : T.map k z = schemePoint B S hS c.U c.point := by
    rw [← pointsToScheme_pointsMap, hwc]
    rfl
  have hwu' : T.map j z = pointsToScheme B S hS U q := by
    rw [← pointsToScheme_pointsMap, hwu]
  have he : j ≫ v = k ≫ g := by
    apply yoneda.map_injective
    apply (cancel_mono d.immersion).mp
    simp only [Functor.map_comp, Category.assoc]
    rw [← hv, ← hcomm]
    simpa only [Category.assoc] using congrArg (fun l => l ≫ f) sq.w.symm
  have hk : Etale (T.map k) := ha.property c.immersion (yoneda.map j) k sq.flip
  have hg' : IsIso ((T.map g).stalkMap (T.map k z)) := hwc'.symm ▸ hg
  have halg₁ := algebraic_residueField_of_isIso_stalkMap (T.map g) (T.map k z)
  have halg₂ : let := ((T.map k).residueFieldMap z).hom.toAlgebra
      Algebra.IsAlgebraic ((T.obj c.U).residueField (T.map k z))
        ((T.obj W).residueField z) := by
    let := ((T.map k).residueFieldMap z).hom.toAlgebra
    infer_instance
  have halg : let := ((T.map k ≫ T.map g).residueFieldMap z).hom.toAlgebra
      Algebra.IsAlgebraic ((T.obj d.U).residueField ((T.map k ≫ T.map g) z))
        ((T.obj W).residueField z) :=
    algebraic_trans_of_ringHom _ _ _
      (congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp _ _ _)) halg₁ halg₂
  exact algebraic_residueField_descends (T.map k ≫ T.map g) (T.map j) (T.map v)
    z (pointsToScheme B S hS U q) hwu'
    (by simpa only [Functor.map_comp] using T.congr_map he) halg

private theorem exists_etale_chart_through_chart
    {X Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (f : X ⟶ Z) {z : points B S hS Z} (d : GenericChart B S hS z)
    (t : points B S hS X) (hft : pointsMap B S hS X f t = z) :
    ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a ∧
      ∃ v : U ⟶ d.U, a ≫ f = yoneda.map v ≫ d.immersion ∧
        ∃ q : points B S hS (yoneda.obj U), pointsMap B S hS _ a q = t := by
  let T := BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T
  obtain ⟨U₀, a₀, ha₀surj, ha₀⟩ := hX.exists_atlas
  obtain ⟨q₀, hq₀⟩ :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS X hX U₀ a₀).mp ha₀surj t
  let rep := d.isOpen.rep
  let U := rep.pullback (a₀ ≫ f)
  let j : U ⟶ U₀ := rep.snd (a₀ ≫ f)
  let v : U ⟶ d.U := rep.fst' (a₀ ≫ f)
  have sq : IsPullback (yoneda.map v) (yoneda.map j) d.immersion (a₀ ≫ f) :=
    rep.isPullback' (a₀ ≫ f)
  have hcompat : pointsMap B S hS _ d.immersion d.point.class =
      pointsMap B S hS _ (a₀ ≫ f) q₀ := by
    rw [pointsMap_comp_apply, hq₀, d.mapsTo, hft]
  obtain ⟨q, hqv, hqj⟩ :=
    exists_point_of_isPullback_presheaf B S hS sq d.point.class q₀ hcompat
  let a := yoneda.map j ≫ a₀
  have hv : a ≫ f = yoneda.map v ≫ d.immersion := (Category.assoc _ _ _).trans sq.w.symm
  have : AlgebraicGeometry.IsOpenImmersion (T.map j) := d.isOpen.property _ _ j sq
  have hj : P.presheaf (yoneda.map j) :=
    MorphismProperty.relative_map (show Etale (T.map j) from inferInstance)
  have : P.IsStableUnderComposition := ⟨by
    intro A₁ A₂ A₃ f₁ f₂ hf₁ hf₂
    show Etale (T.map (f₁ ≫ f₂))
    rw [T.map_comp]
    have : Etale (T.map f₁) := hf₁
    have : Etale (T.map f₂) := hf₂
    infer_instance⟩
  have ha : P.presheaf a := MorphismProperty.comp_mem P.presheaf _ _ hj ha₀
  have hqa : pointsMap B S hS _ a q = t := by
    rw [pointsMap_comp_apply, hqj, hq₀]
  exact ⟨U, a, ha, v, hv, q, hqa⟩

private theorem eq_of_specializes_of_isIso_chartStalkMap
    {X Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hdecent : IsDecentSpace B S hS X)
    (f : X ⟶ Z) (x : points B S hS X)
    (c : GenericChart B S hS x)
    (d : GenericChart B S hS (pointsMap B S hS X f x))
    (g : c.U ⟶ d.U) (hcomm : c.immersion ≫ f = yoneda.map g ≫ d.immersion)
    (hg : IsIso (((BigFppfOver.toScheme B S hS).map g).stalkMap
      (schemePoint B S hS c.U c.point)))
    (t : points B S hS X)
    (hft : pointsMap B S hS X f t = pointsMap B S hS X f x)
    (hst : letI := pointTopology B S hS X; x ⤳ t) : t = x := by
  let := pointTopology B S hS X
  let T := BigFppfOver.toScheme B S hS
  obtain ⟨U, a, ha, v, hv, q, hqa⟩ := exists_etale_chart_through_chart B S hS hX f d t hft
  let := pointTopology B S hS (yoneda.obj U)
  have hfinite : HasFiniteFibresOnEveryAffineEtaleChart B S hS X x := fun U hU φ hφ =>
    (hasFiniteChartAndRelationFibersAt_iff_hasQuasiCompactMonomorphicFieldRepresentative
      B S hS X hX x).2 (hdecent x) U hU φ (presheaf_etale_of_isEtale B S hS hφ)
  obtain ⟨q', hspec, hq'a⟩ := exists_specialization_lift_of_finite_etale_fibers
    B S hS X hX t x hst hfinite U a ha q hqa
  have halg := algebraic_residueField_of_etale_chart B S hS
    f x c d g hcomm hg U a ha v hv q' hq'a
  have hqv' : pointsMap B S hS _ (yoneda.map v) q =
      pointsMap B S hS _ (yoneda.map v) q' := by
    apply pointsMap_injective_of_mono B S hS d.immersion
    simp only [← pointsMap_comp_apply, ← hv]
    rw [pointsMap_comp_apply B S hS a f q,
      pointsMap_comp_apply B S hS a f q', hqa, hq'a, hft]
  have hpoints : T.map v (pointsToScheme B S hS U q) =
      T.map v (pointsToScheme B S hS U q') := by
    simpa only [pointsToScheme_pointsMap] using congrArg (pointsToScheme B S hS d.U) hqv'
  have hspecializes : pointsToScheme B S hS U q' ⤳ pointsToScheme B S hS U q :=
    hspec.map ((schemePointsHomeomorph B S hS U).continuous)
  have he := eq_of_specializes_of_algebraic_residueField (T.map v)
    hspecializes hpoints halg
  have heq := injective_pointsToScheme B S hS U he
  exact hqa.symm.trans ((congrArg (pointsMap B S hS _ a) heq).trans hq'a)

private theorem exists_lift_of_points_range_subset
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U Z : BigFppfOver B S hS)
    (i : yoneda.obj U ⟶ X) (hi : IsOpenImmersion B S hS i)
    (a : yoneda.obj Z ⟶ X)
    (hrange : Set.range (pointsMap B S hS _ a) ⊆ Set.range (pointsMap B S hS _ i)) :
    ∃ b : Z ⟶ U, yoneda.map b ≫ i = a := by
  let T := BigFppfOver.toScheme B S hS
  let W := hi.rep.pullback a
  let j : W ⟶ Z := hi.rep.snd a
  let k : W ⟶ U := hi.rep.fst' a
  have sq : IsPullback (yoneda.map k) (yoneda.map j) i a := hi.rep.isPullback' a
  have hj : AlgebraicGeometry.IsOpenImmersion (T.map j) := hi.property _ _ j sq
  have hjSurj : Function.Surjective (T.map j) := by
    intro z
    obtain ⟨q, rfl⟩ := surjective_pointsToScheme B S hS Z z
    obtain ⟨p, hp⟩ := hrange ⟨q, rfl⟩
    obtain ⟨w, _, hw⟩ := exists_point_of_isPullback_presheaf B S hS sq p q hp
    exact ⟨pointsToScheme B S hS W w, by rw [← pointsToScheme_pointsMap, hw]⟩
  have : IsIso (T.map j) :=
    (AlgebraicGeometry.isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨hj, ⟨hjSurj⟩⟩
  have : IsIso (B.inclusion.map j.left) := inferInstanceAs (IsIso (T.map j))
  have : IsIso j.left := (isIso_iff_of_reflects_iso _ B.inclusion).mp inferInstance
  have : IsIso ((BigFppfOver.forget B S hS).map j) := inferInstanceAs (IsIso j.left)
  have : IsIso j :=
    (isIso_iff_of_reflects_iso j (BigFppfOver.forget B S hS)).mp inferInstance
  refine ⟨inv j ≫ k, ?_⟩
  rw [Functor.map_comp, Category.assoc, sq.w, ← Category.assoc, ← Functor.map_comp]
  simp

private theorem hom_ext_of_comp_eq_of_isIso_stalkMap
    {Z U V : Scheme.{u}} (a b : Z ⟶ U) (g : U ⟶ V)
    (hab : a ≫ g = b ≫ g) (hpoint : ∀ t, a t = b t)
    (hg : ∀ t, IsIso (g.stalkMap (a t))) : a = b := by
  have hbase : a.base = b.base := by
    ext t
    exact hpoint t
  apply Scheme.Hom.ext'
  apply LocallyRingedSpace.forgetToSheafedSpace.map_injective
  apply SheafedSpace.hom_stalk_ext _ _ hbase
  intro t
  show a.stalkMap t = (U.presheaf.stalkCongr _).hom ≫ b.stalkMap t
  have := hg t
  apply (cancel_epi (g.stalkMap (a t))).mp
  rw [← Category.assoc, g.stalkMap_congr_point (a t) (b t) (hpoint t),
    ← Scheme.Hom.stalkMap_comp a g t, Category.assoc, ← Scheme.Hom.stalkMap_comp b g t]
  exact Scheme.Hom.stalkMap_congr_hom (a ≫ g) (b ≫ g) hab t

private theorem pointsMap_fromGenericStalk
    (hdecentY : IsDecentSpace B S hS Y)
    (p : points B S hS (yoneda.obj (genericStalkSpec B S hS hY hdenseY hfiniteY y hy))) :
    pointsMap B S hS _ (fromGenericStalk B S hS hY hdenseY hfiniteY y hy) p = y := by
  let := pointTopology B S hS Y
  have : T0Space (points B S hS Y) :=
    (stacksSober_iff_t0_and_quasiSober.mp
      (stacksSober_points_of_isDecentSpace B S hS hY hdecentY)).1
  let T := BigFppfOver.toScheme B S hS
  let d := schematicGenericChart B S hS hY hdenseY hfiniteY y hy
  let A := genericStalkSpec B S hS hY hdenseY hfiniteY y hy
  let q : A ⟶ d.U := genericStalkInclusion B S hS hY hdenseY hfiniteY y hy
  let := pointTopology B S hS (yoneda.obj d.U)
  have hq : T.map q = (T.obj d.U).fromSpecStalk (schemePoint B S hS d.U d.point) :=
    toScheme_map_genericStalkInclusion B S hS hY hdenseY hfiniteY y hy
  have hs : T.map q (pointsToScheme B S hS A p) ⤳ schemePoint B S hS d.U d.point := by
    rw [hq]
    have hr : (T.obj d.U).fromSpecStalk _ (pointsToScheme B S hS A p) ∈
        Set.range ((T.obj d.U).fromSpecStalk (schemePoint B S hS d.U d.point)) := ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at hr
  have hs' : pointsMap B S hS _ (yoneda.map q) p ⤳ d.point.class := by
    apply (schemePointsHomeomorph B S hS d.U).isEmbedding.isInducing.specializes_iff.mp
    have he : (schemePointsHomeomorph B S hS d.U :
        points B S hS (yoneda.obj d.U) → T.obj d.U) = pointsToScheme B S hS d.U := rfl
    rw [he, pointsToScheme_pointsMap]
    exact hs
  have hsY := hs'.map
    ((pointTopologyFamily B S hS).continuous
      (isAlgebraicSpace_yoneda B S hS d.U) hY d.immersion)
  rw [d.mapsTo] at hsY
  show pointsMap B S hS _ (yoneda.map q ≫ d.immersion) p = y
  rw [pointsMap_comp_apply]
  exact eq_of_specializes_genericPoint hy hsY

private theorem hom_ext_of_comp_eq_of_constant_points
    {X Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Z) (x : points B S hS X)
    (c : GenericChart B S hS x)
    (d : GenericChart B S hS (pointsMap B S hS X f x))
    (g : c.U ⟶ d.U) (hcomm : c.immersion ≫ f = yoneda.map g ≫ d.immersion)
    (hg : IsIso (((BigFppfOver.toScheme B S hS).map g).stalkMap
      (schemePoint B S hS c.U c.point)))
    (W : BigFppfOver B S hS) (a b : yoneda.obj W ⟶ X)
    (hab : a ≫ f = b ≫ f)
    (ha : ∀ p, pointsMap B S hS _ a p = x)
    (hb : ∀ p, pointsMap B S hS _ b p = x) : a = b := by
  have hrange (k : yoneda.obj W ⟶ X) (hk : ∀ p, pointsMap B S hS _ k p = x) :
      Set.range (pointsMap B S hS _ k) ⊆ Set.range (pointsMap B S hS _ c.immersion) := by
    rintro _ ⟨p, rfl⟩
    exact ⟨c.point.class, c.mapsTo.trans (hk p).symm⟩
  obtain ⟨a', ha'⟩ := exists_lift_of_points_range_subset B S hS c.U W
    c.immersion c.isOpen a (hrange a ha)
  obtain ⟨b', hb'⟩ := exists_lift_of_points_range_subset B S hS c.U W
    c.immersion c.isOpen b (hrange b hb)
  have he : a' ≫ g = b' ≫ g := by
    apply yoneda.map_injective
    apply (cancel_mono d.immersion).mp
    simp only [Functor.map_comp, Category.assoc, ← hcomm]
    rw [← Category.assoc, ha', ← Category.assoc, hb']
    exact hab
  let T := BigFppfOver.toScheme B S hS
  have hpoint (k : W ⟶ c.U) (v : yoneda.obj W ⟶ X)
      (hv : ∀ p, pointsMap B S hS _ v p = x)
      (hk : yoneda.map k ≫ c.immersion = v) (t : T.obj W) :
      T.map k t = schemePoint B S hS c.U c.point := by
    obtain ⟨p, rfl⟩ := surjective_pointsToScheme B S hS W t
    have heq : pointsMap B S hS _ (yoneda.map k) p = c.point.class := by
      apply pointsMap_injective_of_mono B S hS c.immersion
      rw [← pointsMap_comp_apply, hk, hv, c.mapsTo]
    have hh := congrArg (pointsToScheme B S hS c.U) heq
    rwa [pointsToScheme_pointsMap] at hh
  have hpa := hpoint a' a ha ha'
  have hpb := hpoint b' b hb hb'
  have hschemes : T.map a' = T.map b' :=
    hom_ext_of_comp_eq_of_isIso_stalkMap (T.map a') (T.map b') (T.map g)
      (by simpa only [Functor.map_comp] using T.congr_map he)
      (fun t => (hpa t).trans (hpb t).symm) (fun t => (hpa t).symm ▸ hg)
  rw [← ha', ← hb', T.map_injective hschemes]

private theorem mono_pullback_snd_of_constant_points
    {X Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Z) (x : points B S hS X)
    (c : GenericChart B S hS x)
    (d : GenericChart B S hS (pointsMap B S hS X f x))
    (g : c.U ⟶ d.U) (hcomm : c.immersion ≫ f = yoneda.map g ≫ d.immersion)
    (hg : IsIso (((BigFppfOver.toScheme B S hS).map g).stalkMap
      (schemePoint B S hS c.U c.point)))
    {A : BigFppfOver B S hS} (q : yoneda.obj A ⟶ Z)
    (hfibre : ∀ t, pointsMap B S hS X f t = pointsMap B S hS X f x → t = x)
    (hq : ∀ p, pointsMap B S hS _ q p = pointsMap B S hS X f x) :
    Mono (pullback.snd f q) := by
  rw [NatTrans.mono_iff_mono_app]
  intro W
  rw [mono_iff_injective]
  intro a b hab
  let α : yoneda.obj W.unop ⟶ pullback f q := yonedaEquiv.symm a
  let β : yoneda.obj W.unop ⟶ pullback f q := yonedaEquiv.symm b
  have hαβ : α ≫ pullback.snd f q = β ≫ pullback.snd f q := by
    apply yonedaEquiv.injective
    simpa only [yonedaEquiv_comp, α, β, Equiv.apply_symm_apply] using hab
  have hpt (k : yoneda.obj W.unop ⟶ pullback f q)
      (z : points B S hS (yoneda.obj W.unop)) :
      pointsMap B S hS _ (k ≫ pullback.fst f q) z = x := by
    apply hfibre
    rw [← pointsMap_comp_apply, Category.assoc, pullback.condition,
      ← Category.assoc, pointsMap_comp_apply]
    exact hq _
  have he : α = β := by
    apply pullback.hom_ext
    · have hcomp : (α ≫ pullback.fst f q) ≫ f = (β ≫ pullback.fst f q) ≫ f := by
        calc
          _ = (α ≫ pullback.snd f q) ≫ q := by
            rw [Category.assoc, pullback.condition, ← Category.assoc]
          _ = (β ≫ pullback.snd f q) ≫ q := congrArg (fun k => k ≫ q) hαβ
          _ = _ := by rw [Category.assoc, ← pullback.condition, ← Category.assoc]
      exact hom_ext_of_comp_eq_of_constant_points B S hS f x c d g hcomm hg
        W.unop (α ≫ pullback.fst f q) (β ≫ pullback.fst f q) hcomp (hpt α) (hpt β)
    · exact hαβ
  simpa only [α, β, Equiv.apply_symm_apply] using
    congrArg (fun k : yoneda.obj W.unop ⟶ pullback f q => yonedaEquiv k) he

/-- **Stacks 0BBD.** A birational morphism of decent algebraic spaces with finitely many
irreducible components becomes an isomorphism after base change to the spectrum of the local
ring of the target at a generic point. -/
@[stacks 0BBD]
theorem isIso_pullback_snd_fromGenericStalk_of_isBirational
    (hdecentY : IsDecentSpace B S hS Y)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hdecentX : IsDecentSpace B S hS X)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (f : X ⟶ Y)
    (hf : IsBirational B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY f) :
    IsIso (pullback.snd f (fromGenericStalk B S hS hY
      (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hY hdecentY)
      hfiniteY y hy)) := by
  let := pointTopology B S hS X
  have hdenseX := hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hX hdecentX
  have hdenseY := hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hY hdecentY
  show IsIso (pullback.snd f (fromGenericStalk B S hS hY hdenseY hfiniteY y hy))
  obtain ⟨x, hx, hxy, _⟩ := exists_genericPoint_preimage_of_isBirational
    B S hS hY hfiniteY y hy hX hdecentX hdecentY hfiniteX f hf
  subst y
  obtain ⟨c, g, hcomm, hpoint⟩ := exists_compatibleGenericCharts
    B S hS hY hdenseY hfiniteY hX hdenseX hfiniteX f x hx hy
  let d := schematicGenericChart B S hS hY hdenseY hfiniteY _ hy
  have hg := isIso_stalkMap_of_isBirational B S hS hY hfiniteY
    hX hdecentX hdecentY hfiniteX f hf x hx c d g hcomm hpoint
  have hfibre (t : points B S hS X)
      (ht : pointsMap B S hS X f t = pointsMap B S hS X f x) : t = x :=
    eq_of_specializes_of_isIso_chartStalkMap B S hS hX hdecentX f x c d g hcomm hg
      t ht (genericPoint_specializes_every_point_over_generic B S hS hY hfiniteY
        _ hy hX hdecentX hdecentY hfiniteX f hf x hx rfl t ht)
  obtain ⟨s, hs⟩ := exists_section_fromGenericStalk_of_isBirational
    B S hS hY hfiniteY _ hy hX hdecentX hdecentY hfiniteX f hf
  let q := fromGenericStalk B S hS hY hdenseY hfiniteY _ hy
  let p := pullback.snd f q
  have hsplit : IsSplitEpi p := IsSplitEpi.mk' {
    section_ := pullback.lift s (𝟙 _) (by simpa using hs)
    id := pullback.lift_snd _ _ _ }
  have hm : Mono p := mono_pullback_snd_of_constant_points B S hS f x c d g hcomm hg q hfibre
    (pointsMap_fromGenericStalk B S hS hY hdenseY hfiniteY _ hy hdecentY)
  exact @isIso_of_mono_of_isSplitEpi _ _ _ _ p hm hsplit

end AlgebraicGeometry.Space

end
