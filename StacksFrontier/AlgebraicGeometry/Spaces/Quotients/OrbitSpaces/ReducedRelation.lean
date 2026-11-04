module

public import Mathlib.AlgebraicGeometry.Properties
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.TopologyComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.OrbitSpaces.OrbitSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Invariance from set-theoretic invariance on a reduced relation

Fix a scheme `S` in a big fppf site `B` and a presheaf `Z` on the big fppf site of `S`, and
let `j : R ⟶ U ×_Z U` be a pre-relation. A morphism out of `U` to a locally separated target
which is only known to identify the endpoints of the arrows of `j` between points over
algebraically closed fields is invariant under `j` outright, provided the relation `R` is
reduced.

The proof compares the two composites on a reduced surjective étale scheme atlas of `R`,
where the two maps agree on every geometric point; local separatedness makes the locus where
they agree an immersion, reducedness and surjectivity on points make it an isomorphism, and
the atlas is locally surjective for the fppf topology, so the agreement descends to `R`.

## Main results

* `AlgebraicGeometry.Space.isInvariant_of_isSetTheoreticallyInvariant_of_reduced`: on a
  reduced relation space, set-theoretic invariance implies invariance.

## Implementation notes

The conclusion is `AlgebraicGeometry.Space.IsInvariant` of **Stacks 048E**, which is stated
over an arbitrary base object of an arbitrary category whose slice has binary products and so
applies to the slice of presheaves used here. Because the target is an arbitrary presheaf and
not an algebraic space, the sheaf condition on it, which an algebraic space satisfies
automatically, is an explicit hypothesis.

Reducedness of the relation space is the étale-local property
`AlgebraicGeometry.Space.HasEtaleLocalProperty` of **Stacks 03E6** for
`AlgebraicGeometry.IsReduced`, so it comes with the reduced atlas the proof works on.

## References

* [Stacks Project, Tag 048Y](https://stacks.math.columbia.edu/tag/048Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space

/-! ### Surjective étale atlases are locally surjective -/

/-- A surjective étale atlas of a presheaf on the big fppf site of `S` is locally surjective
for the topology of that site. -/
private theorem isLocallySurjective_atlas {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (V : BigFppfOver B S hS)
    (a : yoneda.obj V ⟶ F)
    (haSurj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haEtale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) a := by
  let T := BigFppfOver.toScheme B S hS
  refine ⟨fun {W} s ↦ ?_⟩
  let g : yoneda.obj W ⟶ F := yonedaEquiv.symm s
  let rep := MorphismProperty.relative.rep haSurj
  let W' := rep.pullback g
  let q := rep.snd g
  have hsurj : Surjective (T.map q) :=
    haSurj.property g (rep.fst g) q (rep.isPullback g)
  have hetale : Etale (T.map q) :=
    haEtale.property g (rep.fst g) q (rep.isPullback g)
  have hcover : Sieve.generate (Presieve.singleton q) ∈ BigFppfOver.topology B S hS W := by
    rw [BigFppfOver.topology, GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate]
    apply B.topology.superset_covering (Sieve.generate_mono ?_)
      (BigFppfSite.generate_singleton_mem_topology B q.left hsurj hetale)
    exact (Presieve.singleton_le_iff q.left).2
      ⟨W', q, 𝟙 _, Presieve.singleton_self q, by simp⟩
  have hq : Presheaf.imageSieve a s q := by
    let p' := rep.fst' g
    refine ⟨yonedaEquiv (yoneda.map p'), ?_⟩
    have h : yoneda.map p' ≫ a = yoneda.map q ≫ g := by
      rw [rep.map_fst' g]
      exact rep.w g
    show a.app (Opposite.op W') (yonedaEquiv (yoneda.map p')) = F.map q.op s
    rw [yonedaEquiv_yoneda_map]
    exact congrArg (fun k ↦ k.app (Opposite.op W') (𝟙 W')) h
  refine (BigFppfOver.topology B S hS).superset_covering ?_ hcover
  rw [Sieve.generate_le_iff]
  rintro _ _ ⟨⟩
  exact hq

/-- Two morphisms to a sheaf which agree after a locally surjective morphism of presheaves
are equal. -/
@[sga "3 VIB 10.15" "partial"]
private theorem eq_of_isLocallySurjective {C : Type v} [Category.{u, v} C]
    (J : GrothendieckTopology C) {F G H : Cᵒᵖ ⥤ Type u} (a : F ⟶ G) (f g : G ⟶ H)
    (ha : Presheaf.IsLocallySurjective J a) (hH : Presheaf.IsSheaf J H)
    (h : a ≫ f = a ≫ g) : f = g := by
  ext W x
  refine hH.isSeparated W.unop _ (ha.imageSieve_mem x) _ _ ?_
  rintro Zobj i ⟨y, hy⟩
  have hfg : f.app (Opposite.op Zobj) (a.app (Opposite.op Zobj) y) =
      g.app (Opposite.op Zobj) (a.app (Opposite.op Zobj) y) := by
    simpa only [NatTrans.comp_app, types_comp_apply] using
      congrArg (fun k ↦ k.app (Opposite.op Zobj) y) h
  calc
    H.map i.op (f.app W x) = f.app (Opposite.op Zobj) (G.map i.op x) :=
        (NatTrans.naturality_apply f i.op x).symm
    _ = f.app (Opposite.op Zobj) (a.app (Opposite.op Zobj) y) := by rw [hy]
    _ = g.app (Opposite.op Zobj) (a.app (Opposite.op Zobj) y) := hfg
    _ = g.app (Opposite.op Zobj) (G.map i.op x) := by rw [← hy]
    _ = H.map i.op (g.app W x) := NatTrans.naturality_apply g i.op x

/-! ### Set-theoretic invariance on a reduced relation -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- At a geometric point of the relation space the two endpoint composites of a
set-theoretically invariant morphism agree. -/
private theorem endpoints_eq_at_geometricPoint {R U X : Over Z} (j : PreRelation R U)
    (φ : U ⟶ X) (hφ : IsSetTheoreticallyInvariant j φ.left)
    (p : GeometricPoint B S hS R.left) :
    (yonedaEquiv.symm p.val.value ≫ j.target.left) ≫ φ.left =
      (yonedaEquiv.symm p.val.value ≫ j.source.left) ≫ φ.left := by
  let bp : GeometricPoint B S hS Z :=
    ⟨FieldValuedPoint.map B S hS R.left R.hom p.val, p.property⟩
  have hw : yonedaEquiv.symm p.val.value ≫ R.hom = yonedaEquiv.symm
      (R.hom.app (Opposite.op (p.val.siteObject B S hS R.left)) p.val.value) :=
    yonedaEquiv_symm_naturality_right (p.val.siteObject B S hS R.left) R.hom p.val.value
  let pt (e : R ⟶ U) : TestPoint (bp.val.siteObject B S hS Z) (yonedaEquiv.symm bp.val.value) U :=
    ⟨yonedaEquiv.symm p.val.value ≫ e.left, by
      rw [Category.assoc, Over.w e]
      exact hw⟩
  exact hφ bp (pt j.target) (pt j.source) ⟨⟨yonedaEquiv.symm p.val.value, hw⟩, rfl, rfl⟩

/-- Two morphisms from a reduced scheme of the site to a presheaf over `Z` whose structure
morphism is locally separated are equal as soon as they agree over `Z` and at every geometric
point. -/
private theorem eq_of_geometricPoints_of_reduced {X : Over Z} (V : BigFppfOver B S hS)
    (f g : yoneda.obj V ⟶ X.left) (hfgB : f ≫ X.hom = g ≫ X.hom)
    (hred : IsReduced ((BigFppfOver.toScheme B S hS).obj V))
    (hX : IsLocallySeparated B S hS X.hom)
    (hpoints : ∀ p : GeometricPoint B S hS (yoneda.obj V),
      yonedaEquiv.symm p.val.value ≫ f = yonedaEquiv.symm p.val.value ≫ g) :
    f = g := by
  let T := BigFppfOver.toScheme B S hS
  let d := pullback.diagonal X.hom
  let q := pullback.lift f g hfgB
  have hqfst : q ≫ pullback.fst X.hom X.hom = f := pullback.lift_fst _ _ _
  have hqsnd : q ≫ pullback.snd X.hom X.hom = g := pullback.lift_snd _ _ _
  let Pimm := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) T
  have hd : Pimm.presheaf d := hX
  let rep := hd.rep
  let i := rep.snd q
  let W := rep.pullback q
  have hi : AlgebraicGeometry.IsImmersion (T.map i) :=
    hd.property q (rep.fst q) i (rep.isPullback q)
  have hpointsSurj : Function.Surjective
      (pointsMap B S hS (yoneda.obj W) (yoneda.map i)) := by
    intro z
    obtain ⟨p, rfl⟩ := exists_geometricRepresentative B S hS (yoneda.obj V) z
    let u : yoneda.obj (p.val.siteObject B S hS (yoneda.obj V)) ⟶ yoneda.obj V :=
      yonedaEquiv.symm p.val.value
    let h : p.val.siteObject B S hS (yoneda.obj V) ⟶ V := yonedaEquiv u
    have hu : yoneda.map h = u := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_yoneda_map]
    have hdiag : (u ≫ f) ≫ d = yoneda.map h ≫ q := by
      have hfg : yoneda.map h ≫ f = yoneda.map h ≫ g := by rw [hu]; exact hpoints p
      apply pullback.hom_ext <;> simp [d, hqfst, hqsnd, hfg, ← hu]
    let m := rep.lift (u ≫ f) h hdiag
    have hm' : m ≫ i = h := rep.lift_snd (u ≫ f) h hdiag
    let pw : FieldValuedPoint B S hS (yoneda.obj W) :=
      { carrier := p.val.carrier
        field := p.val.field
        contained := p.val.contained
        toBase := p.val.toBase
        value := yonedaEquiv (yoneda.map m) }
    have hval : (FieldValuedPoint.map B S hS (yoneda.obj W) (yoneda.map i) pw).value =
        p.val.value := by
      show yonedaEquiv (yoneda.map m ≫ yoneda.map i) = p.val.value
      rw [← Functor.map_comp, hm', yonedaEquiv_yoneda_map]
      exact Equiv.apply_symm_apply _ _
    have hcommon : FieldValuedPoint.HasCommonExtension B S hS (yoneda.obj V) p.val
        (FieldValuedPoint.map B S hS (yoneda.obj W) (yoneda.map i) pw) :=
      ⟨p.val, FieldValuedPoint.dominates_refl B S hS (yoneda.obj V) p.val, ⟨𝟙 _, hval⟩⟩
    refine ⟨pw.class B S hS (yoneda.obj W), ?_⟩
    rw [pointsMap_class]
    exact FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS (yoneda.obj V)
      (FieldValuedPoint.hasCommonExtension_symm B S hS (yoneda.obj V) hcommon)
  let Psurj := MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) T
  have hsurjPresheaf : Psurj.presheaf (yoneda.map i) :=
    (surjective_iff_surjective_pointsMap B S hS (yoneda.obj V)
      (isAlgebraicSpace_yoneda B S hS V) W (yoneda.map i)).2 hpointsSurj
  have hsurj : AlgebraicGeometry.Surjective (T.map i) :=
    MorphismProperty.of_relative_map (P := Psurj) (F := yoneda) hsurjPresheaf
  have : AlgebraicGeometry.IsImmersion (T.map i) := hi
  have : IsReduced (T.obj V) := hred
  have : AlgebraicGeometry.IsClosedImmersion (T.map i) :=
    AlgebraicGeometry.IsClosedImmersion.iff_isPreimmersion.mpr
      ⟨inferInstance, by rw [Set.range_eq_univ.mpr hsurj.surj]; exact isClosed_univ⟩
  have : AlgebraicGeometry.Surjective (T.map i) := hsurj
  have : IsIso (T.map i) :=
    AlgebraicGeometry.isIso_of_isClosedImmersion_of_surjective (T.map i)
  have : IsIso i := isIso_of_reflects_iso (F := T) i
  have : IsIso (yoneda.map i) := Functor.map_isIso yoneda i
  have hpull : rep.fst q ≫ d = yoneda.map i ≫ q := by simpa [i] using (rep.isPullback q).w
  have hproj : ∀ (π : pullback X.hom X.hom ⟶ X.left) (k : yoneda.obj V ⟶ X.left),
      d ≫ π = 𝟙 _ → q ≫ π = k → yoneda.map i ≫ k = rep.fst q := fun π k hπ hk ↦ by
    rw [← hk, ← Category.assoc, ← hpull, Category.assoc, hπ, Category.comp_id]
  apply (cancel_epi (yoneda.map i)).1
  rw [hproj _ f (by simp [d]) hqfst, hproj _ g (by simp [d]) hqsnd]

/-- **Stacks 048Y.** On a reduced relation space, set-theoretic invariance of a morphism to a
locally separated target implies that the morphism is invariant under the pre-relation. -/
@[stacks 048Y]
theorem isInvariant_of_isSetTheoreticallyInvariant_of_reduced {R U X : Over Z}
    (j : PreRelation R U)
    (φ : U ⟶ X) (hφ : IsSetTheoreticallyInvariant j φ.left)
    (hR : HasEtaleLocalProperty B S hS R.left (fun Y : Scheme.{u} ↦ IsReduced Y))
    (hX : IsLocallySeparated B S hS X.hom)
    (hXsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X.left) :
    IsInvariant j φ.left := by
  obtain ⟨V, a, haSurj, haEtale, hVred⟩ := hR
  have hfgB : (a ≫ (j.target ≫ φ).left) ≫ X.hom = (a ≫ (j.source ≫ φ).left) ≫ X.hom :=
    calc (a ≫ (j.target ≫ φ).left) ≫ X.hom
        = a ≫ ((j.target ≫ φ).left ≫ X.hom) := Category.assoc _ _ _
      _ = a ≫ R.hom := by rw [Over.w (j.target ≫ φ)]
      _ = a ≫ ((j.source ≫ φ).left ≫ X.hom) := by rw [Over.w (j.source ≫ φ)]
      _ = (a ≫ (j.source ≫ φ).left) ≫ X.hom := (Category.assoc _ _ _).symm
  have hpoints : ∀ p : GeometricPoint B S hS (yoneda.obj V),
      yonedaEquiv.symm p.val.value ≫ (a ≫ (j.target ≫ φ).left) =
        yonedaEquiv.symm p.val.value ≫ (a ≫ (j.source ≫ φ).left) := by
    intro p
    let pr : GeometricPoint B S hS R.left :=
      ⟨FieldValuedPoint.map B S hS (yoneda.obj V) a p.val, p.property⟩
    have hrepr : yonedaEquiv.symm pr.val.value = yonedaEquiv.symm p.val.value ≫ a :=
      (yonedaEquiv_symm_naturality_right
        (p.val.siteObject B S hS (yoneda.obj V)) a p.val.value).symm
    show ((yonedaEquiv.symm p.val.value ≫ a) ≫ j.target.left) ≫ φ.left =
      ((yonedaEquiv.symm p.val.value ≫ a) ≫ j.source.left) ≫ φ.left
    rw [← hrepr]
    exact endpoints_eq_at_geometricPoint j φ hφ pr
  have hleft : (j.target ≫ φ).left = (j.source ≫ φ).left :=
    eq_of_isLocallySurjective (BigFppfOver.topology B S hS) a
      (j.target ≫ φ).left (j.source ≫ φ).left
      (isLocallySurjective_atlas V a haSurj haEtale) hXsheaf
      (eq_of_geometricPoints_of_reduced V _ _ hfgB hVred hX hpoints)
  simpa only [IsInvariant, Over.comp_left] using hleft

end AlgebraicGeometry.Space

end
