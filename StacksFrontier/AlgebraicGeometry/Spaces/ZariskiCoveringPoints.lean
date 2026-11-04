module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.SheafFromSubsheaves
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallZariskiSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# Zariski coverings and coverings of the point space (Stacks 03BZ)

A family of open subspaces of an algebraic space over `S` is a Zariski covering exactly when
the sets of points of its members cover the point space of Tag 03BX. Transporting along the
order isomorphism of open subspaces with open sets of points, the covering families of the
small Zariski site of Tag 02YZ are therefore exactly the ordinary open covers.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isZariskiCover_iff_iUnion_points`: **Stacks 03BZ**, a family of
  open subspaces is a Zariski covering exactly when its point sets cover.
* `AlgebraicGeometry.Space.isCovering_iff_iSup_openSubspacesOrderIso`: **Stacks 03BZ**, the
  covering families of the small Zariski site are the open covers of the point space.

## Implementation notes

A Zariski covering is local surjectivity of the map from the coproduct of the members, so the
first result is a comparison of local surjectivity for the fppf topology with surjectivity on
field-valued points. The forward direction evaluates a section at the residue field of a point,
which needs the spectrum of that residue field to be an object of the site; the backward
direction refines a sieve by a covering with
`AlgebraicGeometry.Space.exists_covering_refining_sieve`, transported to the slice site over
`S` by the `exists_overCovering_refining_sieve` block below. The second result transports a
covering family through the order isomorphism of
Tag 03BZ: its members pull back to the target open subspace by Tag 083Q, and the join of the
transported members is the transported target exactly when the family covers.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space


variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

private theorem exists_sigma_component
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (I : Type u) (U : I → Subfunctor F)
    (T : BigFppfOver B S hS)
    (x : (∐ fun i ↦ (U i).toFunctor).obj (Opposite.op T)) :
    ∃ i s, (Sigma.ι (fun i ↦ (U i).toFunctor) i).app (Opposite.op T) s = x := by
  classical
  let dX := (Discrete.functor (fun i ↦ (U i).toFunctor) ⋙
    (evaluation _ _).obj (Opposite.op T))
  let d'X := Discrete.functor (fun i ↦ (U i).toFunctor.obj (Opposite.op T))
  let nX : dX ≅ d'X := Discrete.natIsoFunctor
  let eX : ((∐ fun i ↦ (U i).toFunctor).obj (Opposite.op T)) ≅
      (Σ i, (U i).toFunctor.obj (Opposite.op T)) :=
    colimitObjIsoColimitCompEvaluation
        (Discrete.functor (fun i ↦ (U i).toFunctor)) (Opposite.op T) ≪≫
      HasColimit.isoOfNatIso nX ≪≫
      Types.coproductIso (fun i ↦ (U i).toFunctor.obj (Opposite.op T))
  rcases hx : eX.hom x with ⟨i, s⟩
  refine ⟨i, s, ?_⟩
  have hIso : (Sigma.ι (fun i ↦ (U i).toFunctor) i).app (Opposite.op T) ≫ eX.hom =
      ↾(fun s ↦ (⟨i, s⟩ : Σ j, (U j).toFunctor.obj (Opposite.op T))) := by
    dsimp [eX]
    show (colimit.ι (Discrete.functor (fun i ↦ (U i).toFunctor))
      (Discrete.mk i)).app (Opposite.op T) ≫
        (colimitObjIsoColimitCompEvaluation
          (Discrete.functor (fun i ↦ (U i).toFunctor)) (Opposite.op T)).hom ≫
        (HasColimit.isoOfNatIso nX).hom ≫
        (Types.coproductIso (fun i ↦ (U i).toFunctor.obj (Opposite.op T))).hom = _
    rw [colimitObjIsoColimitCompEvaluation_ι_app_hom_assoc
      (Discrete.functor (fun i ↦ (U i).toFunctor)) (Discrete.mk i) (Opposite.op T)
      ((HasColimit.isoOfNatIso nX).hom ≫
        (Types.coproductIso (fun i ↦ (U i).toFunctor.obj (Opposite.op T))).hom),
      HasColimit.isoOfNatIso_ι_hom_assoc nX (Discrete.mk i)
        ((Types.coproductIso (fun i ↦ (U i).toFunctor.obj (Opposite.op T))).hom),
      Types.coproductIso_ι_comp_hom]
    simp [nX]
  let pair : ToType (Σ j, (U j).toFunctor.obj (Opposite.op T)) := ⟨i, s⟩
  have hcomp : eX.hom ((Sigma.ι (fun i ↦ (U i).toFunctor) i).app
      (Opposite.op T) s) = pair := by simpa [pair] using congrArg (fun f ↦ f s) hIso
  have hx' : eX.hom x = pair := by simpa [pair] using hx
  simpa using congrArg (fun z ↦ eX.inv z) (hcomp.trans hx'.symm)

private noncomputable def residueFieldTestObject
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS)
    (y : (BigFppfOver.toScheme B S hS).obj T) :
    BigFppfOver B S hS := by
  let K := Spec (((BigFppfOver.toScheme B S hS).obj T).residueField y)
  have hK : B.Contains K := B.residueField_spec_contains T.left.property y
  let V := B.obj hK
  let a : K ⟶ (BigFppfOver.toScheme B S hS).obj T :=
    ((BigFppfOver.toScheme B S hS).obj T).fromSpecResidueField y
  let fS : B.inclusion.obj V ⟶ B.inclusion.obj (B.obj hS) :=
    a ≫ B.inclusion.map T.hom
  exact Over.mk (B.inclusion.preimage fS)

private noncomputable def residueFieldTestMap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS)
    (y : (BigFppfOver.toScheme B S hS).obj T) :
    residueFieldTestObject B S hS T y ⟶ T := by
  let K := Spec (((BigFppfOver.toScheme B S hS).obj T).residueField y)
  have hK : B.Contains K := B.residueField_spec_contains T.left.property y
  let V := B.obj hK
  let a : K ⟶ (BigFppfOver.toScheme B S hS).obj T :=
    ((BigFppfOver.toScheme B S hS).obj T).fromSpecResidueField y
  let a' : V ⟶ T.left := B.inclusion.preimage a
  refine Over.homMk a' ?_
  apply B.inclusion.map_injective
  change B.inclusion.map a' ≫ B.inclusion.map T.hom =
    B.inclusion.map (B.inclusion.preimage (a ≫ B.inclusion.map T.hom))
  rw [Functor.map_preimage, Functor.map_preimage]

private noncomputable def fieldPointOfSectionAt
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : BigFppfOver B S hS) (x : G.obj (Opposite.op T))
    (y : (BigFppfOver.toScheme B S hS).obj T) :
    FieldValuedPoint B S hS G where
  carrier := ((BigFppfOver.toScheme B S hS).obj T).residueField y
  field := inferInstance
  contained := B.residueField_spec_contains T.left.property y
  toBase := B.inclusion.map (residueFieldTestObject B S hS T y).hom
  value := G.map (residueFieldTestMap B S hS T y).op x

private theorem schemePoint_fieldPointOfSectionAt
    (T : BigFppfOver B S hS)
    (y : (BigFppfOver.toScheme B S hS).obj T) :
    schemePoint B S hS T
      (fieldPointOfSectionAt B S hS T (𝟙 T) y) = y := by
  let K := Spec (((BigFppfOver.toScheme B S hS).obj T).residueField y)
  have hK : B.Contains K := B.residueField_spec_contains T.left.property y
  let V := B.obj hK
  let a : B.inclusion.obj V ⟶ (BigFppfOver.toScheme B S hS).obj T :=
    ((BigFppfOver.toScheme B S hS).obj T).fromSpecResidueField y
  show (B.inclusion.map (B.inclusion.preimage a))
      (IsLocalRing.closedPoint
        (((BigFppfOver.toScheme B S hS).obj T).residueField y)) = y
  rw [Functor.map_preimage]
  show ((BigFppfOver.toScheme B S hS).obj T).fromSpecResidueField y _ = y
  exact Scheme.fromSpecResidueField_apply y _

private theorem schemePoint_eq_of_pointsMap_eq
    (U V : BigFppfOver B S hS) (f : U ⟶ V)
    (p : FieldValuedPoint B S hS (yoneda.obj U))
    (q : FieldValuedPoint B S hS (yoneda.obj V))
    (h : pointsMap B S hS (yoneda.obj U) (yoneda.map f)
      (p.class B S hS (yoneda.obj U)) = q.class B S hS (yoneda.obj V)) :
    (BigFppfOver.toScheme B S hS).map f
      (schemePoint B S hS U p) =
    schemePoint B S hS V q := by
  rw [pointsMap_class, FieldValuedPoint.class_eq_class_iff] at h
  obtain ⟨r, ⟨a, ha⟩, ⟨b, hb⟩⟩ := h
  have hA : a ≫ p.value ≫ f = r.value := by
    change (yoneda.obj V).map a.op ((yoneda.map f).app _ p.value) = r.value at ha
    simpa using ha
  have hB : b ≫ q.value = r.value := by
    change (yoneda.obj V).map b.op q.value = r.value at hb
    simpa using hb
  have hclosedA : (BigFppfOver.toScheme B S hS).map a
      (IsLocalRing.closedPoint r.carrier) = IsLocalRing.closedPoint p.carrier := by
    have hs : Subsingleton ((BigFppfOver.toScheme B S hS).obj
        (FieldValuedPoint.siteObject B S hS (yoneda.obj V)
          (FieldValuedPoint.map B S hS (yoneda.obj U) (yoneda.map f) p))) := by
      show Subsingleton (Spec (.of p.carrier))
      infer_instance
    exact hs.elim _ _
  have hclosedB : (BigFppfOver.toScheme B S hS).map b
      (IsLocalRing.closedPoint r.carrier) = IsLocalRing.closedPoint q.carrier := by
    have hs : Subsingleton ((BigFppfOver.toScheme B S hS).obj
        (FieldValuedPoint.siteObject B S hS (yoneda.obj V) q)) := by
      show Subsingleton (Spec (.of q.carrier))
      infer_instance
    exact hs.elim _ _
  show (BigFppfOver.toScheme B S hS).map f
      ((BigFppfOver.toScheme B S hS).map p.value
        (IsLocalRing.closedPoint p.carrier)) =
    (BigFppfOver.toScheme B S hS).map q.value
      (IsLocalRing.closedPoint q.carrier)
  have h₁ : (BigFppfOver.toScheme B S hS).map (a ≫ p.value ≫ f)
      (IsLocalRing.closedPoint r.carrier) =
    (BigFppfOver.toScheme B S hS).map (b ≫ q.value)
      (IsLocalRing.closedPoint r.carrier) := by rw [hA, hB]
  rw [Functor.map_comp, Functor.map_comp] at h₁
  rw [← hclosedA, ← hclosedB]
  exact h₁

/-- **Stacks 03H4** for a cartesian square of presheaves whose four corners are algebraic
spaces, rather than for a square in the category of algebraic spaces over `S`. -/
private theorem exists_point_of_isPullback_presheaf
    {P Z X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace B S hS P) (hZ : IsAlgebraicSpace B S hS Z)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    {p : P ⟶ Z} {q : P ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y}
    (sq : IsPullback p q g f)
    (z : points B S hS Z) (x : points B S hS X)
    (h : pointsMap B S hS Z g z = pointsMap B S hS X f x) :
    ∃ w : points B S hS P,
      pointsMap B S hS P p w = z ∧ pointsMap B S hS P q w = x :=
  exists_point_of_isPullback B S hS
    (IsPullback.of_map_of_faithful (ObjectProperty.ι _) sq :
      IsPullback (ObjectProperty.homMk p : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩)
        (ObjectProperty.homMk q : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
        (ObjectProperty.homMk g : (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
        (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)) z x h

private theorem exists_point_in_open_pullback
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : IsAlgebraicSpace B S hS G)
    (U : Subfunctor G) (hU : IsOpenSubspace B S hS U)
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ G)
    (p : points B S hS (yoneda.obj T))
    (q : points B S hS U.toFunctor)
    (h : pointsMap B S hS (yoneda.obj T) f p =
      pointsMap B S hS U.toFunctor U.ι q) :
    ∃ v : points B S hS
        (yoneda.obj ((hU.2.1).pullback f)),
      pointsMap B S hS
        (yoneda.obj ((hU.2.1).pullback f))
        (yoneda.map ((hU.2.1).snd f)) v = p ∧
      pointsMap B S hS
        (yoneda.obj ((hU.2.1).pullback f)) ((hU.2.1).fst f) v = q := by
  obtain ⟨v, hv₁, hv₂⟩ := exists_point_of_isPullback_presheaf B S hS
    (isAlgebraicSpace_yoneda B S hS _) hU.1 (isAlgebraicSpace_yoneda B S hS T) hG
    ((hU.2.1).isPullback f) q p h.symm
  exact ⟨v, hv₂, hv₁⟩

private theorem generated_scheme_fppf_family_mem_topology
    (B : BigFppfSite.{u}) {X : B.Schemes} {I : Type (u + 1)}
    (V : I → B.Schemes) (f : ∀ i, V i ⟶ X)
    (hP : Presieve.ofArrows (fun i ↦ B.inclusion.obj (V i))
      (fun i ↦ B.inclusion.map (f i)) ∈
      Scheme.fppfPrecoverage (B.inclusion.obj X)) :
    Sieve.generate (Presieve.ofArrows V f) ∈ B.topology X := by
  let E : Covering.{u + 1, u, u + 1} B.Schemes := ⟨X,
    (⟨I, V, f⟩ : PreZeroHypercover.{u + 1} X)⟩
  have hE : IsFppfCovering E := by
    show E.2.presieve₀.map B.inclusion ∈
      Scheme.fppfPrecoverage (B.inclusion.obj X)
    simpa [E, PreZeroHypercover.map] using hP
  obtain ⟨E', hE', hEquiv⟩ := B.fppf_has_representative E hE
  have hpre : E.2.presieve₀ ∈ B.precoverage X := by
    obtain ⟨hX, hComb⟩ := hEquiv
    cases hX
    rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hComb]
    exact ⟨E'.2, rfl, hE'⟩
  simpa [E] using Precoverage.generate_mem_toGrothendieck hpre

/-- A family of morphisms of the big fppf category over `S` whose underlying family of
morphisms of schemes is an fppf precovering generates a covering sieve for the topology of
`AlgebraicGeometry.BigFppfOver`.

The sieve is transported between the site over `X` and the site of schemes by
`CategoryTheory.Sieve.overEquiv`, under which it is the sieve generated by the underlying
family. -/
public theorem generated_over_fppf_family_mem_topology
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : BigFppfOver B S hS} {I : Type (u + 1)}
    (W : I → BigFppfOver B S hS) (q : ∀ i, W i ⟶ X)
    (hP : Presieve.ofArrows (fun i ↦ B.inclusion.obj (W i).left)
      (fun i ↦ B.inclusion.map (q i).left) ∈
      Scheme.fppfPrecoverage (B.inclusion.obj X.left)) :
    Sieve.generate (Presieve.ofArrows W q) ∈
      BigFppfOver.topology B S hS X := by
  rw [BigFppfOver.topology, GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate,
    ← Sieve.overEquiv_generate, Sieve.overEquiv_ofArrows]
  exact generated_scheme_fppf_family_mem_topology B
    (fun i ↦ (W i).left) (fun i ↦ (q i).left) hP

private theorem isLocallySurjective_sigma_desc_of_points_cover
    (hF : IsAlgebraicSpace B S hS F)
    (I : Type u) (U : I → Subfunctor F)
    (hU : ∀ i, IsOpenSubspace B S hS (U i))
    (hcover : (⋃ i, Set.range
      (pointsMap B S hS (U i).toFunctor (U i).ι)) = Set.univ) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Sigma.desc fun i ↦ (U i).ι) := by
  classical
  refine ⟨fun {T} x ↦ ?_⟩
  let f : yoneda.obj T ⟶ F := yonedaEquiv.symm x
  let W (i : I) := (hU i).2.1.pullback f
  let q (i : I) : W i ⟶ T := (hU i).2.1.snd f
  have hpoints (y : (BigFppfOver.toScheme B S hS).obj T) :
      ∃ i, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (q i)) := by
    let p : FieldValuedPoint B S hS (yoneda.obj T) :=
      fieldPointOfSectionAt B S hS T (𝟙 T) y
    let pF := FieldValuedPoint.map B S hS (yoneda.obj T) f p
    have hp : pF.class B S hS F ∈ ⋃ i, Set.range
        (pointsMap B S hS (U i).toFunctor (U i).ι) := by
      rw [hcover]
      simp
    obtain ⟨i, r, hr⟩ := Set.mem_iUnion.mp hp
    have hr' : pointsMap B S hS (yoneda.obj T) f
        (p.class B S hS (yoneda.obj T)) =
        pointsMap B S hS (U i).toFunctor (U i).ι r := by
      simpa [pF] using hr.symm
    obtain ⟨v, hv₁, -⟩ := exists_point_in_open_pullback
      B S hS hF (U i) (hU i) T f p.class r hr'
    obtain ⟨v', rfl⟩ := Quot.exists_rep v
    have hscheme := schemePoint_eq_of_pointsMap_eq B S hS (W i) T (q i) v' p (by
      simpa using hv₁)
    have hy : schemePoint B S hS T p = y := by
      simpa [p] using schemePoint_fieldPointOfSectionAt B S hS T y
    refine ⟨i, ?_⟩
    refine ⟨schemePoint B S hS (W i) v', ?_⟩
    simpa [q] using hscheme.trans hy
  have hopen (i : I) : AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (q i)) := by
    show AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map ((hU i).2.1.snd f))
    exact (hU i).2.2 f _ _ ((hU i).2.1.isPullback f)
  let W' (j : ULift.{u + 1, u} I) := W j.down
  let q' (j : ULift.{u + 1, u} I) : W' j ⟶ T := q j.down
  have hP : Presieve.ofArrows
      (fun i ↦ B.inclusion.obj (W' i).left)
      (fun i ↦ B.inclusion.map (q' i).left) ∈
        Scheme.fppfPrecoverage (B.inclusion.obj T.left) := by
    have hz : Presieve.ofArrows
        (fun i ↦ (BigFppfOver.toScheme B S hS).obj (W' i))
        (fun i ↦ (BigFppfOver.toScheme B S hS).map (q' i)) ∈
        Scheme.zariskiPrecoverage ((BigFppfOver.toScheme B S hS).obj T) := by
      rw [Scheme.ofArrows_mem_precoverage_iff (P := @AlgebraicGeometry.IsOpenImmersion)]
      refine ⟨?_, fun j ↦ hopen j.down⟩
      intro y
      obtain ⟨i, z, hz⟩ := hpoints y
      exact ⟨ULift.up i, z, hz⟩
    exact Scheme.zariskiPrecoverage_le_fppfPrecoverage _ hz
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    (generated_over_fppf_family_mem_topology B S hS W' q' hP)
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro j
  let i := j.down
  let sec := ((hU i).2.1.fst f).app (Opposite.op (W i)) (𝟙 (W i))
  refine ⟨(Sigma.ι (fun k ↦ (U k).toFunctor) i).app (Opposite.op (W' j))
      sec, ?_⟩
  show ((Sigma.ι (fun k ↦ (U k).toFunctor) i ≫
      Sigma.desc (fun k ↦ (U k).ι)).app (Opposite.op (W' j)) sec) =
    F.map (q' j).op x
  rw [Sigma.ι_desc]
  have hw := congrArg
    (fun α : yoneda.obj (W i) ⟶ F => α.app (Opposite.op (W i)) (𝟙 (W i)))
    ((hU i).2.1.w f)
  simpa [sec, q, q', W, W', f, yonedaEquiv_naturality,
    yonedaEquiv_yoneda_map] using hw

/-- A family of subfunctors whose coproduct maps locally surjectively onto `F` covers the
points of `F` of Stacks 03BU.

This is the point-set content of local surjectivity, and it is the unconditional input
through which an algebraic space's atlas is shown to be surjective on points without any
effective-descent hypothesis — the routes through `Space.quotientMap_surjective` and
`Space.isAlgebraicSpace_quotientSheaf` all carry one. -/
theorem points_cover_of_isLocallySurjective_sigma_desc
    (I : Type u) (U : I → Subfunctor F)
    (hls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Sigma.desc fun i ↦ (U i).ι)) :
    (⋃ i, Set.range (pointsMap B S hS (U i).toFunctor (U i).ι)) = Set.univ := by
  classical
  refine Set.eq_univ_of_forall fun x ↦ ?_
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  let T := FieldValuedPoint.siteObject B S hS F p
  let sigma := Sigma.desc fun i ↦ (U i).ι
  let R := Presheaf.imageSieve sigma p.value
  let : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) sigma := hls
  have hR : R ∈ BigFppfOver.topology B S hS T :=
    Presheaf.imageSieve_mem _ sigma p.value
  obtain ⟨E, hE, hle⟩ := exists_overCovering_refining_sieve B S hS hR
  let E₀ : Covering B.Schemes :=
    ⟨T.left, E.map (Over.forget (B.obj hS))⟩
  have hfp : IsFppfCovering E₀ := B.isFppfCovering_of_isCovering hE
  let E₁ := (E.map (Over.forget (B.obj hS))).map B.inclusion
  have hfp' : E₁.presieve₀ ∈
      Scheme.fppfPrecoverage (B.inclusion.obj T.left) := by
    simpa [E₁, E₀, IsFppfCovering, PreZeroHypercover.map] using hfp
  have hdata := (Scheme.presieve₀_mem_precoverage_iff E₁).mp hfp'
  let y₀ : (BigFppfOver.toScheme B S hS).obj T :=
    IsLocalRing.closedPoint p.carrier
  obtain ⟨j₁, z, hz⟩ := hdata.1 y₀
  let j : E.I₀ := j₁
  let z' : (BigFppfOver.toScheme B S hS).obj (E.X j) := by
    simpa [j, E₁, PreZeroHypercover.map] using z
  obtain ⟨s, hs⟩ : ∃ s : (∐ fun i ↦ (U i).toFunctor).obj (Opposite.op (E.X j)),
      sigma.app (Opposite.op (E.X j)) s = F.map (E.f j).op p.value := hle _ _ ⟨j⟩
  obtain ⟨i, t, htcomp⟩ := exists_sigma_component B S hS I U (E.X j) s
  have hcomp : sigma.app (Opposite.op (E.X j))
      ((Sigma.ι (fun k ↦ (U k).toFunctor) i).app
        (Opposite.op (E.X j)) t) = (U i).ι.app (Opposite.op (E.X j)) t := by
    show ((Sigma.ι (fun k ↦ (U k).toFunctor) i ≫
      Sigma.desc (fun k ↦ (U k).ι)).app (Opposite.op (E.X j)) t) = _
    rw [Sigma.ι_desc]
  have ht : (U i).ι.app (Opposite.op (E.X j)) t =
      F.map (E.f j).op p.value := hcomp.symm.trans (by rw [htcomp, hs])
  let qpt : FieldValuedPoint B S hS (U i).toFunctor :=
    fieldPointOfSectionAt B S hS (E.X j) t z'
  let qF := FieldValuedPoint.map B S hS (U i).toFunctor (U i).ι qpt
  let a := residueFieldTestMap B S hS (E.X j) z'
  let g : qpt.siteObject B S hS (U i).toFunctor ⟶ T := a ≫ E.f j
  have hmap : F.map (a ≫ E.f j).op p.value =
      F.map a.op (F.map (E.f j).op p.value) := by
    show F.map ((E.f j).op ≫ a.op) p.value = _
    rw [Functor.map_comp_apply]
  have hsite : qpt.siteObject B S hS (U i).toFunctor =
      residueFieldTestObject B S hS (E.X j) z' := by
    rfl
  cases hsite
  have hval : F.map g.op p.value = qF.value := by
    show F.map (a ≫ E.f j).op p.value = qF.value
    rw [hmap, ht.symm]
    dsimp [qF, FieldValuedPoint.map]
    show F.map a.op ((U i).ι.app (Opposite.op (E.X j)) t) =
      (U i).ι.app (Opposite.op (residueFieldTestObject B S hS (E.X j) z'))
        ((U i).toFunctor.map a.op t)
    rw [(U i).ι.naturality_apply a.op t]
  have hEq : qF.class B S hS F = p.class B S hS F :=
    FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS F
      ⟨qF, FieldValuedPoint.dominates_refl B S hS F qF,
        ⟨g, hval⟩⟩
  exact Set.mem_iUnion.mpr ⟨i, qpt.class B S hS (U i).toFunctor, by simpa [qF] using hEq⟩


/-- Open subspaces cover an algebraic space in the Zariski topology if and only
if their images on the space of points cover all points. -/
@[stacks 03BZ "zariski_coverings"]
theorem isZariskiCover_iff_iUnion_points
    (hF : IsAlgebraicSpace B S hS F) (I : Type u)
    (U : I → Subfunctor F)
    (hU : ∀ i, IsOpenSubspace B S hS (U i)) :
    IsZariskiCover B S hS I U ↔
      (⋃ i, Set.range (pointsMap B S hS (U i).toFunctor (U i).ι)) =
        Set.univ :=
  ⟨fun hcov ↦ points_cover_of_isLocallySurjective_sigma_desc B S hS F I U hcov.2,
    fun hpoints ↦ ⟨hU, isLocallySurjective_sigma_desc_of_points_cover B S hS F hF I U hU
      hpoints⟩⟩

/-- Via the canonical identification with open subsets of the point space,
covering families of the small Zariski site are precisely open covers. -/
@[stacks 03BZ "zariski_coverings"]
theorem isCovering_iff_iSup_openSubspacesOrderIso
    (hF : IsAlgebraicSpace B S hS F)
    (E : Covering.{u + 1, u + 1, u} (OpenSubspaces B S hS F)) :
    let : TopologicalSpace (points B S hS F) :=
      pointTopology B S hS F
    OpenSubspaces.IsCovering B S hS F E ↔
      (⨆ i, openSubspacesOrderIso B S hS F hF
        (E.2.X i)) =
        openSubspacesOrderIso B S hS F hF E.1 := by
  let : TopologicalSpace (points B S hS F) :=
    pointTopology B S hS F
  let G : Subfunctor F := E.1.1
  have hG : IsAlgebraicSpace B S hS G.toFunctor := E.1.2.1
  let W (i : E.2.I₀) : Subfunctor F := (E.2.X i).1
  have hle (i : E.2.I₀) : W i ≤ G := (E.2.f i).le
  let V (i : E.2.I₀) : Subfunctor G.toFunctor := (W i).preimage G.ι
  have hV (i : E.2.I₀) : IsOpenSubspace B S hS (V i) := by
    rw [show V i = Subfunctor.range (Subfunctor.homOfLe (hle i)) from
      preimage_eq_range_homOfLe (hle i)]
    exact isOpenSubspace_of_le B S hS (W i) G (E.2.X i).2
      (hle i)
  let gmap := pointsMap B S hS G.toFunctor G.ι
  let umap (i : E.2.I₀) :=
    pointsMap B S hS (W i).toFunctor (W i).ι
  let vmap (i : E.2.I₀) :=
    pointsMap B S hS (V i).toFunctor (V i).ι
  let fromV (i : E.2.I₀) := Subfunctor.fromPreimage (W i) G.ι
  let fromU (i : E.2.I₀) := Subfunctor.homOfLe (hle i)
  have hfromU (i : E.2.I₀) : fromU i ≫ G.ι = (W i).ι := by
    ext X x
    rfl
  have hfromV (i : E.2.I₀) : fromV i ≫ (W i).ι = (V i).ι ≫ G.ι :=
    Subfunctor.fromPreimage_ι (W i) G.ι
  have hcoverPts :
      OpenSubspaces.IsCovering B S hS F E ↔
        (⋃ i, Set.range (vmap i)) = Set.univ := by
    show IsZariskiCover B S hS E.2.I₀
        (fun i => (E.2.X i).1.preimage E.1.1.ι) ↔ _
    simpa [G, V] using
      (isZariskiCover_iff_iUnion_points B S hS G.toFunctor hG E.2.I₀ V hV)
  have hpoints_iff :
      (⋃ i : E.2.I₀, Set.range (vmap i)) = Set.univ ↔
        (⋃ i : E.2.I₀, Set.range (umap i)) = Set.range gmap := by
    constructor
    · intro hv
      apply Set.ext
      intro x
      constructor
      · intro hx
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        obtain ⟨p, hp⟩ := Set.mem_range.mp hi
        refine ⟨pointsMap B S hS (W i).toFunctor (fromU i) p, ?_⟩
        rw [← hp]
        exact (pointsMap_comp_apply B S hS (fromU i) G.ι p).symm.trans
          (congrArg (fun α ↦ pointsMap B S hS _ α p) (hfromU i))
      · intro hx
        obtain ⟨p, hp⟩ := Set.mem_range.mp hx
        have hpcover : p ∈ ⋃ i : E.2.I₀, Set.range (vmap i) := by
          rw [hv]
          simp
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpcover
        obtain ⟨q, hq⟩ := Set.mem_range.mp hi
        refine Set.mem_iUnion.mpr ⟨i, Set.mem_range.mpr ?_⟩
        refine ⟨pointsMap B S hS (V i).toFunctor (fromV i) q, ?_⟩
        exact (pointsMap_apply_comm B S hS (hfromV i) q).trans
          ((congrArg gmap hq).trans hp)
    · intro h
      apply Set.ext
      intro p
      constructor
      · intro _
        simp
      · intro _
        have hp : gmap p ∈ ⋃ i : E.2.I₀, Set.range (umap i) := by
          rw [h]
          exact Set.mem_range.mpr ⟨p, rfl⟩
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
        obtain ⟨q, hq⟩ := Set.mem_range.mp hi
        obtain ⟨v, -, hv₂⟩ := exists_point_of_isPullback_presheaf B S hS
          (hV i).1 (E.2.X i).2.1 hG hF (Subfunctor.isPullback_preimage G.ι (W i)) q p hq
        exact Set.mem_iUnion.mpr ⟨i, Set.mem_range.mpr ⟨v, hv₂⟩⟩
  let e := openSubspacesOrderIso B S hS F hF
  have he_i (i : E.2.I₀) : (e (E.2.X i) : Set (points B S hS F)) =
      Set.range (umap i) := by
    simpa [e, umap] using
      (openSubspacesOrderIso_apply B S hS F hF
        (E.2.X i))
  have he_target : (e E.1 : Set (points B S hS F)) =
      Set.range gmap := by
    simpa [e, gmap] using
      (openSubspacesOrderIso_apply B S hS F hF E.1)
  have hopen_iff :
      (⨆ i, e (E.2.X i)) = e E.1 ↔
        (⋃ i, Set.range (umap i)) = Set.range gmap := by
    rw [← SetLike.coe_set_eq, TopologicalSpace.Opens.coe_iSup, Set.iUnion_congr he_i,
      he_target]
  exact hcoverPts.trans (hpoints_iff.trans hopen_iff.symm)

/-! ### Surjectivity on points

These two were duplicated as `private` in `Spaces/Morphisms/UniversallyClosed.lean` and
`Spaces/Morphisms/UniversallyInjective.lean`, which could not share them precisely because
they were private. They live here because this is the module that proves
`points_cover_of_isLocallySurjective_sigma_desc`, which the second one uses, and because
both of those modules already reach this one. -/

/-- A morphism of presheaves on the big fppf site of `S` which is surjective in every degree is
surjective on the points of Stacks 03BU: a field-valued representative of a point of the target
lifts to a field-valued point of the source over the same field spectrum. -/
theorem surjective_pointsMap_of_surjective_app
    {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (α : P ⟶ Q)
    (hα : ∀ T, Function.Surjective (α.app T)) :
    Function.Surjective (pointsMap B S hS P α) := by
  intro y
  obtain ⟨q, rfl⟩ := Quot.exists_rep y
  obtain ⟨v, hv⟩ := hα (Opposite.op q.siteObject) q.value
  refine ⟨({ carrier := q.carrier
             field := q.field
             contained := q.contained
             toBase := q.toBase
             value := v } : FieldValuedPoint B S hS P).class B S hS P, ?_⟩
  exact congrArg (fun w ↦ ({ carrier := q.carrier
                             field := q.field
                             contained := q.contained
                             toBase := q.toBase
                             value := w } : FieldValuedPoint B S hS Q).class B S hS Q) hv

/-- A locally surjective morphism of presheaves on the big fppf site of `S` is surjective on the
points of Stacks 03BU.

This is `AlgebraicGeometry.Space.points_cover_of_isLocallySurjective_sigma_desc` for the
one-member family consisting of the range of the morphism, which is locally surjective because
the morphism factors through it, together with the surjectivity in every degree of the morphism
onto its range. -/
theorem surjective_pointsMap_of_isLocallySurjective
    {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : P ⟶ Q)
    (hf : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f) :
    Function.Surjective (pointsMap B S hS P f) := by
  have : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Subfunctor.range f).ι :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ (Subfunctor.toRange_ι f)
  have : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Sigma.desc fun _ : PUnit.{u + 1} ↦ (Subfunctor.range f).ι) :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
      (Sigma.ι_desc (fun _ : PUnit.{u + 1} ↦ (Subfunctor.range f).ι) PUnit.unit)
  have hcover := points_cover_of_isLocallySurjective_sigma_desc B S hS Q PUnit.{u + 1}
    (fun _ ↦ Subfunctor.range f) inferInstance
  have hrange : Function.Surjective
      (pointsMap B S hS P (Subfunctor.toRange f)) := by
    refine surjective_pointsMap_of_surjective_app B S hS _ fun T ↦ ?_
    rw [← CategoryTheory.epi_iff_surjective]
    exact (NatTrans.epi_iff_epi_app (Subfunctor.toRange f)).mp inferInstance T
  intro y
  obtain ⟨-, z, hz⟩ := Set.mem_iUnion.1 (hcover ▸ Set.mem_univ y)
  obtain ⟨w, hw⟩ := hrange z
  refine ⟨w, ?_⟩
  rw [← Subfunctor.toRange_ι f, pointsMap_comp, Function.comp_apply, hw, hz]

end AlgebraicGeometry.Space

end
