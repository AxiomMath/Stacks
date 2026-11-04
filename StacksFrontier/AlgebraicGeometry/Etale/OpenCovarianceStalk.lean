module

public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportStalkIso
public import StacksFrontier.AlgebraicGeometry.Etale.OpenCovariance
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.CoefficientsGerm

/-!
# Covariance and the geometric stalks of the finite-support direct image

Let `j : X' ⟶ X` be an open immersion and `f : X ⟶ Y` locally of finite type and locally
quasi-finite in a big étale site, write `f' = j ≫ f`, and let `F` be an abelian sheaf on the small
étale site of `X`. A point of the geometric fibre of `f'` over a geometric point `s` of `Y` gives
a point of the geometric fibre of `f` by composing with `j`, injectively, and over corresponding
points the stalk of the restriction `F|_{X'}` is the stalk of `F`. This file proves that the
covariance map of Stacks 0F6S is, on the stalk decomposition of Stacks 0F6P, extension by zero
along that inclusion of geometric fibres.

## Main definitions

* `AlgebraicGeometry.SmallEtale.openFiberPoint` — the inclusion of the geometric fibre of `f'`
  into the geometric fibre of `f`.
* `AlgebraicGeometry.SmallEtale.openFiberStalkIso` — the identification of the stalk of `F|_{X'}`
  at a point of the geometric fibre of `f'` with the stalk of `F` at its image.
* `AlgebraicGeometry.SmallEtale.finiteSupportStalkGenerator` — the germ at the geometric point of
  the base of a section supported on a support finite over an étale neighbourhood.
* `AlgebraicGeometry.SmallEtale.openCovarianceStalkMap` — the map of Stacks 0F6S read on the
  geometric stalk at `s`.

## Main results

* `AlgebraicGeometry.SmallEtale.fiberPointLift_openBaseChangeHom` — the lift of a point of the
  geometric fibre of `f'` to `X'_V` becomes the lift of its image to `X_V`.
* `AlgebraicGeometry.SmallEtale.hasFiberLift_openFiberPoint_iff` — a point of the geometric fibre
  of `f'` meets the canonical open of a support exactly when its image meets the canonical open of
  the image support.
* `AlgebraicGeometry.SmallEtale.exists_openFiberPoint_of_mem_image` — a point of the geometric
  fibre of `f` whose lift meets the image of a support of `f'` comes from the geometric fibre
  of `f'`.
* `AlgebraicGeometry.SmallEtale.fiberStalkComponent_covarianceSectionMap` and
  `AlgebraicGeometry.SmallEtale.fiberStalkComponent_covarianceSectionMap_eq_zero` — **Stacks 0F6S,
  part (1)** on a colimit generator: the germ of the extended section at the image of a point of
  the geometric fibre of `f'` is the germ of the original section read through the identification
  of the two stalks, and it vanishes in every other summand.
* `AlgebraicGeometry.SmallEtale.fiberStalks_openCovarianceStalkMap_openFiberPoint` and
  `AlgebraicGeometry.SmallEtale.fiberStalks_openCovarianceStalkMap_eq_zero` — **Stacks 0F6S,
  part (1)** for the finite-support direct-image presheaves: on the stalk decompositions of
  Stacks 0F6P the covariance map of Stacks 0F6S is the extension by zero along the inclusion of
  geometric fibres.

## Implementation notes

The identification of the two stalks over corresponding points of the geometric fibres is the
inverse-image comparison of Stacks 03Q1 with abelian coefficients, since the restriction functor
`AlgebraicGeometry.SmallEtale.openRestriction` *is* the inverse image along small étale base
change. What makes the computation possible is its description on germs,
`AlgebraicGeometry.smallEtalePullbackSheafFiberIso_germ`, together with the fact that the
covariance generator data of `AlgebraicGeometry.SmallEtale.covarianceGeneratorData` records
exactly the restriction of the extended section along the unit of that adjunction.

## References

* [Stacks Project, Tag 0F6S](https://stacks.math.columbia.edu/tag/0F6S)
* [Stacks Project, Tag 0F6P](https://stacks.math.columbia.edu/tag/0F6P)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

section FiberPoints

variable (B : BigEtaleSite.{u}) {X' X Y : B.Scheme} (j : X' ⟶ X) (f : X ⟶ Y)
  [IsOpenImmersion (B.inclusion.map j)] (s : GeometricPoint Y.obj)

/-- A point of the geometric fibre of `j ≫ f` gives a point of the geometric fibre of `f`, by
composing with the open immersion. -/
public def openFiberPoint (x : GeometricFiberPoint B (j ≫ f) s) : GeometricFiberPoint B f s :=
  ⟨x.1 ≫ B.inclusion.map j, by
    rw [Category.assoc, ← Functor.map_comp]
    exact x.2⟩

/-- The inclusion of geometric fibres is injective, an open immersion being a monomorphism. -/
public theorem openFiberPoint_injective : Function.Injective (openFiberPoint B j f s) :=
  fun _ _ h => Subtype.ext ((cancel_mono (B.inclusion.map j)).1 (congrArg Subtype.val h))

omit [IsOpenImmersion (B.inclusion.map j)] in
/-- The geometric point of `X` underlying the image of a point of the geometric fibre of `j ≫ f`
is the image of the geometric point of `X'` underlying it. -/
public theorem openFiberPoint_toGeometricPoint (x : GeometricFiberPoint B (j ≫ f) s) :
    (openFiberPoint B j f s x).toGeometricPoint B f s =
      (x.toGeometricPoint B (j ≫ f) s).map (B.inclusion.map j) :=
  rfl

end FiberPoints

section Lifts

variable (B : BigEtaleSite.{u}) {X' X Y : B.Scheme} (j : X' ⟶ X) (f : X ⟶ Y)
  [IsOpenImmersion (B.inclusion.map j)] (s : GeometricPoint Y.obj)

/-- The induced open immersion of étale base changes is a morphism over `X`, so it carries the
structure morphism of `X'_V` composed with `j` to the structure morphism of `X_V`. -/
public theorem openBaseChangeHom_comp_hom (V : SmallEtale B Y.obj Y.property) :
    openBaseChangeHom B j f V ≫ B.inclusion.map ((baseChange B f V).obj.hom) =
      B.inclusion.map ((baseChange B (j ≫ f) V).obj.hom) ≫ B.inclusion.map j := by
  have h := SmallEtale.toScheme_map_comp B X.obj X.property ((openBaseChangeMap B j f).app V)
  rw [openBaseChangeMap_toScheme] at h
  exact h.trans (B.inclusion.map_comp ((baseChange B (j ≫ f) V).obj.hom) j)

/-- The lift to `X'_V` of a point of the geometric fibre of `j ≫ f` becomes, through the induced
open immersion of base changes, the lift to `X_V` of its image in the geometric fibre of `f`. -/
public theorem fiberPointLift_openBaseChangeHom (V : SmallEtale B Y.obj Y.property)
    (u : (geometricPointFiber B Y.obj Y.property s).obj V)
    (x : GeometricFiberPoint B (j ≫ f) s) :
    fiberPointLift B (j ≫ f) s V u x ≫ openBaseChangeHom B j f V =
      fiberPointLift B f s V u (openFiberPoint B j f s x) := by
  have hsnd : openBaseChangeHom B j f V ≫ B.inclusion.map (pullback.snd V.obj.hom f) =
      B.inclusion.map (pullback.snd V.obj.hom (j ≫ f)) ≫ B.inclusion.map j :=
    openBaseChangeHom_comp_hom B j f V
  refine ((IsPullback.of_hasPullback V.obj.hom f).map B.inclusion).hom_ext ?_ ?_
  · calc (fiberPointLift B (j ≫ f) s V u x ≫ openBaseChangeHom B j f V) ≫
          B.inclusion.map (pullback.fst V.obj.hom f)
        = fiberPointLift B (j ≫ f) s V u x ≫
            (openBaseChangeHom B j f V ≫ B.inclusion.map (pullback.fst V.obj.hom f)) :=
          Category.assoc _ _ _
      _ = fiberPointLift B (j ≫ f) s V u x ≫
            B.inclusion.map (pullback.fst V.obj.hom (j ≫ f)) :=
          congrArg (fun m => fiberPointLift B (j ≫ f) s V u x ≫ m)
            (openBaseChangeHom_comp B j f V)
      _ = u.1 := fiberPointLift_comp_fst B (j ≫ f) s V u x
      _ = fiberPointLift B f s V u (openFiberPoint B j f s x) ≫
            B.inclusion.map (pullback.fst V.obj.hom f) :=
          (fiberPointLift_comp_fst B f s V u (openFiberPoint B j f s x)).symm
  · calc (fiberPointLift B (j ≫ f) s V u x ≫ openBaseChangeHom B j f V) ≫
          B.inclusion.map (pullback.snd V.obj.hom f)
        = fiberPointLift B (j ≫ f) s V u x ≫
            (openBaseChangeHom B j f V ≫ B.inclusion.map (pullback.snd V.obj.hom f)) :=
          Category.assoc _ _ _
      _ = fiberPointLift B (j ≫ f) s V u x ≫
            (B.inclusion.map (pullback.snd V.obj.hom (j ≫ f)) ≫ B.inclusion.map j) :=
          congrArg (fun m => fiberPointLift B (j ≫ f) s V u x ≫ m) hsnd
      _ = (fiberPointLift B (j ≫ f) s V u x ≫
            B.inclusion.map (pullback.snd V.obj.hom (j ≫ f))) ≫ B.inclusion.map j :=
          (Category.assoc _ _ _).symm
      _ = x.1 ≫ B.inclusion.map j :=
          congrArg (fun m => m ≫ B.inclusion.map j)
            (fiberPointLift_comp_snd B (j ≫ f) s V u x)
      _ = fiberPointLift B f s V u (openFiberPoint B j f s x) ≫
            B.inclusion.map (pullback.snd V.obj.hom f) :=
          (fiberPointLift_comp_snd B f s V u (openFiberPoint B j f s x)).symm

/-- A point of the geometric fibre of `j ≫ f` lifts into the canonical open of a support exactly
when its image lifts into the canonical open of the image support. -/
public theorem hasFiberLift_openFiberPoint_iff (V : SmallEtale B Y.obj Y.property)
    (u : (geometricPointFiber B Y.obj Y.property s).obj V)
    (E : FiniteSupport B (j ≫ f) V) (D : FiniteSupport B f V)
    (hD : D.1 = (openBaseChangeHom B j f V).base '' E.1)
    (x : GeometricFiberPoint B (j ≫ f) s) :
    HasFiberLift B f s V u D (openFiberPoint B j f s x) ↔
      HasFiberLift B (j ≫ f) s V u E x := by
  have hbase : (fiberPointLift B f s V u (openFiberPoint B j f s x)).base default =
      (openBaseChangeHom B j f V).base ((fiberPointLift B (j ≫ f) s V u x).base default) :=
    congrArg (fun m => m.base (default : ↥s.source))
      (fiberPointLift_openBaseChangeHom B j f s V u x).symm
  have hpre := openBaseChangeHom_supportOpen_preimage B j f V E D hD
  show (fiberPointLift B f s V u (openFiberPoint B j f s x)).base default ∈
      (finiteSupportOpen B f V D : Set _) ↔
    (fiberPointLift B (j ≫ f) s V u x).base default ∈
      (finiteSupportOpen B (j ≫ f) V E : Set _)
  rw [hbase, ← hpre]
  exact Iff.rfl

end Lifts

section Germ

variable (B : BigEtaleSite.{u}) {X' X : B.Scheme} (j : X' ⟶ X)
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- **Stacks 03Q1** on germs, in the form used for the restriction functor: the identification of
the stalk of `F|_{X'}` at a geometric point `t` of `X'` with the stalk of `F` at its image sends
the germ of a restricted section to the germ of the original section. -/
public theorem etaleGerm_pullbackSectionAlongHom (t : GeometricPoint X'.obj)
    (W : SmallEtale B X.obj X.property)
    (q : (geometricPointFiber B X.obj X.property (t.map (B.inclusion.map j))).obj W)
    (W' : SmallEtale B X'.obj X'.property)
    (q' : (geometricPointFiber B X'.obj X'.property t).obj W')
    (b : W' ⟶ (smallEtaleBaseChange B j).obj W)
    (hb : q'.1 ≫ (SmallEtale.toScheme B X'.obj X'.property).map b ≫
      B.inclusion.map (pullback.fst W.obj.hom j) = q.1)
    (τ : F.obj.obj (op W)) :
    (etaleStalkSmallEtalePullObjIso B j t AddCommGrpCat.{max (u + 1) v} F).hom
        (etaleGerm B X'.obj X'.property t ((openRestriction.{u, v} B j).obj F).obj W' q'
          (pullbackSectionAlongHom B j AddCommGrpCat.{max (u + 1) v} F W W' b τ)) =
      etaleGerm B X.obj X.property (t.map (B.inclusion.map j)) F.obj W q τ := by
  have h := ConcreteCategory.congr_hom
    (etaleStalkSmallEtalePullObjIso_germ B j t AddCommGrpCat.{max (u + 1) v} F
      (⟨W', q'⟩ : (geometricPointFiber B X'.obj X'.property t).Elements)
      (⟨W, q⟩ : (geometricPointFiber B X.obj X.property
        (t.map (B.inclusion.map j))).Elements) b hb) τ
  simp only [ConcreteCategory.comp_apply] at h
  exact h

end Germ

section Generator

variable (B : BigEtaleSite.{u}) {X' X Y : B.Scheme} (j : X' ⟶ X) (f : X ⟶ Y)
  [IsOpenImmersion (B.inclusion.map j)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
  (s : GeometricPoint Y.obj)

/-- The identification of the stalk of the restriction `F|_{X'}` at a point of the geometric fibre
of `j ≫ f` with the stalk of `F` at its image in the geometric fibre of `f`. -/
public abbrev openFiberStalkIso (x : GeometricFiberPoint B (j ≫ f) s) :
    etaleStalk B X'.obj X'.property (x.toGeometricPoint B (j ≫ f) s)
        ((openRestriction.{u, v} B j).obj F).obj ≅
      etaleStalk B X.obj X.property ((openFiberPoint B j f s x).toGeometricPoint B f s) F.obj :=
  etaleStalkSmallEtalePullObjIso B j (x.toGeometricPoint B (j ≫ f) s)
    AddCommGrpCat.{max (u + 1) v} F

/-- The lift of a point of the geometric fibre of `j ≫ f` into the canonical open of a support is
carried by the comparison of canonical support opens to the lift of its image into the canonical
open of the image support. -/
public theorem openObjectLift_covarianceOpenMap (V : SmallEtale B Y.obj Y.property)
    (u : (geometricPointFiber B Y.obj Y.property s).obj V)
    (E : FiniteSupport B (j ≫ f) V) (D : FiniteSupport B f V)
    (hD : D.1 = (openBaseChangeHom B j f V).base '' E.1)
    (x : GeometricFiberPoint B (j ≫ f) s)
    (h' : HasFiberLift B (j ≫ f) s V u E x)
    (h : HasFiberLift B f s V u D (openFiberPoint B j f s x)) :
    (openObjectLift B X'.obj X'.property (x.toGeometricPoint B (j ≫ f) s)
          (baseChange B (j ≫ f) V) (fiberPointElement B (j ≫ f) s V u x)
          (finiteSupportOpen B (j ≫ f) V E) h').1 ≫
        (SmallEtale.toScheme B X'.obj X'.property).map (covarianceOpenMap B j f V E D hD) ≫
          B.inclusion.map (pullback.fst ((finiteSupportOpenObject B f V D).obj.hom) j) =
      (openObjectLift B X.obj X.property ((openFiberPoint B j f s x).toGeometricPoint B f s)
        (baseChange B f V) (fiberPointElement B f s V u (openFiberPoint B j f s x))
        (finiteSupportOpen B f V D) h).1 := by
  refine (cancel_mono (finiteSupportOpen B f V D).ι).1 ?_
  calc ((openObjectLift B X'.obj X'.property (x.toGeometricPoint B (j ≫ f) s)
          (baseChange B (j ≫ f) V) (fiberPointElement B (j ≫ f) s V u x)
          (finiteSupportOpen B (j ≫ f) V E) h').1 ≫
        (SmallEtale.toScheme B X'.obj X'.property).map (covarianceOpenMap B j f V E D hD) ≫
          B.inclusion.map (pullback.fst ((finiteSupportOpenObject B f V D).obj.hom) j)) ≫
        (finiteSupportOpen B f V D).ι
      = (openObjectLift B X'.obj X'.property (x.toGeometricPoint B (j ≫ f) s)
          (baseChange B (j ≫ f) V) (fiberPointElement B (j ≫ f) s V u x)
          (finiteSupportOpen B (j ≫ f) V E) h').1 ≫
          ((SmallEtale.toScheme B X'.obj X'.property).map (covarianceOpenMap B j f V E D hD) ≫
            B.inclusion.map (pullback.fst ((finiteSupportOpenObject B f V D).obj.hom) j) ≫
            (finiteSupportOpen B f V D).ι) := by
        simp only [Category.assoc]
    _ = (openObjectLift B X'.obj X'.property (x.toGeometricPoint B (j ≫ f) s)
          (baseChange B (j ≫ f) V) (fiberPointElement B (j ≫ f) s V u x)
          (finiteSupportOpen B (j ≫ f) V E) h').1 ≫
          ((finiteSupportOpen B (j ≫ f) V E).ι ≫ openBaseChangeHom B j f V) :=
        congrArg (fun m => (openObjectLift B X'.obj X'.property
            (x.toGeometricPoint B (j ≫ f) s) (baseChange B (j ≫ f) V)
            (fiberPointElement B (j ≫ f) s V u x)
            (finiteSupportOpen B (j ≫ f) V E) h').1 ≫ m)
          (covarianceOpenMap_commutes B j f V E D hD)
    _ = ((openObjectLift B X'.obj X'.property (x.toGeometricPoint B (j ≫ f) s)
          (baseChange B (j ≫ f) V) (fiberPointElement B (j ≫ f) s V u x)
          (finiteSupportOpen B (j ≫ f) V E) h').1 ≫
          (finiteSupportOpen B (j ≫ f) V E).ι) ≫ openBaseChangeHom B j f V :=
        (Category.assoc _ _ _).symm
    _ = fiberPointLift B (j ≫ f) s V u x ≫ openBaseChangeHom B j f V :=
        congrArg (fun m => m ≫ openBaseChangeHom B j f V)
          (openObjectLift_comp_ι B X'.obj X'.property (x.toGeometricPoint B (j ≫ f) s)
            (baseChange B (j ≫ f) V) (fiberPointElement B (j ≫ f) s V u x)
            (finiteSupportOpen B (j ≫ f) V E) h')
    _ = fiberPointLift B f s V u (openFiberPoint B j f s x) :=
        fiberPointLift_openBaseChangeHom B j f s V u x
    _ = (openObjectLift B X.obj X.property
          ((openFiberPoint B j f s x).toGeometricPoint B f s) (baseChange B f V)
          (fiberPointElement B f s V u (openFiberPoint B j f s x))
          (finiteSupportOpen B f V D) h).1 ≫ (finiteSupportOpen B f V D).ι :=
        (openObjectLift_comp_ι B X.obj X.property
          ((openFiberPoint B j f s x).toGeometricPoint B f s) (baseChange B f V)
          (fiberPointElement B f s V u (openFiberPoint B j f s x))
          (finiteSupportOpen B f V D) h).symm

/-- **Stacks Project, Tag 0F6S part (1)** on a colimit generator, in a summand indexed by a point
of the geometric fibre of `j ≫ f`: the germ of the extended section at the image point is the
germ of the original section, read through the identification of the two stalks. -/
@[stacks 0F6S "part (1), stalk compatibility on a generator, summand in the open"]
public theorem fiberStalkComponent_covarianceSectionMap
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    (V : SmallEtale B Y.obj Y.property)
    (u : (geometricPointFiber B Y.obj Y.property s).obj V)
    (E : FiniteSupport B (j ≫ f) V)
    (a : supportedSections B X'.obj X'.property ((openRestriction.{u, v} B j).obj F)
      (baseChange B (j ≫ f) V) E.1 (finiteSupport_isLocallyClosed B (j ≫ f) V E))
    (x : GeometricFiberPoint B (j ≫ f) s) :
    fiberStalkComponent.{u, max (u + 1) v} B f s F V u (imageFiniteSupport B j f V E)
        (covarianceSectionMap B j f F V E _ (imageFiniteSupport_coe B j f V E) a)
        (openFiberPoint B j f s x) =
      (openFiberStalkIso.{u, v} B j f F s x).hom
        (fiberStalkComponent.{u, max (u + 1) v} B (j ≫ f) s
          ((openRestriction.{u, v} B j).obj F) V u E a x) := by
  by_cases h' : HasFiberLift B (j ≫ f) s V u E x
  · have h : HasFiberLift B f s V u (imageFiniteSupport B j f V E)
        (openFiberPoint B j f s x) :=
      (hasFiberLift_openFiberPoint_iff B j f s V u E _
        (imageFiniteSupport_coe B j f V E) x).2 h'
    have hsec : pullbackSectionAlongHom B j AddCommGrpCat.{max (u + 1) v} F
          (finiteSupportOpenObject B f V (imageFiniteSupport B j f V E))
          (finiteSupportOpenObject B (j ≫ f) V E)
          (covarianceOpenMap B j f V E _ (imageFiniteSupport_coe B j f V E))
          (covarianceSectionMap B j f F V E _ (imageFiniteSupport_coe B j f V E) a).val =
        a.val := by
      simp only [pullbackSectionAlongHom]
      exact (covarianceGeneratorData B j f F V E).sectionMap_apply a
    rw [fiberStalkComponent_of_hasFiberLift B f s F V u _ _ _ h,
      fiberStalkComponent_of_hasFiberLift B (j ≫ f) s
        ((openRestriction.{u, v} B j).obj F) V u E a x h']
    refine Eq.trans (etaleGerm_pullbackSectionAlongHom B j F
      (x.toGeometricPoint B (j ≫ f) s) _ _ _ _
      (covarianceOpenMap B j f V E _ (imageFiniteSupport_coe B j f V E))
      (openObjectLift_covarianceOpenMap B j f s V u E _
        (imageFiniteSupport_coe B j f V E) x h' h) _).symm ?_
    exact congrArg (fun z => (openFiberStalkIso.{u, v} B j f F s x).hom
      (etaleGerm B X'.obj X'.property (x.toGeometricPoint B (j ≫ f) s)
        ((openRestriction.{u, v} B j).obj F).obj (finiteSupportOpenObject B (j ≫ f) V E)
        (openObjectLift B X'.obj X'.property (x.toGeometricPoint B (j ≫ f) s)
          (baseChange B (j ≫ f) V) (fiberPointElement B (j ≫ f) s V u x)
          (finiteSupportOpen B (j ≫ f) V E) h') z)) hsec
  · have h : ¬ HasFiberLift B f s V u (imageFiniteSupport B j f V E)
        (openFiberPoint B j f s x) :=
      mt (hasFiberLift_openFiberPoint_iff B j f s V u E _
        (imageFiniteSupport_coe B j f V E) x).1 h'
    rw [fiberStalkComponent_of_not_hasFiberLift B f s F V u _ _ _ h,
      fiberStalkComponent_of_not_hasFiberLift B (j ≫ f) s
        ((openRestriction.{u, v} B j).obj F) V u E a x h']
    exact (map_zero _).symm

/-- A point of the geometric fibre of `f` whose lift to `X_V` meets the image of a support of
`j ≫ f` comes from a point of the geometric fibre of `j ≫ f`: the induced map of base changes is
an open immersion, so the lift factors through it. -/
public theorem exists_openFiberPoint_of_mem_image (V : SmallEtale B Y.obj Y.property)
    (u : (geometricPointFiber B Y.obj Y.property s).obj V)
    (y : GeometricFiberPoint B f s)
    (hy : (fiberPointLift B f s V u y).base default ∈
      Set.range (openBaseChangeHom B j f V).base) :
    ∃ x : GeometricFiberPoint B (j ≫ f) s, openFiberPoint B j f s x = y := by
  have hsnd : openBaseChangeHom B j f V ≫ B.inclusion.map (pullback.snd V.obj.hom f) =
      B.inclusion.map (pullback.snd V.obj.hom (j ≫ f)) ≫ B.inclusion.map j :=
    openBaseChangeHom_comp_hom B j f V
  have hr : Set.range (fiberPointLift B f s V u y).base ⊆
      Set.range (openBaseChangeHom B j f V).base := by
    rintro _ ⟨z, rfl⟩
    rwa [Subsingleton.elim z default]
  set g := IsOpenImmersion.lift (openBaseChangeHom B j f V) (fiberPointLift B f s V u y) hr
  have hfac : g ≫ openBaseChangeHom B j f V = fiberPointLift B f s V u y :=
    IsOpenImmersion.lift_fac _ _ hr
  have hfst : g ≫ B.inclusion.map (pullback.fst V.obj.hom (j ≫ f)) = u.1 :=
    calc g ≫ B.inclusion.map (pullback.fst V.obj.hom (j ≫ f))
        = g ≫ (openBaseChangeHom B j f V ≫
            B.inclusion.map (pullback.fst V.obj.hom f)) :=
          congrArg (fun m => g ≫ m) (openBaseChangeHom_comp B j f V).symm
      _ = (g ≫ openBaseChangeHom B j f V) ≫
            B.inclusion.map (pullback.fst V.obj.hom f) := (Category.assoc _ _ _).symm
      _ = fiberPointLift B f s V u y ≫ B.inclusion.map (pullback.fst V.obj.hom f) :=
          congrArg (fun m => m ≫ B.inclusion.map (pullback.fst V.obj.hom f)) hfac
      _ = u.1 := fiberPointLift_comp_fst B f s V u y
  refine ⟨⟨g ≫ B.inclusion.map (pullback.snd V.obj.hom (j ≫ f)), ?_⟩, Subtype.ext ?_⟩
  · calc (g ≫ B.inclusion.map (pullback.snd V.obj.hom (j ≫ f))) ≫
          B.inclusion.map (j ≫ f)
        = g ≫ (B.inclusion.map (pullback.snd V.obj.hom (j ≫ f)) ≫
            B.inclusion.map (j ≫ f)) := Category.assoc _ _ _
      _ = g ≫ (B.inclusion.map (pullback.fst V.obj.hom (j ≫ f)) ≫
            B.inclusion.map V.obj.hom) :=
          congrArg (fun m => g ≫ m)
            (((IsPullback.of_hasPullback V.obj.hom (j ≫ f)).map B.inclusion).w).symm
      _ = (g ≫ B.inclusion.map (pullback.fst V.obj.hom (j ≫ f))) ≫
            B.inclusion.map V.obj.hom := (Category.assoc _ _ _).symm
      _ = u.1 ≫ B.inclusion.map V.obj.hom :=
          congrArg (fun m => m ≫ B.inclusion.map V.obj.hom) hfst
      _ = s.hom := u.2
  · calc (g ≫ B.inclusion.map (pullback.snd V.obj.hom (j ≫ f))) ≫ B.inclusion.map j
        = g ≫ (B.inclusion.map (pullback.snd V.obj.hom (j ≫ f)) ≫ B.inclusion.map j) :=
          Category.assoc _ _ _
      _ = g ≫ (openBaseChangeHom B j f V ≫
            B.inclusion.map (pullback.snd V.obj.hom f)) :=
          congrArg (fun m => g ≫ m) hsnd.symm
      _ = (g ≫ openBaseChangeHom B j f V) ≫
            B.inclusion.map (pullback.snd V.obj.hom f) := (Category.assoc _ _ _).symm
      _ = fiberPointLift B f s V u y ≫ B.inclusion.map (pullback.snd V.obj.hom f) :=
          congrArg (fun m => m ≫ B.inclusion.map (pullback.snd V.obj.hom f)) hfac
      _ = y.1 := fiberPointLift_comp_snd B f s V u y

/-- **Stacks Project, Tag 0F6S part (1)** on a colimit generator, in a summand outside the image
of the geometric fibre of `j ≫ f`: the germ of the extended section vanishes there, the extended
section being supported on the image of the original support. -/
@[stacks 0F6S "part (1), stalk compatibility on a generator, summand outside the open"]
public theorem fiberStalkComponent_covarianceSectionMap_eq_zero
    (V : SmallEtale B Y.obj Y.property)
    (u : (geometricPointFiber B Y.obj Y.property s).obj V)
    (E : FiniteSupport B (j ≫ f) V) (D : FiniteSupport B f V)
    (hD : D.1 = (openBaseChangeHom B j f V).base '' E.1)
    (a : supportedSections B X'.obj X'.property ((openRestriction.{u, v} B j).obj F)
      (baseChange B (j ≫ f) V) E.1 (finiteSupport_isLocallyClosed B (j ≫ f) V E))
    (y : GeometricFiberPoint B f s)
    (hy : ∀ x : GeometricFiberPoint B (j ≫ f) s, openFiberPoint B j f s x ≠ y) :
    fiberStalkComponent.{u, max (u + 1) v} B f s F V u D
      (covarianceSectionMap B j f F V E D hD a) y = 0 := by
  refine fiberStalkComponent_eq_zero_of_notMem B f s F V u D _ y fun hmem => ?_
  rw [hD] at hmem
  obtain ⟨x, hx⟩ := exists_openFiberPoint_of_mem_image B j f s V u y
    (Set.image_subset_range _ _ hmem)
  exact hy x hx

end Generator

section Stalk

variable (B : BigEtaleSite.{u})

/-- The germ at a geometric point `t` of the base of a section supported on a support finite over
a pointed étale neighbourhood of `t`, as a map into the stalk of the finite-support direct
image. -/
public def finiteSupportStalkGenerator {S T : B.Scheme} (g : S ⟶ T)
    [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
    (G : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{max (u + 1) v})
    (t : GeometricPoint T.obj)
    (U : (geometricPointFiber B T.obj T.property t).Elements) (E : FiniteSupport B g U.1) :
    (finiteSupportDiagram B g G U.1).obj E ⟶
      etaleStalk B T.obj T.property t
        ((finiteSupportPushforward.{u, max (u + 1) v} B g
          (fun _ => inferInstance)).val.obj G) :=
  finiteSupportPushforwardGenerator B g G U.1 E ≫
    colimit.ι (etaleStalkDiagram B T.obj T.property t
      ((finiteSupportPushforward.{u, max (u + 1) v} B g
        (fun _ => inferInstance)).val.obj G)) (op U)

/-- The germ of a supported section is the colimit generator of the finite-support direct image
followed by the canonical map into the stalk. -/
public theorem finiteSupportStalkGenerator_def {S T : B.Scheme} (g : S ⟶ T)
    [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
    (G : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{max (u + 1) v})
    (t : GeometricPoint T.obj)
    (U : (geometricPointFiber B T.obj T.property t).Elements) (E : FiniteSupport B g U.1) :
    finiteSupportStalkGenerator.{u, v} B g G t U E =
      finiteSupportPushforwardGenerator B g G U.1 E ≫
        colimit.ι (etaleStalkDiagram B T.obj T.property t
          ((finiteSupportPushforward.{u, max (u + 1) v} B g
            (fun _ => inferInstance)).val.obj G)) (op U) :=
  rfl

/-- **Stacks 0F6P** on a generator: the stalk decomposition sends the germ of a supported section
to the family of its germs over the geometric fibre. -/
public theorem finiteSupportStalkGenerator_comp_stalkIso {S T : B.Scheme} (g : S ⟶ T)
    [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
    (G : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{max (u + 1) v})
    (t : GeometricPoint T.obj) (V : SmallEtale B T.obj T.property)
    (w : (geometricPointFiber B T.obj T.property t).obj V) (E : FiniteSupport B g V) :
    finiteSupportStalkGenerator.{u, v} B g G t
          (Functor.elementsMk (geometricPointFiber B T.obj T.property t) V w) E ≫
        (finiteSupportStalkIso.{u, max (u + 1) v} B g t G (fun _ => inferInstance)).hom =
      fiberStalkHom.{u, max (u + 1) v} B g t G V w E :=
  ((Category.assoc _ _ _).trans (Category.assoc _ _ _)).trans
    (finiteSupportStalkToFiberStalks_generator B g t G (fun _ => inferInstance)
      (Functor.elementsMk (geometricPointFiber B T.obj T.property t) V w) E)

variable {X' X Y : B.Scheme} (j : X' ⟶ X) (f : X ⟶ Y)
  [IsOpenImmersion (B.inclusion.map j)]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
  (s : GeometricPoint Y.obj)

/-- The map induced on the geometric stalk at `s` by the covariance map of Stacks 0F6S on
finite-support direct-image presheaves. -/
public def openCovarianceStalkMap :
    etaleStalk B Y.obj Y.property s
        ((finiteSupportPushforward.{u, max (u + 1) v} B (j ≫ f)
          (fun _ => inferInstance)).val.obj ((openRestriction.{u, v} B j).obj F)) ⟶
      etaleStalk B Y.obj Y.property s
        ((finiteSupportPushforward.{u, max (u + 1) v} B f
          (fun _ => inferInstance)).val.obj F) :=
  colim.map (Functor.whiskerLeft
    (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op
    ((openCovariancePresheafMap.{u, v} B j f).val.app F))

/-- On a generator of the stalk the covariance map of Stacks 0F6S is extension by zero of the
supported section onto the image of its support. -/
public theorem finiteSupportStalkGenerator_comp_openCovarianceStalkMap
    (V : SmallEtale B Y.obj Y.property)
    (w : (geometricPointFiber B Y.obj Y.property s).obj V) (E : FiniteSupport B (j ≫ f) V) :
    finiteSupportStalkGenerator.{u, v} B (j ≫ f) ((openRestriction.{u, v} B j).obj F) s
          (Functor.elementsMk (geometricPointFiber B Y.obj Y.property s) V w) E ≫
        openCovarianceStalkMap.{u, v} B j f F s =
      AddCommGrpCat.ofHom (covarianceSectionMap B j f F V E _
          (imageFiniteSupport_coe B j f V E)) ≫
        finiteSupportStalkGenerator.{u, v} B f F s
          (Functor.elementsMk (geometricPointFiber B Y.obj Y.property s) V w)
          (imageFiniteSupport B j f V E) := by
  have hι : colimit.ι (etaleStalkDiagram B Y.obj Y.property s
          ((finiteSupportPushforward.{u, max (u + 1) v} B (j ≫ f)
            (fun _ => inferInstance)).val.obj ((openRestriction.{u, v} B j).obj F)))
          (op (Functor.elementsMk (geometricPointFiber B Y.obj Y.property s) V w)) ≫
        openCovarianceStalkMap.{u, v} B j f F s =
      covariancePresheafApp B j f F V ≫
        colimit.ι (etaleStalkDiagram B Y.obj Y.property s
          ((finiteSupportPushforward.{u, max (u + 1) v} B f
            (fun _ => inferInstance)).val.obj F))
          (op (Functor.elementsMk (geometricPointFiber B Y.obj Y.property s) V w)) :=
    colimit.ι_map _ _
  exact (((Category.assoc _ _ _).trans
      (congrArg (fun k => finiteSupportPushforwardGenerator B (j ≫ f)
        ((openRestriction.{u, v} B j).obj F) V E ≫ k) hι)).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ colimit.ι (etaleStalkDiagram B Y.obj Y.property s
          ((finiteSupportPushforward.{u, max (u + 1) v} B f
            (fun _ => inferInstance)).val.obj F))
          (op (Functor.elementsMk (geometricPointFiber B Y.obj Y.property s) V w)))
        (covariancePresheafApp_generator B j f F V E _
          (imageFiniteSupport_coe B j f V E))))).trans (Category.assoc _ _ _)

/-- The stalk decomposition of Stacks 0F6P carries the covariance stalk map of a generator to the
fibre stalk component of the extended section. -/
private theorem stalkIso_openCovarianceStalkMap_generator
    (V : SmallEtale B Y.obj Y.property)
    (w : (geometricPointFiber B Y.obj Y.property s).obj V) (E : FiniteSupport B (j ≫ f) V)
    (a : (finiteSupportDiagram B (j ≫ f) ((openRestriction.{u, v} B j).obj F) V).obj E) :
    (finiteSupportStalkIso.{u, max (u + 1) v} B f s F (fun _ => inferInstance)).hom
        ((openCovarianceStalkMap.{u, v} B j f F s)
          (finiteSupportStalkGenerator.{u, v} B (j ≫ f)
            ((openRestriction.{u, v} B j).obj F) s
            (Functor.elementsMk (geometricPointFiber B Y.obj Y.property s) V w) E a)) =
      (fiberStalkHom.{u, max (u + 1) v} B f s F V w (imageFiniteSupport B j f V E))
        (covarianceSectionMap B j f F V E _ (imageFiniteSupport_coe B j f V E) a) := by
  have h1 := ConcreteCategory.congr_hom
    (finiteSupportStalkGenerator_comp_openCovarianceStalkMap.{u, v} B j f F s V w E) a
  have h2 := ConcreteCategory.congr_hom
    (finiteSupportStalkGenerator_comp_stalkIso.{u, v} B f F s V w
      (imageFiniteSupport B j f V E))
    (covarianceSectionMap B j f F V E _ (imageFiniteSupport_coe B j f V E) a)
  rw [(CategoryTheory.comp_apply _ _ a).symm.trans (h1.trans (CategoryTheory.comp_apply _ _ a))]
  exact (CategoryTheory.comp_apply _ _ _).symm.trans h2

/-- **Stacks Project, Tag 0F6S part (1)** for the finite-support direct-image presheaves, in a
summand indexed by a point of the geometric fibre of `j ≫ f`: on the stalk decompositions of
Stacks 0F6P the covariance map of Stacks 0F6S carries the summand at a point of the geometric
fibre of `j ≫ f` to the summand at its image, through the identification of the two stalks. -/
@[stacks 0F6S "part (1), stalk compatibility, presheaf form, summands in the open"]
public theorem fiberStalks_openCovarianceStalkMap_openFiberPoint
    (V : SmallEtale B Y.obj Y.property)
    (w : (geometricPointFiber B Y.obj Y.property s).obj V) (E : FiniteSupport B (j ≫ f) V)
    (a : (finiteSupportDiagram B (j ≫ f) ((openRestriction.{u, v} B j).obj F) V).obj E)
    (x : GeometricFiberPoint B (j ≫ f) s) :
    ((finiteSupportStalkIso.{u, max (u + 1) v} B f s F (fun _ => inferInstance)).hom
          ((openCovarianceStalkMap.{u, v} B j f F s)
            (finiteSupportStalkGenerator.{u, v} B (j ≫ f)
              ((openRestriction.{u, v} B j).obj F) s
              (Functor.elementsMk (geometricPointFiber B Y.obj Y.property s) V w) E a)) :
        fiberStalks.{u, max (u + 1) v} B f s F) (openFiberPoint B j f s x) =
      (openFiberStalkIso.{u, v} B j f F s x).hom
        (((finiteSupportStalkIso.{u, max (u + 1) v} B (j ≫ f) s
              ((openRestriction.{u, v} B j).obj F) (fun _ => inferInstance)).hom
            (finiteSupportStalkGenerator.{u, v} B (j ≫ f)
              ((openRestriction.{u, v} B j).obj F) s
              (Functor.elementsMk (geometricPointFiber B Y.obj Y.property s) V w) E a) :
          fiberStalks.{u, max (u + 1) v} B (j ≫ f) s
            ((openRestriction.{u, v} B j).obj F)) x) := by
  have h3 := ConcreteCategory.congr_hom
    (finiteSupportStalkGenerator_comp_stalkIso.{u, v} B (j ≫ f)
      ((openRestriction.{u, v} B j).obj F) s V w E) a
  have e3 : (finiteSupportStalkIso.{u, max (u + 1) v} B (j ≫ f) s
          ((openRestriction.{u, v} B j).obj F) (fun _ => inferInstance)).hom
        (finiteSupportStalkGenerator.{u, v} B (j ≫ f) ((openRestriction.{u, v} B j).obj F) s
          (Functor.elementsMk (geometricPointFiber B Y.obj Y.property s) V w) E a) =
      (fiberStalkHom.{u, max (u + 1) v} B (j ≫ f) s ((openRestriction.{u, v} B j).obj F)
        V w E) a :=
    (CategoryTheory.comp_apply _ _ a).symm.trans h3
  rw [stalkIso_openCovarianceStalkMap_generator.{u, v} B j f F s V w E a, e3]
  exact fiberStalkComponent_covarianceSectionMap B j f F s V w E a x

/-- **Stacks Project, Tag 0F6S part (1)** for the finite-support direct-image presheaves, in a
summand outside the image of the geometric fibre of `j ≫ f`: on the stalk decompositions of
Stacks 0F6P the covariance map of Stacks 0F6S has vanishing component there. Together with the
previous theorem this says that on the stalk at `s` the covariance map is the extension by zero
along the inclusion of geometric fibres. -/
@[stacks 0F6S "part (1), stalk compatibility, presheaf form, summands outside the open"]
public theorem fiberStalks_openCovarianceStalkMap_eq_zero
    (V : SmallEtale B Y.obj Y.property)
    (w : (geometricPointFiber B Y.obj Y.property s).obj V) (E : FiniteSupport B (j ≫ f) V)
    (a : (finiteSupportDiagram B (j ≫ f) ((openRestriction.{u, v} B j).obj F) V).obj E)
    (y : GeometricFiberPoint B f s)
    (hy : ∀ x : GeometricFiberPoint B (j ≫ f) s, openFiberPoint B j f s x ≠ y) :
    ((finiteSupportStalkIso.{u, max (u + 1) v} B f s F (fun _ => inferInstance)).hom
        ((openCovarianceStalkMap.{u, v} B j f F s)
          (finiteSupportStalkGenerator.{u, v} B (j ≫ f)
            ((openRestriction.{u, v} B j).obj F) s
            (Functor.elementsMk (geometricPointFiber B Y.obj Y.property s) V w) E a)) :
      fiberStalks.{u, max (u + 1) v} B f s F) y = 0 := by
  rw [stalkIso_openCovarianceStalkMap_generator.{u, v} B j f F s V w E a]
  exact fiberStalkComponent_covarianceSectionMap_eq_zero B j f F s V w E _
    (imageFiniteSupport_coe B j f V E) a y hy

end Stalk

end AlgebraicGeometry.SmallEtale

end
