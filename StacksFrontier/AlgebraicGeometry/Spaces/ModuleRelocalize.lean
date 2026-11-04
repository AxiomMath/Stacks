module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PushforwardIndexIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsUnit
public import StacksFrontier.AlgebraicGeometry.Topologies.SiteEquivalenceTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRelocalize
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable

/-!
# Modules on an algebraic space viewed over a larger base

Let `h : W ⟶ S` be a morphism of a big fppf site and let `Λ` be the lower-shriek extension
`CategoryTheory.OverShriek.relocalizePresheafFunctor h`, which views an algebraic space `X` over
`W` as an algebraic space `Λ X = AlgebraicGeometry.Space.relocalizeSpace B hW hS h X` over `S`
(Stacks 03I5 (2)). The small étale sites of `X` and of
`Λ X` are equivalent (`AlgebraicGeometry.Space.SmallEtale.relocalizeEquivalence`), with the
same structure sheaf, so `𝒪_{Λ X}`-modules are read as `𝒪_X`-modules by
`Stacks.SheafOfModules.reindexEquivalence`. This file shows that this reading commutes with the
inverse image of modules along a representable morphism of algebraic spaces.

## Main definitions

* `AlgebraicGeometry.Space.relocalizeSpaceMap`: the morphism `Λ f`.
* `AlgebraicGeometry.Space.moduleDerelocalize`: the `𝒪_X`-module read off an
  `𝒪_{Λ X}`-module, an equivalence of categories
  (`AlgebraicGeometry.Space.moduleRelocalizeEquivalence`).

## Main results

* `AlgebraicGeometry.Space.smallBaseChangeRelocalizeIso`: base change of étale charts along a
  representable morphism commutes with the equivalence of small étale sites.
* `AlgebraicGeometry.Space.modulePushforwardRelocalizeIso` and
  `AlgebraicGeometry.Space.modulePullbackRelocalizeIso`: the direct and inverse images of
  modules along a representable morphism commute with reading modules over `W`; the second is
  obtained from the first by uniqueness of left adjoints.
* `AlgebraicGeometry.Space.restrictToChartSchemeDerelocalizeIso`: restriction to the scheme of an
  étale chart commutes with reading modules over `W`.
* `AlgebraicGeometry.Space.baseChangeModuleDerelocalizeIso`: the pullback of a module to a scheme
  does not depend on the base.
* `AlgebraicGeometry.Space.isInvertible_moduleDerelocalize_iff`: invertibility does not depend on
  the base (the reading carries tensor products and the unit to tensor products and the unit).

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS)

variable {B W S hW hS} in
/-- The morphism `Λ f : Λ X ⟶ Λ Y` of algebraic spaces over `S`. -/
abbrev relocalizeSpaceMap {X Y : AlgebraicSpaces B W hW} (f : X ⟶ Y) :
    relocalizeSpace B hW hS h X ⟶ relocalizeSpace B hW hS h Y :=
  ObjectProperty.homMk ((OverShriek.relocalizePresheafFunctor h).map f.hom)

/-- The equivalence between `𝒪_{Λ X}`-modules and `𝒪_X`-modules: reindexing along the
equivalence of small étale sites. -/
abbrev moduleRelocalizeEquivalence (X : AlgebraicSpaces B W hW) :
    Modules.{u, u} B S hS (relocalizeSpace B hW hS h X).1 (relocalizeSpace B hW hS h X).2 ≌
      Modules.{u, u} B W hW X.1 X.2 :=
  Stacks.SheafOfModules.reindexEquivalence (J' := SmallEtale.topology B W hW X.1)
    (SmallEtale.relocalizeEquivalence B W S hW hS h X.1)
    (smallEtaleRingSheaf B S hS _ (relocalizeSpace B hW hS h X).2)

/-- The `𝒪_X`-module read off an `𝒪_{Λ X}`-module. -/
abbrev moduleDerelocalize (X : AlgebraicSpaces B W hW) :
    Modules.{u, u} B S hS (relocalizeSpace B hW hS h X).1 (relocalizeSpace B hW hS h X).2 ⥤
      Modules.{u, u} B W hW X.1 X.2 :=
  (moduleRelocalizeEquivalence B W S hW hS h X).functor

/-! ### Relocalization of representable base changes -/

variable {B W S hW hS}

/-- `Λ` carries a representable base change of a morphism along a chart to a representable base
change of the extended morphism along the extended chart. -/
theorem isPullback_relocalizeChart_of_isPullback {X Y : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    {f : X ⟶ Y} {V P : BigFppfOver B W hW} {a : yoneda.obj V ⟶ Y} {p : yoneda.obj P ⟶ X}
    {q : P ⟶ V} (hsq : IsPullback p (yoneda.map q) f a) :
    IsPullback (relocalizeChart B W S hW hS h p) (yoneda.map ((Over.map h).map q))
      ((OverShriek.relocalizePresheafFunctor h).map f) (relocalizeChart B W S hW hS h a) := by
  refine (hsq.map (OverShriek.relocalizePresheafFunctor h)).of_iso
    (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h P) (Iso.refl _)
    (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h V) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [relocalizeChart]
  · exact relocalizedYonedaIso_naturality B (B.obj hW) (B.obj hS) h q
  · simp
  · simp [relocalizeChart]

/-- `Λ` of a representable morphism of presheaves is representable. -/
theorem relativelyRepresentable_relocalize {X Y : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    yoneda.relativelyRepresentable ((OverShriek.relocalizePresheafFunctor h).map f) :=
  (OverShriek.presheaf_map_relocalize h (P₁ := ⊤) (P₂ := ⊤) (fun _ _ => trivial)
    ⟨hf, fun _ _ _ _ _ _ => trivial⟩).rep

/-! ### Base change of étale charts commutes with the equivalence of small étale sites -/

section SmallBaseChange

variable {X Y : AlgebraicSpaces B W hW} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)

/-- The comparison of the two base changes of a chart `V` of `Y`: the relocalization of the base
change of `V` along `f` is the base change of the relocalized chart along `Λ f`. -/
def relocalizePullbackIso (V : SmallEtale B W hW Y.1) :
    (Over.map h).obj (hf.pullback V.1.hom) ≅
      (relativelyRepresentable_relocalize h hf).pullback
        (relocalizeChart B W S hW hS h V.1.hom) :=
  yoneda.preimageIso
    ((isPullback_relocalizeChart_of_isPullback h (hf.isPullback V.1.hom)).isoIsPullback
      _ _ ((relativelyRepresentable_relocalize h hf).isPullback _))

/-- Composed with the first projection, the comparison `relocalizePullbackIso` is the
relocalization of the first projection of the base change of `V` along `f`. -/
@[reassoc (attr := simp)]
theorem relocalizePullbackIso_hom_fst (V : SmallEtale B W hW Y.1) :
    yoneda.map (relocalizePullbackIso h f hf V).hom ≫
        (relativelyRepresentable_relocalize h hf).fst (relocalizeChart B W S hW hS h V.1.hom) =
      relocalizeChart B W S hW hS h (hf.fst V.1.hom) := by
  simp only [relocalizePullbackIso, Functor.preimageIso_hom, Functor.map_preimage]
  exact IsPullback.isoIsPullback_hom_fst _ _
    (isPullback_relocalizeChart_of_isPullback h (hf.isPullback V.1.hom))
    ((relativelyRepresentable_relocalize h hf).isPullback _)

/-- Composed with the second projection, the comparison `relocalizePullbackIso` is the
relocalization of the second projection of the base change of `V` along `f`. -/
@[reassoc (attr := simp)]
theorem relocalizePullbackIso_hom_snd (V : SmallEtale B W hW Y.1) :
    (relocalizePullbackIso h f hf V).hom ≫
        (relativelyRepresentable_relocalize h hf).snd (relocalizeChart B W S hW hS h V.1.hom) =
      (Over.map h).map (hf.snd V.1.hom) := by
  apply yoneda.map_injective
  simp only [relocalizePullbackIso, Functor.preimageIso_hom, Functor.map_comp,
    Functor.map_preimage]
  exact IsPullback.isoIsPullback_hom_snd _ _
    (isPullback_relocalizeChart_of_isPullback h (hf.isPullback V.1.hom))
    ((relativelyRepresentable_relocalize h hf).isPullback _)

variable {h} in
/-- The equivalence of small étale sites sends a morphism of charts to its image under
`Over.map h`. -/
@[simp]
theorem relocalizeEquivalence_functor_map_hom_left {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    {V V' : SmallEtale B W hW F} (g : V ⟶ V') :
    ((SmallEtale.relocalizeEquivalence B W S hW hS h F).functor.map g).hom.left =
      (Over.map h).map g.hom.left := rfl

variable {h} in
/-- The equivalence of small étale sites sends a chart `V` to the relocalized chart
`relocalizeChart B W S hW hS h V.1.hom`. -/
@[simp]
theorem relocalizeEquivalence_functor_obj_hom {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    (V : SmallEtale B W hW F) :
    ((SmallEtale.relocalizeEquivalence B W S hW hS h F).functor.obj V).1.hom =
      relocalizeChart B W S hW hS h V.1.hom := rfl

/-- The base change along `f` of a morphism of charts `k : V ⟶ V'` is the morphism into the
pullback lifting the first projection and the second projection followed by `k`. -/
@[simp]
theorem smallBaseChange_map_hom_left_eq_lift {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) {V V' : SmallEtale B S hS Y.1} (k : V ⟶ V') :
    ((smallBaseChange B S hS f hf).map k).hom.left =
      hf.lift (hf.fst V.1.hom) (hf.snd V.1.hom ≫ k.hom.left)
        (representablePullback_lift_cond B S hS f hf k) := rfl

/-- The commutativity condition for the base change along `Λ f` of a morphism of extended
charts. -/
theorem relocalizeChart_lift_cond {V V' : SmallEtale B W hW Y.1} (k : V ⟶ V') :
    (relativelyRepresentable_relocalize h hf).fst (relocalizeChart B W S hW hS h V.1.hom) ≫
        (OverShriek.relocalizePresheafFunctor h).map f.hom =
      yoneda.map ((relativelyRepresentable_relocalize h hf).snd
          (relocalizeChart B W S hW hS h V.1.hom) ≫ (Over.map h).map k.hom.left) ≫
        relocalizeChart B W S hW hS h V'.1.hom := by
  rw [(relativelyRepresentable_relocalize h hf).w, Functor.map_comp, Category.assoc,
    relocalizeChart_naturality, CostructuredArrow.w k.hom]

/-- The comparison of base changes is natural in the chart. -/
theorem relocalizePullbackIso_naturality {V V' : SmallEtale B W hW Y.1} (k : V ⟶ V') :
    (Over.map h).map (hf.lift (hf.fst V.1.hom) (hf.snd V.1.hom ≫ k.hom.left)
        (representablePullback_lift_cond B W hW f hf k)) ≫
        (relocalizePullbackIso h f hf V').hom =
      (relocalizePullbackIso h f hf V).hom ≫
        (relativelyRepresentable_relocalize h hf).lift
          ((relativelyRepresentable_relocalize h hf).fst (relocalizeChart B W S hW hS h V.1.hom))
          ((relativelyRepresentable_relocalize h hf).snd (relocalizeChart B W S hW hS h V.1.hom) ≫
            (Over.map h).map k.hom.left)
          (relocalizeChart_lift_cond h f hf k) := by
  apply (relativelyRepresentable_relocalize h hf).hom_ext
  · rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
      relocalizePullbackIso_hom_fst, Functor.relativelyRepresentable.lift_fst,
      relocalizeChart_naturality, Functor.relativelyRepresentable.lift_fst,
      relocalizePullbackIso_hom_fst]
  · rw [Category.assoc, Category.assoc, relocalizePullbackIso_hom_snd,
      Functor.relativelyRepresentable.lift_snd, ← Functor.map_comp,
      Functor.relativelyRepresentable.lift_snd, Functor.map_comp, ← Category.assoc,
      relocalizePullbackIso_hom_snd]

/-- **Base change of étale charts along a representable morphism commutes with the
equivalence of small étale sites.** -/
def smallBaseChangeRelocalizeIso :
    smallBaseChange B W hW f hf ⋙ (SmallEtale.relocalizeEquivalence B W S hW hS h X.1).functor ≅
      (SmallEtale.relocalizeEquivalence B W S hW hS h Y.1).functor ⋙
        smallBaseChange B S hS (relocalizeSpaceMap h f) (relativelyRepresentable_relocalize h hf) :=
  NatIso.ofComponents
    (fun V => ObjectProperty.isoMk _ (CostructuredArrow.isoMk (relocalizePullbackIso h f hf V)
      (relocalizePullbackIso_hom_fst h f hf V)))
    (fun {V V'} k => by
      apply ObjectProperty.hom_ext
      apply CostructuredArrow.hom_ext
      exact relocalizePullbackIso_naturality h f hf k)

/-- **The direct image along a representable morphism commutes with reading modules over the
smaller base.** -/
def smallBaseChangeModulePushforwardRelocalizeIso :
    smallBaseChangeModulePushforward.{u, u} B S hS (relocalizeSpaceMap h f)
        (relativelyRepresentable_relocalize h hf) ⋙ moduleDerelocalize B W S hW hS h Y ≅
      moduleDerelocalize B W S hW hS h X ⋙ smallBaseChangeModulePushforward.{u, u} B W hW f hf :=
  letI := isContinuous_smallBaseChange B S hS (relocalizeSpaceMap h f)
    (relativelyRepresentable_relocalize h hf)
  letI := isContinuous_smallBaseChange B W hW f hf
  letI := Functor.isContinuous_comp (smallBaseChange B W hW f hf)
    (SmallEtale.relocalizeEquivalence B W S hW hS h X.1).functor
    (SmallEtale.topology B W hW Y.1) (SmallEtale.topology B W hW X.1)
    (SmallEtale.topology B S hS (relocalizeSpace B hW hS h X).1)
  letI := Functor.isContinuous_comp (SmallEtale.relocalizeEquivalence B W S hW hS h Y.1).functor
    (smallBaseChange B S hS (relocalizeSpaceMap h f) (relativelyRepresentable_relocalize h hf))
    (SmallEtale.topology B W hW Y.1) (SmallEtale.topology B S hS (relocalizeSpace B hW hS h Y).1)
    (SmallEtale.topology B S hS (relocalizeSpace B hW hS h X).1)
  SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardCongr₂ _ (smallBaseChangeRelocalizeIso h f hf) (by
      have key : ∀ V : SmallEtale B W hW Y.1,
          (BigFppfOver.toScheme B S hS).map (relocalizePullbackIso h f hf V).hom ≫
            (BigFppfOver.toScheme B S hS).map ((relativelyRepresentable_relocalize h hf).snd
              (relocalizeChart B W S hW hS h V.1.hom)) =
          (BigFppfOver.toScheme B W hW).map (hf.snd V.1.hom) := fun V => by
        rw [← Functor.map_comp, relocalizePullbackIso_hom_snd]
        rfl
      ext V : 3
      change (forget₂ CommRingCat RingCat).map
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
              ((relativelyRepresentable_relocalize h hf).snd
                (relocalizeChart B W S hW hS h V.unop.1.hom))).op ≫
            Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
              (relocalizePullbackIso h f hf V.unop).hom).op) =
        (forget₂ CommRingCat RingCat).map
          (Scheme.Γ.map ((BigFppfOver.toScheme B W hW).map (hf.snd V.unop.1.hom)).op)
      rw [← Functor.map_comp, ← op_comp, key]) ≪≫
    (SheafOfModules.pushforwardComp _ _).symm

/-- **The direct image of modules along a representable morphism commutes with reading modules
over the smaller base**, for the direct image of Stacks 03LU. -/
def modulePushforwardRelocalizeIso :
    modulePushforward B S hS (relocalizeSpaceMap h f) ⋙ moduleDerelocalize B W S hW hS h Y ≅
      moduleDerelocalize B W S hW hS h X ⋙ modulePushforward B W hW f :=
  Functor.isoWhiskerRight (modulePushforwardChartIso B S hS (relocalizeSpaceMap h f)
      (relativelyRepresentable_relocalize h hf)) _ ≪≫
    smallBaseChangeModulePushforwardRelocalizeIso h f hf ≪≫
    Functor.isoWhiskerLeft _ (modulePushforwardChartIso B W hW f hf).symm

/-- **The inverse image of modules along a representable morphism commutes with reading modules
over the smaller base.** For a representable morphism `f : X ⟶ Y` of algebraic spaces over `W`,
reading an `𝒪_{Λ Y}`-module on `Y` and pulling it back to `X` is pulling it back along `Λ f` and
reading it on `X`. Both are left adjoint to the same functor, by
`AlgebraicGeometry.Space.modulePushforwardRelocalizeIso`. -/
def modulePullbackRelocalizeIso :
    moduleDerelocalize B W S hW hS h Y ⋙ modulePullback B W hW f ≅
      modulePullback B S hS (relocalizeSpaceMap h f) ⋙ moduleDerelocalize B W S hW hS h X :=
  let eX := moduleRelocalizeEquivalence B W S hW hS h X
  let eY := moduleRelocalizeEquivalence B W S hW hS h Y
  let adj₁ := (modulePullbackAdjunction B S hS (relocalizeSpaceMap h f)).comp eX.toAdjunction
  let adj₂ := eY.toAdjunction.comp (modulePullbackAdjunction B W hW f)
  let ρ : eX.inverse ⋙ modulePushforward B S hS (relocalizeSpaceMap h f) ≅
      modulePushforward B W hW f ⋙ eY.inverse :=
    Functor.isoWhiskerLeft _ ((Functor.rightUnitor _).symm ≪≫
        Functor.isoWhiskerLeft _ eY.unitIso ≪≫ (Functor.associator _ _ _).symm) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (modulePushforwardRelocalizeIso h f hf) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight eX.counitIso _ ≪≫ Functor.leftUnitor _) _
  adj₂.leftAdjointUniq (adj₁.ofNatIsoRight ρ)

end SmallBaseChange

/-! ### Restriction to the scheme of a chart commutes with reading modules over `W` -/

section ChartRestriction

variable {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}

/-- The relocalization of an open subobject of an object of the site is the open subobject of
the relocalized object cut out by the same open. -/
def openSubRelocalizeIso (A : BigFppfOver B W hW)
    (O : ((BigFppfOver.toScheme B W hW).obj A).Opens) :
    (Over.map h).obj (openSub A O) ≅ openSub ((Over.map h).obj A) O :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ _ ≫ (A.hom ≫ h) = (_ ≫ A.hom) ≫ h
    exact (Category.id_comp _).trans (Category.assoc _ _ _).symm)

/-- The comparison `openSubRelocalizeIso` commutes with the inclusions of the open subobjects. -/
theorem openSubRelocalizeIso_hom_comp (A : BigFppfOver B W hW)
    (O : ((BigFppfOver.toScheme B W hW).obj A).Opens) :
    (openSubRelocalizeIso h A O).hom ≫ openSubHom ((Over.map h).obj A) O =
      (Over.map h).map (openSubHom A O) :=
  Over.OverMorphism.ext (Category.id_comp _)

/-- The open subcharts of a chart `U` of `F`, relocalized, are the open subcharts of the
relocalized chart: the comparison is the identity on the underlying open subschemes. -/
def openChartRelocalizeIso (U : SmallEtale B W hW F) (O : (chartScheme U).Opens) :
    (SmallEtale.relocalizeEquivalence B W S hW hS h F).functor.obj
        (openChart B W hW F U O) ≅
      openChart B S hS _ ((SmallEtale.relocalizeEquivalence B W S hW hS h F).functor.obj U) O :=
  ObjectProperty.isoMk _ (CostructuredArrow.isoMk (openSubRelocalizeIso h U.1.left O)
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ relocalizeChart B W S hW hS h U.1.hom)
        ((yoneda.map_comp _ _).symm.trans
          (congrArg yoneda.map (openSubRelocalizeIso_hom_comp h U.1.left O)))).trans
      (relocalizeChart_naturality B W S hW hS h (openSubHom U.1.left O) U.1.hom))))

/-- The relocalized open subcharts of a chart form the open-subchart functor of the relocalized
chart. -/
def openChartFunctorRelocalizeIso (U : SmallEtale B W hW F) :
    openChartFunctor B W hW F U ⋙ (SmallEtale.relocalizeEquivalence B W S hW hS h F).functor ≅
      openChartFunctor B S hS _
        ((SmallEtale.relocalizeEquivalence B W S hW hS h F).functor.obj U) :=
  NatIso.ofComponents (openChartRelocalizeIso h U) (fun {O O'} i => by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    apply Over.OverMorphism.ext
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The change of scalars of the chart restrictions on the two sides agree under the comparison
of open subcharts. -/
theorem chartSchemeRestrictionRingHom_relocalize (U : SmallEtale B W hW F) :
    chartSchemeRestrictionRingHom B W hW F U ≫
        Functor.whiskerRight (NatIso.op (openChartFunctorRelocalizeIso h U)).inv
          (structurePresheaf B S hS ((OverShriek.relocalizePresheafFunctor h).obj F) ⋙
            forget₂ CommRingCat RingCat) =
      chartSchemeRestrictionRingHom B S hS _
        ((SmallEtale.relocalizeEquivalence B W S hW hS h F).functor.obj U) := by
  ext O : 2
  have h1 : (Functor.whiskerRight (NatIso.op (openChartFunctorRelocalizeIso h U)).inv
      (structurePresheaf B S hS ((OverShriek.relocalizePresheafFunctor h).obj F) ⋙
        forget₂ CommRingCat RingCat)).app O = 𝟙 _ :=
    (structurePresheaf B S hS ((OverShriek.relocalizePresheafFunctor h).obj F) ⋙
      forget₂ CommRingCat RingCat).map_id _
  exact (NatTrans.comp_app _ _ O).trans
    ((congrArg ((chartSchemeRestrictionRingHom B W hW F U).app O ≫ ·) h1).trans
      (Category.comp_id _))

/-- The sections restricted to the open subcharts of a chart, read over `W`, are the sections of
the module over `S` restricted along the relocalized open subcharts. -/
theorem pushforward_ulift_moduleDerelocalize (X : AlgebraicSpaces B W hW)
    (N : Modules.{u, u} B S hS (relocalizeSpace B hW hS h X).1
      (relocalizeSpace B hW hS h X).2) (U : SmallEtale B W hW X.1) :
    (PresheafOfModules.pushforward.{u} (chartSchemeRestrictionRingHom B W hW X.1 U)).obj
        (_root_.SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u}
          ((moduleDerelocalize B W S hW hS h X).obj N)).val =
      (PresheafOfModules.pushforward.{u} (F := openChartFunctor B W hW X.1 U ⋙
          (SmallEtale.relocalizeEquivalence B W S hW hS h X.1).functor)
          (R := (smallEtaleRingSheaf B S hS _ (relocalizeSpace B hW hS h X).2).obj)
          (chartSchemeRestrictionRingHom B W hW X.1 U)).obj
        (_root_.SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u} N).val :=
  Stacks.SheafOfModules.pushforward_ulift_pushforward_id
    (F := openChartFunctor B W hW X.1 U)
    (G := (SmallEtale.relocalizeEquivalence B W S hW hS h X.1).functor)
    (K := SmallEtale.topology B W hW X.1)
    (L := SmallEtale.topology B S hS (relocalizeSpace B hW hS h X).1)
    (R := smallEtaleRingSheaf B S hS _ (relocalizeSpace B hW hS h X).2)
    (hcont := SmallEtale.isContinuous_relocalizeEquivalence_functor B W S hW hS h X.1)
    (chartSchemeRestrictionRingHom B W hW X.1 U) N

/-- **Restriction to the scheme of an étale chart commutes with reading modules over `W`.** -/
def restrictToChartSchemeDerelocalizeIso (X : AlgebraicSpaces B W hW)
    (N : Modules.{u, u} B S hS (relocalizeSpace B hW hS h X).1
      (relocalizeSpace B hW hS h X).2) (U : SmallEtale B W hW X.1) :
    restrictToChartScheme B W hW X.1 X.2 ((moduleDerelocalize B W S hW hS h X).obj N) U ≅
      restrictToChartScheme B S hS (relocalizeSpace B hW hS h X).1
        (relocalizeSpace B hW hS h X).2 N
        ((SmallEtale.relocalizeEquivalence B W S hW hS h X.1).functor.obj U) :=
  letI : HasSheafify (Opens.grothendieckTopology (chartScheme U)) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite _ _
  letI : (Opens.grothendieckTopology (chartScheme U)).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  have e₁ : restrictToChartScheme B W hW X.1 X.2 ((moduleDerelocalize B W S hW hS h X).obj N) U =
      (PresheafOfModules.sheafification (𝟙 (chartScheme U).ringCatSheaf.obj)).obj
        ((PresheafOfModules.pushforward.{u} (F := openChartFunctor B W hW X.1 U ⋙
          (SmallEtale.relocalizeEquivalence B W S hW hS h X.1).functor)
          (R := (smallEtaleRingSheaf B S hS _ (relocalizeSpace B hW hS h X).2).obj)
          (chartSchemeRestrictionRingHom B W hW X.1 U)).obj
        (_root_.SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u} N).val) :=
    (restrictToChartScheme_eq_sheafification B W hW X.1 X.2 _ U).trans
      (congrArg (PresheafOfModules.sheafification (𝟙 (chartScheme U).ringCatSheaf.obj)).obj
        (pushforward_ulift_moduleDerelocalize h X N U))
  have e₂ : restrictToChartScheme B S hS (relocalizeSpace B hW hS h X).1
        (relocalizeSpace B hW hS h X).2 N
        ((SmallEtale.relocalizeEquivalence B W S hW hS h X.1).functor.obj U) =
      (PresheafOfModules.sheafification (𝟙 (chartScheme U).ringCatSheaf.obj)).obj
        ((PresheafOfModules.pushforward.{u} (chartSchemeRestrictionRingHom B S hS _
          ((SmallEtale.relocalizeEquivalence B W S hW hS h X.1).functor.obj U))).obj
        (_root_.SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u} N).val) :=
    restrictToChartScheme_eq_sheafification B S hS _ _ N _
  eqToIso e₁ ≪≫
    (PresheafOfModules.sheafification (𝟙 (chartScheme U).ringCatSheaf.obj)).mapIso
      ((Stacks.PresheafOfModules.pushforwardIsoOfIndexIso (openChartFunctorRelocalizeIso h U)
        (chartSchemeRestrictionRingHom_relocalize h U)).app
          (_root_.SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u} N).val) ≪≫
    eqToIso e₂.symm

end ChartRestriction

/-! ### The pullback of a module to a scheme, read over either base -/

section BaseChangeModule

/-- The relocalized chart of a morphism from a scheme factors through the relocalized identity
chart of that scheme. -/
theorem relocalizeChart_eq_comp {X : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u} {U : BigFppfOver B W hW}
    (p : yoneda.obj U ⟶ X) :
    relocalizeChart B W S hW hS h p =
      relocalizeChart B W S hW hS h (𝟙 (yoneda.obj U)) ≫
        (OverShriek.relocalizePresheafFunctor h).map p := by
  simp [relocalizeChart]

/-- **The pullback of a module to a scheme does not depend on the base.** For an
`𝒪_{Λ X}`-module `M` and a morphism `p : h_U ⟶ X` from a scheme over `W`, the pullback to `U` of
the module `M` read over `W` is the pullback of `M` along the relocalized morphism
`h_{Λ U} ⟶ Λ X`. -/
def baseChangeModuleDerelocalizeIso (X : AlgebraicSpaces B W hW)
    (M : Modules.{u, u} B S hS (relocalizeSpace B hW hS h X).1
      (relocalizeSpace B hW hS h X).2) (U : BigFppfOver B W hW) (p : yoneda.obj U ⟶ X.1) :
    baseChangeModule B W hW ((moduleDerelocalize B W S hW hS h X).obj M) U p ≅
      baseChangeModule B S hS M ((Over.map h).obj U) (relocalizeChart B W S hW hS h p) := by
  let Us : AlgebraicSpaces B W hW := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B W hW U⟩
  let pₛ : Us ⟶ X := ObjectProperty.homMk p
  let V := (SmallEtale.relocalizeEquivalence B W S hW hS h (yoneda.obj U)).functor.obj
    (idEtaleChart B W hW U)
  let N := (modulePullback B S hS (relocalizeSpaceMap h pₛ)).obj M
  let i₁ : baseChangeModule B W hW ((moduleDerelocalize B W S hW hS h X).obj M) U p ≅
      restrictToChartScheme B W hW Us.1 Us.2 ((moduleDerelocalize B W S hW hS h Us).obj N)
        (idEtaleChart B W hW U) :=
    (restrictToChartSchemeFunctor B W hW Us.1 Us.2 (idEtaleChart B W hW U)).mapIso
      ((modulePullbackRelocalizeIso h pₛ
        ((Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := X.1)).1
          X.2.diagonal_representable p)).app M)
  let Xs := relocalizeSpace B hW hS h Us
  let i₂ : restrictToChartScheme B W hW Us.1 Us.2 ((moduleDerelocalize B W S hW hS h Us).obj N)
        (idEtaleChart B W hW U) ≅ restrictToChartScheme B S hS Xs.1 Xs.2 N V :=
    restrictToChartSchemeDerelocalizeIso h Us N (idEtaleChart B W hW U)
  let i₃ : restrictToChartScheme B S hS Xs.1 Xs.2 N V ≅
      restrictToChartScheme B S hS (chartSpace B S hS Xs V).1 (chartSpace B S hS Xs V).2
        ((etaleModulePullback B S hS (chartToSpace B S hS Xs V)
          (isEtale_chartToSpace B S hS Xs V)).obj N)
        (idEtaleChart B S hS (chartFppfObject B S hS Xs V)) :=
    eqToIso (restrictToChartScheme_etaleModulePullback_idEtaleChart B S hS Xs N V).symm
  let i₄ := (restrictToChartSchemeFunctor B S hS (chartSpace B S hS Xs V).1
      (chartSpace B S hS Xs V).2 (idEtaleChart B S hS (chartFppfObject B S hS Xs V))).mapIso
    (((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS Xs V)
        (isEtale_chartToSpace B S hS Xs V)).app N).symm ≪≫
      (modulePullbackCompIso B S hS (chartToSpace B S hS Xs V) (relocalizeSpaceMap h pₛ)).app M)
  have hcomp : chartToSpace B S hS Xs V ≫ relocalizeSpaceMap h pₛ =
      ObjectProperty.homMk (relocalizeChart B W S hW hS h p) := by
    ext1
    exact (relocalizeChart_eq_comp h p).symm
  refine i₁ ≪≫ i₂ ≪≫ i₃ ≪≫ i₄ ≪≫ eqToIso ?_
  rw [hcomp]
  rfl

end BaseChangeModule

/-! ### Invertibility -/

section Invertible

variable (X : AlgebraicSpaces B W hW)

/-- Types have limits indexed by the category of structured arrows from `V` to the opposite of
the inverse of the equivalence of small étale sites. -/
instance hasLimitsOfShape_structuredArrow_relocalizeEquivalence_inverse
    (V : (SmallEtale B W hW X.1)ᵒᵖ) :
    Limits.HasLimitsOfShape
      (StructuredArrow V (SmallEtale.relocalizeEquivalence B W S hW hS h X.1).inverse.op)
      (Type u) :=
  Limits.hasLimitsOfShape_of_essentiallySmall _ _

/-- The inverse of the equivalence of small étale sites, from the small étale site of `Λ X` to
that of `X`, is a morphism of sites. -/
instance isMorphismOfSites_relocalizeEquivalence_inverse :
    IsMorphismOfSites.{u} (SmallEtale.relocalizeEquivalence B W S hW hS h X.1).inverse
      (SmallEtale.topology B S hS (relocalizeSpace B hW hS h X).1)
      (SmallEtale.topology B W hW X.1) :=
  IsMorphismOfSites.ofIsDenseSubsite _

/-- Reading `𝒪_{Λ X}` as a module over `W` gives `𝒪_X`. -/
def moduleDerelocalizeUnitIso :
    (moduleDerelocalize B W S hW hS h X).obj
        (SheafOfModules.unit (smallEtaleRingSheaf B S hS _ (relocalizeSpace B hW hS h X).2)) ≅
      SheafOfModules.unit (smallEtaleRingSheaf B W hW X.1 X.2) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.pushforwardUnitIso (𝟙 _))

/-- Reading modules over `W` carries tensor products to tensor products. -/
def moduleDerelocalizeTensorIso
    (M N : Modules.{u, u} B S hS (relocalizeSpace B hW hS h X).1
      (relocalizeSpace B hW hS h X).2) :
    (moduleDerelocalize B W S hW hS h X).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS _ (relocalizeSpace B hW hS h X).2)).obj M).obj N) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B W hW X.1 X.2)).obj ((moduleDerelocalize B W S hW hS h X).obj M)).obj
        ((moduleDerelocalize B W S hW hS h X).obj N) :=
  Stacks.SheafOfModules.reindexTensorIso (SmallEtale.topology B W hW X.1)
    (SmallEtale.relocalizeEquivalence B W S hW hS h X.1)
    (structureSheaf B S hS _ (relocalizeSpace B hW hS h X).2) M N

omit h in
/-- Invertibility of a module on an algebraic space only depends on its isomorphism class. -/
theorem isInvertible_of_iso_modules {T : Scheme.{u}} {hT : B.Contains T}
    {F : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B T hT F}
    {L L' : Modules.{u, u} B T hT F hF} (e : L ≅ L')
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B T hT F)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B T hT F hF).O)).property L) :
    Stacks.SheafOfModules.IsInvertible (structurePresheaf B T hT F)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B T hT F hF).O)).property
        L' := by
  obtain ⟨N, ⟨i⟩⟩ := (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit L).1 hL
  exact (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit L').2
    ⟨N, ⟨((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B T hT F hF)).mapIso e).symm.app N ≪≫ i⟩⟩

/-- **Invertibility is unchanged by reading a module over `W`.** -/
theorem isInvertible_moduleDerelocalize_iff
    (M : Modules.{u, u} B S hS (relocalizeSpace B hW hS h X).1
      (relocalizeSpace B hW hS h X).2) :
    Stacks.SheafOfModules.IsInvertible (structurePresheaf B W hW X.1)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B W hW X.1 X.2).O)).property
        ((moduleDerelocalize B W S hW hS h X).obj M) ↔
      Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS (relocalizeSpace B hW hS h X).1)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
          (relocalizeSpace B hW hS h X).1 (relocalizeSpace B hW hS h X).2).O)).property M := by
  let E := moduleRelocalizeEquivalence B W S hW hS h X
  refine (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
      ((moduleDerelocalize B W S hW hS h X).obj M)).trans
    (Iff.trans ?_ (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit M).symm)
  constructor
  · rintro ⟨N', ⟨e⟩⟩
    exact ⟨E.inverse.obj N', ⟨E.fullyFaithfulFunctor.preimageIso
      (moduleDerelocalizeTensorIso h X M (E.inverse.obj N') ≪≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B W hW X.1 X.2)).obj (E.functor.obj M)).mapIso (E.counitIso.app N') ≪≫
        e ≪≫ (moduleDerelocalizeUnitIso h X).symm)⟩⟩
  · rintro ⟨N, ⟨e⟩⟩
    exact ⟨E.functor.obj N, ⟨(moduleDerelocalizeTensorIso h X M N).symm ≪≫ E.functor.mapIso e ≪≫
      moduleDerelocalizeUnitIso h X⟩⟩

end Invertible

end AlgebraicGeometry.Space

end
