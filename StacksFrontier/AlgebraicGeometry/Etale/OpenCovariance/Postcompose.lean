module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition

/-!
# Post-composition with an open immersion and images of finite supports

Let `j : X' ⟶ X` be an open immersion in a big étale site. This file sets up the comparison of
the small étale sites of `X'` and `X` used to build the covariance map
`(j ≫ f)_!(F|_{X'}) ⟶ f_!F` of Stacks 0F6S: post-composition with `j`, restriction of abelian
sheaves along `j`, the open immersions `X'_V ⟶ X_V` it induces on étale base changes, and the
image of a support finite over an étale test object `V` under them.

## Main definitions

* `AlgebraicGeometry.SmallEtale.openPostcompose` — post-composition with `j`, the left adjoint
  of small étale base change along an open immersion, with
  `AlgebraicGeometry.SmallEtale.openPostcomposeAdjunction` that adjunction and
  `AlgebraicGeometry.SmallEtale.openRestrictionIso` the resulting identification of the inverse
  image `AlgebraicGeometry.SmallEtale.openRestriction` of abelian sheaves along `j` with direct
  image along post-composition.
* `AlgebraicGeometry.SmallEtale.openBaseChangeHom` — the open immersion `X'_V ⟶ X_V` induced on
  the étale base changes, and `AlgebraicGeometry.SmallEtale.imageFiniteSupport` the image of a
  support finite over `V` under it.

## Main results

* `AlgebraicGeometry.SmallEtale.openPostcompose_isContinuous` — post-composition with an open
  immersion is a continuous functor of small étale sites.

## Implementation notes

Post-composition with `j` is `AlgebraicGeometry.smallEtalePostcompose` at `j` itself, viewed as
an object of the small étale site of `X`, so full faithfulness, preservation of fibre products
and continuity are the general statements proved there. Fullness needs the structure morphism
of that object to be a monomorphism, which it is because an open immersion is.

`AlgebraicGeometry.SmallEtale.openCovarianceSupportOpen` and
`AlgebraicGeometry.SmallEtale.openCovarianceSupportObject` are convenience abbreviations for the
canonical open of a finite support and that open as an object of the small étale site.

## References

* [Stacks Project, Tag 0F6S](https://stacks.math.columbia.edu/tag/0F6S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X' X Y : B.Scheme} (j : X' ⟶ X)
  [IsOpenImmersion (B.inclusion.map j)]

section Postcompose

/-- Post-composition with an open immersion `j : X' ⟶ X`, as a functor from the small étale
site of `X'` to the small étale site of `X`: this is composition with `j` viewed as an object
of the small étale site of `X`. -/
public def openPostcompose :
    SmallEtale B X'.obj X'.property ⥤ SmallEtale B X.obj X.property :=
  smallEtalePostcompose B X.obj X.property
    ⟨Over.mk j, inferInstanceAs (Etale (B.inclusion.map j))⟩

/-- Post-composition with `j` is pointwise post-composition in the ambient slice categories. -/
public theorem openPostcompose_comp_inclusion :
    openPostcompose B j ⋙ SmallEtale.inclusion B X.obj X.property =
      SmallEtale.inclusion B X'.obj X'.property ⋙ Over.map j := rfl

/-- Post-composition with `j` does not change the underlying scheme. -/
public theorem openPostcompose_toScheme_obj (W : SmallEtale B X'.obj X'.property) :
    (SmallEtale.toScheme B X.obj X.property).obj ((openPostcompose B j).obj W) =
      (SmallEtale.toScheme B X'.obj X'.property).obj W := rfl

/-- Post-composition with `j` does not change the underlying morphism of schemes. -/
public theorem openPostcompose_toScheme_map {W W' : SmallEtale B X'.obj X'.property}
    (g : W' ⟶ W) :
    (SmallEtale.toScheme B X.obj X.property).map ((openPostcompose B j).map g) =
      (SmallEtale.toScheme B X'.obj X'.property).map g := rfl

/-- The structure morphism of an object post-composed with `j` is the original structure
morphism followed by `j`. -/
public theorem openPostcompose_obj_hom (W : SmallEtale B X'.obj X'.property) :
    ((openPostcompose B j).obj W).obj.hom = W.obj.hom ≫ j := rfl

/-- An open immersion of a big étale site is a monomorphism of that site. -/
public instance mono_openImmersion : Mono j := by
  refine ⟨fun {Z} g h e => B.inclusion.map_injective ?_⟩
  have : Mono (B.inclusion.map j) := inferInstance
  rw [← cancel_mono (B.inclusion.map j), ← Functor.map_comp, ← Functor.map_comp, e]

/-- Post-composition with an open immersion is faithful. -/
public instance : (openPostcompose B j).Faithful :=
  faithful_smallEtalePostcompose B X.obj X.property _

/-- Post-composition with an open immersion is full, since `j` is a monomorphism. -/
public instance : (openPostcompose B j).Full :=
  haveI : Mono (Over.mk j).hom := mono_openImmersion B j
  full_smallEtalePostcompose B X.obj X.property _

/-- Post-composition between slice categories preserves fibre products: the forgetful functor
of a slice creates connected limits, and post-composition does not change it. -/
public instance preservesPullbacks_overMap {P Q : B.Scheme} (g : P ⟶ Q) :
    PreservesLimitsOfShape WalkingCospan (Over.map g) := by
  have h : PreservesLimitsOfShape WalkingCospan (Over.map g ⋙ Over.forget Q) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (Over.forget P))
  exact preservesLimitsOfShape_of_reflects_of_preserves (Over.map g) (Over.forget Q)

/-- Post-composition with `j` preserves fibre products of the small étale sites. -/
public instance preservesPullbacks_openPostcompose :
    PreservesLimitsOfShape WalkingCospan (openPostcompose B j) :=
  preservesPullbacks_smallEtalePostcompose B X.obj X.property _

/-- Post-composition with `j` is compatible-preserving. -/
public theorem openPostcompose_compatiblePreserving :
    CompatiblePreserving.{u + 1} (SmallEtale.topology B X.obj X.property)
      (openPostcompose B j) :=
  smallEtalePostcompose_compatiblePreserving B X.obj X.property _

/-- Post-composition with `j` carries covering families to covering families. -/
public theorem openPostcompose_coverPreserving :
    CoverPreserving (SmallEtale.topology B X'.obj X'.property)
      (SmallEtale.topology B X.obj X.property) (openPostcompose B j) :=
  smallEtalePostcompose_coverPreserving B X.obj X.property
    ⟨Over.mk j, inferInstanceAs (Etale (B.inclusion.map j))⟩

/-- **Post-composition with an open immersion is continuous.** It therefore induces a direct
image on abelian sheaves. -/
public instance openPostcompose_isContinuous :
    (openPostcompose B j).IsContinuous
      (SmallEtale.topology B X'.obj X'.property)
      (SmallEtale.topology B X.obj X.property) :=
  smallEtalePostcompose_isContinuous B X.obj X.property _

/-- Post-composition with `j` is left adjoint to small étale base change along `j`. -/
public def openPostcomposeAdjunction :
    openPostcompose B j ⊣ smallEtaleBaseChange B j :=
  (Over.mapPullbackAdj j).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι (BigEtaleOver.IsEtaleOver B X'.obj X'.property))
    (ObjectProperty.fullyFaithfulι (BigEtaleOver.IsEtaleOver B X.obj X.property))
    (eqToIso (openPostcompose_comp_inclusion B j))
    (eqToIso (smallEtaleBaseChange_comp_inclusion B j).symm)

/-- The counit of the adjunction is, on schemes, the projection of the fibre product with the
open subscheme. -/
public theorem openPostcomposeAdjunction_counit_toScheme (W : SmallEtale B X.obj X.property) :
    (SmallEtale.toScheme B X.obj X.property).map
      ((openPostcomposeAdjunction B j).counit.app W) =
        B.inclusion.map (pullback.fst W.obj.hom j) := rfl

end Postcompose

section Restriction

variable (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- Restriction of abelian sheaves to the open subscheme: the inverse image along small étale
base change. -/
public abbrev openRestriction :
    Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (SmallEtale.topology B X'.obj X'.property) AddCommGrpCat.{max (u + 1) v} :=
  (smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{max (u + 1) v}
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B X'.obj X'.property)

/-- Restriction to the open subscheme is the direct image along post-composition with `j`:
both are left adjoint to the direct image along base change. -/
public def openRestrictionIso :
    (openPostcompose B j).sheafPushforwardContinuous
        AddCommGrpCat.{max (u + 1) v}
        (SmallEtale.topology B X'.obj X'.property)
        (SmallEtale.topology B X.obj X.property) ≅
      openRestriction.{u, v} B j :=
  Adjunction.leftAdjointUniq
    (Adjunction.sheafPushforwardContinuous (openPostcomposeAdjunction B j)
      (SmallEtale.topology B X'.obj X'.property)
      (SmallEtale.topology B X.obj X.property))
    ((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X'.obj X'.property))

/-- The comparison of the two descriptions of restriction carries the restriction of a section
along the counit to the unit of the base-change adjunction. -/
public theorem openRestrictionIso_unit_app
    (W : SmallEtale B X.obj X.property) (s : F.obj.obj (op W)) :
    ((openRestrictionIso.{u, v} B j).hom.app F).hom.app
        (op ((smallEtaleBaseChange B j).obj W))
        (F.obj.map ((openPostcomposeAdjunction B j).counit.app W).op s) =
      (((smallEtaleBaseChange B j).sheafAdjunctionContinuous
        AddCommGrpCat.{max (u + 1) v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app (op W) s :=
  congrArg (fun η => η.hom.app (op W) s)
    (Adjunction.unit_leftAdjointUniq_hom_app
      (Adjunction.sheafPushforwardContinuous (openPostcomposeAdjunction B j)
        (SmallEtale.topology B X'.obj X'.property)
        (SmallEtale.topology B X.obj X.property))
      ((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property)) F)

end Restriction

section BaseChangeHom

variable (f : X ⟶ Y)

/-- The open immersion `X'_V ⟶ X_V` induced on the étale base changes by `j`. -/
public def openBaseChangeHom (V : SmallEtale B Y.obj Y.property) :
    (SmallEtale.toScheme B X'.obj X'.property).obj (baseChange B (j ≫ f) V) ⟶
      (SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V) :=
  (SmallEtale.toScheme B X'.obj X'.property).map
      ((smallEtaleBaseChange_compIso B X' X Y j f).val.inv.app V) ≫
    B.inclusion.map (pullback.fst ((baseChange B f V).obj.hom) j)

/-- The induced map on the étale base changes is an open immersion. -/
public instance openBaseChangeHom_isOpenImmersion (V : SmallEtale B Y.obj Y.property) :
    IsOpenImmersion (openBaseChangeHom B j f V) := by
  let e := (smallEtaleBaseChange_compIso B X' X Y j f).val
  have : IsIso ((SmallEtale.toScheme B X'.obj X'.property).map (e.inv.app V)) :=
    Functor.map_isIso _ _
  have hfst : IsOpenImmersion
      (B.inclusion.map (pullback.fst ((baseChange B f V).obj.hom) j)) :=
    MorphismProperty.of_isPullback
      (IsPullback.map B.inclusion
        (IsPullback.of_hasPullback ((baseChange B f V).obj.hom) j).flip)
      (show IsOpenImmersion (B.inclusion.map j) from inferInstance)
  change IsOpenImmersion
    ((SmallEtale.toScheme B X'.obj X'.property).map (e.inv.app V) ≫
      B.inclusion.map (pullback.fst ((baseChange B f V).obj.hom) j))
  exact MorphismProperty.comp_mem @IsOpenImmersion _ _ inferInstance hfst

omit [IsOpenImmersion (B.inclusion.map j)] in
/-- The induced map on the étale base changes is compatible with the projections to `X`. -/
public theorem openBaseChangeHom_comp (V : SmallEtale B Y.obj Y.property) :
    openBaseChangeHom B j f V ≫ B.inclusion.map (pullback.fst V.obj.hom f) =
      B.inclusion.map (pullback.fst V.obj.hom (j ≫ f)) := by
  let e := (smallEtaleBaseChange_compIso B X' X Y j f).val
  have hInv : (SmallEtale.inclusion B X'.obj X'.property).map (e.inv.app V) =
      (Over.pullbackComp j f).hom.app V.obj := by
    have he := smallEtaleBaseChange_compIso_app B X' X Y j f V
    refine (cancel_mono ((SmallEtale.inclusion B X'.obj X'.property).map
      (e.hom.app V))).1 ?_
    have h₁ : (SmallEtale.inclusion B X'.obj X'.property).map (e.inv.app V) ≫
        (SmallEtale.inclusion B X'.obj X'.property).map (e.hom.app V) = 𝟙 _ := by
      rw [← Functor.map_comp]
      simp [e]
    have h₂ : (Over.pullbackComp j f).hom.app V.obj ≫
        (SmallEtale.inclusion B X'.obj X'.property).map (e.hom.app V) = 𝟙 _ := by
      rw [he]
      simp
    exact h₁.trans h₂.symm
  have hfgB : ((SmallEtale.inclusion B X'.obj X'.property).map (e.inv.app V)).left ≫
      pullback.fst ((Over.pullback f).obj V.obj).hom j ≫ pullback.fst V.obj.hom f =
        pullback.fst V.obj.hom (j ≫ f) := by
    rw [congrArg (fun g => g.left) hInv]
    exact Over.pullbackComp_hom_app_left_fst_fst j f V.obj
  have hW : (baseChange B f V).obj = (Over.pullback f).obj V.obj :=
    smallEtaleBaseChange_obj_obj B f V
  cases hW
  change B.inclusion.map
      (((SmallEtale.inclusion B X'.obj X'.property).map (e.inv.app V)).left ≫
        pullback.fst ((Over.pullback f).obj V.obj).hom j ≫
          pullback.fst V.obj.hom f) = _
  exact congrArg B.inclusion.map hfgB

/-- The natural transformation of base-change functors underlying
`AlgebraicGeometry.SmallEtale.openBaseChangeHom`. -/
public def openBaseChangeMap :
    smallEtaleBaseChange B (j ≫ f) ⋙ openPostcompose B j ⟶ smallEtaleBaseChange B f :=
  Functor.whiskerRight (smallEtaleBaseChange_compIso B X' X Y j f).val.inv
      (openPostcompose B j) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (smallEtaleBaseChange B f) (openPostcomposeAdjunction B j).counit ≫
    (Functor.rightUnitor _).hom

/-- On schemes, the natural transformation of base changes is the induced open immersion. -/
public theorem openBaseChangeMap_toScheme (V : SmallEtale B Y.obj Y.property) :
    (SmallEtale.toScheme B X.obj X.property).map ((openBaseChangeMap B j f).app V) =
      openBaseChangeHom B j f V := by
  simp only [openBaseChangeMap, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Category.id_comp, Functor.map_comp,
    openPostcomposeAdjunction_counit_toScheme, openPostcompose_toScheme_map]
  rfl

/-- The induced open immersions on étale base changes are natural in the test object. -/
public theorem openBaseChangeHom_naturality {V V' : SmallEtale B Y.obj Y.property}
    (g : V' ⟶ V) :
    openBaseChangeHom B j f V' ≫
      (SmallEtale.toScheme B X.obj X.property).map ((smallEtaleBaseChange B f).map g) =
    (SmallEtale.toScheme B X'.obj X'.property).map
      ((smallEtaleBaseChange B (j ≫ f)).map g) ≫ openBaseChangeHom B j f V := by
  have h := congrArg (SmallEtale.toScheme B X.obj X.property).map
    ((openBaseChangeMap B j f).naturality g)
  change (SmallEtale.toScheme B X.obj X.property).map
      ((openPostcompose B j).map ((smallEtaleBaseChange B (j ≫ f)).map g)) ≫
        (SmallEtale.toScheme B X.obj X.property).map ((openBaseChangeMap B j f).app V) =
      (SmallEtale.toScheme B X.obj X.property).map ((openBaseChangeMap B j f).app V') ≫
        (SmallEtale.toScheme B X.obj X.property).map ((smallEtaleBaseChange B f).map g) at h
  rw [openBaseChangeMap_toScheme, openBaseChangeMap_toScheme,
    openPostcompose_toScheme_map] at h
  exact h.symm

omit [IsOpenImmersion (B.inclusion.map j)] in
/-- Precomposing with an isomorphism of schemes does not change the image of a morphism. -/
public theorem scheme_range_comp_iso {P Q R : Scheme.{u}} (e : P ⟶ Q) [IsIso e] (k : Q ⟶ R) :
    Set.range (e ≫ k).base = Set.range k.base := by
  have hsurj : Function.Surjective e.base := fun x =>
    ⟨(inv e).base x, congrArg (fun m : Q ⟶ Q => m.base x) (IsIso.inv_hom_id e)⟩
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.range_eq, Set.image_univ]

omit [IsOpenImmersion (B.inclusion.map j)] in
/-- The image of the induced open immersion on étale base changes is the inverse image of the
open subscheme. -/
public theorem openBaseChangeHom_range (V : SmallEtale B Y.obj Y.property) :
    Set.range (openBaseChangeHom B j f V).base =
      (B.inclusion.map (baseChange B f V).obj.hom).base ⁻¹'
        Set.range (B.inclusion.map j).base := by
  have h := IsPullback.map B.inclusion
    (IsPullback.of_hasPullback (baseChange B f V).obj.hom j)
  rw [openBaseChangeHom, scheme_range_comp_iso]
  change Set.range (B.inclusion.map (pullback.fst (baseChange B f V).obj.hom j)).base = _
  calc
    _ = Set.range (h.isoPullback.hom ≫ pullback.fst _ _).base :=
      congrArg (fun k => Set.range k.base) h.isoPullback_hom_fst.symm
    _ = Set.range (pullback.fst (B.inclusion.map (baseChange B f V).obj.hom)
        (B.inclusion.map j)).base := scheme_range_comp_iso h.isoPullback.hom _
    _ = _ := Scheme.Pullback.range_fst _ _

omit [IsOpenImmersion (B.inclusion.map j)] in
/-- The images of the induced open immersions are compatible with base change. -/
public theorem openBaseChangeHom_range_preimage {V V' : SmallEtale B Y.obj Y.property}
    (g : V' ⟶ V) :
    ((SmallEtale.toScheme B X.obj X.property).map
      ((smallEtaleBaseChange B f).map g)).base ⁻¹'
        Set.range (openBaseChangeHom B j f V).base =
      Set.range (openBaseChangeHom B j f V').base := by
  rw [openBaseChangeHom_range, openBaseChangeHom_range]
  have h := congrArg B.inclusion.map (Over.w (((smallEtaleBaseChange B f).map g).hom))
  rw [Functor.map_comp] at h
  change (SmallEtale.toScheme B X.obj X.property).map
      ((smallEtaleBaseChange B f).map g) ≫ B.inclusion.map (baseChange B f V).obj.hom =
    B.inclusion.map (baseChange B f V').obj.hom at h
  exact congrArg (fun k => k.base ⁻¹' Set.range (B.inclusion.map j).base) h

/-- Taking the image of a subset under the induced open immersion commutes with base
change. -/
public theorem openBaseChangeHom_image_preimage {V V' : SmallEtale B Y.obj Y.property}
    (g : V' ⟶ V)
    (E : Set ((SmallEtale.toScheme B X'.obj X'.property).obj (baseChange B (j ≫ f) V))) :
    (openBaseChangeHom B j f V').base ''
      (((SmallEtale.toScheme B X'.obj X'.property).map
        ((smallEtaleBaseChange B (j ≫ f)).map g)).base ⁻¹' E) =
    ((SmallEtale.toScheme B X.obj X.property).map
      ((smallEtaleBaseChange B f).map g)).base ⁻¹'
        ((openBaseChangeHom B j f V).base '' E) := by
  let φ := (openBaseChangeHom B j f V).base
  let φ' := (openBaseChangeHom B j f V').base
  let a := ((SmallEtale.toScheme B X'.obj X'.property).map
    ((smallEtaleBaseChange B (j ≫ f)).map g)).base
  let b := ((SmallEtale.toScheme B X.obj X.property).map
    ((smallEtaleBaseChange B f).map g)).base
  have hc (x) : b (φ' x) = φ (a x) :=
    congrArg (fun k => k.base x) (openBaseChangeHom_naturality B j f g)
  have hi : Function.Injective φ := (openBaseChangeHom B j f V).isOpenEmbedding.injective
  have hr : b ⁻¹' Set.range φ = Set.range φ' := openBaseChangeHom_range_preimage B j f g
  change φ' '' (a ⁻¹' E) = b ⁻¹' (φ '' E)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨a y, hy, (hc y).symm⟩
  · rintro ⟨y, hy, he⟩
    have hx : x ∈ b ⁻¹' Set.range φ := ⟨y, he⟩
    rw [hr] at hx
    obtain ⟨z, rfl⟩ := hx
    refine ⟨z, ?_, rfl⟩
    change a z ∈ E
    rwa [hi ((hc z).symm.trans he.symm)]

end BaseChangeHom

section ImageSupport

variable (f : X ⟶ Y)

/-- The image of a support finite over `V` under the induced open immersion is again a support
finite over `V`. -/
public theorem finiteSupport_image (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B (j ≫ f) V) :
    ∃ D : FiniteSupport B f V, D.1 = (openBaseChangeHom B j f V).base '' E.1 := by
  obtain ⟨Z, i, hi, hfin, hrange⟩ := E.property
  let φ := openBaseChangeHom B j f V
  have : IsImmersion i := hi
  have : IsImmersion (i ≫ φ) := inferInstance
  have hcomp : (i ≫ φ) ≫ B.inclusion.map (pullback.fst V.obj.hom f) =
      i ≫ B.inclusion.map (pullback.fst V.obj.hom (j ≫ f)) :=
    (Category.assoc i φ _).trans
      (congrArg (fun k => i ≫ k) (openBaseChangeHom_comp B j f V))
  have hfinite : IsFinite ((i ≫ φ) ≫ B.inclusion.map (pullback.fst V.obj.hom f)) := by
    rwa [hcomp]
  have himage : Set.range (i ≫ φ).base = φ.base '' E.1 := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange]
  exact ⟨⟨φ.base '' E.1, Z, i ≫ φ, inferInstance, hfinite, himage⟩, rfl⟩

/-- The image of a support finite over `V` under the induced open immersion, as a support
finite over `V`. -/
public def imageFiniteSupport (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B (j ≫ f) V) : FiniteSupport B f V :=
  Classical.choose (finiteSupport_image B j f V E)

/-- The underlying subset of the image support is the image of the subset. -/
public theorem imageFiniteSupport_coe (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B (j ≫ f) V) :
    (imageFiniteSupport B j f V E).1 = (openBaseChangeHom B j f V).base '' E.1 :=
  Classical.choose_spec (finiteSupport_image B j f V E)

/-- Taking the image support is monotone. -/
public theorem imageFiniteSupport_mono (V : SmallEtale B Y.obj Y.property)
    {E E' : FiniteSupport B (j ≫ f) V} (h : E ≤ E') :
    imageFiniteSupport B j f V E ≤ imageFiniteSupport B j f V E' := by
  change (imageFiniteSupport B j f V E).1 ⊆ (imageFiniteSupport B j f V E').1
  rw [imageFiniteSupport_coe, imageFiniteSupport_coe]
  exact Set.image_mono h

/-- The canonical open of the image support pulls back to the canonical open of the original
support. -/
public theorem openBaseChangeHom_supportOpen_preimage (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B (j ≫ f) V) (D : FiniteSupport B f V)
    (hD : D.1 = (openBaseChangeHom B j f V).base '' E.1) :
    (openBaseChangeHom B j f V).base ⁻¹'
        supportOpen B X.obj X.property (baseChange B f V) D.1
          (finiteSupport_isLocallyClosed B f V D) =
      supportOpen B X'.obj X'.property (baseChange B (j ≫ f) V) E.1
        (finiteSupport_isLocallyClosed B (j ≫ f) V E) := by
  let φ := openBaseChangeHom B j f V
  change φ.base ⁻¹' coborder D.1 = coborder E.1
  rw [hD, ← φ.isOpenEmbedding.coborder_preimage,
    Set.preimage_image_eq _ φ.isOpenEmbedding.injective]

end ImageSupport

section SupportObject

/-- The canonical open of `X_V` attached to a support finite over `V`. -/
public abbrev openCovarianceSupportOpen {S T : B.Scheme} (g : S ⟶ T)
    (V : SmallEtale B T.obj T.property) (E : FiniteSupport B g V) :
    ((SmallEtale.toScheme B S.obj S.property).obj (baseChange B g V)).Opens :=
  supportOpen B S.obj S.property (baseChange B g V) E.1
    (finiteSupport_isLocallyClosed B g V E)

/-- The canonical open of `X_V` attached to a support finite over `V`, as an object of the
small étale site. -/
public abbrev openCovarianceSupportObject {S T : B.Scheme} (g : S ⟶ T)
    (V : SmallEtale B T.obj T.property) (E : FiniteSupport B g V) :
    SmallEtale B S.obj S.property :=
  openObject B S.obj S.property (baseChange B g V) (openCovarianceSupportOpen B g V E)

/-- The transition morphism of canonical support opens for an inclusion of finite supports. -/
public abbrev finiteSupportTransitionOpenMap {S T : B.Scheme} (g : S ⟶ T)
    (V : SmallEtale B T.obj T.property) {E E' : FiniteSupport B g V} (h : E ⟶ E') :
    openCovarianceSupportObject B g V E' ⟶ openCovarianceSupportObject B g V E :=
  openObjectHomOfLE B S.obj S.property (baseChange B g V)
    (supportOpen_antitone B S.obj S.property (baseChange B g V) E.1 E'.1
      (finiteSupport_isLocallyClosed B g V E) (finiteSupport_isLocallyClosed B g V E')
      (leOfHom h) (finiteSupport_closedWithin B g V E E' (leOfHom h)))

/-- The transition map of the finite-support diagram is restriction along the transition
morphism of canonical support opens. -/
public theorem finiteSupportDiagram_map_val {S T : B.Scheme} (g : S ⟶ T)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{v})
    (V : SmallEtale B T.obj T.property) {E E' : FiniteSupport B g V} (h : E ⟶ E')
    (s : (finiteSupportDiagram B g F V).obj E) :
    ((finiteSupportDiagram B g F V).map h s).val =
      F.obj.map (finiteSupportTransitionOpenMap B g V h).op s.val :=
  supportedSectionsMap_apply B S.obj S.property F (baseChange B g V) E.1 E'.1 _ _
    (leOfHom h) (finiteSupport_closedWithin B g V E E' (leOfHom h)) s

end SupportObject

end AlgebraicGeometry.SmallEtale

end
