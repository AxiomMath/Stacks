module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.LimitsOver
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.GuitartExact.KanExtension
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.Modules.Differentials
public import StacksCore.Tactic.StacksAttribute

/-!
# The small Zariski site inside the big Zariski site

The small Zariski site of a scheme `S` is the full subcategory of the big Zariski site of `S`
on the open immersions into `S`, equivalently the site of open subsets of the underlying space
of `S`. Its inclusion into the big Zariski site is realised by
`AlgebraicGeometry.Scheme.restrictFunctor`, which sends an open `U ⊆ S` to the open subscheme
`U` viewed as a scheme over `S`. That functor is continuous, cocontinuous and fully faithful,
so it is a morphism of sites and restriction along it has both adjoints.

An abelian sheaf `F` on the small Zariski site therefore has an *extension* to the big Zariski
site: the left adjoint of restriction, applied to `F`. Because the inclusion is fully faithful,
the unit of the adjunction is an isomorphism, so the extension really does restrict back to
`F`. The extension is computed geometrically: its value at a scheme `T` over `S` is the group
of global sections on `T` of the inverse image of `F` along the structure morphism
`T ⟶ S`, and this identification is natural in `T`.

## Main definitions

* `AlgebraicGeometry.SmallZariski.adjunction` — the adjunction between extension from, and
  restriction to, the small Zariski site.
* `AlgebraicGeometry.SmallZariski.extension` — the extension of an abelian sheaf from the
  small Zariski site of `S` to the big Zariski site of `S`.
* `AlgebraicGeometry.SmallZariski.sheafComparisonIso` — base change for sheaf pullback along a
  Guitart exact square of sites.
* `AlgebraicGeometry.SmallZariski.relativeOpens` and
  `AlgebraicGeometry.SmallZariski.inverseImageOpens` — the two legs comparing the opens of a
  scheme `T` over `S` with the opens of `S`.
* `AlgebraicGeometry.SmallZariski.pullbackSectionsRestriction` — the restriction map on global
  sections of the geometric inverse images along a morphism over `S`.

## Main results

* `AlgebraicGeometry.SmallZariski.restrictFunctor_isContinuous`,
  `AlgebraicGeometry.SmallZariski.restrictFunctor_isCocontinuous` and
  `AlgebraicGeometry.SmallZariski.restrictFunctor_full` — the inclusion of the small Zariski
  site is a fully faithful morphism of sites.
* `AlgebraicGeometry.SmallZariski.extension_sections` — the value of the extension at a scheme
  `T` over `S` is the group of global sections of the inverse image of the sheaf along the
  structure morphism of `T`.
* `AlgebraicGeometry.SmallZariski.extension_sections_naturality` — that identification is
  natural in `T`.
* `AlgebraicGeometry.SmallZariski.isIso_extension_unit` — restricting the extension back to
  the small Zariski site returns the original sheaf.

## Implementation notes

The small Zariski site is modelled by `TopologicalSpace.Opens S` with
`TopologicalSpace.Opens.grothendieckTopology`, and the big Zariski site of `S` by `Over S`
with `AlgebraicGeometry.Scheme.zariskiTopology.over S`. This differs from
`AlgebraicGeometry.SmallZariski`, which cuts the small Zariski site out of a chosen big
Zariski site of bounded size; the present model is the one for which Mathlib's inverse image
of sheaves on a topological space is available.

Coefficients lie in `AddCommGrpCat.{max (u + 1) v}` with `v` independent of the scheme
universe `u`. The `u + 1` is forced: the big Zariski site has objects in `Type (u + 1)`, so
sheafification over it needs coefficients with limits and colimits of that size. Only the
site-level `CategoryTheory.Functor.sheafPullback` is used, whose coefficient universe is
independent of both site universes; the space-level `TopCat.Sheaf.pullback` is avoided because
it ties the coefficient universe to the universe of the topological space.

For each morphism `T' ⟶ T` over `S` the geometric restriction is defined directly from the
inverse-image adjunction and the composition isomorphism for pullback of opens. Its
compatibility with the extension comparison is stated separately, so the formula is natural in
`T`, not merely pointwise.

## References

* [Stacks Project, Tag 03FI](https://stacks.math.columbia.edu/tag/03FI)
* [Stacks Project, Tag 020T](https://stacks.math.columbia.edu/tag/020T)
* [Stacks Project, Tag 020Z](https://stacks.math.columbia.edu/tag/020Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v w

namespace AlgebraicGeometry.SmallZariski

/-- Sheafification of abelian groups on the site of opens of a topological space, at the
coefficient universe needed for the big Zariski site. -/
public instance hasSheafify_opens (X : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology X)
      AddCommGrpCat.{max (u + 1) v} := by
  have : EssentiallySmall.{max (u + 1) v} (Opens X) := inferInstance
  have : HasSheafify ((equivSmallModel.{max (u + 1) v} (Opens X)).inverse.inducedTopology
      (Opens.grothendieckTopology X)) AddCommGrpCat.{max (u + 1) v} := inferInstance
  exact hasSheafifyEssentiallySmallSite _ _

/-- The inclusion of the small Zariski site of a scheme, as the open subschemes
inside its big Zariski site, is continuous. -/
public instance restrictFunctor_isContinuous (S : Scheme.{u}) :
    S.restrictFunctor.IsContinuous (Opens.grothendieckTopology S)
      (Scheme.zariskiTopology.over S) := by
  let J : Precoverage S.Opens :=
    (Opens.grothendieckTopology S).toPrecoverage
  have hJ : J.toGrothendieck = Opens.grothendieckTopology S := by
    refine le_antisymm (GrothendieckTopology.toGrothendieck_toPrecoverage_le _) fun U R hR => ?_
    rw [← GrothendieckTopology.arrows_mem_toPrecoverage_iff] at hR
    simpa using Precoverage.generate_mem_toGrothendieck hR
  rw [← hJ]
  change S.restrictFunctor.IsContinuous J.toGrothendieck
    ((Scheme.precoverage @IsOpenImmersion).toGrothendieck.over S)
  rw [CategoryTheory.over_toGrothendieck_eq_toGrothendieck_comap_forget]
  have hscheme : PreservesLimitsOfShape WalkingCospan
      (S.restrictFunctor ⋙ Over.forget S) := by
    apply Limits.preservesLimitsOfShape_walkingCospan_of_forall_isPullback
    intro U V W (f : U ⟶ W) (g : V ⟶ W) _
    have hf : f = homOfLE f.le := Subsingleton.elim _ _
    have hg : g = homOfLE g.le := Subsingleton.elim _ _
    rw [hf, hg]
    refine ⟨U ⊓ V, homOfLE inf_le_left, homOfLE inf_le_right, ?_, ?_⟩
    · refine (CategoryTheory.isPullback_iff_isLimit_binaryFan_of_isThin).2 ?_
      exact ⟨BinaryFan.IsLimit.mk _
        (fun {A} (a : A ⟶ U) (b : A ⟶ V) => homOfLE (le_inf a.le b.le))
        (fun _ _ => Subsingleton.elim _ _) (fun _ _ => Subsingleton.elim _ _)
        (fun _ _ _ _ _ => Subsingleton.elim _ _)⟩
    · change IsPullback (S.homOfLE inf_le_left) (S.homOfLE inf_le_right)
        (S.homOfLE f.le) (S.homOfLE g.le)
      exact AlgebraicGeometry.isPullback_opens_inf_le f.le g.le
  have : PreservesLimitsOfShape WalkingCospan S.restrictFunctor :=
    preservesLimitsOfShape_of_reflects_of_preserves S.restrictFunctor (Over.forget S)
  apply Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy
  intro U R hR
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  rw [Precoverage.mem_comap_iff, Precoverage.mem_comap_iff]
  simp only [Presieve.map_ofArrows]
  change Presieve.ofArrows (fun i => (V i).toScheme)
      (fun i => S.homOfLE (f i).le) ∈
    Scheme.precoverage @IsOpenImmersion ((U : S.Opens).toScheme)
  rw [Scheme.ofArrows_mem_precoverage_iff]
  refine ⟨?_, ?_⟩
  · have hcover : Sieve.generate (Presieve.ofArrows V f) ∈
        Opens.grothendieckTopology S U := by
      simpa [J, GrothendieckTopology.mem_toPrecoverage_iff] using hR
    rw [Opens.mem_grothendieckTopology] at hcover
    intro x
    obtain ⟨W, g, hg, hxW⟩ := hcover x.1 x.2
    let y : W := ⟨x.1, hxW⟩
    obtain ⟨Z, k, r, hr, hkr⟩ := hg
    rcases hr with ⟨i⟩
    refine ⟨i, ⟨k y, ?_⟩⟩
    apply Subtype.ext
    rw [Scheme.homOfLE_apply]
    calc
      ↑(k y) = (f i (k y)).1 := rfl
      _ = (g y).1 := by simp
      _ = x.1 := rfl
  · exact fun _ => inferInstance

/-- The inclusion of the small Zariski site of a scheme into its big Zariski site is
cocontinuous: every Zariski covering of an open subscheme is refined by a covering by opens. -/
public instance restrictFunctor_isCocontinuous (S : Scheme.{u}) :
    (S.restrictFunctor).IsCocontinuous (Opens.grothendieckTopology S)
      (Scheme.zariskiTopology.over S) where
  cover_lift := by
    intro U R hR
    rw [GrothendieckTopology.mem_over_iff] at hR
    obtain ⟨C, hC⟩ := Scheme.exists_cover_of_mem_grothendieckTopology
      (P := @IsOpenImmersion) hR
    have hCmem := C.mem₀
    rw [Scheme.ofArrows_mem_precoverage_iff] at hCmem
    rcases hCmem with ⟨hjoint, hopen⟩
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    let y : U.toScheme := ⟨x, hx⟩
    obtain ⟨i, z, hz⟩ := hjoint y
    let g := C.f i ≫ (S.restrictFunctor.obj U).hom
    have : IsOpenImmersion (C.f i) := hopen i
    have : IsOpenImmersion (S.restrictFunctor.obj U).hom := by
      dsimp [Scheme.restrictFunctor]
      infer_instance
    have : IsOpenImmersion g := by
      dsimp [g]
      infer_instance
    let V := g.opensRange
    have hrange : Set.range g = Set.range V.ι := by simp [V]
    let e := IsOpenImmersion.isoOfRangeEq g V.ι hrange
    have hev : e.inv ≫ g = V.ι :=
      IsOpenImmersion.isoOfRangeEq_inv_fac g V.ι hrange
    have hVle : V ≤ U := by
      apply SetLike.coe_subset_coe.mp
      intro p hp
      obtain ⟨q, hq⟩ := Set.mem_range.mp (by simpa [V, Scheme.Hom.coe_opensRange] using hp)
      have hqp : (S.restrictFunctor.obj U).hom (C.f i q) = p := hq
      rw [← hqp]
      exact (C.f i q).property
    have hxV : x ∈ V := by
      change x ∈ Set.range g
      exact ⟨z, congrArg U.ι hz⟩
    let r : Over.mk (C.f i ≫ U.ι) ⟶ S.restrictFunctor.obj U :=
      Over.homMk (C.f i) (by simp [Scheme.restrictFunctor])
    have hr : R.arrows r :=
      (Sieve.overEquiv_iff R (C.f i)).1 (hC (C.X i) (C.f i) (Presieve.ofArrows.mk i))
    let a : S.restrictFunctor.obj V ⟶ Over.mk (C.f i ≫ U.ι) :=
      Over.homMk e.inv hev
    have hqa : (S.restrictFunctor.map (homOfLE hVle)) = a ≫ r := by
      apply Over.OverMorphism.ext
      apply (cancel_mono (S.restrictFunctor.obj U).hom).1
      calc
        S.homOfLE hVle ≫ (S.restrictFunctor.obj U).hom = V.ι := by
          simp [Scheme.restrictFunctor]
        _ = e.inv ≫ C.f i ≫ (S.restrictFunctor.obj U).hom := by
          simpa [g] using hev.symm
    refine ⟨V, homOfLE hVle, ?_, hxV⟩
    rw [Sieve.functorPullback_apply, Presieve.functorPullback_mem, hqa]
    exact R.downward_closed hr a

/-- The inclusion of the small Zariski site of a scheme into its big Zariski site is full:
a morphism over `S` between two open subschemes of `S` is the inclusion of one open in the
other. -/
public instance restrictFunctor_full (S : Scheme.{u}) :
    (S.restrictFunctor).Full where
  map_surjective := by
    intro U V f
    have hw : f.left ≫ V.ι = U.ι := by
      simpa [Scheme.restrictFunctor] using Over.w f
    have hset : Set.range U.ι ⊆ Set.range V.ι := by
      rintro x ⟨y, rfl⟩
      exact ⟨f.left y, congrArg (fun q => q y) hw⟩
    have hle : U ≤ V := by
      have hsub : (U.ι.opensRange : Set S) ⊆ V.ι.opensRange := by
        simpa only [← Scheme.Hom.coe_opensRange] using hset
      simpa only [Scheme.Opens.opensRange_ι] using SetLike.coe_subset_coe.mp hsub
    refine ⟨homOfLE hle, ?_⟩
    apply Over.OverMorphism.ext
    change S.homOfLE hle = f.left
    apply (cancel_mono V.ι).1
    rw [S.homOfLE_ι hle]
    exact hw.symm

/-- Restriction of a big Zariski sheaf of abelian groups to the small Zariski site admits a
left adjoint, namely extension. -/
public instance restrictFunctor_sheafPushforward_isRightAdjoint
    (S : Scheme.{u}) :
    ((S.restrictFunctor).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
      (Opens.grothendieckTopology S) (Scheme.zariskiTopology.over S)).IsRightAdjoint :=
  by
    have : HasSheafify (Scheme.zariskiTopology.over S)
        AddCommGrpCat.{max (u + 1) v} := by
      have : EssentiallySmall.{max (u + 1) v} (Over S) := inferInstance
      have : HasSheafify ((equivSmallModel.{max (u + 1) v} (Over S)).inverse.inducedTopology
          (Scheme.zariskiTopology.over S)) AddCommGrpCat.{max (u + 1) v} := inferInstance
      exact hasSheafifyEssentiallySmallSite _ _
    infer_instance

/-- The adjunction between extension from, and restriction to, the small Zariski
site of a scheme. -/
public abbrev adjunction (S : Scheme.{u}) :=
  (S.restrictFunctor).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
    (Opens.grothendieckTopology S) (Scheme.zariskiTopology.over S)

/-- The extension of an abelian sheaf from the small Zariski site of `S` to the
big Zariski site of `S`, along the inclusion of the open subschemes. -/
public abbrev extension (S : Scheme.{u})
    (F : Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{max (u + 1) v}) :
    Sheaf (Scheme.zariskiTopology.over S) AddCommGrpCat.{max (u + 1) v} :=
  ((S.restrictFunctor).sheafPullback AddCommGrpCat.{max (u + 1) v}
    (Opens.grothendieckTopology S) (Scheme.zariskiTopology.over S)).obj F

section SheafComparison
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {A : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} A]
  (a : C ⥤ D) (i : C ⥤ E) (j : D ⥤ E)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (L : GrothendieckTopology E)
  [a.IsContinuous J K] [i.IsContinuous J L] [j.IsContinuous K L]
  [j.IsCocontinuous K L]
  [HasWeakSheafify K A] [HasWeakSheafify L A]
  [∀ F : Cᵒᵖ ⥤ A, a.op.HasLeftKanExtension F]
  [∀ F : Cᵒᵖ ⥤ A, i.op.HasPointwiseLeftKanExtension F]
  [∀ F : Dᵒᵖ ⥤ A, j.op.HasPointwiseRightKanExtension F]
  (w : a ⋙ j ⟶ i)
  [hw : (TwoSquare.mk (𝟭 Cᵒᵖ) a.op i.op j.op (NatTrans.op w)).GuitartExact]

/-- Base change for sheaf pullback: if `w : a ⋙ j ⟶ i` is a natural transformation of
continuous functors of sites whose associated square is Guitart exact and `j` is moreover
cocontinuous, then pullback along `a` is pullback along `i` followed by pushforward along
`j`. -/
public def sheafComparisonIso :
    a.sheafPullback A J K ≅ i.sheafPullback A J L ⋙ j.sheafPushforwardContinuous A K L := by
  let q := TwoSquare.mk (𝟭 Cᵒᵖ) a.op i.op j.op (NatTrans.op w)
  let b := asIso (q.lanBaseChange (D := A))
  let t := j.pushforwardContinuousSheafificationCompatibility A K L
  let ai := Functor.sheafPullbackConstruction.sheafPullbackIso a A J K
  let ii := Functor.sheafPullbackConstruction.sheafPullbackIso i A J L
  refine ai ≪≫ ?_ ≪≫ Functor.isoWhiskerRight ii.symm _
  exact Functor.isoWhiskerLeft (sheafToPresheaf J A)
    (Functor.isoWhiskerRight b (presheafToSheaf K A) ≪≫ Functor.isoWhiskerLeft i.op.lan t)

-- The two lemmas below compare the abstract sheaf pullback with the one built from a left Kan
-- extension. Recognising those two functors as adjoint to the same pushforward, and reading a
-- section of a pushforward as a section over the image open, both need the definitions of the
-- constructed pullback and of the pushforward at `implicit` transparency.
attribute [local implicit_reducible]
  Functor.sheafPullbackConstruction.sheafPullback Functor.sheafPushforwardContinuous

/-- The unit of the sheaf adjunction attached to a continuous functor agrees, after the
comparison with the Kan-extension construction of the pullback, with the unit of the left Kan
extension followed by sheafification. -/
public lemma sheafPullbackIso_unit (F : Sheaf J A) (U : Cᵒᵖ) :
    ((a.sheafAdjunctionContinuous A J K).unit.app F).hom.app U ≫
      ((Functor.sheafPullbackConstruction.sheafPullbackIso a A J K).hom.app F).hom.app
        (Opposite.op (a.obj U.unop)) =
    (a.op.lanUnit.app F.obj).app U ≫
      (toSheafify K (a.op.lan.obj F.obj)).app (Opposite.op (a.obj U.unop)) := by
  have h := congrArg (fun f => f.hom.app U)
    (Adjunction.unit_leftAdjointUniq_hom_app (a.sheafAdjunctionContinuous A J K)
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous a A J K) F)
  trans ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous a A J K).unit.app
    F).hom.app U
  · exact h
  change ((sheafToPresheaf J A).map
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous a A J K).unit.app F)).app U = _
  delta Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
  rw [Adjunction.map_restrictFullyFaithful_unit_app]
  simp [Adjunction.comp_unit_app]

/-- The base change isomorphism for sheaf pullback is compatible with the units of the two
adjunctions, up to the restriction map along `w`. -/
public lemma sheafComparisonIso_unit (F : Sheaf J A) (U : Cᵒᵖ) :
    ((a.sheafAdjunctionContinuous A J K).unit.app F).hom.app U ≫
      ((sheafComparisonIso a i j J K L w).hom.app F).hom.app (a.op.obj U) =
    ((i.sheafAdjunctionContinuous A J L).unit.app F).hom.app U ≫
      ((i.sheafPullback A J L).obj F).obj.map (w.app U.unop).op := by
  let q := TwoSquare.mk (𝟭 Cᵒᵖ) a.op i.op j.op (NatTrans.op w)
  let b := q.lanBaseChange.app F.obj
  have hn := congrArg (fun f => f.app (a.op.obj U)) (toSheafify_naturality (J := K) b)
  have ht := congrArg (fun f => f.app (a.op.obj U))
    (j.toSheafify_pullbackSheafificationCompatibility A K L (i.op.lan.obj F.obj))
  dsimp only [NatTrans.comp_app, Functor.op_obj, Functor.comp_obj, Functor.id_obj,
    Functor.whiskeringLeft_obj_obj, Functor.id_comp, Functor.whiskerLeft_app] at hn ht
  dsimp [sheafComparisonIso]
  simp only [Category.assoc]
  rw [reassoc_of% (sheafPullbackIso_unit (A := A) a J K F U), reassoc_of% hn.symm,
    reassoc_of% ht]
  have hb := congrArg (fun f => f.app U)
    ((a.op.lanAdjunction A).homEquiv _ _ |>.apply_symm_apply
      ((Functor.LeftExtension.mk _ (i.op.lanUnit.app F.obj)).compTwoSquare q).hom)
  simp only [Adjunction.homEquiv_unit] at hb
  dsimp [Functor.LeftExtension.compTwoSquare, q] at hb
  have hb' : (a.op.lanUnit.app F.obj).app U ≫ b.app (Opposite.op (a.obj U.unop)) =
      (i.op.lanUnit.app F.obj).app U ≫ (i.op.lan.obj F.obj).map (w.app U.unop).op := by
    simpa [b, q, TwoSquare.lanBaseChange, Functor.LeftExtension.compTwoSquare,
      Functor.lanAdjunction_unit, Functor.id_comp] using hb
  rw [reassoc_of% hb',
    reassoc_of% (toSheafify L (i.op.lan.obj F.obj)).naturality (w.app U.unop).op]
  set ii := Functor.sheafPullbackConstruction.sheafPullbackIso i A J L
  have hninv : (sheafify L (i.op.lan.obj F.obj)).map (w.app U.unop).op ≫
      ((j.sheafPushforwardContinuous A K L).map (ii.inv.app F)).hom.app
        (Opposite.op (a.obj U.unop)) =
      (ii.inv.app F).hom.app (Opposite.op (i.obj U.unop)) ≫
        ((i.sheafPullback A J L).obj F).obj.map (w.app U.unop).op :=
    (ii.inv.app F).hom.naturality _
  rw [hninv, ← reassoc_of% (sheafPullbackIso_unit (A := A) i J L F U)]
  have hi : ((ii.hom.app F).hom.app (Opposite.op (i.obj U.unop))) ≫
      ((ii.inv.app F).hom.app (Opposite.op (i.obj U.unop))) = 𝟙 _ :=
    congrArg (fun f => f.hom.app (Opposite.op (i.obj U.unop))) (ii.hom_inv_id_app F)
  rw [reassoc_of% hi]

end SheafComparison

/-- The opens of a scheme `T` over `S`, viewed as schemes over `S`: the inclusion of the small
Zariski site of `T` into the big Zariski site of `S`. -/
public abbrev relativeOpens (S : Scheme.{u}) (T : Over S) :=
  T.left.restrictFunctor ⋙ Over.map T.hom

/-- Viewing the opens of a scheme over `S` as schemes over `S` is continuous. -/
public theorem relativeOpens_isContinuous (S : Scheme.{u}) (T : Over S) :
    (relativeOpens S T).IsContinuous (Opens.grothendieckTopology T.left)
      (Scheme.zariskiTopology.over S) :=
  Functor.isContinuous_comp _ _ _ (Scheme.zariskiTopology.over T.left) _

attribute [local instance] relativeOpens_isContinuous

/-- Viewing the opens of a scheme over `S` as schemes over `S` is cocontinuous. -/
public theorem relativeOpens_isCocontinuous (S : Scheme.{u}) (T : Over S) :
    (relativeOpens S T).IsCocontinuous (Opens.grothendieckTopology T.left)
      (Scheme.zariskiTopology.over S) :=
  isCocontinuous_comp T.left.restrictFunctor (Over.map T.hom)
    (Opens.grothendieckTopology T.left) (Scheme.zariskiTopology.over T.left)

attribute [local instance] relativeOpens_isCocontinuous

/-- Inverse image of opens along the structure morphism of a scheme `T` over `S`. -/
public abbrev inverseImageOpens (S : Scheme.{u}) (T : Over S) :=
  Opens.map (Scheme.forgetToTop.map T.hom)

-- `AlgebraicGeometry.Scheme.restrictFunctor` sends an open to its open subscheme. The
-- naturality squares below have to be recognised as composable at `implicit` transparency, and
-- that identification of the underlying scheme is exactly what it takes.
attribute [local implicit_reducible] Scheme.restrictFunctor

/-- The inverse image of an open along the continuous map underlying a morphism of schemes is
its scheme-theoretic preimage: `TopologicalSpace.Opens.map (Scheme.forgetToTop.map f)` and
`f ⁻¹ᵁ ·` are the same operation. Phrasing the comparison as a lemma gives the bound required
by `AlgebraicGeometry.Scheme.Hom.resLE` a type that needs no unfolding of
`AlgebraicGeometry.Scheme.forgetToTop`. -/
public lemma map_forgetToTop_obj_le_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Opens Y) :
    (Opens.map (Scheme.forgetToTop.map f)).obj V ≤ f ⁻¹ᵁ V := le_rfl

/-- For an open `U ⊆ S` the open subscheme `T ×_S U = (T.hom ⁻¹ᵁ U)` of `T` maps to `U`, and
these maps compare the two legs out of the opens of `S`. -/
public def relativeOpensMap (S : Scheme.{u}) (T : Over S) :
    inverseImageOpens S T ⋙ relativeOpens S T ⟶ S.restrictFunctor where
  app U := Over.homMk (T.hom.resLE U _ (map_forgetToTop_obj_le_preimage T.hom U))
    (T.hom.resLE_comp_ι (map_forgetToTop_obj_le_preimage T.hom U))
  naturality {U V} f := by
    apply Over.OverMorphism.ext
    apply (cancel_mono (Scheme.Opens.ι (X := S) V)).1
    simp [relativeOpens, Over.homMk_left, Scheme.Hom.resLE_comp_ι]

/-- An open `V ⊆ T` that admits a morphism over `S` to an open `U ⊆ S` is contained in the
inverse image of `U`. -/
public lemma le_inverseImage_of_hom (S : Scheme.{u}) (T : Over S)
    (V : Opens T.left) (U : Opens S)
    (f : (relativeOpens S T).obj V ⟶ S.restrictFunctor.obj U) :
    V ≤ (inverseImageOpens S T).obj U := by
  intro x hx
  have h := congrArg (fun q : (Scheme.Opens.toScheme (X := T.left) V) ⟶ S => q ⟨x, hx⟩) (Over.w f)
  change (Scheme.Opens.ι (X := S) U) (f.left ⟨x, hx⟩) = T.hom x at h
  change T.hom x ∈ U
  rw [← h]
  exact (f.left ⟨x, hx⟩).property

/-- The square of opposite categories comparing inverse image of opens along `T ⟶ S` with the
two inclusions of small Zariski sites into the big Zariski site of `S`. -/
public def relativeOpensSquare (S : Scheme.{u}) (T : Over S) :
    TwoSquare (𝟭 (Opens S)ᵒᵖ) (inverseImageOpens S T).op
      S.restrictFunctor.op (relativeOpens S T).op :=
  TwoSquare.mk _ _ _ _ (NatTrans.op (relativeOpensMap S T))

/-- Two morphisms over `S` into an open subscheme of `S` are equal. -/
private theorem over_hom_ext_restrictFunctor {S : Scheme.{u}} {A : Over S} {U : Opens S}
    (f g : A ⟶ S.restrictFunctor.obj U) : f = g := by
  apply Over.OverMorphism.ext
  apply (cancel_mono (Scheme.Opens.ι (X := S) U)).1
  exact (Over.w f).trans (Over.w g).symm

/-- The comparison square for inverse image of opens is Guitart exact: for an open `V ⊆ T` the
opens `U ⊆ S` with a morphism `V ⟶ U` over `S` are exactly the opens with
`V ≤ T.hom ⁻¹ᵁ U`. -/
public theorem relativeOpensSquare_exact (S : Scheme.{u}) (T : Over S) :
    (relativeOpensSquare S T).GuitartExact := by
  rw [TwoSquare.guitartExact_iff_final]
  intro V
  let K := (relativeOpensSquare S T).costructuredArrowRightwards V
  have : K.Full := ⟨fun f => by
    refine ⟨CostructuredArrow.homMk f.left ?_, ?_⟩
    · apply Subsingleton.elim
    · apply CostructuredArrow.hom_ext
      rfl⟩
  have : K.Faithful := ⟨fun h => CostructuredArrow.hom_ext _ _ (congrArg (·.left) h)⟩
  have : K.EssSurj := ⟨fun U => by
    let h := le_inverseImage_of_hom S T V.unop U.left.unop U.hom.unop
    refine ⟨CostructuredArrow.mk (homOfLE h).op, ⟨CostructuredArrow.isoMk
      (Iso.refl _) ?_⟩⟩
    exact Quiver.Hom.unop_inj (over_hom_ext_restrictFunctor _ _)⟩
  have : K.IsEquivalence := {}
  change K.Final
  infer_instance

attribute [local instance] relativeOpensSquare_exact

/-- Abelian sheaves on the big Zariski site of a scheme can be sheafified at the coefficient
universe `max (u + 1) v`. -/
public theorem hasSheafify_bigZariski (S : Scheme.{u}) :
    HasSheafify (Scheme.zariskiTopology.over S) AddCommGrpCat.{max (u + 1) v} := by
  have : EssentiallySmall.{max (u + 1) v} (Over S) := inferInstance
  have : HasSheafify ((equivSmallModel.{max (u + 1) v} (Over S)).inverse.inducedTopology
      (Scheme.zariskiTopology.over S)) AddCommGrpCat.{max (u + 1) v} := inferInstance
  exact hasSheafifyEssentiallySmallSite _ _

attribute [local instance] hasSheafify_bigZariski

-- Reading a section of a pushforward as a section over the image open needs the definition of
-- `CategoryTheory.Functor.sheafPushforwardContinuous` at `implicit` transparency. The abstract
-- sheaf pullback, on the other hand, must not be unfolded at all: it is a `Classical.choose` of
-- a left adjoint, so unification that descends into it reduces the whole sheafification
-- construction — tens of thousands of unfoldings — and never learns anything, because two
-- differently spelled pullbacks are compared through their adjunctions, not their values.
attribute [local implicit_reducible] Functor.sheafPushforwardContinuous
attribute [local irreducible] Functor.sheafPullback
  Functor.sheafPullbackConstruction.sheafPullback

/-- Extension to the big Zariski site of `S`, then restriction to the opens of a scheme `T`
over `S`, is the inverse image of sheaves along the structure morphism of `T`. -/
public def extensionRestrictionIso (S : Scheme.{u}) (T : Over S) :
    (inverseImageOpens S T).sheafPullback AddCommGrpCat.{max (u + 1) v}
      (Opens.grothendieckTopology S) (Opens.grothendieckTopology T.left) ≅
    S.restrictFunctor.sheafPullback AddCommGrpCat.{max (u + 1) v}
      (Opens.grothendieckTopology S) (Scheme.zariskiTopology.over S) ⋙
    (relativeOpens S T).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
      (Opens.grothendieckTopology T.left) (Scheme.zariskiTopology.over S) := by
  have := restrictFunctor_isContinuous S
  have := relativeOpens_isContinuous S T
  have := relativeOpens_isCocontinuous S T
  have : (TwoSquare.mk (𝟭 (Opens S)ᵒᵖ) (inverseImageOpens S T).op
      S.restrictFunctor.op (relativeOpens S T).op
      (NatTrans.op (relativeOpensMap S T))).GuitartExact :=
    relativeOpensSquare_exact S T
  exact sheafComparisonIso (A := AddCommGrpCat.{max (u + 1) v}) (inverseImageOpens S T)
    S.restrictFunctor (relativeOpens S T)
    (Opens.grothendieckTopology S) (Opens.grothendieckTopology T.left)
    (Scheme.zariskiTopology.over S) (relativeOpensMap S T)

/-- The whole of a scheme `T` over `S`, viewed as an open of `T` over `S`, is `T` itself. -/
public def relativeOpensTopIso (S : Scheme.{u}) (T : Over S) :
    (relativeOpens S T).obj ⊤ ≅ T :=
  Over.isoMk T.left.topIso

/-- The identification of the restricted extension with the inverse image is compatible with
the units of the two adjunctions. -/
public lemma extensionRestrictionIso_unit (S : Scheme.{u}) (T : Over S)
    (F : Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{max (u + 1) v})
    (U : (Opens S)ᵒᵖ) :
    (((inverseImageOpens S T).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
      (Opens.grothendieckTopology S)
      (Opens.grothendieckTopology T.left)).unit.app F).hom.app U ≫
        ((extensionRestrictionIso S T).hom.app F).hom.app
          ((inverseImageOpens S T).op.obj U) =
    ((adjunction S).unit.app F).hom.app U ≫
      (extension S F).obj.map ((relativeOpensMap S T).app U.unop).op := by
  have := restrictFunctor_isContinuous S
  have := relativeOpens_isContinuous S T
  have := relativeOpens_isCocontinuous S T
  have : (TwoSquare.mk (𝟭 (Opens S)ᵒᵖ) (inverseImageOpens S T).op
      S.restrictFunctor.op (relativeOpens S T).op
      (NatTrans.op (relativeOpensMap S T))).GuitartExact :=
    relativeOpensSquare_exact S T
  exact sheafComparisonIso_unit (inverseImageOpens S T) S.restrictFunctor (relativeOpens S T)
    (Opens.grothendieckTopology S) (Opens.grothendieckTopology T.left)
    (Scheme.zariskiTopology.over S) (relativeOpensMap S T) F U

/-- The value of the small-to-big Zariski extension on a scheme `T` over `S`
is the global sections on `T` of the inverse image of the sheaf along its
structure morphism. -/
@[stacks 03FI "case (c), geometric extension formula"]
public def extension_sections (S : Scheme.{u}) (T : Over S) :
    ((S.restrictFunctor).sheafPullback AddCommGrpCat.{max (u + 1) v}
        (Opens.grothendieckTopology S) (Scheme.zariskiTopology.over S)) ⋙
      (sheafSections (Scheme.zariskiTopology.over S)
        AddCommGrpCat.{max (u + 1) v}).obj (Opposite.op T) ≅
    ((Opens.map (Scheme.forgetToTop.map T.hom)).sheafPullback
        AddCommGrpCat.{max (u + 1) v}
        (Opens.grothendieckTopology S)
        (Opens.grothendieckTopology T.left)) ⋙
      Sheaf.Γ (Opens.grothendieckTopology T.left)
        AddCommGrpCat.{max (u + 1) v} := by
  let A := AddCommGrpCat.{max (u + 1) v}
  let i := S.restrictFunctor.sheafPullback A
    (Opens.grothendieckTopology S) (Scheme.zariskiTopology.over S)
  let a := (inverseImageOpens S T).sheafPullback A
    (Opens.grothendieckTopology S) (Opens.grothendieckTopology T.left)
  exact Functor.isoWhiskerLeft i
      ((sheafSections (Scheme.zariskiTopology.over S) A).mapIso
        (relativeOpensTopIso S T).op) ≪≫
    Functor.isoWhiskerRight (extensionRestrictionIso S T).symm
      ((sheafSections (Opens.grothendieckTopology T.left) A).obj (Opposite.op ⊤)) ≪≫
    Functor.isoWhiskerLeft a
      (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology T.left) A
        (isTerminalTop : IsTerminal (⊤ : Opens T.left))).symm

/-- For a morphism `g : T' ⟶ T` over `S`, restriction of an open `V ⊆ T` to `g ⁻¹ᵁ V ⊆ T'`,
as a morphism of schemes over `S`. -/
public def relativeOpensTransition (S : Scheme.{u}) {T T' : Over S} (g : T' ⟶ T) :
    Opens.map (Scheme.forgetToTop.map g.left) ⋙ relativeOpens S T' ⟶ relativeOpens S T where
  app V := Over.homMk (g.left.resLE V _ (map_forgetToTop_obj_le_preimage g.left V)) (by
    dsimp [relativeOpens]
    simp only [Scheme.restrictFunctor_obj_hom]
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Over.w])
  naturality {V W} f := by
    apply Over.OverMorphism.ext
    dsimp [relativeOpens]
    apply (cancel_mono (Scheme.Opens.ι (X := T.left) W)).1
    simp [Scheme.Hom.resLE_comp_ι]

/-- The restriction map along `g : T' ⟶ T` between the direct images on the opens of `T` and
of `T'` of a sheaf on the big Zariski site of `S`. -/
public def relativeRestrictionMap (S : Scheme.{u}) {T T' : Over S} (g : T' ⟶ T)
    (F : Sheaf (Scheme.zariskiTopology.over S) AddCommGrpCat.{max (u + 1) v}) :
    ((relativeOpens S T).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
      (Opens.grothendieckTopology T.left) (Scheme.zariskiTopology.over S)).obj F ⟶
    ((Opens.map (Scheme.forgetToTop.map g.left)).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (Opens.grothendieckTopology T.left)
      (Opens.grothendieckTopology T'.left)).obj
      (((relativeOpens S T').sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
        (Opens.grothendieckTopology T'.left) (Scheme.zariskiTopology.over S)).obj F) :=
  ⟨Functor.whiskerRight (NatTrans.op (relativeOpensTransition S g)) F.obj⟩

/-- The canonical map from the inverse image of a sheaf on the opens of `S` along `T ⟶ S` to
the direct image along `g : T' ⟶ T` of its inverse image along `T' ⟶ S`. -/
public def inverseImageSheafMap (S : Scheme.{u}) {T T' : Over S} (g : T' ⟶ T)
    (F : Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{max (u + 1) v}) :
    ((inverseImageOpens S T).sheafPullback AddCommGrpCat.{max (u + 1) v}
      (Opens.grothendieckTopology S) (Opens.grothendieckTopology T.left)).obj F ⟶
    ((Opens.map (Scheme.forgetToTop.map g.left)).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (Opens.grothendieckTopology T.left)
      (Opens.grothendieckTopology T'.left)).obj
      (((inverseImageOpens S T').sheafPullback AddCommGrpCat.{max (u + 1) v}
        (Opens.grothendieckTopology S) (Opens.grothendieckTopology T'.left)).obj F) := by
  let a := Opens.map (Scheme.forgetToTop.map T.hom)
  let b := Opens.map (Scheme.forgetToTop.map g.left)
  let c := Opens.map (Scheme.forgetToTop.map T'.hom)
  let e : a ⋙ b ≅ c := eqToIso (by
    dsimp [a, b, c]
    rw [← Opens.map_comp_eq, ← Functor.map_comp, Over.w g])
  exact ((a.sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
    (Opens.grothendieckTopology S)
    (Opens.grothendieckTopology T.left)).homEquiv _ _).symm
      (((c.sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
        (Opens.grothendieckTopology S)
        (Opens.grothendieckTopology T'.left)).unit.app F) ≫
        (Functor.sheafPushforwardContinuousComp' e
          AddCommGrpCat.{max (u + 1) v}
          (Opens.grothendieckTopology S)
          (Opens.grothendieckTopology T.left)
          (Opens.grothendieckTopology T'.left)).inv.app _)

/-- Restricting opens along the structure morphism of `T` and then along `g : T' ⟶ T` is
restricting opens along the structure morphism of `T'`, because `g` is a morphism over `S`. -/
public def inverseImageOpensComp (S : Scheme.{u}) {T T' : Over S} (g : T' ⟶ T) :
    inverseImageOpens S T ⋙ Opens.map (Scheme.forgetToTop.map g.left) ≅
      inverseImageOpens S T' :=
  eqToIso (by
    dsimp [inverseImageOpens]
    rw [← Opens.map_comp_eq, ← Functor.map_comp, Over.w g])

/-- The naturality of the identification of the restricted extension with the inverse image,
evaluated at an open `U ⊆ S`: restricting a section of the extension to the opens of `T` and
then along `g` is the same as restricting it to the opens of `T'` and transporting along the
comparison `AlgebraicGeometry.SmallZariski.inverseImageOpensComp` of the two inverse images.
This is the pointwise content of
`AlgebraicGeometry.SmallZariski.extensionRestrictionIso_naturality`; it is stated separately
because both it and the reduction of the adjoint identity to it are large elaborations. -/
public lemma extensionRestrictionIso_naturality_app (S : Scheme.{u}) {T T' : Over S}
    (g : T' ⟶ T)
    (F : Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{max (u + 1) v})
    (U : (Opens S)ᵒᵖ) :
    ((adjunction S).unit.app F).hom.app U ≫
      (extension S F).obj.map ((relativeOpensMap S T).app U.unop).op ≫
      (extension S F).obj.map
        ((relativeOpensTransition S g).app ((inverseImageOpens S T).obj U.unop)).op =
    (((inverseImageOpens S T').sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
      (Opens.grothendieckTopology S)
      (Opens.grothendieckTopology T'.left)).unit.app F).hom.app U ≫
      (((inverseImageOpens S T').sheafPullback AddCommGrpCat.{max (u + 1) v}
        (Opens.grothendieckTopology S) (Opens.grothendieckTopology T'.left)).obj F).obj.map
        ((inverseImageOpensComp S g).hom.app U.unop).op ≫
      ((extensionRestrictionIso S T').hom.app F).hom.app
        (Opposite.op ((inverseImageOpens S T ⋙
          Opens.map (Scheme.forgetToTop.map g.left)).obj U.unop)) := by
  refine Eq.trans ?_ (congrArg (_ ≫ ·)
    (((extensionRestrictionIso S T').hom.app F).hom.naturality
      ((inverseImageOpensComp S g).hom.app U.unop).op)).symm
  refine Eq.trans ?_ (Eq.symm ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) (extensionRestrictionIso_unit S T' F U)).trans (Category.assoc _ _ _))))
  congr 1
  change _ = (extension S F).obj.map _ ≫ (extension S F).obj.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact Quiver.Hom.unop_inj (over_hom_ext_restrictFunctor _ _)

/-- The identification of the restricted extension with the inverse image is natural in the
scheme over `S`. -/
public lemma extensionRestrictionIso_naturality (S : Scheme.{u}) {T T' : Over S}
    (g : T' ⟶ T)
    (F : Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{max (u + 1) v}) :
    (extensionRestrictionIso S T).hom.app F ≫
      relativeRestrictionMap S g (extension S F) =
    inverseImageSheafMap S g F ≫
      ((Opens.map (Scheme.forgetToTop.map g.left)).sheafPushforwardContinuous
        AddCommGrpCat.{max (u + 1) v} (Opens.grothendieckTopology T.left)
        (Opens.grothendieckTopology T'.left)).map
        ((extensionRestrictionIso S T').hom.app F) := by
  let adj := (inverseImageOpens S T).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
    (Opens.grothendieckTopology S) (Opens.grothendieckTopology T.left)
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
  change _ = adj.homEquiv _ _ (inverseImageSheafMap S g F) ≫ _
  dsimp only [inverseImageSheafMap]
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  dsimp only [Functor.comp_obj, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  refine (congrArg (· ≫ _) (extensionRestrictionIso_unit S T F U)).trans ?_
  dsimp only [Functor.id_obj, Functor.comp_obj, Functor.op_obj,
    Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousComp,
    Functor.sheafPushforwardContinuousIso, eqToIso.inv,
    Functor.sheafPushforwardContinuousNatTrans, ObjectProperty.ι_obj, eqToIso.hom, Iso.trans_inv,
    Iso.refl_inv, NatTrans.comp_app, NatTrans.id_app, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.id_hom, Functor.whiskerRight_app, NatTrans.op_app]
  simp only [Category.assoc]
  exact extensionRestrictionIso_naturality_app S g F U

/-- The canonical restriction on sections of the geometric inverse image along
`g : T' ⟶ T`, obtained from the composition comparison for inverse images and the adjunction
unit. -/
public def pullbackSectionsRestriction
    (S : Scheme.{u}) {T T' : Over S} (g : T' ⟶ T)
    (F : Sheaf (Opens.grothendieckTopology S)
      AddCommGrpCat.{max (u + 1) v}) :
    (Sheaf.Γ (Opens.grothendieckTopology T.left)
      AddCommGrpCat.{max (u + 1) v}).obj
        (((Opens.map (Scheme.forgetToTop.map T.hom)).sheafPullback
          AddCommGrpCat.{max (u + 1) v}
          (Opens.grothendieckTopology S)
          (Opens.grothendieckTopology T.left)).obj F) ⟶
    (Sheaf.Γ (Opens.grothendieckTopology T'.left)
      AddCommGrpCat.{max (u + 1) v}).obj
        (((Opens.map (Scheme.forgetToTop.map T'.hom)).sheafPullback
          AddCommGrpCat.{max (u + 1) v}
          (Opens.grothendieckTopology S)
          (Opens.grothendieckTopology T'.left)).obj F) := by
  let a := Opens.map (Scheme.forgetToTop.map T.hom)
  let b := Opens.map (Scheme.forgetToTop.map g.left)
  let c := Opens.map (Scheme.forgetToTop.map T'.hom)
  let e : a ⋙ b ≅ c := eqToIso (by
    dsimp [a, b, c]
    rw [← Opens.map_comp_eq, ← Functor.map_comp, Over.w g])
  let m := ((a.sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
    (Opens.grothendieckTopology S)
    (Opens.grothendieckTopology T.left)).homEquiv _ _).symm
      (((c.sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
        (Opens.grothendieckTopology S)
        (Opens.grothendieckTopology T'.left)).unit.app F) ≫
        (Functor.sheafPushforwardContinuousComp' e
          AddCommGrpCat.{max (u + 1) v}
          (Opens.grothendieckTopology S)
          (Opens.grothendieckTopology T.left)
          (Opens.grothendieckTopology T'.left)).inv.app _)
  exact (Sheaf.ΓNatIsoSheafSections
    (Opens.grothendieckTopology T.left) AddCommGrpCat.{max (u + 1) v}
    (isTerminalTop : IsTerminal (⊤ : Opens T.left))).hom.app _ ≫
      m.hom.app (Opposite.op (⊤ : Opens T.left)) ≫
      (Sheaf.ΓNatIsoSheafSections
        (Opens.grothendieckTopology T'.left) AddCommGrpCat.{max (u + 1) v}
        (by
          change IsTerminal (⊤ : Opens (Scheme.forgetToTop.obj T'.left))
          exact isTerminalTop :
          IsTerminal (b.obj (⊤ : Opens T.left)))).inv.app _

/-- The valuewise geometric comparison respects every morphism over `S`.
Thus the small-to-big extension is identified with the presheaf of sections
of the geometric inverse image, not merely with its values at each object. -/
@[stacks 03FI "case (c), naturality of the geometric extension"]
public theorem extension_sections_naturality
    (S : Scheme.{u}) {T T' : Over S} (g : T' ⟶ T)
    (F : Sheaf (Opens.grothendieckTopology S)
      AddCommGrpCat.{max (u + 1) v}) :
    (extension_sections.{u, v} S T).hom.app F ≫
      pullbackSectionsRestriction.{u, v} S g F =
      ((extension.{u, v} S F).obj.map g.op) ≫
        (extension_sections.{u, v} S T').hom.app F := by
  let P := extension S F
  let A := AddCommGrpCat.{max (u + 1) v}
  let eT := ((sheafSections (Opens.grothendieckTopology T.left) A).obj
    (Opposite.op (⊤ : Opens T.left))).mapIso ((extensionRestrictionIso S T).app F)
  let eT' := ((sheafSections (Opens.grothendieckTopology T'.left) A).obj
    (Opposite.op (⊤ : Opens T'.left))).mapIso ((extensionRestrictionIso S T').app F)
  let qT := (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology T.left) A
    (isTerminalTop : IsTerminal (⊤ : Opens T.left))).app
      (((inverseImageOpens S T).sheafPullback AddCommGrpCat.{max (u + 1) v}
        (Opens.grothendieckTopology S) (Opens.grothendieckTopology T.left)).obj F)
  let qT' := (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology T'.left) A
    (isTerminalTop : IsTerminal (⊤ : Opens T'.left))).app
      (((inverseImageOpens S T').sheafPullback AddCommGrpCat.{max (u + 1) v}
        (Opens.grothendieckTopology S) (Opens.grothendieckTopology T'.left)).obj F)
  -- `m` is the geometric restriction map on the sections over the whole of `T`. Its type is
  -- written out so that each composite below is the composite of two morphisms whose shared
  -- object is spelled the same way on both sides.
  let m : ((sheafSections (Opens.grothendieckTopology T.left) A).obj
        (Opposite.op (⊤ : Opens T.left))).obj
        (((inverseImageOpens S T).sheafPullback AddCommGrpCat.{max (u + 1) v}
          (Opens.grothendieckTopology S) (Opens.grothendieckTopology T.left)).obj F) ⟶
      ((sheafSections (Opens.grothendieckTopology T'.left) A).obj
        (Opposite.op (⊤ : Opens T'.left))).obj
        (((inverseImageOpens S T').sheafPullback AddCommGrpCat.{max (u + 1) v}
          (Opens.grothendieckTopology S) (Opens.grothendieckTopology T'.left)).obj F) :=
    (inverseImageSheafMap S g F).hom.app (Opposite.op (⊤ : Opens T.left))
  have hn := congrArg (fun f => f.hom.app (Opposite.op (⊤ : Opens T.left)))
    (extensionRestrictionIso_naturality S g F)
  change eT.hom ≫ P.obj.map ((relativeOpensTransition S g).app ⊤).op = m ≫ eT'.hom at hn
  have hn' : eT.inv ≫ m = P.obj.map ((relativeOpensTransition S g).app ⊤).op ≫ eT'.inv :=
    (Iso.eq_comp_inv eT').2 <| by
      rw [Category.assoc, ← hn]
      exact eT.inv_hom_id_assoc _
  change (P.obj.map (relativeOpensTopIso S T).hom.op ≫ eT.inv ≫ qT.inv) ≫
      (qT.hom ≫ m ≫ qT'.inv) =
    P.obj.map g.op ≫ P.obj.map (relativeOpensTopIso S T').hom.op ≫ eT'.inv ≫ qT'.inv
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hstep : eT.inv ≫ m ≫ qT'.inv =
      P.obj.map ((relativeOpensTransition S g).app ⊤).op ≫ eT'.inv ≫ qT'.inv :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ qT'.inv) hn').trans (Category.assoc _ _ _))
  have hgeom : (relativeOpensTransition S g).app ⊤ ≫ (relativeOpensTopIso S T).hom =
      (relativeOpensTopIso S T').hom ≫ g := by
    apply Over.OverMorphism.ext
    change (g.left.resLE ⊤ _ (map_forgetToTop_obj_le_preimage g.left ⊤)) ≫
        (Scheme.Opens.ι (X := T.left) ⊤) =
      (Scheme.Opens.ι (X := T'.left) ⊤) ≫ g.left
    exact g.left.resLE_comp_ι (map_forgetToTop_obj_le_preimage g.left ⊤)
  have hmaps : P.obj.map (relativeOpensTopIso S T).hom.op ≫
      P.obj.map ((relativeOpensTransition S g).app ⊤).op =
      P.obj.map g.op ≫ P.obj.map (relativeOpensTopIso S T').hom.op := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, hgeom]
    rfl
  exact (congrArg (P.obj.map (relativeOpensTopIso S T).hom.op ≫ ·) hstep).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ eT'.inv ≫ qT'.inv) hmaps).trans (Category.assoc _ _ _)))

/-- Restricting the extension of an abelian sheaf on the small Zariski site back
to the open subschemes returns the sheaf itself: the unit of the adjunction is an
isomorphism. This pins `AlgebraicGeometry.SmallZariski.extension` as an extension of the
given sheaf. -/
@[stacks 03FI "case (c), the extension restricts to the given sheaf"]
public theorem isIso_extension_unit (S : Scheme.{u})
    (F : Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{max (u + 1) v}) :
    IsIso ((adjunction.{u, v} S).unit.app F) := by
  infer_instance

end AlgebraicGeometry.SmallZariski

end
