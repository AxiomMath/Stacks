module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.BinaryProductRestrict
public import StacksFrontier.AlgebraicGeometry.Crystalline.SheafComparison

/-!
# Zariski descent for morphisms of the big crystalline category

Let `(p, (S, I, γ), X)` be a global crystalline situation and let `T` be an object of the big
crystalline category `CRIS(X/S)`.  The restrictions of `T` to the opens of its ambient scheme
(`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpen`) form a diagram over the lattice
of opens, with transition maps
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenLE`.  This file proves that
`Hom(-, C)` turns that diagram into a sheaf: a morphism out of `T` is determined by its
restrictions to the members of an open cover of the ambient scheme, and compatible morphisms out
of the members of an open cover glue.  Together with the factorization
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenLift` of a morphism through a
restriction of its target, this is the Zariski-descent toolkit used to reduce statements about
`CRIS(X/S)` to the affine case.

Everything is proved by descending to the two underlying schemes.  On the ambient divided power
scheme, gluing is the gluing of morphisms of schemes over an open cover
(`AlgebraicGeometry.Scheme.Cover.glueMorphisms`) together with the fact that divided power
compatibility of a morphism of schemes is a local condition on the source
(`Crystalline.DividedPowerScheme.isDPMorphism_app_of_local`); the restriction of a divided power
scheme to an open has, by construction, the sections of the original over the image, so no
comparison of ideal sheaves is needed.  On the thickened scheme, gluing is again the gluing of
morphisms of schemes, over the preimage cover.  The two glued maps commute with the immersions
because they do so on each member of the cover, and a morphism of schemes is determined by its
restrictions to an open cover.

## Main definitions

* `Crystalline.opensCover` — the open cover of a scheme by a family of opens whose supremum is the
  whole space, with `Crystalline.glueOpensMorphisms` gluing a compatible family of morphisms out
  of the members.
* `Crystalline.DividedPowerScheme.glueRestrict` — a morphism of divided power schemes glued from
  compatible morphisms out of the restrictions to the members of an open cover.
* `Crystalline.GlobalCrystallineSituation.Thickening.glueTargetHom` and
  `Crystalline.GlobalCrystallineSituation.Thickening.glueSourceHom` — the two glued components.
* `Crystalline.GlobalCrystallineSituation.Thickening.glueHom` — a morphism of `CRIS(X/S)` glued
  from compatible morphisms out of the restrictions of its source to the members of an open cover
  of the ambient scheme.

## Main results

* `Crystalline.scheme_hom_ext_of_iSup_eq_top` — a morphism of schemes is determined by its
  restrictions to a family of opens covering the source.
* `Crystalline.DividedPowerScheme.isDPMorphism_app_of_local` — divided power compatibility of a
  morphism of schemes on an open of the target is a local condition on the source.
* `Crystalline.DividedPowerScheme.compatible_of_iSup_eq_top` — a morphism of schemes which is a
  morphism of divided power schemes on the restrictions to a family of opens covering the source
  is one.
* `Crystalline.GlobalCrystallineSituation.Thickening.hom_ext_of_iSup_eq_top` — two morphisms out
  of `T` which agree on the restrictions of `T` to the members of an open cover of its ambient
  scheme are equal.
* `Crystalline.GlobalCrystallineSituation.Thickening.glueHom_restrictOpenHom` — the glued morphism
  restricts to the given one on each member of the cover.

## What is and is not proved

What is proved is exactly Zariski descent for the presheaf `Hom(-, C)` on the restrictions of a
fixed object `T` of `CRIS(X/S)` to the opens of its ambient scheme: the separation property
(`hom_ext_of_iSup_eq_top`) and the gluing property (`glueHom`, `glueHom_restrictOpenHom`).  The
two remaining ingredients of the toolkit are *not* proved here because the library already has
them: the transition maps of the restriction diagram are
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenLE` with
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenLE_restrictOpenHom`, and the
factorization of a morphism through a restriction of its target is
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenLift` with
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenLift_restrictOpenHom`; both are
imported and both are used below.

Nothing here is a statement about sheaves on the crystalline site itself: no Grothendieck topology
is mentioned, no descent for objects is claimed, and no comparison with the covering families of
`Crystalline.GlobalCrystallineSituation.Thickening.isZariskiCovering` is made.  The index type of
a cover is arbitrary; the covers are by opens of the *ambient* scheme of `T`, and the
corresponding cover of the thickened scheme is always the preimage cover, so no independent cover
of the thickened scheme is allowed.  Finally, the gluing hypothesis is stated on the pairwise
intersections `U i ⊓ U j` only; no higher compatibility is used or proved.

## References

* [Stacks Project, Tag 07I6](https://stacks.math.columbia.edu/tag/07I6)
* [Stacks Project, Tag 07I9](https://stacks.math.columbia.edu/tag/07I9)
* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Crystalline

/-! ### Gluing morphisms of schemes over a family of opens -/

/-- Every point lies in one member of a family of opens whose supremum is the whole space. -/
private theorem exists_mem_of_iSup_eq_top {X : Scheme.{u}} {ι : Type*} {U : ι → X.Opens}
    (hU : ⨆ i, U i = ⊤) (x : X) : ∃ i, x ∈ U i := by
  have hx : x ∈ ⨆ i, U i := by rw [hU]; trivial
  exact TopologicalSpace.Opens.mem_iSup.mp hx

/-- **The open cover of a scheme by a family of opens whose supremum is the whole space.** -/
noncomputable def opensCover {X : Scheme.{u}} {ι : Type*} (U : ι → X.Opens)
    (hU : ⨆ i, U i = ⊤) : X.OpenCover :=
  Scheme.Cover.mkOfCovers ι (fun i ↦ (U i).toScheme) (fun i ↦ (U i).ι)
    (fun x ↦ by
      have hx : x ∈ ⨆ i, U i := by rw [hU]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact ⟨i, ⟨x, hi⟩, rfl⟩)
    (fun _ ↦ inferInstance)

/-- **Agreement on the intersection of two opens is agreement on their fibre product.**  The
intersection of two opens is their fibre product over the ambient scheme,
`AlgebraicGeometry.isPullback_opens_inf`. -/
theorem pullback_condition_of_inf_opens {X Y : Scheme.{u}} {ι : Type*} (U : ι → X.Opens)
    (g : ∀ i, (U i).toScheme ⟶ Y)
    (hg : ∀ i j, X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ g i =
      X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ g j) (i j : ι) :
    pullback.fst (U i).ι (U j).ι ≫ g i = pullback.snd (U i).ι (U j).ι ≫ g j := by
  refine (cancel_epi (isPullback_opens_inf (U i) (U j)).isoPullback.hom).mp ?_
  rw [← Category.assoc, ← Category.assoc, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd]
  exact hg i j

/-- **A family of morphisms out of a family of opens covering a scheme, agreeing on the pairwise
intersections, glues to a morphism out of the scheme.** -/
noncomputable def glueOpensMorphisms {X Y : Scheme.{u}} {ι : Type*} (U : ι → X.Opens)
    (hU : ⨆ i, U i = ⊤) (g : ∀ i, (U i).toScheme ⟶ Y)
    (hg : ∀ i j, X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ g i =
      X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ g j) : X ⟶ Y :=
  (opensCover U hU).glueMorphisms g (fun i j ↦ pullback_condition_of_inf_opens U g hg i j)

/-- The glued morphism restricts to the given one on each member of the cover. -/
@[reassoc (attr := simp)]
theorem ι_glueOpensMorphisms {X Y : Scheme.{u}} {ι : Type*} (U : ι → X.Opens)
    (hU : ⨆ i, U i = ⊤) (g : ∀ i, (U i).toScheme ⟶ Y)
    (hg : ∀ i j, X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ g i =
      X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ g j) (i : ι) :
    (U i).ι ≫ glueOpensMorphisms U hU g hg = g i :=
  (opensCover U hU).ι_glueMorphisms _ _ i

/-- **A morphism of schemes is determined by its restrictions to a family of opens covering the
source.** -/
theorem scheme_hom_ext_of_iSup_eq_top {X Y : Scheme.{u}} {ι : Type*} (U : ι → X.Opens)
    (hU : ⨆ i, U i = ⊤) {a b : X ⟶ Y} (h : ∀ i, (U i).ι ≫ a = (U i).ι ≫ b) : a = b :=
  (opensCover U hU).hom_ext a b h

namespace DividedPowerScheme

/-! ### Gluing morphisms of divided power schemes over a family of opens -/

/-- **Divided power compatibility of a morphism of schemes over an open of the target is a local
condition on the source.**  Membership in the quasi-coherent ideal sheaf of the source is local,
and two sections of the source agreeing locally agree. -/
theorem isDPMorphism_app_of_local (X Y : DividedPowerScheme.{u}) (f : X.scheme ⟶ Y.scheme)
    (U : Y.scheme.Opens)
    (hlocal : ∀ x : X.scheme, x ∈ f ⁻¹ᵁ U → ∃ V, ∃ hV : V ≤ f ⁻¹ᵁ U, x ∈ V ∧
      DividedPowers.IsDPMorphism (Y.dividedPowers.dividedPowers (op U))
        (X.dividedPowers.dividedPowers (op V)) (f.appLE U V hV).hom) :
    DividedPowers.IsDPMorphism (Y.dividedPowers.dividedPowers (op U))
      (X.dividedPowers.dividedPowers (op (f ⁻¹ᵁ U))) (f.app U).hom := by
  have hmem (a : Γ(Y.scheme, U)) (ha : a ∈ Y.ideal.obj (op U)) :
      f.app U a ∈ X.ideal.obj (op (f ⁻¹ᵁ U)) := by
    refine X.ideal.isSheaf _ fun x hx ↦ ?_
    obtain ⟨V, hV, hxV, hdp⟩ := hlocal x hx
    exact ⟨V, homOfLE hV, hdp.ideal_comp (Ideal.mem_map_of_mem _ ha), hxV⟩
  refine ⟨Ideal.map_le_iff_le_comap.mpr hmem, fun a ha ↦
    TopCat.Presheaf.IsSheaf.section_ext X.scheme.sheaf.property fun x hx ↦ ?_⟩
  obtain ⟨V, hV, hxV, hdp⟩ := hlocal x hx
  exact ⟨V, hV, hxV,
    ((X.dividedPowers.naturality (homOfLE hV).op).map_dpow (hmem a ha)).trans
      (hdp.map_dpow ha).symm⟩

/-- **A morphism of schemes which is a morphism of divided power schemes on the restrictions to a
family of opens covering the source is one.**  Divided power compatibility is local on the source,
`Crystalline.DividedPowerScheme.isDPMorphism_app_of_local`, and the restriction of the source to a
member of the cover has the divided power ideal of the source over the image. -/
theorem compatible_of_iSup_eq_top {X Y : DividedPowerScheme.{u}} (f : X.scheme ⟶ Y.scheme)
    {ι : Type*} (U : ι → X.scheme.Opens) (hU : ⨆ i, U i = ⊤)
    (k : ∀ i, X.restrict (U i) ⟶ Y) (hk : ∀ i, (U i).ι ≫ f = (k i).hom)
    (W : Y.scheme.Opens) :
    DividedPowers.IsDPMorphism (Y.dividedPowers.dividedPowers (op W))
      (X.dividedPowers.dividedPowers (op (f ⁻¹ᵁ W))) (f.app W).hom := by
  refine isDPMorphism_app_of_local X Y f W fun x hx ↦ ?_
  obtain ⟨i, hi⟩ := exists_mem_of_iSup_eq_top hU x
  have hV : (U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ (f ⁻¹ᵁ W)) ≤ f ⁻¹ᵁ W := by
    rintro _ ⟨y, hy, rfl⟩
    exact hy
  refine ⟨(U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ (f ⁻¹ᵁ W)), hV, ⟨⟨x, hi⟩, hx, rfl⟩, ?_⟩
  have H := (k i).compatible W
  rwa [← hk i] at H

/-- The compatibility of a family of morphisms out of the restrictions to a family of opens, read
on the underlying morphisms of schemes. -/
theorem homOfLE_comp_hom_of_restrictLE {X Y : DividedPowerScheme.{u}} {ι : Type*}
    {U : ι → X.scheme.Opens} {k : ∀ i, X.restrict (U i) ⟶ Y}
    (hk : ∀ i j, X.restrictLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ k i =
      X.restrictLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ k j) (i j : ι) :
    X.scheme.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ (k i).hom =
      X.scheme.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ (k j).hom :=
  congrArg (fun m : X.restrict (U i ⊓ U j) ⟶ Y ↦ m.hom) (hk i j)

/-- **A family of morphisms of divided power schemes out of the restrictions to a family of opens
covering the source, agreeing on the pairwise intersections, glues.**  The underlying morphisms of
schemes glue by `Crystalline.glueOpensMorphisms`, and the glued morphism of schemes is
compatible with the divided powers by
`Crystalline.DividedPowerScheme.compatible_of_iSup_eq_top`. -/
noncomputable def glueRestrict {X Y : DividedPowerScheme.{u}} {ι : Type*}
    (U : ι → X.scheme.Opens) (hU : ⨆ i, U i = ⊤) (k : ∀ i, X.restrict (U i) ⟶ Y)
    (hk : ∀ i j, X.restrictLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ k i =
      X.restrictLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ k j) : X ⟶ Y where
  hom := glueOpensMorphisms U hU (fun i ↦ (k i).hom) (homOfLE_comp_hom_of_restrictLE hk)
  compatible W := compatible_of_iSup_eq_top _ U hU k
    (fun i ↦ ι_glueOpensMorphisms U hU (fun i ↦ (k i).hom)
      (homOfLE_comp_hom_of_restrictLE hk) i) W

/-- The underlying morphism of schemes of
`Crystalline.DividedPowerScheme.glueRestrict`. -/
@[simp]
theorem glueRestrict_hom {X Y : DividedPowerScheme.{u}} {ι : Type*}
    (U : ι → X.scheme.Opens) (hU : ⨆ i, U i = ⊤) (k : ∀ i, X.restrict (U i) ⟶ Y)
    (hk : ∀ i j, X.restrictLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ k i =
      X.restrictLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ k j) :
    (glueRestrict U hU k hk).hom =
      glueOpensMorphisms U hU (fun i ↦ (k i).hom) (homOfLE_comp_hom_of_restrictLE hk) := rfl

/-- The glued morphism of divided power schemes restricts to the given one on each member of the
cover. -/
@[reassoc]
theorem restrictι_glueRestrict {X Y : DividedPowerScheme.{u}} {ι : Type*}
    (U : ι → X.scheme.Opens) (hU : ⨆ i, U i = ⊤) (k : ∀ i, X.restrict (U i) ⟶ Y)
    (hk : ∀ i j, X.restrictLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ k i =
      X.restrictLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ k j) (i : ι) :
    X.restrictι (U i) ≫ glueRestrict U hU k hk = k i :=
  Hom.ext (ι_glueOpensMorphisms U hU (fun i ↦ (k i).hom)
    (homOfLE_comp_hom_of_restrictLE hk) i)

end DividedPowerScheme

namespace GlobalCrystallineSituation.Thickening

variable {S : GlobalCrystallineSituation.{u}}

/-! ### Separation -/

/-- **Two morphisms out of `T` which agree on the restrictions of `T` to the members of an open
cover of its ambient scheme are equal.**  A morphism of `CRIS(X/S)` is determined by its map on
ambient schemes, and a morphism of schemes by its restrictions to an open cover. -/
theorem hom_ext_of_iSup_eq_top {T C : Thickening S} {ι : Type*}
    (U : ι → T.thickening.target.scheme.Opens) (hU : ⨆ i, U i = ⊤) {h k : T ⟶ C}
    (e : ∀ i, T.restrictOpenHom (U i) ≫ h = T.restrictOpenHom (U i) ≫ k) : h = k := by
  refine hom_ext_of_targetHom (Scheme.hom_ext_of_forall _ _ fun x ↦ ?_)
  obtain ⟨i, hi⟩ := exists_mem_of_iSup_eq_top hU x
  exact ⟨U i, hi, congrArg (fun m : T.restrictOpen (U i) ⟶ C ↦ m.targetHom.hom) (e i)⟩

/-! ### Gluing -/

/-- The preimages in the thickened scheme of a family of opens covering the ambient scheme cover
the thickened scheme. -/
theorem iSup_preimage_immersion_eq_top (T : Thickening S) {ι : Type*}
    (U : ι → T.thickening.target.scheme.Opens) (hU : ⨆ i, U i = ⊤) :
    ⨆ i, T.thickening.immersion ⁻¹ᵁ U i = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, hU, Scheme.Hom.preimage_top]

/-- The gluing hypothesis read on the maps on ambient divided power schemes. -/
theorem restrictLE_comp_targetHom {T C : Thickening S} {ι : Type*}
    {U : ι → T.thickening.target.scheme.Opens} {g : ∀ i, T.restrictOpen (U i) ⟶ C}
    (hg : ∀ i j, T.restrictOpenLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ g i =
      T.restrictOpenLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ g j) (i j : ι) :
    T.thickening.target.restrictLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ (g i).targetHom =
      T.thickening.target.restrictLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ (g j).targetHom :=
  congrArg (fun m : T.restrictOpen (U i ⊓ U j) ⟶ C ↦ m.targetHom) (hg i j)

/-- The gluing hypothesis read on the maps on thickened schemes. -/
theorem homOfLE_comp_sourceHom {T C : Thickening S} {ι : Type*}
    {U : ι → T.thickening.target.scheme.Opens} {g : ∀ i, T.restrictOpen (U i) ⟶ C}
    (hg : ∀ i j, T.restrictOpenLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ g i =
      T.restrictOpenLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ g j) (i j : ι) :
    T.thickening.source.homOfLE
        (inf_le_left : T.thickening.immersion ⁻¹ᵁ U i ⊓ T.thickening.immersion ⁻¹ᵁ U j ≤
          T.thickening.immersion ⁻¹ᵁ U i) ≫ (g i).sourceHom =
      T.thickening.source.homOfLE
        (inf_le_right : T.thickening.immersion ⁻¹ᵁ U i ⊓ T.thickening.immersion ⁻¹ᵁ U j ≤
          T.thickening.immersion ⁻¹ᵁ U j) ≫ (g j).sourceHom :=
  congrArg (fun m : T.restrictOpen (U i ⊓ U j) ⟶ C ↦ m.sourceHom) (hg i j)

/-- **The glued map on ambient divided power schemes.** -/
noncomputable def glueTargetHom {T C : Thickening S} {ι : Type*}
    (U : ι → T.thickening.target.scheme.Opens) (hU : ⨆ i, U i = ⊤)
    (g : ∀ i, T.restrictOpen (U i) ⟶ C)
    (hg : ∀ i j, T.restrictOpenLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ g i =
      T.restrictOpenLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ g j) :
    T.thickening.target ⟶ C.thickening.target :=
  DividedPowerScheme.glueRestrict U hU (fun i ↦ (g i).targetHom)
    (restrictLE_comp_targetHom hg)

/-- **The glued map on thickened schemes**, obtained from the preimage cover. -/
noncomputable def glueSourceHom {T C : Thickening S} {ι : Type*}
    (U : ι → T.thickening.target.scheme.Opens) (hU : ⨆ i, U i = ⊤)
    (g : ∀ i, T.restrictOpen (U i) ⟶ C)
    (hg : ∀ i j, T.restrictOpenLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ g i =
      T.restrictOpenLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ g j) :
    T.thickening.source ⟶ C.thickening.source :=
  glueOpensMorphisms (fun i ↦ T.thickening.immersion ⁻¹ᵁ U i)
    (T.iSup_preimage_immersion_eq_top U hU) (fun i ↦ (g i).sourceHom)
    (homOfLE_comp_sourceHom hg)

/-- The glued map on ambient divided power schemes restricts to the given one on each member of
the cover. -/
theorem restrictι_glueTargetHom {T C : Thickening S} {ι : Type*}
    (U : ι → T.thickening.target.scheme.Opens) (hU : ⨆ i, U i = ⊤)
    (g : ∀ i, T.restrictOpen (U i) ⟶ C)
    (hg : ∀ i j, T.restrictOpenLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ g i =
      T.restrictOpenLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ g j) (i : ι) :
    T.thickening.target.restrictι (U i) ≫ glueTargetHom U hU g hg = (g i).targetHom :=
  DividedPowerScheme.restrictι_glueRestrict U hU (fun i ↦ (g i).targetHom)
    (restrictLE_comp_targetHom hg) i

/-- The glued map on ambient divided power schemes restricts to the given one on each member of
the cover, read on underlying schemes. -/
theorem ι_glueTargetHom_hom {T C : Thickening S} {ι : Type*}
    (U : ι → T.thickening.target.scheme.Opens) (hU : ⨆ i, U i = ⊤)
    (g : ∀ i, T.restrictOpen (U i) ⟶ C)
    (hg : ∀ i j, T.restrictOpenLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ g i =
      T.restrictOpenLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ g j) (i : ι) :
    (U i).ι ≫ (glueTargetHom U hU g hg).hom = (g i).targetHom.hom :=
  congrArg
    (fun m : T.thickening.target.restrict (U i) ⟶ C.thickening.target ↦ m.hom)
    (restrictι_glueTargetHom U hU g hg i)

/-- The glued map on thickened schemes restricts to the given one on each member of the preimage
cover. -/
theorem ι_glueSourceHom {T C : Thickening S} {ι : Type*}
    (U : ι → T.thickening.target.scheme.Opens) (hU : ⨆ i, U i = ⊤)
    (g : ∀ i, T.restrictOpen (U i) ⟶ C)
    (hg : ∀ i j, T.restrictOpenLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ g i =
      T.restrictOpenLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ g j) (i : ι) :
    (T.thickening.immersion ⁻¹ᵁ U i).ι ≫ glueSourceHom U hU g hg = (g i).sourceHom :=
  ι_glueOpensMorphisms (fun i ↦ T.thickening.immersion ⁻¹ᵁ U i)
    (T.iSup_preimage_immersion_eq_top U hU) (fun i ↦ (g i).sourceHom)
    (homOfLE_comp_sourceHom hg) i

/-- **The glued maps make the square of immersions commute**, because they do so on each member of
the cover and a morphism of schemes is determined by its restrictions to an open cover. -/
theorem glueHom_immersion_naturality {T C : Thickening S} {ι : Type*}
    (U : ι → T.thickening.target.scheme.Opens) (hU : ⨆ i, U i = ⊤)
    (g : ∀ i, T.restrictOpen (U i) ⟶ C)
    (hg : ∀ i j, T.restrictOpenLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ g i =
      T.restrictOpenLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ g j) :
    T.thickening.immersion ≫ (glueTargetHom U hU g hg).hom =
      glueSourceHom U hU g hg ≫ C.thickening.immersion := by
  refine scheme_hom_ext_of_iSup_eq_top (fun i ↦ T.thickening.immersion ⁻¹ᵁ U i)
    (T.iSup_preimage_immersion_eq_top U hU) fun i ↦ ?_
  rw [← Category.assoc, ← morphismRestrict_ι T.thickening.immersion (U i), Category.assoc,
    ι_glueTargetHom_hom, ← Category.assoc, ι_glueSourceHom]
  exact (g i).immersion_naturality

/-- **The glued map on ambient divided power schemes is a morphism over the divided power
base.** -/
theorem glueHom_base_naturality {T C : Thickening S} {ι : Type*}
    (U : ι → T.thickening.target.scheme.Opens) (hU : ⨆ i, U i = ⊤)
    (g : ∀ i, T.restrictOpen (U i) ⟶ C)
    (hg : ∀ i j, T.restrictOpenLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ g i =
      T.restrictOpenLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ g j) :
    glueTargetHom U hU g hg ≫ C.toBase = T.toBase := by
  refine DividedPowerScheme.Hom.ext (scheme_hom_ext_of_iSup_eq_top U hU fun i ↦ ?_)
  rw [DividedPowerScheme.Hom.comp_hom, ← Category.assoc, ι_glueTargetHom_hom]
  exact congrArg (fun m : T.thickening.target.restrict (U i) ⟶ S.S ↦ m.hom)
    (g i).base_naturality

/-- **The glued map on thickened schemes is a morphism over `X`.** -/
theorem glueHom_toX_naturality {T C : Thickening S} {ι : Type*}
    (U : ι → T.thickening.target.scheme.Opens) (hU : ⨆ i, U i = ⊤)
    (g : ∀ i, T.restrictOpen (U i) ⟶ C)
    (hg : ∀ i j, T.restrictOpenLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ g i =
      T.restrictOpenLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ g j) :
    glueSourceHom U hU g hg ≫ C.toX = T.toX := by
  refine scheme_hom_ext_of_iSup_eq_top (fun i ↦ T.thickening.immersion ⁻¹ᵁ U i)
    (T.iSup_preimage_immersion_eq_top U hU) fun i ↦ ?_
  rw [← Category.assoc, ι_glueSourceHom]
  exact (g i).toX_naturality

/-- **A family of morphisms out of the restrictions of `T` to the members of an open cover of its
ambient scheme, agreeing on the pairwise intersections, glues to a morphism out of `T`.**  The
maps on ambient schemes glue by `Crystalline.DividedPowerScheme.glueRestrict` and the maps on
thickened schemes by `Crystalline.glueOpensMorphisms` over the preimage cover; the two squares of
[Stacks, Tag 07I6] hold because they hold on each member of the cover. -/
noncomputable def glueHom {T C : Thickening S} {ι : Type*}
    (U : ι → T.thickening.target.scheme.Opens) (hU : ⨆ i, U i = ⊤)
    (g : ∀ i, T.restrictOpen (U i) ⟶ C)
    (hg : ∀ i j, T.restrictOpenLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ g i =
      T.restrictOpenLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ g j) : T ⟶ C where
  sourceHom := glueSourceHom U hU g hg
  targetHom := glueTargetHom U hU g hg
  immersion_naturality := glueHom_immersion_naturality U hU g hg
  base_naturality := glueHom_base_naturality U hU g hg
  toX_naturality := glueHom_toX_naturality U hU g hg

/-- The map on ambient divided power schemes of
`Crystalline.GlobalCrystallineSituation.Thickening.glueHom`. -/
@[simp]
theorem glueHom_targetHom {T C : Thickening S} {ι : Type*}
    (U : ι → T.thickening.target.scheme.Opens) (hU : ⨆ i, U i = ⊤)
    (g : ∀ i, T.restrictOpen (U i) ⟶ C)
    (hg : ∀ i j, T.restrictOpenLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ g i =
      T.restrictOpenLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ g j) :
    (glueHom U hU g hg).targetHom = glueTargetHom U hU g hg := rfl

/-- The map on thickened schemes of
`Crystalline.GlobalCrystallineSituation.Thickening.glueHom`. -/
@[simp]
theorem glueHom_sourceHom {T C : Thickening S} {ι : Type*}
    (U : ι → T.thickening.target.scheme.Opens) (hU : ⨆ i, U i = ⊤)
    (g : ∀ i, T.restrictOpen (U i) ⟶ C)
    (hg : ∀ i j, T.restrictOpenLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ g i =
      T.restrictOpenLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ g j) :
    (glueHom U hU g hg).sourceHom = glueSourceHom U hU g hg := rfl

/-- **The glued morphism restricts to the given one on each member of the cover.** -/
@[reassoc (attr := simp)]
theorem glueHom_restrictOpenHom {T C : Thickening S} {ι : Type*}
    (U : ι → T.thickening.target.scheme.Opens) (hU : ⨆ i, U i = ⊤)
    (g : ∀ i, T.restrictOpen (U i) ⟶ C)
    (hg : ∀ i j, T.restrictOpenLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ g i =
      T.restrictOpenLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ g j) (i : ι) :
    T.restrictOpenHom (U i) ≫ glueHom U hU g hg = g i :=
  hom_ext_of_targetHom
    (congrArg (fun m : T.thickening.target.restrict (U i) ⟶ C.thickening.target ↦ m.hom)
      (restrictι_glueTargetHom U hU g hg i))

end GlobalCrystallineSituation.Thickening

end Crystalline

end
