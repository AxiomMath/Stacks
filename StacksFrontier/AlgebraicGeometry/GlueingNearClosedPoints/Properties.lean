module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ChowFiniteType.ModuleSupport
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Germ
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Diagonal
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Finite
public import StacksFrontier.AlgebraicGeometry.StalkAffineNhdsLimit.Basic

/-!
# Properties of schemes glued near a point

Let `S` be a scheme, let `U ⊆ S` be a retrocompact open and let `s` be a point of `S` outside
`U`.  Separatedness, properness, finiteness and étaleness of a morphism between schemes of finite
presentation over an open neighbourhood `U'` of `U ∪ {s}` can be checked on the restriction to `U`
together with the restriction to the local scheme `Spec 𝒪_{S, s}`, after shrinking `U'` to a
smaller open which still contains `U` and `s`.  The same holds for the structure morphism of a
single scheme of finite presentation over such a neighbourhood.

## Main results

* `AlgebraicGeometry.GlueingNearPoint.exists_open_isSeparated_baseChange`,
  `AlgebraicGeometry.GlueingNearPoint.exists_open_isProper_baseChange`,
  `AlgebraicGeometry.GlueingNearPoint.exists_open_isFinite_baseChange`,
  `AlgebraicGeometry.GlueingNearPoint.exists_open_etale_baseChange`: the four properties for a
  morphism between two schemes of finite presentation over `U'`.
* `AlgebraicGeometry.GlueingNearPoint.exists_open_isSeparated`,
  `AlgebraicGeometry.GlueingNearPoint.exists_open_isProper`,
  `AlgebraicGeometry.GlueingNearPoint.exists_open_isFinite`,
  `AlgebraicGeometry.GlueingNearPoint.exists_open_etale`: the four properties for the structure
  morphism of a `AlgebraicGeometry.GlueingNearPoint.FinitePresentationNeighborhoodModel`.

## Implementation notes

A scheme over the open subscheme `U'` is an object of `CategoryTheory.Over U'.toScheme`, and it is
regarded as a scheme over `S` by the functor `CategoryTheory.Over.map U'.ι`.  Restriction to an
open `V ⊆ S`, to `Spec 𝒪_{S, s}` and to a smaller neighbourhood are all base changes along a
morphism to `S`, and the base change of a morphism over `U'` is the morphism
`AlgebraicGeometry.baseChangeMap` between those base changes.

A scheme of finite presentation over `U'` is turned into a morphism of such schemes by mapping it
to the terminal object of the slice category over `U'`.

## References

* [Stacks Project, Lemma 32.20.4 (0EY3)](https://stacks.math.columbia.edu/tag/0EY3)
* [Stacks Project, Lemma 32.14.3 (0BQ5)](https://stacks.math.columbia.edu/tag/0BQ5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.GlueingNearPoint

/-! ### Comparing base changes over an open subscheme and over the ambient scheme -/

/-- For a monomorphism `j : B ⟶ D`, the fibre product over `D` of two morphisms which both factor
through `j` is their fibre product over `B`. -/
private noncomputable def pullbackCompMonoIso {A B C D : Scheme.{u}} (f : A ⟶ B) (j : B ⟶ D)
    [Mono j] (l : C ⟶ B) :
    pullback (f ≫ j) (l ≫ j) ≅ pullback f l where
  hom := pullback.lift (pullback.fst (f ≫ j) (l ≫ j)) (pullback.snd (f ≫ j) (l ≫ j))
    ((cancel_mono j).1 (by
      simpa only [Category.assoc] using pullback.condition (f := f ≫ j) (g := l ≫ j)))
  inv := pullback.lift (pullback.fst f l) (pullback.snd f l) (by
    rw [← Category.assoc, ← Category.assoc, pullback.condition])
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]

private lemma pullbackCompMonoIso_hom_fst {A B C D : Scheme.{u}} (f : A ⟶ B) (j : B ⟶ D)
    [Mono j] (l : C ⟶ B) :
    (pullbackCompMonoIso f j l).hom ≫ pullback.fst f l = pullback.fst (f ≫ j) (l ≫ j) :=
  pullback.lift_fst _ _ _

private lemma pullbackCompMonoIso_hom_snd {A B C D : Scheme.{u}} (f : A ⟶ B) (j : B ⟶ D)
    [Mono j] (l : C ⟶ B) :
    (pullbackCompMonoIso f j l).hom ≫ pullback.snd f l = pullback.snd (f ≫ j) (l ≫ j) :=
  pullback.lift_snd _ _ _

/-- Base changing a scheme over an open subscheme `U' ⊆ S` along a morphism `l` into `U'` agrees
with regarding it as a scheme over `S` and base changing along `l ≫ U'.ι`. -/
private lemma prop_pullback_obj_overMap_iff {S T : Scheme.{u}} (U' : S.Opens)
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (X : Over U'.toScheme)
    (l : T ⟶ U'.toScheme) {g : T ⟶ S} (hg : l ≫ U'.ι = g) :
    P ((Over.pullback g).obj ((Over.map U'.ι).obj X)).hom ↔
      P ((Over.pullback l).obj X).hom := by
  subst hg
  refine P.arrow_mk_iso_iff (Arrow.isoMk (pullbackCompMonoIso X.hom U'.ι l) (Iso.refl T) ?_)
  change (pullbackCompMonoIso X.hom U'.ι l).hom ≫ pullback.snd X.hom l =
    pullback.snd (X.hom ≫ U'.ι) (l ≫ U'.ι) ≫ 𝟙 T
  rw [pullbackCompMonoIso_hom_snd, Category.comp_id]

/-- Base changing a morphism of schemes over an open subscheme `U' ⊆ S` along a morphism `l` into
`U'` agrees with regarding it as a morphism over `S` and base changing along `l ≫ U'.ι`. -/
private noncomputable def overMapPullbackArrowIso {S T : Scheme.{u}} (U' : S.Opens)
    (l : T ⟶ U'.toScheme) {X₁ X₂ : Over U'.toScheme} (a : X₁ ⟶ X₂) :
    Arrow.mk (((Over.pullback (l ≫ U'.ι)).map ((Over.map U'.ι).map a)).left) ≅
      Arrow.mk (((Over.pullback l).map a).left) :=
  Arrow.isoMk (pullbackCompMonoIso X₁.hom U'.ι l) (pullbackCompMonoIso X₂.hom U'.ι l) (by
    have h1 : ((Over.pullback (l ≫ U'.ι)).map ((Over.map U'.ι).map a)).left ≫
        pullback.fst (X₂.hom ≫ U'.ι) (l ≫ U'.ι) =
        pullback.fst (X₁.hom ≫ U'.ι) (l ≫ U'.ι) ≫ a.left :=
      overPullback_map_left_fst (l ≫ U'.ι) ((Over.map U'.ι).map a)
    have h2 : ((Over.pullback (l ≫ U'.ι)).map ((Over.map U'.ι).map a)).left ≫
        pullback.snd (X₂.hom ≫ U'.ι) (l ≫ U'.ι) =
        pullback.snd (X₁.hom ≫ U'.ι) (l ≫ U'.ι) :=
      overPullback_map_left_snd (l ≫ U'.ι) ((Over.map U'.ι).map a)
    have h3 : ((Over.pullback l).map a).left ≫ pullback.fst X₂.hom l =
        pullback.fst X₁.hom l ≫ a.left := overPullback_map_left_fst l a
    have h4 : ((Over.pullback l).map a).left ≫ pullback.snd X₂.hom l =
        pullback.snd X₁.hom l := overPullback_map_left_snd l a
    change (pullbackCompMonoIso X₁.hom U'.ι l).hom ≫ ((Over.pullback l).map a).left =
      ((Over.pullback (l ≫ U'.ι)).map ((Over.map U'.ι).map a)).left ≫
        (pullbackCompMonoIso X₂.hom U'.ι l).hom
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullbackCompMonoIso_hom_fst, h1, h3,
        ← Category.assoc, pullbackCompMonoIso_hom_fst]
    · rw [Category.assoc, Category.assoc, pullbackCompMonoIso_hom_snd, h2, h4,
        pullbackCompMonoIso_hom_snd])

/-- A property of the base change of a relative morphism along a morphism `g : T ⟶ S` which
factors as `l ≫ U'.ι` is a property of its base change along `l`. -/
private lemma baseChangeMap_overMap_iff {S T : Scheme.{u}} (U' : S.Opens)
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] {X₁ X₂ : Over U'.toScheme} (a : X₁ ⟶ X₂)
    (l : T ⟶ U'.toScheme) {g : T ⟶ S} (hg : l ≫ U'.ι = g) :
    P (baseChangeMap g ((Over.map U'.ι).obj X₁) ((Over.map U'.ι).obj X₂)
        ((Over.map U'.ι).map a)) ↔ P (((Over.pullback l).map a).left) := by
  subst hg
  refine (baseChangeMap_prop_iff P (l ≫ U'.ι) _ _ _).trans ?_
  exact P.arrow_mk_iso_iff (overMapPullbackArrowIso U' l a)

/-- The fibre product of a morphism with an identity is the source of that morphism. -/
private noncomputable def pullbackIdIso {T Y : Scheme.{u}} (l : Y ⟶ T) :
    pullback (𝟙 T) l ≅ Y where
  hom := pullback.snd (𝟙 T) l
  inv := pullback.lift l (𝟙 Y) (by rw [Category.comp_id, Category.id_comp])
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp, ← pullback.condition,
        Category.comp_id]
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]
  inv_hom_id := pullback.lift_snd _ _ _

/-- The base change of the morphism from a scheme over `T` to the terminal object of the slice
category over `T` is the structure morphism of the base change. -/
private noncomputable def overPullbackToIdArrowIso {T Y Z : Scheme.{u}} (l : Y ⟶ T) (f : Z ⟶ T) :
    Arrow.mk (((Over.pullback l).map
        (Over.homMk f (by simp) : Over.mk f ⟶ Over.mk (𝟙 T))).left) ≅
      Arrow.mk (((Over.pullback l).obj (Over.mk f)).hom) :=
  Arrow.isoMk (Iso.refl _) (pullbackIdIso l) (by
    change 𝟙 _ ≫ pullback.snd f l =
      ((Over.pullback l).map
        (Over.homMk f (by simp) : Over.mk f ⟶ Over.mk (𝟙 T))).left ≫ pullback.snd (𝟙 T) l
    rw [Category.id_comp]
    exact (overPullback_map_left_snd l
      (Over.homMk f (by simp) : Over.mk f ⟶ Over.mk (𝟙 T))).symm)

/-! ### Gluing a property over two opens -/

/-- A property of morphisms which respects isomorphisms holds for the restriction of a relative
morphism to the image of an open immersion as soon as it holds for the base change along it. -/
private lemma prop_morphismRestrict_of_overPullback {B : Scheme.{u}} {X₁ X₂ : Over B}
    (a : X₁ ⟶ X₂) (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {T : Scheme.{u}} (p : T ⟶ B) [IsOpenImmersion p]
    (h : P (((Over.pullback p).map a).left)) :
    P (a.left ∣_ (pullback.fst X₂.hom p).opensRange) := by
  rw [P.arrow_mk_iso_iff (morphismRestrictOpensRange a.left (pullback.fst X₂.hom p))]
  have hpb := overPullback_isPullback p X₁ X₂ a
  rwa [← MorphismProperty.cancel_left_of_respectsIso P hpb.isoPullback.hom,
    hpb.isoPullback_hom_snd]

/-- A property of morphisms which is local on the target holds for a relative morphism as soon as
it holds for its base changes along two open immersions whose images cover the base. -/
private lemma prop_left_of_two_opens {B : Scheme.{u}} {X₁ X₂ : Over B} (a : X₁ ⟶ X₂)
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    {T₁ T₂ : Scheme.{u}} (p₁ : T₁ ⟶ B) (p₂ : T₂ ⟶ B)
    [IsOpenImmersion p₁] [IsOpenImmersion p₂]
    (hcov : p₁.opensRange ⊔ p₂.opensRange = ⊤)
    (h₁ : P (((Over.pullback p₁).map a).left))
    (h₂ : P (((Over.pullback p₂).map a).left)) :
    P a.left := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun b : Bool ↦ cond b (pullback.fst X₂.hom p₁).opensRange
      (pullback.fst X₂.hom p₂).opensRange) ?_ ?_
  · rw [iSup_bool_eq]
    simp only [Bool.cond_true, Bool.cond_false, Scheme.Hom.opensRange_pullbackFst,
      ← Scheme.Hom.preimage_sup, hcov]
    simp
  · rintro (_ | _)
    · exact prop_morphismRestrict_of_overPullback a P p₂ h₂
    · exact prop_morphismRestrict_of_overPullback a P p₁ h₁

/-- A property of morphisms which is local on the target spreads from two opens of a neighbourhood
to their union. -/
private lemma prop_sup {S : Scheme.{u}} {U W U' : S.Opens} (hUU' : U ≤ U') (hWU' : W ≤ U')
    {X₁ X₂ : Over U'.toScheme} (a : X₁ ⟶ X₂)
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (hU : P (((Over.pullback (S.homOfLE hUU')).map a).left))
    (hW : P (((Over.pullback (S.homOfLE hWU')).map a).left)) :
    P (((Over.pullback (S.homOfLE (sup_le hUU' hWU'))).map a).left) := by
  refine prop_left_of_two_opens ((Over.pullback (S.homOfLE (sup_le hUU' hWU'))).map a) P
    (S.homOfLE (le_sup_left : U ≤ U ⊔ W)) (S.homOfLE (le_sup_right : W ≤ U ⊔ W)) ?_ ?_ ?_
  · simp only [Scheme.opensRange_homOfLE, ← Scheme.Hom.preimage_sup]
    simp
  · rwa [← P.arrow_mk_iso_iff (overPullbackCompArrowIso (S.homOfLE (sup_le hUU' hWU'))
      (S.homOfLE (le_sup_left : U ≤ U ⊔ W)) a), Scheme.homOfLE_homOfLE]
  · rwa [← P.arrow_mk_iso_iff (overPullbackCompArrowIso (S.homOfLE (sup_le hUU' hWU'))
      (S.homOfLE (le_sup_right : W ≤ U ⊔ W)) a), Scheme.homOfLE_homOfLE]

/-! ### Descending a property to an affine open neighbourhood -/

/-- Given a descent statement along the inverse system of affine open neighbourhoods of `s`, a
property of the base change of a relative morphism to the local scheme at `s` already holds over
some open neighbourhood of `s` inside `U'`. -/
private lemma exists_open_of_descent {S : Scheme.{u}} (s : S) (U' : S.Opens) (hsU' : s ∈ U')
    (X₁ X₂ : Over U'.toScheme) (a : X₁ ⟶ X₂)
    (hX₁ : FinitePresentation X₁.hom) (hX₂ : FinitePresentation X₂.hom)
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hP : P (((Over.pullback (U'.fromSpecStalkOfMem s hsU')).map a).left))
    (hdescend : ∀ (i₀ : AffineOpenNhds S s)
        (X₀ Y₀ : Over ((affineOpenNhdsDiagram S s).obj i₀)) (f₀ : X₀ ⟶ Y₀),
        CompactSpace X₀.left → QuasiSeparatedSpace X₀.left →
        CompactSpace Y₀.left → QuasiSeparatedSpace Y₀.left →
        LocallyOfFinitePresentation f₀.left →
        P (((Over.pullback ((specStalkCone S s).π.app i₀)).map f₀).left) →
        ∃ (i : AffineOpenNhds S s) (g : i ⟶ i₀),
          P (((Over.pullback ((affineOpenNhdsDiagram S s).map g)).map f₀).left)) :
    ∃ (W : S.Opens) (hW : W ≤ U'), s ∈ W ∧
      P (((Over.pullback (S.homOfLE hW)).map a).left) := by
  obtain ⟨i₀, hi₀⟩ := exists_affineOpenNhds_le S s ⟨U', hsU'⟩
  have hi₀' : (OpenNhds.inclusion s).obj ((affineOpenNhds S s).ι.obj i₀) ≤ U' :=
    (OpenNhds.le_def i₀.obj ⟨U', hsU'⟩).mp hi₀
  obtain ⟨_, _, _⟩ := hX₁
  obtain ⟨_, _, _⟩ := hX₂
  obtain ⟨g₀, hg₀ι⟩ : ∃ g₀ : (affineOpenNhdsDiagram S s).obj i₀ ⟶ U'.toScheme,
      g₀ ≫ U'.ι = Scheme.Opens.ι (X := S) i₀.obj.1 :=
    ⟨S.homOfLE hi₀', S.homOfLE_ι hi₀'⟩
  have hlfp₁ : LocallyOfFinitePresentation ((Over.pullback g₀).obj X₁).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd X₁.hom g₀))
  have hlfp₂ : LocallyOfFinitePresentation ((Over.pullback g₀).obj X₂).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd X₂.hom g₀))
  have hc₁ : CompactSpace ((Over.pullback g₀).obj X₁).left :=
    (quasiCompact_iff_compactSpace ((Over.pullback g₀).obj X₁).hom).mp
      (inferInstanceAs (QuasiCompact (pullback.snd X₁.hom g₀)))
  have hc₂ : CompactSpace ((Over.pullback g₀).obj X₂).left :=
    (quasiCompact_iff_compactSpace ((Over.pullback g₀).obj X₂).hom).mp
      (inferInstanceAs (QuasiCompact (pullback.snd X₂.hom g₀)))
  have hs₁ : QuasiSeparatedSpace ((Over.pullback g₀).obj X₁).left :=
    (quasiSeparated_iff_quasiSeparatedSpace ((Over.pullback g₀).obj X₁).hom).mp
      (inferInstanceAs (QuasiSeparated (pullback.snd X₁.hom g₀)))
  have hs₂ : QuasiSeparatedSpace ((Over.pullback g₀).obj X₂).left :=
    (quasiSeparated_iff_quasiSeparatedSpace ((Over.pullback g₀).obj X₂).hom).mp
      (inferInstanceAs (QuasiSeparated (pullback.snd X₂.hom g₀)))
  have hcomp : LocallyOfFinitePresentation
      (((Over.pullback g₀).map a).left ≫ ((Over.pullback g₀).obj X₂).hom) := by
    rwa [Over.w ((Over.pullback g₀).map a)]
  have hlfpa : LocallyOfFinitePresentation ((Over.pullback g₀).map a).left :=
    locallyOfFinitePresentation_of_comp _ ((Over.pullback g₀).obj X₂).hom
  have hπ : U'.fromSpecStalkOfMem s hsU' =
      Scheme.Opens.fromSpecStalkOfMem (X := S) i₀.obj.1 s i₀.obj.2 ≫ g₀ :=
    (cancel_mono U'.ι).1 (calc
      U'.fromSpecStalkOfMem s hsU' ≫ U'.ι = S.fromSpecStalk s :=
          Scheme.Opens.fromSpecStalkOfMem_ι U' s hsU'
      _ = Scheme.Opens.fromSpecStalkOfMem (X := S) i₀.obj.1 s i₀.obj.2 ≫
            Scheme.Opens.ι (X := S) i₀.obj.1 :=
          (Scheme.Opens.fromSpecStalkOfMem_ι _ s i₀.obj.2).symm
      _ = Scheme.Opens.fromSpecStalkOfMem (X := S) i₀.obj.1 s i₀.obj.2 ≫ (g₀ ≫ U'.ι) :=
          congrArg
            (fun k ↦ Scheme.Opens.fromSpecStalkOfMem (X := S) i₀.obj.1 s i₀.obj.2 ≫ k) hg₀ι.symm
      _ = (Scheme.Opens.fromSpecStalkOfMem (X := S) i₀.obj.1 s i₀.obj.2 ≫ g₀) ≫ U'.ι :=
          (Category.assoc _ _ _).symm)
  rw [hπ] at hP
  have hlim : P (((Over.pullback ((specStalkCone S s).π.app i₀)).map
      ((Over.pullback g₀).map a)).left) := by
    rw [specStalkCone_π_app]
    exact (P.arrow_mk_iso_iff (overPullbackCompArrowIso g₀
      (Scheme.Opens.fromSpecStalkOfMem (X := S) i₀.obj.1 s i₀.obj.2) a)).mp hP
  obtain ⟨i, g, hstage⟩ := hdescend i₀ ((Over.pullback g₀).obj X₁) ((Over.pullback g₀).obj X₂)
    ((Over.pullback g₀).map a) hc₁ hs₁ hc₂ hs₂ hlfpa hlim
  have hii₀ : i.obj.1 ≤ i₀.obj.1 :=
    (OpenNhds.le_def i.obj i₀.obj).mp (leOfHom ((affineOpenNhds S s).ι.map g))
  have hiU' : i.obj.1 ≤ U' := hii₀.trans hi₀'
  refine ⟨i.obj.1, hiU', i.obj.2, ?_⟩
  have hdg : (affineOpenNhdsDiagram S s).map g ≫ Scheme.Opens.ι (X := S) i₀.obj.1 =
      Scheme.Opens.ι (X := S) i.obj.1 := by
    rw [affineOpenNhdsDiagram_map]
    exact S.homOfLE_ι _
  have hmap : (affineOpenNhdsDiagram S s).map g ≫ g₀ = S.homOfLE hiU' := by
    apply (cancel_mono U'.ι).1
    rw [Category.assoc, hg₀ι, hdg]
    exact (S.homOfLE_ι hiU').symm
  rw [← hmap]
  exact (P.arrow_mk_iso_iff
    (overPullbackCompArrowIso g₀ ((affineOpenNhdsDiagram S s).map g) a)).mpr hstage

/-- Let `U ⊆ S` be a retrocompact open and `s` a point of `S`. A property of morphisms which is
local on the target and which can be descended along the affine open neighbourhoods of `s` holds for
a relative morphism over some open neighbourhood of `U ∪ {s}` as soon as it holds over `U` and over
`Spec 𝒪_{S, s}`. -/
private lemma exists_open_baseChange_of_descent {S : Scheme.{u}} (U U' : S.Opens) (s : S)
    (hsU' : s ∈ U') (hUU' : U ≤ U') (X₁ X₂ : Over U'.toScheme) (a : X₁ ⟶ X₂)
    (hX₁ : FinitePresentation X₁.hom) (hX₂ : FinitePresentation X₂.hom)
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (hU : P (baseChangeMap U.ι ((Over.map U'.ι).obj X₁)
      ((Over.map U'.ι).obj X₂) ((Over.map U'.ι).map a)))
    (hS : P (baseChangeMap (S.fromSpecStalk s) ((Over.map U'.ι).obj X₁)
      ((Over.map U'.ι).obj X₂) ((Over.map U'.ι).map a)))
    (hdescend : ∀ (i₀ : AffineOpenNhds S s)
        (X₀ Y₀ : Over ((affineOpenNhdsDiagram S s).obj i₀)) (f₀ : X₀ ⟶ Y₀),
        CompactSpace X₀.left → QuasiSeparatedSpace X₀.left →
        CompactSpace Y₀.left → QuasiSeparatedSpace Y₀.left →
        LocallyOfFinitePresentation f₀.left →
        P (((Over.pullback ((specStalkCone S s).π.app i₀)).map f₀).left) →
        ∃ (i : AffineOpenNhds S s) (g : i ⟶ i₀),
          P (((Over.pullback ((affineOpenNhdsDiagram S s).map g)).map f₀).left)) :
    ∃ V : S.Opens, U ≤ V ∧ V ≤ U' ∧ s ∈ V ∧
      P (baseChangeMap V.ι ((Over.map U'.ι).obj X₁)
        ((Over.map U'.ι).obj X₂) ((Over.map U'.ι).map a)) := by
  rw [baseChangeMap_overMap_iff U' P a (S.homOfLE hUU') (Scheme.homOfLE_ι S hUU')] at hU
  rw [baseChangeMap_overMap_iff U' P a (U'.fromSpecStalkOfMem s hsU')
    (Scheme.Opens.fromSpecStalkOfMem_ι U' s hsU')] at hS
  obtain ⟨W, hWU', hsW, hWprop⟩ := exists_open_of_descent s U' hsU' X₁ X₂ a hX₁ hX₂ P hS hdescend
  refine ⟨U ⊔ W, le_sup_left, sup_le hUU' hWU', Or.inr hsW, ?_⟩
  rw [baseChangeMap_overMap_iff U' P a (S.homOfLE (sup_le hUU' hWU'))
    (Scheme.homOfLE_ι S (sup_le hUU' hWU'))]
  exact prop_sup hUU' hWU' a P hU hWprop

/-! ### Properties of a morphism of relative schemes -/

/-- Let `U ⊆ S` be a retrocompact open, let `s` be a point of `S` outside `U` and let `a` be a
morphism of schemes of finite presentation over an open neighbourhood `U'` of `U ∪ {s}`. If `a` is
separated over `U` and over `Spec 𝒪_{S, s}`, then it is separated over some open neighbourhood of
`U ∪ {s}` contained in `U'`. -/
@[stacks 0EY3 "properties_of_relative_morphism"]
theorem exists_open_isSeparated_baseChange
    (S : Scheme.{u}) (U U' : S.Opens) (s : S) (_hsU : s ∉ U) (hsU' : s ∈ U')
    (_hU : IsRetrocompact (U : Set S)) (hUU' : U ≤ U')
    (X₁ X₂ : Over U'.toScheme) (a : X₁ ⟶ X₂)
    (hX₁ : FinitePresentation X₁.hom) (hX₂ : FinitePresentation X₂.hom)
    (hsepU : IsSeparated (baseChangeMap U.ι ((Over.map U'.ι).obj X₁)
      ((Over.map U'.ι).obj X₂) ((Over.map U'.ι).map a)))
    (hsepS : IsSeparated (baseChangeMap (S.fromSpecStalk s) ((Over.map U'.ι).obj X₁)
      ((Over.map U'.ι).obj X₂) ((Over.map U'.ι).map a))) :
    ∃ V : S.Opens, U ≤ V ∧ V ≤ U' ∧ s ∈ V ∧
      IsSeparated (baseChangeMap V.ι ((Over.map U'.ι).obj X₁)
        ((Over.map U'.ι).obj X₂) ((Over.map U'.ι).map a)) := by
  exact exists_open_baseChange_of_descent U U' s hsU' hUU' X₁ X₂ a hX₁ hX₂ (@IsSeparated)
    hsepU hsepS
    (fun i₀ X₀ Y₀ f₀ _ _ _ _ _ _ ↦
      exists_isSeparated_baseChange_of_isLimit (affineOpenNhdsDiagram S s)
        (specStalkCone S s) i₀ X₀ Y₀ f₀ (isLimitSpecStalkCone S s))

/-- Let `U ⊆ S` be a retrocompact open, let `s` be a point of `S` outside `U` and let `a` be a
morphism of schemes of finite presentation over an open neighbourhood `U'` of `U ∪ {s}`. If `a` is
proper over `U` and over `Spec 𝒪_{S, s}`, then it is proper over some open neighbourhood of
`U ∪ {s}` contained in `U'`. -/
@[stacks 0EY3 "properties_of_relative_morphism", ega "IV 8.1.2" "partial"]
theorem exists_open_isProper_baseChange
    (S : Scheme.{u}) (U U' : S.Opens) (s : S) (_hsU : s ∉ U) (hsU' : s ∈ U')
    (_hU : IsRetrocompact (U : Set S)) (hUU' : U ≤ U')
    (X₁ X₂ : Over U'.toScheme) (a : X₁ ⟶ X₂)
    (hX₁ : FinitePresentation X₁.hom) (hX₂ : FinitePresentation X₂.hom)
    (hproperU : IsProper (baseChangeMap U.ι ((Over.map U'.ι).obj X₁)
      ((Over.map U'.ι).obj X₂) ((Over.map U'.ι).map a)))
    (hproperS : IsProper (baseChangeMap (S.fromSpecStalk s) ((Over.map U'.ι).obj X₁)
      ((Over.map U'.ι).obj X₂) ((Over.map U'.ι).map a))) :
    ∃ V : S.Opens, U ≤ V ∧ V ≤ U' ∧ s ∈ V ∧
      IsProper (baseChangeMap V.ι ((Over.map U'.ι).obj X₁)
        ((Over.map U'.ι).obj X₂) ((Over.map U'.ι).map a)) := by
  exact exists_open_baseChange_of_descent U U' s hsU' hUU' X₁ X₂ a hX₁ hX₂ (@IsProper)
    hproperU hproperS
    (fun i₀ X₀ Y₀ f₀ _ _ _ _ _ _ ↦
      exists_isProper_baseChange_of_isLimit (affineOpenNhdsDiagram S s)
        (specStalkCone S s) i₀ (isLimitSpecStalkCone S s) X₀ Y₀ f₀)

/-- Let `U ⊆ S` be a retrocompact open, let `s` be a point of `S` outside `U` and let `a` be a
morphism of schemes of finite presentation over an open neighbourhood `U'` of `U ∪ {s}`. If `a` is
finite over `U` and over `Spec 𝒪_{S, s}`, then it is finite over some open neighbourhood of
`U ∪ {s}` contained in `U'`. -/
@[stacks 0EY3 "properties_of_relative_morphism"]
theorem exists_open_isFinite_baseChange
    (S : Scheme.{u}) (U U' : S.Opens) (s : S) (_hsU : s ∉ U) (hsU' : s ∈ U')
    (_hU : IsRetrocompact (U : Set S)) (hUU' : U ≤ U')
    (X₁ X₂ : Over U'.toScheme) (a : X₁ ⟶ X₂)
    (hX₁ : FinitePresentation X₁.hom) (hX₂ : FinitePresentation X₂.hom)
    (hfiniteU : IsFinite (baseChangeMap U.ι ((Over.map U'.ι).obj X₁)
      ((Over.map U'.ι).obj X₂) ((Over.map U'.ι).map a)))
    (hfiniteS : IsFinite (baseChangeMap (S.fromSpecStalk s) ((Over.map U'.ι).obj X₁)
      ((Over.map U'.ι).obj X₂) ((Over.map U'.ι).map a))) :
    ∃ V : S.Opens, U ≤ V ∧ V ≤ U' ∧ s ∈ V ∧
      IsFinite (baseChangeMap V.ι ((Over.map U'.ι).obj X₁)
        ((Over.map U'.ι).obj X₂) ((Over.map U'.ι).map a)) := by
  have : IsZariskiLocalAtTarget (@IsFinite.{u}) :=
    AlgebraicGeometry.isZariskiLocalAtTarget_isFinite
  exact exists_open_baseChange_of_descent U U' s hsU' hUU' X₁ X₂ a hX₁ hX₂ (@IsFinite)
    hfiniteU hfiniteS
    (fun i₀ X₀ Y₀ f₀ _ _ _ _ _ _ ↦
      exists_isFinite_baseChange_of_isLimit (affineOpenNhdsDiagram S s)
        (specStalkCone S s) (isLimitSpecStalkCone S s) i₀ X₀ Y₀ f₀)

/-- Let `U ⊆ S` be a retrocompact open, let `s` be a point of `S` outside `U` and let `a` be a
morphism of schemes of finite presentation over an open neighbourhood `U'` of `U ∪ {s}`. If `a` is
étale over `U` and over `Spec 𝒪_{S, s}`, then it is étale over some open neighbourhood of `U ∪ {s}`
contained in `U'`. -/
@[stacks 0EY3 "properties_of_relative_morphism"]
theorem exists_open_etale_baseChange
    (S : Scheme.{u}) (U U' : S.Opens) (s : S) (_hsU : s ∉ U) (hsU' : s ∈ U')
    (_hU : IsRetrocompact (U : Set S)) (hUU' : U ≤ U')
    (X₁ X₂ : Over U'.toScheme) (a : X₁ ⟶ X₂)
    (hX₁ : FinitePresentation X₁.hom) (hX₂ : FinitePresentation X₂.hom)
    (hetaleU : Etale (baseChangeMap U.ι ((Over.map U'.ι).obj X₁)
      ((Over.map U'.ι).obj X₂) ((Over.map U'.ι).map a)))
    (hetaleS : Etale (baseChangeMap (S.fromSpecStalk s) ((Over.map U'.ι).obj X₁)
      ((Over.map U'.ι).obj X₂) ((Over.map U'.ι).map a))) :
    ∃ V : S.Opens, U ≤ V ∧ V ≤ U' ∧ s ∈ V ∧
      Etale (baseChangeMap V.ι ((Over.map U'.ι).obj X₁)
        ((Over.map U'.ι).obj X₂) ((Over.map U'.ι).map a)) := by
  have : IsZariskiLocalAtTarget (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (@Etale.{u})
  exact exists_open_baseChange_of_descent U U' s hsU' hUU' X₁ X₂ a hX₁ hX₂ (@Etale)
    hetaleU hetaleS
    (fun i₀ X₀ Y₀ f₀ _ _ _ _ _ _ ↦ by
      obtain ⟨j, hj⟩ := exists_etale_pullback_of_isLimit (affineOpenNhdsDiagram S s)
        (specStalkCone S s) (isLimitSpecStalkCone S s) i₀ X₀ Y₀ f₀
      exact ⟨j.left, j.hom, hj⟩)

/-! ### Properties of a scheme of finite presentation over a neighbourhood -/

/-- A scheme of finite presentation over an open neighbourhood of `U ∪ {s}` is the source of the
morphism to the terminal object of the slice category over that neighbourhood, so a statement
about morphisms of relative schemes specialises to one about the scheme itself. -/
private lemma spread_of_relative (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {S : Scheme.{u}} (U : S.Opens) (s : S) (T : S.Opens) (hUT : U ≤ T) (hsT : s ∈ T)
    {Y : Scheme.{u}} (f : Y ⟶ T.toScheme) (hf : FinitePresentation f)
    (hopen : P ((Over.pullback U.ι).obj (Over.mk (f ≫ T.ι))).hom)
    (hlocal : P ((Over.pullback (S.fromSpecStalk s)).obj (Over.mk (f ≫ T.ι))).hom)
    (hspread : ∀ (X₁ X₂ : Over T.toScheme) (a : X₁ ⟶ X₂),
        FinitePresentation X₁.hom → FinitePresentation X₂.hom →
        P (baseChangeMap U.ι ((Over.map T.ι).obj X₁) ((Over.map T.ι).obj X₂)
          ((Over.map T.ι).map a)) →
        P (baseChangeMap (S.fromSpecStalk s) ((Over.map T.ι).obj X₁)
          ((Over.map T.ι).obj X₂) ((Over.map T.ι).map a)) →
        ∃ V : S.Opens, U ≤ V ∧ V ≤ T ∧ s ∈ V ∧
          P (baseChangeMap V.ι ((Over.map T.ι).obj X₁) ((Over.map T.ι).obj X₂)
            ((Over.map T.ι).map a))) :
    ∃ V : S.Opens, U ≤ V ∧ V ≤ T ∧ s ∈ V ∧
      P ((Over.pullback V.ι).obj (Over.mk (f ≫ T.ι))).hom := by
  have key : ∀ (Z : Scheme.{u}) (g : Z ⟶ S) (l : Z ⟶ T.toScheme), l ≫ T.ι = g →
      (P (baseChangeMap g ((Over.map T.ι).obj (Over.mk f))
          ((Over.map T.ι).obj (Over.mk (𝟙 T.toScheme)))
          ((Over.map T.ι).map (Over.homMk f (by simp) :
            (Over.mk f : Over T.toScheme) ⟶ Over.mk (𝟙 T.toScheme)))) ↔
        P ((Over.pullback g).obj (Over.mk (f ≫ T.ι))).hom) := fun Z g l hl ↦
    ((baseChangeMap_overMap_iff T P _ l hl).trans
      (P.arrow_mk_iso_iff (overPullbackToIdArrowIso l f))).trans
      (prop_pullback_obj_overMap_iff T P (Over.mk f) l hl).symm
  obtain ⟨V, hUV, hVT, hsV, hPV⟩ := hspread (Over.mk f) (Over.mk (𝟙 T.toScheme))
    (Over.homMk f (by simp)) hf
    (show FinitePresentation (𝟙 T.toScheme) from ⟨inferInstance, inferInstance, inferInstance⟩)
    ((key _ U.ι (S.homOfLE hUT) (Scheme.homOfLE_ι S hUT)).mpr hopen)
    ((key _ (S.fromSpecStalk s) (T.fromSpecStalkOfMem s hsT)
      (Scheme.Opens.fromSpecStalkOfMem_ι T s hsT)).mpr hlocal)
  exact ⟨V, hUV, hVT, hsV, (key _ V.ι (S.homOfLE hVT) (Scheme.homOfLE_ι S hVT)).mp hPV⟩

/-- A scheme of finite presentation over an open neighbourhood of `U ∪ {s}` whose restrictions to
the retrocompact open `U` and to the local scheme `Spec 𝒪_{S, s}` are separated is separated over
some smaller open neighbourhood of `U ∪ {s}`. -/
@[stacks 0EY3 "properties_of_glued_morphism"]
theorem exists_open_isSeparated
    (S : Scheme.{u}) (U : S.Opens) (s : S) (hs : s ∉ U)
    (hU : IsRetrocompact (U : Set S))
    (X : FinitePresentationNeighborhoodModel S U s)
    (hopen : IsSeparated ((Over.pullback U.ι).obj
      ((neighborhoodModelToAmbient S U s).obj X)).hom)
    (hlocal : IsSeparated ((Over.pullback (S.fromSpecStalk s)).obj
      ((neighborhoodModelToAmbient S U s).obj X)).hom) :
    ∃ V : S.Opens, U ≤ V ∧ V ≤ X.neighborhood.V ∧ s ∈ V ∧
      IsSeparated ((Over.pullback V.ι).obj
        ((neighborhoodModelToAmbient S U s).obj X)).hom :=
  spread_of_relative (@IsSeparated) U s X.neighborhood.V X.neighborhood.le_V
    X.neighborhood.mem_V X.hom X.finitePresentation hopen hlocal
    (fun X₁ X₂ a hX₁ hX₂ hU' hS' ↦
      exists_open_isSeparated_baseChange S U X.neighborhood.V s hs X.neighborhood.mem_V hU
        X.neighborhood.le_V X₁ X₂ a hX₁ hX₂ hU' hS')

/-- A scheme of finite presentation over an open neighbourhood of `U ∪ {s}` whose restrictions to
the retrocompact open `U` and to the local scheme `Spec 𝒪_{S, s}` are proper is proper over some
smaller open neighbourhood of `U ∪ {s}`. -/
@[stacks 0EY3 "properties_of_glued_morphism"]
theorem exists_open_isProper
    (S : Scheme.{u}) (U : S.Opens) (s : S) (hs : s ∉ U)
    (hU : IsRetrocompact (U : Set S))
    (X : FinitePresentationNeighborhoodModel S U s)
    (hopen : IsProper ((Over.pullback U.ι).obj
      ((neighborhoodModelToAmbient S U s).obj X)).hom)
    (hlocal : IsProper ((Over.pullback (S.fromSpecStalk s)).obj
      ((neighborhoodModelToAmbient S U s).obj X)).hom) :
    ∃ V : S.Opens, U ≤ V ∧ V ≤ X.neighborhood.V ∧ s ∈ V ∧
      IsProper ((Over.pullback V.ι).obj
        ((neighborhoodModelToAmbient S U s).obj X)).hom :=
  spread_of_relative (@IsProper) U s X.neighborhood.V X.neighborhood.le_V
    X.neighborhood.mem_V X.hom X.finitePresentation hopen hlocal
    (fun X₁ X₂ a hX₁ hX₂ hU' hS' ↦
      exists_open_isProper_baseChange S U X.neighborhood.V s hs X.neighborhood.mem_V hU
        X.neighborhood.le_V X₁ X₂ a hX₁ hX₂ hU' hS')

/-- A scheme of finite presentation over an open neighbourhood of `U ∪ {s}` whose restrictions to
the retrocompact open `U` and to the local scheme `Spec 𝒪_{S, s}` are finite is finite over some
smaller open neighbourhood of `U ∪ {s}`. -/
@[stacks 0EY3 "properties_of_glued_morphism"]
theorem exists_open_isFinite
    (S : Scheme.{u}) (U : S.Opens) (s : S) (hs : s ∉ U)
    (hU : IsRetrocompact (U : Set S))
    (X : FinitePresentationNeighborhoodModel S U s)
    (hopen : IsFinite ((Over.pullback U.ι).obj
      ((neighborhoodModelToAmbient S U s).obj X)).hom)
    (hlocal : IsFinite ((Over.pullback (S.fromSpecStalk s)).obj
      ((neighborhoodModelToAmbient S U s).obj X)).hom) :
    ∃ V : S.Opens, U ≤ V ∧ V ≤ X.neighborhood.V ∧ s ∈ V ∧
      IsFinite ((Over.pullback V.ι).obj
        ((neighborhoodModelToAmbient S U s).obj X)).hom := by
  have : MorphismProperty.RespectsIso (@IsFinite.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact spread_of_relative (@IsFinite) U s X.neighborhood.V X.neighborhood.le_V
    X.neighborhood.mem_V X.hom X.finitePresentation hopen hlocal
    (fun X₁ X₂ a hX₁ hX₂ hU' hS' ↦
      exists_open_isFinite_baseChange S U X.neighborhood.V s hs X.neighborhood.mem_V hU
        X.neighborhood.le_V X₁ X₂ a hX₁ hX₂ hU' hS')

/-- A scheme of finite presentation over an open neighbourhood of `U ∪ {s}` whose restrictions to
the retrocompact open `U` and to the local scheme `Spec 𝒪_{S, s}` are étale is étale over some
smaller open neighbourhood of `U ∪ {s}`. -/
@[stacks 0EY3 "properties_of_glued_morphism"]
theorem exists_open_etale
    (S : Scheme.{u}) (U : S.Opens) (s : S) (hs : s ∉ U)
    (hU : IsRetrocompact (U : Set S))
    (X : FinitePresentationNeighborhoodModel S U s)
    (hopen : Etale ((Over.pullback U.ι).obj
      ((neighborhoodModelToAmbient S U s).obj X)).hom)
    (hlocal : Etale ((Over.pullback (S.fromSpecStalk s)).obj
      ((neighborhoodModelToAmbient S U s).obj X)).hom) :
    ∃ V : S.Opens, U ≤ V ∧ V ≤ X.neighborhood.V ∧ s ∈ V ∧
      Etale ((Over.pullback V.ι).obj
        ((neighborhoodModelToAmbient S U s).obj X)).hom := by
  have : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact spread_of_relative (@Etale) U s X.neighborhood.V X.neighborhood.le_V
    X.neighborhood.mem_V X.hom X.finitePresentation hopen hlocal
    (fun X₁ X₂ a hX₁ hX₂ hU' hS' ↦
      exists_open_etale_baseChange S U X.neighborhood.V s hs X.neighborhood.mem_V hU
        X.neighborhood.le_V X₁ X₂ a hX₁ hX₂ hU' hS')

end AlgebraicGeometry.GlueingNearPoint

end
