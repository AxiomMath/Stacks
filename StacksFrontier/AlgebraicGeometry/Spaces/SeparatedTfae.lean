module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.Descent.FiniteDescentFromAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.QuasiCompactLocal
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable

/-!
# Local criteria for the separation axioms of a morphism of algebraic spaces

The separation axioms of a morphism of algebraic spaces — separatedness, local separatedness and
quasi-separatedness — are properties of the relative diagonal. We prove that each can be tested
on base changes along objects of the big fppf site, along those objects whose underlying scheme
is affine, along one surjective étale scheme chart of the target, and over the members of a
Zariski covering of the target, and for separatedness and local separatedness we collect these
criteria into six equivalent conditions.

## Main definitions

* `Stacks.SeparationLocal.diagonalObjMap`: the comparison morphism
  `(X ×[Y] Z) ×[Z] (X ×[Y] Z) ⟶ X ×[Y] X`.
* `Stacks.SeparationLocal.openObj` and `Stacks.SeparationLocal.openObjHom`: an open subscheme
  of the scheme underlying an object of the big fppf site over `S`, as an object of that site.
* `Stacks.SeparationLocal.DiagonalProp`: the property of a morphism of presheaves that its
  relative diagonal has `P` after every represented base change; for `P = IsClosedImmersion` and
  `P = IsImmersion` it is `AlgebraicGeometry.Space.IsSeparated` and
  `AlgebraicGeometry.Space.IsLocallySeparated`.

## Main results

* `Stacks.Descent.isImmersion_descendsAlong_fppf`: immersions of schemes satisfy fppf descent.
* `Stacks.SeparationLocal.isPullback_diagonal_pullbackSnd`: the relative diagonal of a base
  change is a base change of the relative diagonal.
* `Stacks.SeparationLocal.diagonalProp_iff_affine` and
  `Stacks.SeparationLocal.diagonalProp_iff_all`: `DiagonalProp P` can be tested on base changes
  along objects of the site with affine underlying scheme, or along all objects of the site.
* `Stacks.SeparationLocal.DiagonalProp.of_etaleChart` and
  `Stacks.SeparationLocal.DiagonalProp.of_zariskiCover`: `DiagonalProp P` descends along a
  surjective étale chart and along a Zariski covering of the target.
* `AlgebraicGeometry.Space.isQuasiSeparated_iff_forall_pullback`: quasi-separatedness can be
  tested on base changes along objects of the site.
* `AlgebraicGeometry.Space.isSeparated_comp` and `AlgebraicGeometry.Space.isLocallySeparated_comp`:
  separatedness and local separatedness are stable under composition.
* `AlgebraicGeometry.Space.isSeparated_tfae` and
  `AlgebraicGeometry.Space.isLocallySeparated_tfae`: the six equivalent conditions for a morphism
  of algebraic spaces to be separated, respectively locally separated.

## References

* [Stacks Project, Tag 03KM](https://stacks.math.columbia.edu/tag/03KM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-! ### Covering sieves of the big fppf site are jointly surjective on points -/

namespace CategoryTheory.Subfunctor

variable {C : Type*} [Category C] {F : Cᵒᵖ ⥤ Type u}

/-- A section of the coproduct of a family of subfunctors maps, under the canonical morphism to the
ambient presheaf, into one of the members. -/
theorem exists_mem_obj_of_sigmaDesc {I : Type*} (U : I → Subfunctor F)
    [Limits.HasCoproduct fun i => (U i).toFunctor] (c : Cᵒᵖ)
    (t : (∐ fun i => (U i).toFunctor).obj c) :
    ∃ i, (Limits.Sigma.desc fun i => (U i).ι).app c t ∈ (U i).obj c := by
  have hfac : (Limits.Sigma.desc fun i => homOfLe (le_iSup U i)) ≫ (⨆ i, U i).ι =
      Limits.Sigma.desc fun i => (U i).ι :=
    Limits.Sigma.hom_ext _ _ fun i => by
      rw [Limits.Sigma.ι_comp_desc_assoc, homOfLe_ι, Limits.Sigma.ι_comp_desc]
  have hmem : (Limits.Sigma.desc fun i => (U i).ι).app c t ∈ (⨆ i, U i).obj c := by
    rw [← hfac]
    exact ((Limits.Sigma.desc fun i => homOfLe (le_iSup U i)).app c t).property
  rw [iSup_obj] at hmem
  simpa using hmem

/-- A section `s` of `F` over `c` lying in a subfunctor `G` factors the morphism `h_c ⟶ F` it
determines through the inclusion of `G`. -/
theorem exists_comp_ι_eq (G : Subfunctor F) {c : C} (s : F.obj (Opposite.op c))
    (hs : s ∈ G.obj (Opposite.op c)) :
    ∃ m : yoneda.obj c ⟶ G.toFunctor, m ≫ G.ι = yonedaEquiv.symm s :=
  ⟨yonedaEquiv.symm ⟨s, hs⟩, yonedaEquiv_symm_naturality_right c G.ι _⟩

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry

open Opposite

/-- Let `U` be a Zariski covering of a presheaf `Y` on the big fppf site of `S` by representable
relative open immersions, and let `g₀ : h_a ⟶ Y`. Then the open subschemes of `a` representing the
base changes of the members along `g₀` cover the scheme underlying `a`. -/
theorem Space.exists_mem_range_of_isZariskiCover (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {I : Type u}
    {U : I → Subfunctor Y} (hU : Space.IsZariskiCover B S hS I U)
    (hg : ∀ i, yoneda.relativelyRepresentable (U i).ι)
    (a : BigFppfOver B S hS) (g₀ : yoneda.obj a ⟶ Y)
    (x : (BigFppfOver.toScheme B S hS).obj a) :
    ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map ((hg i).snd g₀)) := by
  have hls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Limits.Sigma.desc fun i => (U i).ι) := hU.2
  have hR := Presheaf.imageSieve_mem (BigFppfOver.topology B S hS)
    (Limits.Sigma.desc fun i => (U i).ι) (U := op a) (yonedaEquiv g₀)
  obtain ⟨c, h, ⟨t, ht⟩, y, hy⟩ := BigFppfOver.exists_mem_arrows_mem_range B S hS hR x
  obtain ⟨i, hi⟩ := Subfunctor.exists_mem_obj_of_sigmaDesc U (op c) t
  rw [ht] at hi
  obtain ⟨m, hm⟩ := Subfunctor.exists_comp_ι_eq (U i) _ hi
  have hsq : m ≫ (U i).ι = yoneda.map h ≫ g₀ := by
    rw [hm, yonedaEquiv_naturality]
    exact yonedaEquiv.symm_apply_apply _
  refine ⟨i, (BigFppfOver.toScheme B S hS).map ((hg i).lift m h hsq) y, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Functor.map_comp,
    Functor.relativelyRepresentable.lift_snd]
  exact hy

end AlgebraicGeometry

/-! ### Immersions of schemes are fppf local on the base -/

namespace Stacks.Descent

open AlgebraicGeometry CategoryTheory.MorphismProperty

/-- Closed immersions satisfy fppf descent: if the base change of `g` along a surjective flat
morphism locally of finite presentation is a closed immersion, then so is `g`. -/
@[sga "1 VIII 5.5" "special case", sga "3 IV 4.7" "special case"]
theorem isClosedImmersion_descendsAlong_fppf :
    MorphismProperty.DescendsAlong (@IsClosedImmersion : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
  AlgebraicGeometry.descendsAlong_fppf_of _

/-- Immersions of schemes satisfy fppf descent: if the base change of `g : Y ⟶ Z` along a
surjective flat morphism `c : X ⟶ Z` locally of finite presentation is an immersion, then so is
`g`. -/
@[ega "II 3.8.1" "Immersion clause"]
theorem isImmersion_descendsAlong_fppf :
    MorphismProperty.DescendsAlong (@IsImmersion : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) := by
  have := isClosedImmersion_descendsAlong_fppf.{u}
  have : MorphismProperty.RespectsIso (@IsImmersion : MorphismProperty Scheme.{u}) :=
    MorphismProperty.RespectsIso.mk _
      (fun _ f hf => by have : IsImmersion f := hf; infer_instance)
      (fun _ f hf => by have : IsImmersion f := hf; infer_instance)
  refine MorphismProperty.DescendsAlong.mk' ?_
  intro X Y Z c g _ hQ himm
  obtain ⟨⟨hsurj, hflat⟩, hfp⟩ := hQ
  have _ : Surjective c := hsurj
  have _ : Flat c := hflat
  have _ : LocallyOfFinitePresentation c := hfp
  have _ : UniversallyOpen c := UniversallyOpen.of_flat c
  have _ : IsImmersion (pullback.fst c g) := himm
  have ho : IsOpenMap c.base := c.isOpenMap
  have hs : Function.Surjective c.base := hsurj.surj
  have hcob : coborder (Set.range (pullback.fst c g).base)
      = c.base ⁻¹' coborder (Set.range g.base) := by
    rw [Scheme.Pullback.range_fst c g, coborder_preimage ho c.continuous]
  have hopen : IsOpen (coborder (Set.range g.base)) := by
    have h1 : IsOpen (c.base ⁻¹' coborder (Set.range g.base)) := by
      rw [← hcob]
      exact (pullback.fst c g).isLocallyClosed_range.isOpen_coborder
    have h2 := ho _ h1
    rwa [Set.image_preimage_eq _ hs] at h2
  set U : Z.Opens := ⟨coborder (Set.range g.base), hopen⟩
  have hsub : Set.range g.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]; exact subset_coborder
  set gU : Y ⟶ U.toScheme := IsOpenImmersion.lift U.ι g hsub
  have hfac : gU ≫ U.ι = g := IsOpenImmersion.lift_fac _ _ _
  have hpre : c ⁻¹ᵁ U = (pullback.fst c g).coborderRange := TopologicalSpace.Opens.ext hcob.symm
  have hQU : (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation :
      MorphismProperty Scheme.{u}) (c ∣_ U) :=
    ⟨⟨MorphismProperty.of_isPullback (isPullback_morphismRestrict c U).flip hsurj,
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U).flip hflat⟩,
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U).flip hfp⟩
  have key : ∀ V : X.Opens, V = (pullback.fst c g).coborderRange →
      ∀ m : pullback c g ⟶ V.toScheme, m ≫ V.ι = pullback.fst c g → IsClosedImmersion m := by
    rintro V rfl m hm
    have : m = (pullback.fst c g).liftCoborder := by
      rw [← cancel_mono (pullback.fst c g).coborderRange.ι, hm, Scheme.Hom.liftCoborder_ι]
    rw [this]
    infer_instance
  have t : IsPullback ((c ⁻¹ᵁ U).ι) (c ∣_ U) c U.ι :=
    (isPullback_morphismRestrict c U).flip
  have big : IsPullback (pullback.fst c g) (pullback.snd c g) c (gU ≫ U.ι) := by
    rw [hfac]; exact IsPullback.of_hasPullback c g
  have hci : IsClosedImmersion gU :=
    of_isPullback_of_descendsAlong (P := @IsClosedImmersion)
      (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) (IsPullback.of_right' big t) hQU
      (key _ hpre _ (t.lift_fst _ _ _))
  rw [← hfac]
  infer_instance

end Stacks.Descent

namespace Stacks.SeparationLocal

variable {C : Type*} [Category C] [HasPullbacks C]

section Diag

variable [HasBinaryProducts C]

/-- The canonical map from the relative diagonal object of `f : X ⟶ Y` to `X ⨯ X`. -/
noncomputable abbrev toProd {X Y : C} (f : X ⟶ Y) : pullback f f ⟶ X ⨯ X :=
  prod.lift (pullback.fst f f) (pullback.snd f f)

/-- The relative diagonal of `f : X ⟶ Y` is the base change of the absolute diagonal of `X`
along the canonical map `X ×[Y] X ⟶ X ⨯ X`. -/
theorem isPullback_diagonal_diag {X Y : C} (f : X ⟶ Y) :
    IsPullback (pullback.diagonal f) (𝟙 X) (toProd f) (diag X) := by
  have w : CommSq (pullback.diagonal f) (𝟙 X) (toProd f) (diag X) := ⟨by ext <;> simp⟩
  refine IsPullback.of_isLimit' w (PullbackCone.IsLimit.mk w.w (fun s => s.snd) ?_ ?_ ?_)
  · intro s
    have h1 := s.condition =≫ Limits.prod.fst
    have h2 := s.condition =≫ Limits.prod.snd
    simp only [Category.assoc, prod.lift_fst, prod.lift_snd] at h1 h2
    refine pullback.hom_ext ?_ ?_
    · simpa using h1.symm
    · simpa using h2.symm
  · intro s; simp
  · intro s m _ h₂; simpa using h₂

end Diag

/-- The canonical map `(X ×[Y] Z) ×[Z] (X ×[Y] Z) ⟶ X ×[Y] X` comparing the relative
diagonal object of a base change with that of the original morphism. -/
noncomputable def diagonalObjMap {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ Y) :
    pullback (pullback.snd f g) (pullback.snd f g) ⟶ pullback f f :=
  pullback.lift
    (pullback.fst (pullback.snd f g) (pullback.snd f g) ≫ pullback.fst f g)
    (pullback.snd (pullback.snd f g) (pullback.snd f g) ≫ pullback.fst f g)
    (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc,
      ← Category.assoc, pullback.condition])

/-- `diagonalObjMap f g` followed by the first projection of `X ×[Y] X`. -/
@[simp]
theorem diagonalObjMap_fst {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ Y) :
    diagonalObjMap f g ≫ pullback.fst f f =
      pullback.fst (pullback.snd f g) (pullback.snd f g) ≫ pullback.fst f g :=
  pullback.lift_fst _ _ _

/-- `diagonalObjMap f g` followed by the second projection of `X ×[Y] X`. -/
@[simp]
theorem diagonalObjMap_snd {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ Y) :
    diagonalObjMap f g ≫ pullback.snd f f =
      pullback.snd (pullback.snd f g) (pullback.snd f g) ≫ pullback.fst f g :=
  pullback.lift_snd _ _ _

/-- For `f : X ⟶ Y` and `g : Z ⟶ Y`, the relative diagonal of the projection `X ×[Y] Z ⟶ Z` is the
base change of the relative diagonal of `f` along `diagonalObjMap f g`. -/
theorem isPullback_diagonal_pullbackSnd {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ Y) :
    IsPullback (pullback.fst f g) (pullback.diagonal (pullback.snd f g))
      (pullback.diagonal f) (diagonalObjMap f g) := by
  have w : CommSq (pullback.fst f g) (pullback.diagonal (pullback.snd f g))
      (pullback.diagonal f) (diagonalObjMap f g) := ⟨by ext <;> simp⟩
  have key : ∀ s : PullbackCone (pullback.diagonal f) (diagonalObjMap f g),
      s.fst = s.snd ≫ pullback.fst (pullback.snd f g) (pullback.snd f g) ≫
        pullback.fst f g := fun s => by simpa using s.condition =≫ pullback.fst f f
  have key2 : ∀ s : PullbackCone (pullback.diagonal f) (diagonalObjMap f g),
      s.fst = s.snd ≫ pullback.snd (pullback.snd f g) (pullback.snd f g) ≫
        pullback.fst f g := fun s => by simpa using s.condition =≫ pullback.snd f f
  have cond : ∀ s : PullbackCone (pullback.diagonal f) (diagonalObjMap f g),
      s.fst ≫ f = (s.snd ≫ pullback.fst (pullback.snd f g) (pullback.snd f g) ≫
        pullback.snd f g) ≫ g := by
    intro s
    rw [key s]
    simp only [Category.assoc]
    rw [pullback.condition]
  refine IsPullback.of_isLimit' w (PullbackCone.IsLimit.mk w.w
    (fun s => pullback.lift s.fst (s.snd ≫ pullback.fst (pullback.snd f g)
      (pullback.snd f g) ≫ pullback.snd f g) (cond s))
    (fun s => pullback.lift_fst _ _ _) ?_ ?_)
  · intro s
    have e1 : s.snd ≫ pullback.fst (pullback.snd f g) (pullback.snd f g)
        = pullback.lift s.fst (s.snd ≫ pullback.fst (pullback.snd f g)
            (pullback.snd f g) ≫ pullback.snd f g) (cond s) :=
      pullback.hom_ext (by simp only [pullback.lift_fst, Category.assoc]; exact (key s).symm)
        (by rw [pullback.lift_snd, Category.assoc])
    have e2 : s.snd ≫ pullback.snd (pullback.snd f g) (pullback.snd f g)
        = pullback.lift s.fst (s.snd ≫ pullback.fst (pullback.snd f g)
            (pullback.snd f g) ≫ pullback.snd f g) (cond s) :=
      pullback.hom_ext (by simp only [pullback.lift_fst, Category.assoc]; exact (key2 s).symm)
        (by simp only [pullback.lift_snd, Category.assoc]; rw [← pullback.condition])
    exact pullback.hom_ext (by simpa using e1.symm) (by simpa using e2.symm)
  · intro s m h₁ h₂
    have hm : m = s.snd ≫ pullback.fst (pullback.snd f g) (pullback.snd f g) := by
      rw [← h₂]; simp
    refine pullback.hom_ext ?_ ?_
    · exact h₁.trans (pullback.lift_fst _ _ _).symm
    · rw [hm, Category.assoc, pullback.lift_snd]

/-- A morphism `h : T ⟶ X ×[Y] X` whose composite to `Y` factors through `g : Z ⟶ Y` factors
through the comparison morphism `diagonalObjMap f g`, hence through the relative diagonal
object of the base change `X ×[Y] Z ⟶ Z`. -/
theorem exists_lift_diagonalObjMap {X Y Z T : C} (f : X ⟶ Y) (g : Z ⟶ Y)
    (h : T ⟶ pullback f f) (k : T ⟶ Z) (w : h ≫ pullback.fst f f ≫ f = k ≫ g) :
    ∃ h' : T ⟶ pullback (pullback.snd f g) (pullback.snd f g),
      h' ≫ diagonalObjMap f g = h := by
  have w1 : (h ≫ pullback.fst f f) ≫ f = k ≫ g := (Category.assoc _ _ _).trans w
  have w2 : (h ≫ pullback.snd f f) ≫ f = k ≫ g := by
    rw [Category.assoc, ← pullback.condition]; exact w
  have w3 : pullback.lift (h ≫ pullback.fst f f) k w1 ≫ pullback.snd f g =
      pullback.lift (h ≫ pullback.snd f f) k w2 ≫ pullback.snd f g := by
    rw [pullback.lift_snd, pullback.lift_snd]
  refine ⟨pullback.lift _ _ w3, pullback.hom_ext ?_ ?_⟩
  · rw [Category.assoc, diagonalObjMap_fst, pullback.lift_fst_assoc, pullback.lift_fst]
  · rw [Category.assoc, diagonalObjMap_snd, pullback.lift_snd_assoc, pullback.lift_fst]

/-- The fibre product of a morphism `h'` into the relative diagonal object of a base change
`X ×[Y] Z ⟶ Z` with the relative diagonal of that base change, read as the fibre product of
the composite `h' ≫ diagonalObjMap f g` with the relative diagonal of `f`. -/
theorem isPullback_pullback_diagonalObjMap {X Y Z T : C} (f : X ⟶ Y) (g : Z ⟶ Y)
    (h' : T ⟶ pullback (pullback.snd f g) (pullback.snd f g)) :
    IsPullback (pullback.fst h' (pullback.diagonal (pullback.snd f g)))
      (pullback.snd h' (pullback.diagonal (pullback.snd f g)) ≫ pullback.fst f g)
      (h' ≫ diagonalObjMap f g) (pullback.diagonal f) :=
  (((IsPullback.of_hasPullback h' (pullback.diagonal (pullback.snd f g))).flip).paste_horiz
    (isPullback_diagonal_pullbackSnd f g)).flip

/-- If `h' ≫ diagonalObjMap f g = h`, then the fibre product of `h` with the relative diagonal of
`f` is the fibre product of `h'` with the relative diagonal of the base change `X ×[Y] Z ⟶ Z`. -/
theorem isPullback_of_lift_diagonalObjMap {X Y Z T : C} (f : X ⟶ Y) (g : Z ⟶ Y)
    {h : T ⟶ pullback f f} {h' : T ⟶ pullback (pullback.snd f g) (pullback.snd f g)}
    (hfac : h' ≫ diagonalObjMap f g = h) :
    IsPullback (pullback.fst h' (pullback.diagonal (pullback.snd f g)))
      (pullback.snd h' (pullback.diagonal (pullback.snd f g)) ≫ pullback.fst f g)
      h (pullback.diagonal f) :=
  hfac ▸ isPullback_pullback_diagonalObjMap f g h'

/-- A functor which preserves fibre products carries the relative diagonal of a morphism to the
relative diagonal of its image, read through the comparison isomorphism. -/
theorem map_pullback_diagonal {D : Type*} [Category D] [HasPullbacks D] (F : C ⥤ D)
    [PreservesLimitsOfShape WalkingCospan F] {a b : C} (m : a ⟶ b) :
    F.map (pullback.diagonal m) ≫ (PreservesPullback.iso F m m).hom =
      pullback.diagonal (F.map m) := by
  refine pullback.hom_ext ?_ ?_ <;> simp [← Functor.map_comp]

section Site

open AlgebraicGeometry

/-- A morphism which fits into a pullback square over `f` and `iY` has the same properties as
the chosen pullback projection `pullback.snd f iY`. -/
theorem prop_pullback_snd {P : MorphismProperty Scheme.{u}} [P.RespectsIso]
    {X Y UX UY : Scheme.{u}} {f : X ⟶ Y} {iY : UY ⟶ Y}
    {iX : UX ⟶ X} {f' : UX ⟶ UY} (sq : IsPullback iX f' f iY) (h : P f') :
    P (pullback.snd f iY) :=
  (P.arrow_mk_iso_iff (Arrow.isoMk (sq.isoIsPullback X UY (IsPullback.of_hasPullback f iY))
    (Iso.refl UY) (by simp))).mp h

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An open subscheme of the scheme underlying an object `a` of the big fppf site over `S`,
viewed again as an object of that site. -/
def openObj (a : BigFppfOver B S hS) {U : Scheme.{u}}
    (p : U ⟶ (BigFppfOver.toScheme B S hS).obj a)
    [AlgebraicGeometry.IsOpenImmersion p] : BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk (p ≫ a.hom.hom) :
    (⟨U, Scheme.size_lt_of_isOpenImmersion p a.left.property⟩ : B.Schemes) ⟶ B.obj hS)

/-- The canonical morphism of the site from an open subscheme to the ambient object. -/
def openObjHom (a : BigFppfOver B S hS) {U : Scheme.{u}}
    (p : U ⟶ (BigFppfOver.toScheme B S hS).obj a)
    [AlgebraicGeometry.IsOpenImmersion p] : openObj B S hS a p ⟶ a :=
  Over.homMk (ObjectProperty.homMk p) rfl

/-- The scheme underlying `openObj B S hS a p` is the source of `p`. -/
theorem toScheme_obj_openObj (a : BigFppfOver B S hS) {U : Scheme.{u}}
    (p : U ⟶ (BigFppfOver.toScheme B S hS).obj a) [AlgebraicGeometry.IsOpenImmersion p] :
    (BigFppfOver.toScheme B S hS).obj (openObj B S hS a p) = U := rfl

/-- The morphism of schemes underlying `openObjHom B S hS a p` is `p`. -/
theorem toScheme_map_openObjHom (a : BigFppfOver B S hS) {U : Scheme.{u}}
    (p : U ⟶ (BigFppfOver.toScheme B S hS).obj a) [AlgebraicGeometry.IsOpenImmersion p] :
    (BigFppfOver.toScheme B S hS).map (openObjHom B S hS a p) = p := rfl

/-- If the source `X` of `f : X ⟶ Y` is an algebraic space over `S`, then the relative diagonal of
`f` is representable. -/
theorem relativelyRepresentable_diagonal {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) :
    yoneda.relativelyRepresentable (pullback.diagonal f) :=
  (Functor.relativelyRepresentable.isStableUnderBaseChange
    (yoneda (C := BigFppfOver B S hS))).of_isPullback
      (isPullback_diagonal_diag f).flip hX.diagonal_representable

/-- If `P` holds for the represented base change of `u` along `yoneda.map φ ≫ g`, then it holds for
the base change of `hu.snd g` along `φ`. -/
private theorem pullback_snd_of_snd_yoneda_map {P : MorphismProperty Scheme.{u}} [P.RespectsIso]
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {u : F ⟶ G}
    (hu : yoneda.relativelyRepresentable u) {a' a : BigFppfOver B S hS} (φ : a' ⟶ a)
    (g : yoneda.obj a ⟶ G)
    (h : P ((BigFppfOver.toScheme B S hS).map (hu.snd (yoneda.map φ ≫ g)))) :
    P (pullback.snd ((BigFppfOver.toScheme B S hS).map (hu.snd g))
      ((BigFppfOver.toScheme B S hS).map φ)) := by
  have sq := IsPullback.of_right' (hu.isPullback (yoneda.map φ ≫ g)) (hu.isPullback g)
  obtain ⟨l, hl⟩ := (yoneda (C := BigFppfOver B S hS)).map_surjective
    ((hu.isPullback g).lift (hu.fst (yoneda.map φ ≫ g))
      (yoneda.map (hu.snd (yoneda.map φ ≫ g)) ≫ yoneda.map φ)
      (by rw [(hu.isPullback (yoneda.map φ ≫ g)).w, Category.assoc]))
  rw [← hl] at sq
  exact prop_pullback_snd
    ((sq.of_map_of_faithful (yoneda (C := BigFppfOver B S hS))).map
      (BigFppfOver.toScheme B S hS)) h

/-- Let `P` be a property of morphisms of schemes which is Zariski local on the target and let `u`
be a representable morphism of presheaves on the big fppf site of `S`. If every base change of `u`
along an object of the site whose underlying scheme is affine has `P`, then so does every base
change of `u`. -/
theorem presheaf_of_affine {P : MorphismProperty Scheme.{u}}
    [AlgebraicGeometry.IsZariskiLocalAtTarget P]
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {u : F ⟶ G}
    (hu : yoneda.relativelyRepresentable u)
    (H : ∀ (a : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj a) →
      ∀ (g : yoneda.obj a ⟶ G),
        P ((BigFppfOver.toScheme B S hS).map (hu.snd g))) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf u := by
  have : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine MorphismProperty.relative_of_snd hu (fun a g => ?_)
  change P ((BigFppfOver.toScheme B S hS).map (hu.snd g))
  refine AlgebraicGeometry.IsZariskiLocalAtTarget.of_openCover
    ((BigFppfOver.toScheme B S hS).obj a).affineCover fun j => ?_
  refine pullback_snd_of_snd_yoneda_map B S hS hu (openObjHom B S hS a
    (((BigFppfOver.toScheme B S hS).obj a).affineCover.f j)) g
    (H (openObj B S hS a (((BigFppfOver.toScheme B S hS).obj a).affineCover.f j)) ?_ _)
  change IsAffine (((BigFppfOver.toScheme B S hS).obj a).affineCover.X j)
  infer_instance

/-- The property of a morphism of presheaves on the big fppf site of `S` that its relative diagonal
has `P` after every represented base change. -/
abbrev DiagonalProp (P : MorphismProperty Scheme.{u})
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) : Prop :=
  (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf
    (pullback.diagonal f)

/-- `DiagonalProp` is stable under base change. -/
theorem DiagonalProp.pullbackSnd {P : MorphismProperty Scheme.{u}}
    [AlgebraicGeometry.IsZariskiLocalAtTarget P]
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} (g : Z ⟶ Y)
    (h : DiagonalProp B S hS P f) : DiagonalProp B S hS P (pullback.snd f g) := by
  have h1 : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have h2 := MorphismProperty.relative_isStableUnderBaseChange
    (F := yoneda (C := BigFppfOver B S hS))
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS))
  exact (MorphismProperty.IsStableUnderBaseChange.diagonal
    (P := (MorphismProperty.inverseImage P
      (BigFppfOver.toScheme B S hS)).presheaf)).of_isPullback
      (IsPullback.of_hasPullback f g) h

/-- Let `h : h_b ⟶ X ×[Y] X` be a morphism whose composite to `Y` factors through `g : Z ⟶ Y` by
`k`. If the base change of `f` along `g` has `DiagonalProp P`, then the represented base change of
the relative diagonal of `f` along `h` has `P`. -/
theorem DiagonalProp.prop_snd_of_factorization {P : MorphismProperty Scheme.{u}}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {g : Z ⟶ Y}
    (hP : DiagonalProp B S hS P (pullback.snd f g))
    (hu : yoneda.relativelyRepresentable (pullback.diagonal f))
    {b : BigFppfOver B S hS} (h : yoneda.obj b ⟶ pullback f f) (k : yoneda.obj b ⟶ Z)
    (w : h ≫ pullback.fst f f ≫ f = k ≫ g) :
    P ((BigFppfOver.toScheme B S hS).map (hu.snd h)) := by
  obtain ⟨h', hfac⟩ := exists_lift_diagonalObjMap f g h k w
  have s : IsPullback (hu.fst h) (yoneda.map (hu.snd h)) (pullback.diagonal f)
      (h' ≫ diagonalObjMap f g) := hfac ▸ hu.isPullback h
  exact hP.property h' _ _ (IsPullback.of_right' s (isPullback_diagonal_pullbackSnd f g))

/-- If the source of `f` is an algebraic space over `S` and every base change of `f` along an
object of the site with affine underlying scheme has `DiagonalProp P`, then so does `f`. -/
theorem DiagonalProp.of_affine {P : MorphismProperty Scheme.{u}}
    [AlgebraicGeometry.IsZariskiLocalAtTarget P]
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y}
    (H : ∀ (a : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj a) →
      ∀ (g : yoneda.obj a ⟶ Y), DiagonalProp B S hS P (pullback.snd f g)) :
    DiagonalProp B S hS P f :=
  presheaf_of_affine B S hS (relativelyRepresentable_diagonal B S hS hX f) fun a ha h =>
    DiagonalProp.prop_snd_of_factorization B S hS
      (H a ha (h ≫ pullback.fst f f ≫ f)) _ h (𝟙 (yoneda.obj a)) (Category.id_comp _).symm

/-- Let `f : X ⟶ Y` have algebraic source and let `g i : Z i ⟶ Y` be relatively representable
morphisms whose represented base changes jointly suffice to test `P`. If every base change of `f`
along a `g i` has `DiagonalProp P`, then so does `f`. -/
theorem DiagonalProp.of_cover {P : MorphismProperty Scheme.{u}} [P.RespectsIso] {I : Type*}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Z : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y} {g : ∀ i, Z i ⟶ Y}
    (hg : ∀ i, yoneda.relativelyRepresentable (g i))
    (hloc : ∀ (a : BigFppfOver B S hS) (g₀ : yoneda.obj a ⟶ Y) {W : Scheme.{u}}
      (q : W ⟶ (BigFppfOver.toScheme B S hS).obj a),
      (∀ i, P (pullback.snd q ((BigFppfOver.toScheme B S hS).map ((hg i).snd g₀)))) → P q)
    (hP : ∀ i, DiagonalProp B S hS P (pullback.snd f (g i))) :
    DiagonalProp B S hS P f := by
  have : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hu := relativelyRepresentable_diagonal B S hS hX f
  refine MorphismProperty.relative_of_snd hu (fun a h => ?_)
  refine hloc a (h ≫ pullback.fst f f ≫ f) _ (fun i => ?_)
  have w : (yoneda.map ((hg i).snd (h ≫ pullback.fst f f ≫ f)) ≫ h) ≫
      pullback.fst f f ≫ f = (hg i).fst (h ≫ pullback.fst f f ≫ f) ≫ g i := by
    rw [Category.assoc, ← (hg i).w]
  have hb := DiagonalProp.prop_snd_of_factorization B S hS (hP i) hu
    (yoneda.map ((hg i).snd (h ≫ pullback.fst f f ≫ f)) ≫ h) _ w
  exact pullback_snd_of_snd_yoneda_map B S hS hu ((hg i).snd _) h hb

/-- Let `P` be fppf local on the target. If the base change of `f` along a surjective étale
morphism `g : h_V ⟶ Y` has `DiagonalProp P`, then so does `f`. -/
theorem DiagonalProp.of_etaleChart {P : MorphismProperty Scheme.{u}}
    [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y}
    {V : BigFppfOver B S hS} {g : yoneda.obj V ⟶ Y}
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (hP : DiagonalProp B S hS P (pullback.snd f g)) :
    DiagonalProp B S hS P f := by
  refine DiagonalProp.of_cover B S hS (I := PUnit.{u + 1}) hX
    (g := fun _ => g) (fun _ => hsurj.rep) ?_ (fun _ => hP)
  intro a g₀ W q hq
  have hsur : AlgebraicGeometry.Surjective
      ((BigFppfOver.toScheme B S hS).map (hsurj.rep.snd g₀)) := hsurj.property_snd g₀
  have het : AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map (hsurj.rep.snd g₀)) :=
    hetale.property g₀ _ _ (hsurj.rep.isPullback g₀)
  obtain ⟨hfl, -, hfp⟩ := AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified.mp het
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (Scheme.Hom.singleton_mem_fppfPrecoverage
      ((BigFppfOver.toScheme B S hS).map (hsurj.rep.snd g₀))) ?_
  rintro U g' _ ⟨⟩
  exact hq PUnit.unit

/-- Let `P` respect isomorphisms and descend along surjective flat morphisms locally of finite
presentation. If the base change of `f` along a surjective étale morphism `g : h_V ⟶ Y` has
`DiagonalProp P`, then so does `f`. -/
theorem DiagonalProp.of_etaleChart_of_descendsAlong {P : MorphismProperty Scheme.{u}}
    [P.RespectsIso]
    [P.DescendsAlong (@AlgebraicGeometry.Surjective ⊓ @AlgebraicGeometry.Flat ⊓
      @AlgebraicGeometry.LocallyOfFinitePresentation)]
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y}
    {V : BigFppfOver B S hS} {g : yoneda.obj V ⟶ Y}
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (hP : DiagonalProp B S hS P (pullback.snd f g)) :
    DiagonalProp B S hS P f := by
  refine DiagonalProp.of_cover B S hS (I := PUnit.{u + 1}) hX
    (g := fun _ => g) (fun _ => hsurj.rep) ?_ (fun _ => hP)
  intro a g₀ W q hq
  have hsur : AlgebraicGeometry.Surjective
      ((BigFppfOver.toScheme B S hS).map (hsurj.rep.snd g₀)) := hsurj.property_snd g₀
  have het : AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map (hsurj.rep.snd g₀)) :=
    hetale.property g₀ _ _ (hsurj.rep.isPullback g₀)
  obtain ⟨hfl, -, -⟩ := AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified.mp het
  have _ : AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map (hsurj.rep.snd g₀)) := het
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (Q := @AlgebraicGeometry.Surjective ⊓ @AlgebraicGeometry.Flat ⊓
      @AlgebraicGeometry.LocallyOfFinitePresentation)
    ⟨⟨hsur, hfl⟩, inferInstance⟩ (hq PUnit.unit)

/-- Let `P` be Zariski local on the target. If the base change of `f` along every member of a
Zariski covering of `Y` has `DiagonalProp P`, then so does `f`. -/
theorem DiagonalProp.of_zariskiCover {P : MorphismProperty Scheme.{u}}
    [AlgebraicGeometry.IsZariskiLocalAtTarget P]
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y}
    {I : Type u} {U : I → Subfunctor Y} (hU : Space.IsZariskiCover B S hS I U)
    (hP : ∀ i, DiagonalProp B S hS P (pullback.snd f (U i).ι)) :
    DiagonalProp B S hS P f := by
  refine DiagonalProp.of_cover B S hS hX (g := fun i => (U i).ι)
    (fun i => (hU.1 i).2.rep) ?_ hP
  intro a g₀ W q hq
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (K := Scheme.zariskiPrecoverage)
    (R := Presieve.ofArrows
      (fun i => (BigFppfOver.toScheme B S hS).obj ((hU.1 i).2.rep.pullback g₀))
      (fun i => (BigFppfOver.toScheme B S hS).map ((hU.1 i).2.rep.snd g₀))) ?_ ?_
  · rw [Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨Space.exists_mem_range_of_isZariskiCover B S hS hU
      (fun i => (hU.1 i).2.rep) a g₀, fun i => (hU.1 i).2.property_snd g₀⟩
  · rintro Z g' _ ⟨i⟩
    exact hq i

/-- For a morphism `f : X ⟶ Y` of presheaves on the big fppf site of `S` with algebraic source,
`DiagonalProp P` holds for `f` if and only if it holds for every base change of `f` along an object
of the site with affine underlying scheme. -/
theorem diagonalProp_iff_affine {P : MorphismProperty Scheme.{u}}
    [AlgebraicGeometry.IsZariskiLocalAtTarget P]
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) :
    DiagonalProp B S hS P f ↔
      ∀ (a : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj a) →
        ∀ (g : yoneda.obj a ⟶ Y), DiagonalProp B S hS P (pullback.snd f g) :=
  ⟨fun h _ _ g => DiagonalProp.pullbackSnd B S hS g h, DiagonalProp.of_affine B S hS hX⟩

/-- For a morphism `f` with algebraic source, `DiagonalProp P` holds for `f` if and only if it
holds for every base change of `f` along an object of the site. -/
theorem diagonalProp_iff_all {P : MorphismProperty Scheme.{u}}
    [AlgebraicGeometry.IsZariskiLocalAtTarget P]
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) :
    DiagonalProp B S hS P f ↔
      ∀ (a : BigFppfOver B S hS) (g : yoneda.obj a ⟶ Y),
        DiagonalProp B S hS P (pullback.snd f g) :=
  ⟨fun h _ g => DiagonalProp.pullbackSnd B S hS g h,
    fun H => DiagonalProp.of_affine B S hS hX fun a _ g => H a g⟩

end Site

end Stacks.SeparationLocal

namespace AlgebraicGeometry.Space

open Stacks.SeparationLocal

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism `f : X ⟶ Y` with algebraic source is separated if and only if its base change along
every object of the site with affine underlying scheme is separated. -/
theorem isSeparated_iff_affine (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) :
    IsSeparated B S hS f ↔
      ∀ (T : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
        ∀ (g : yoneda.obj T ⟶ Y), IsSeparated B S hS (pullback.snd f g) :=
  diagonalProp_iff_affine B S hS hX f

/-- A morphism with algebraic source is separated if and only if its base change along every object
of the site is separated. -/
theorem isSeparated_iff_forall_pullback (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) :
    IsSeparated B S hS f ↔
      ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
        IsSeparated B S hS (pullback.snd f g) :=
  diagonalProp_iff_all B S hS hX f

/-- A morphism `f : X ⟶ Y` with algebraic source is locally separated if and only if its base
change along every object of the site with affine underlying scheme is locally separated. -/
theorem isLocallySeparated_iff_affine (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) :
    IsLocallySeparated B S hS f ↔
      ∀ (T : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
        ∀ (g : yoneda.obj T ⟶ Y), IsLocallySeparated B S hS (pullback.snd f g) :=
  diagonalProp_iff_affine B S hS hX f

/-- A morphism with algebraic source is locally separated if and only if its base change along
every object of the site is locally separated. -/
theorem isLocallySeparated_iff_forall_pullback (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) :
    IsLocallySeparated B S hS f ↔
      ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
        IsLocallySeparated B S hS (pullback.snd f g) :=
  diagonalProp_iff_all B S hS hX f

/-- A separated morphism stays separated after any base change. -/
@[stacks 03KL "separated_base_change"]
theorem isSeparated_pullbackSnd {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} (g : Z ⟶ Y)
    (h : IsSeparated B S hS f) : IsSeparated B S hS (pullback.snd f g) :=
  DiagonalProp.pullbackSnd B S hS g h

/-- A locally separated morphism stays locally separated after any base change. -/
theorem isLocallySeparated_pullbackSnd {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (g : Z ⟶ Y) (h : IsLocallySeparated B S hS f) :
    IsLocallySeparated B S hS (pullback.snd f g) :=
  DiagonalProp.pullbackSnd B S hS g h

/-! ### The surjective étale chart and the Zariski covering -/

/-- A separated morphism whose target is an algebraic space stays separated after base change along
some surjective étale scheme chart of its target. -/
theorem isSeparated_exists_etaleChart (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (h : IsSeparated B S hS f) :
    ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) g ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) g ∧
      IsSeparated B S hS (pullback.snd f g) :=
  let ⟨V, g, h₁, h₂⟩ := hY.exists_atlas
  ⟨V, g, h₁, h₂, isSeparated_pullbackSnd B S hS g h⟩

/-- A locally separated morphism whose target is an algebraic space stays locally separated after
base change along some surjective étale scheme chart of its target. -/
theorem isLocallySeparated_exists_etaleChart (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (h : IsLocallySeparated B S hS f) :
    ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) g ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) g ∧
      IsLocallySeparated B S hS (pullback.snd f g) :=
  let ⟨V, g, h₁, h₂⟩ := hY.exists_atlas
  ⟨V, g, h₁, h₂, isLocallySeparated_pullbackSnd B S hS g h⟩

/-- A separated morphism whose target is an algebraic space stays separated over the members of
some Zariski covering of its target. -/
theorem isSeparated_exists_zariskiCover (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (h : IsSeparated B S hS f) :
    ∃ (I : Type u) (U : I → Subfunctor Y), IsZariskiCover B S hS I U ∧
      ∀ i, IsSeparated B S hS (pullback.snd f (U i).ι) :=
  ⟨PUnit.{u + 1}, fun _ ↦ ⊤, isZariskiCover_top hY,
    fun _ ↦ isSeparated_pullbackSnd B S hS _ h⟩

/-- A locally separated morphism whose target is an algebraic space stays locally separated over
the members of some Zariski covering of its target. -/
theorem isLocallySeparated_exists_zariskiCover (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (h : IsLocallySeparated B S hS f) :
    ∃ (I : Type u) (U : I → Subfunctor Y), IsZariskiCover B S hS I U ∧
      ∀ i, IsLocallySeparated B S hS (pullback.snd f (U i).ι) :=
  ⟨PUnit.{u + 1}, fun _ ↦ ⊤, isZariskiCover_top hY,
    fun _ ↦ isLocallySeparated_pullbackSnd B S hS _ h⟩

/-- If the base change of `f` along a surjective étale morphism from a representable presheaf is
separated, then so is `f`. -/
theorem isSeparated_of_etaleChart (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y}
    {V : BigFppfOver B S hS} {g : yoneda.obj V ⟶ Y}
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (h : IsSeparated B S hS (pullback.snd f g)) :
    IsSeparated B S hS f :=
  have := Stacks.Descent.isLocalAtTarget_fppfPrecoverage
    (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u})
  DiagonalProp.of_etaleChart B S hS hX hsurj hetale h

/-- A morphism with algebraic source and algebraic target is separated if and only if there is a
surjective étale scheme chart of the target along which its base change is separated. -/
theorem isSeparated_iff_exists_etaleChart (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsSeparated B S hS f ↔
      ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        IsSeparated B S hS (pullback.snd f g) :=
  ⟨isSeparated_exists_etaleChart B S hS hY,
    fun ⟨_, _, hsurj, hetale, h⟩ => isSeparated_of_etaleChart B S hS hX hsurj hetale h⟩

/-- Immersions of schemes respect isomorphisms. -/
private instance respectsIso_isImmersion :
    MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) :=
  MorphismProperty.RespectsIso.mk _
    (fun _ f hf => by have : _root_.AlgebraicGeometry.IsImmersion f := hf; infer_instance)
    (fun _ f hf => by have : _root_.AlgebraicGeometry.IsImmersion f := hf; infer_instance)

/-- If the base change of `f` along a surjective étale morphism from a representable presheaf is
locally separated, then so is `f`. -/
theorem isLocallySeparated_of_etaleChart (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y}
    {V : BigFppfOver B S hS} {g : yoneda.obj V ⟶ Y}
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (h : IsLocallySeparated B S hS (pullback.snd f g)) :
    IsLocallySeparated B S hS f :=
  have := Stacks.Descent.isImmersion_descendsAlong_fppf.{u}
  DiagonalProp.of_etaleChart_of_descendsAlong B S hS hX hsurj hetale h

/-- A morphism with algebraic source and algebraic target is locally separated if and only if there
is a surjective étale scheme chart of the target along which its base change is locally
separated. -/
theorem isLocallySeparated_iff_exists_etaleChart (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsLocallySeparated B S hS f ↔
      ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        IsLocallySeparated B S hS (pullback.snd f g) :=
  ⟨isLocallySeparated_exists_etaleChart B S hS hY,
    fun ⟨_, _, hsurj, hetale, h⟩ => isLocallySeparated_of_etaleChart B S hS hX hsurj hetale h⟩

/-- If the base change of `f` along every member of a Zariski covering of its target is separated,
then so is `f`. -/
theorem isSeparated_of_zariskiCover (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y}
    {I : Type u} {U : I → Subfunctor Y} (hU : IsZariskiCover B S hS I U)
    (h : ∀ i, IsSeparated B S hS (pullback.snd f (U i).ι)) :
    IsSeparated B S hS f :=
  DiagonalProp.of_zariskiCover B S hS hX hU h

/-- If the base change of `f` along every member of a Zariski covering of its target is locally
separated, then so is `f`. -/
theorem isLocallySeparated_of_zariskiCover (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y}
    {I : Type u} {U : I → Subfunctor Y} (hU : IsZariskiCover B S hS I U)
    (h : ∀ i, IsLocallySeparated B S hS (pullback.snd f (U i).ι)) :
    IsLocallySeparated B S hS f :=
  DiagonalProp.of_zariskiCover B S hS hX hU h

/-- A morphism with algebraic source and algebraic target is separated if and only if there is a
Zariski covering of the target over whose members its base changes are separated. -/
theorem isSeparated_iff_exists_zariskiCover (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsSeparated B S hS f ↔
      ∃ (I : Type u) (U : I → Subfunctor Y), IsZariskiCover B S hS I U ∧
        ∀ i, IsSeparated B S hS (pullback.snd f (U i).ι) :=
  ⟨isSeparated_exists_zariskiCover B S hS hY,
    fun ⟨_, _, hU, h⟩ => isSeparated_of_zariskiCover B S hS hX hU h⟩

/-- A morphism with algebraic source and algebraic target is locally separated if and only if there
is a Zariski covering of the target over whose members its base changes are locally separated. -/
theorem isLocallySeparated_iff_exists_zariskiCover (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsLocallySeparated B S hS f ↔
      ∃ (I : Type u) (U : I → Subfunctor Y), IsZariskiCover B S hS I U ∧
        ∀ i, IsLocallySeparated B S hS (pullback.snd f (U i).ι) :=
  ⟨isLocallySeparated_exists_zariskiCover B S hS hY,
    fun ⟨_, _, hU, h⟩ => isLocallySeparated_of_zariskiCover B S hS hX hU h⟩

/-! ### Quasi-separatedness -/

/-- Quasi-compactness of an algebraic space over `S` transfers along an isomorphism of
presheaves. -/
theorem IsQuasiCompactSpace.of_iso {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (h : IsQuasiCompactSpace B S hS F) (e : F ≅ F') : IsQuasiCompactSpace B S hS F' := by
  obtain ⟨U, a, hU, hs, he⟩ := h
  refine ⟨U, a ≫ e.hom, hU, MorphismProperty.RespectsIso.postcomp _ e.hom a hs,
    fun V φ hφ => ?_⟩
  rw [← Category.assoc]
  exact MorphismProperty.RespectsIso.postcomp _ e.hom _ (he V φ hφ)

/-- Quasi-compactness of a morphism of presheaves on the big fppf site is stable under base change:
if `d'` is a base change of `d` and `d` is quasi-compact, then so is `d'`. -/
theorem IsQuasiCompact.of_isPullback {F G F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {d : F ⟶ G} {d' : F' ⟶ G'} {t : F' ⟶ F} {m : G' ⟶ G} (sq : IsPullback t d' d m)
    (h : IsQuasiCompact B S hS d) : IsQuasiCompact B S hS d' := by
  intro Z hZ hqc g
  have hpb : IsPullback (pullback.fst g d') (pullback.snd g d' ≫ t) (g ≫ m) d :=
    (((IsPullback.of_hasPullback g d').flip).paste_horiz sq).flip
  exact (h Z hZ hqc (g ≫ m)).of_iso B S hS hpb.isoPullback.symm

/-- A quasi-separated morphism stays quasi-separated after any base change. -/
theorem isQuasiSeparated_pullbackSnd {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (g : Z ⟶ Y) (h : IsQuasiSeparated B S hS f) :
    IsQuasiSeparated B S hS (pullback.snd f g) :=
  IsQuasiCompact.of_isPullback B S hS (isPullback_diagonal_pullbackSnd f g) h

/-- Surjectivity of scheme morphisms, tested after every representable base change, contains
the identities and is stable under composition. -/
theorem isMultiplicative_presheaf_surjective :
    MorphismProperty.IsMultiplicative
      ((MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf) := by
  have h₁ : MorphismProperty.ContainsIdentities
      (@Surjective.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  have h₂ : MorphismProperty.IsStableUnderComposition
      (@Surjective.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have hI₁ : MorphismProperty.ContainsIdentities
      (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.ContainsIdentities.inverseImage (BigFppfOver.toScheme B S hS)
  have hI₂ : MorphismProperty.IsStableUnderComposition
      (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.IsStableUnderComposition.inverseImage (BigFppfOver.toScheme B S hS)
  have hI₃ : MorphismProperty.RespectsIso
      (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ (BigFppfOver.toScheme B S hS)
  have hI₄ : MorphismProperty.IsMultiplicative
      (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) := ⟨⟩
  exact ⟨⟩

/-- A representable presheaf whose underlying scheme is quasi-compact is a quasi-compact algebraic
space over `S`. -/
theorem isQuasiCompactSpace_yoneda_obj {U : BigFppfOver B S hS}
    (hU : CompactSpace ((BigFppfOver.toScheme B S hS).obj U)) :
    IsQuasiCompactSpace B S hS (yoneda.obj U) := by
  have := isMultiplicative_presheaf_surjective B S hS
  have := isMultiplicative_presheaf_etale B S hS
  exact ⟨U, 𝟙 (yoneda.obj U), hU, MorphismProperty.id_mem _ _,
    isEtale_of_presheaf_etale B S hS (MorphismProperty.id_mem _ _)⟩

/-- If `p : F ⟶ G` is surjective and étale after every representable base change and `F` is a
quasi-compact algebraic space over `S`, then so is `G`. -/
theorem IsQuasiCompactSpace.of_surjective_etale {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : F ⟶ G}
    (hs : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (he : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (h : IsQuasiCompactSpace B S hS F) : IsQuasiCompactSpace B S hS G := by
  have := isMultiplicative_presheaf_surjective B S hS
  have hmul := isMultiplicative_presheaf_etale B S hS
  obtain ⟨U, a, hU, has, hae⟩ := h
  refine ⟨U, a ≫ p, hU, MorphismProperty.comp_mem _ a p has hs, fun V φ hφ => ?_⟩
  rw [← Category.assoc]
  exact MorphismProperty.comp_mem _ (φ ≫ a) p (hae V φ hφ) he

/-- If every base change of `f` along a morphism from a representable presheaf is quasi-separated,
then `f` is quasi-separated. -/
theorem isQuasiSeparated_of_forall_pullback {f : X ⟶ Y}
    (H : ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
      IsQuasiSeparated B S hS (pullback.snd f g)) :
    IsQuasiSeparated B S hS f := by
  intro Z _ hqc g₀
  obtain ⟨U, a, hU, hasurj, haetale⟩ := hqc
  have hU' : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) := hU
  obtain ⟨h', hfac⟩ := exists_lift_diagonalObjMap f
    ((a ≫ g₀) ≫ pullback.fst f f ≫ f) (a ≫ g₀) (𝟙 (yoneda.obj U))
    (Category.id_comp _).symm
  have key := H U ((a ≫ g₀) ≫ pullback.fst f f ≫ f) (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS U) (isQuasiCompactSpace_yoneda_obj B S hS hU') h'
  have hqc1 := key.of_iso B S hS
    (isPullback_of_lift_diagonalObjMap f
      ((a ≫ g₀) ≫ pullback.fst f f ≫ f) hfac).isoPullback
  have sqA := IsPullback.of_right'
    (IsPullback.of_hasPullback (a ≫ g₀) (pullback.diagonal f)).flip
    (IsPullback.of_hasPullback g₀ (pullback.diagonal f)).flip
  exact IsQuasiCompactSpace.of_surjective_etale B S hS
    ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sqA.flip hasurj)
    ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sqA.flip
      (presheaf_etale_of_isEtale B S hS haetale)) hqc1

/-- A morphism of presheaves on the big fppf site of `S` is quasi-separated if and only if its base
change along every morphism from a representable presheaf is quasi-separated. -/
theorem isQuasiSeparated_iff_forall_pullback (f : X ⟶ Y) :
    IsQuasiSeparated B S hS f ↔
      ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
        IsQuasiSeparated B S hS (pullback.snd f g) :=
  ⟨fun h _ g => isQuasiSeparated_pullbackSnd B S hS g h,
    isQuasiSeparated_of_forall_pullback B S hS⟩

/-- A quasi-separated morphism whose target is an algebraic space stays quasi-separated after base
change along some surjective étale scheme chart of its target. -/
theorem isQuasiSeparated_exists_etaleChart (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (h : IsQuasiSeparated B S hS f) :
    ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) g ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) g ∧
      IsQuasiSeparated B S hS (pullback.snd f g) :=
  let ⟨V, g, h₁, h₂⟩ := hY.exists_atlas
  ⟨V, g, h₁, h₂, isQuasiSeparated_pullbackSnd B S hS g h⟩

/-- A quasi-separated morphism whose target is an algebraic space stays quasi-separated over the
members of some Zariski covering of its target. -/
theorem isQuasiSeparated_exists_zariskiCover (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (h : IsQuasiSeparated B S hS f) :
    ∃ (I : Type u) (U : I → Subfunctor Y), IsZariskiCover B S hS I U ∧
      ∀ i, IsQuasiSeparated B S hS (pullback.snd f (U i).ι) :=
  ⟨PUnit.{u + 1}, fun _ ↦ ⊤, isZariskiCover_top hY,
    fun _ ↦ isQuasiSeparated_pullbackSnd B S hS _ h⟩

/-! ### Separatedness over the terminal scheme -/

/-- Closed immersions of schemes are stable under composition. -/
private instance isStableUnderComposition_isClosedImmersion :
    MorphismProperty.IsStableUnderComposition
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsMultiplicative.toIsStableUnderComposition

/-- Isomorphisms of schemes are closed immersions. -/
private instance containsIdentities_isClosedImmersion :
    MorphismProperty.ContainsIdentities
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsMultiplicative.toContainsIdentities

/-- The closed-immersion property of a morphism of the site is stable under base change. -/
private instance isStableUnderBaseChange_inverseImage_isClosedImmersion :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
  BigFppfOver.isStableUnderBaseChange_inverseImage B S hS _

/-- The closed-immersion property of a morphism of the site contains the identities. -/
private instance containsIdentities_inverseImage_isClosedImmersion :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).ContainsIdentities :=
  MorphismProperty.ContainsIdentities.inverseImage _

/-- The closed-immersion property of a morphism of the site is stable under composition. -/
private instance isStableUnderComposition_inverseImage_isClosedImmersion :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
  MorphismProperty.IsStableUnderComposition.inverseImage _

/-- The closed-immersion property of a morphism of the site is multiplicative. -/
private instance isMultiplicative_inverseImage_isClosedImmersion :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsMultiplicative := ⟨⟩

/-- The representable closed-immersion property is stable under base change. -/
private instance isStableUnderBaseChange_closedImmersionPresheafProperty :
    (closedImmersionPresheafProperty B S hS).IsStableUnderBaseChange :=
  MorphismProperty.relative_isStableUnderBaseChange _

/-- Immersions of schemes are stable under composition. -/
private instance isStableUnderComposition_isImmersion :
    MorphismProperty.IsStableUnderComposition
      (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsMultiplicative.toIsStableUnderComposition

/-- Isomorphisms of schemes are immersions. -/
private instance containsIdentities_isImmersion :
    MorphismProperty.ContainsIdentities
      (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsMultiplicative.toContainsIdentities

/-- The immersion property of a morphism of the site is stable under base change. -/
private instance isStableUnderBaseChange_inverseImage_isImmersion :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
  BigFppfOver.isStableUnderBaseChange_inverseImage B S hS _

/-- The immersion property of a morphism of the site contains the identities. -/
private instance containsIdentities_inverseImage_isImmersion :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).ContainsIdentities :=
  MorphismProperty.ContainsIdentities.inverseImage _

/-- The immersion property of a morphism of the site is stable under composition. -/
private instance isStableUnderComposition_inverseImage_isImmersion :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
  MorphismProperty.IsStableUnderComposition.inverseImage _

/-- The immersion property of a morphism of the site is multiplicative. -/
private instance isMultiplicative_inverseImage_isImmersion :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsMultiplicative := ⟨⟩

/-- The representable immersion property is stable under base change. -/
private instance isStableUnderBaseChange_immersionPresheafProperty :
    (immersionPresheafProperty B S hS).IsStableUnderBaseChange :=
  MorphismProperty.relative_isStableUnderBaseChange _

/-- Separatedness of morphisms of algebraic spaces is stable under composition. -/
@[stacks 03KQ "separated"]
theorem isSeparated_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : F ⟶ G) (q : G ⟶ H)
    (hp : IsSeparated B S hS p) (hq : IsSeparated B S hS q) :
    IsSeparated B S hS (p ≫ q) :=
  MorphismProperty.comp_mem (closedImmersionPresheafProperty B S hS).diagonal p q hp hq

/-- An isomorphism of presheaves on the big fppf site of `S` is a separated morphism: its
relative diagonal is an isomorphism. -/
theorem isSeparated_of_isIso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ⟶ G) [IsIso e] :
    IsSeparated B S hS e := by
  have : IsIso (pullback.diagonal e) := (pullback.isIso_diagonal_iff e).2 inferInstance
  exact MorphismProperty.of_isIso (closedImmersionPresheafProperty B S hS) (pullback.diagonal e)

/-- Every morphism out of an algebraic space which is separated over `S` is separated. -/
@[stacks 04ZI "part (4)"]
theorem isSeparated_of_isSeparatedOver {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsSeparatedOver B S hS F) (p : F ⟶ G) : IsSeparated B S hS p :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := closedImmersionPresheafProperty B S hS)
    (Stacks.SeparationLocal.isPullback_diagonal_diag p).flip hF

/-- If the relative diagonal of a morphism `t` to a terminal presheaf has `P`, then so does the
diagonal of its source. -/
private theorem diag_of_diagonal_of_isTerminal
    {P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)} [P.RespectsIso]
    {F H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hH : IsTerminal H) (t : F ⟶ H)
    (h : P.diagonal t) : P (diag F) := by
  have hd : diag F = pullback.diagonal (terminal.from F) ≫ (prodIsoPullback F F).inv := by
    refine prod.hom_ext ?_ ?_ <;> simp
  have h' : P.diagonal (terminal.from F ≫ (terminalIsTerminal.uniqueUpToIso hH).hom) := by
    rw [← hH.hom_ext t (terminal.from F ≫ (terminalIsTerminal.uniqueUpToIso hH).hom)]
    exact h
  rw [hd]
  exact MorphismProperty.RespectsIso.postcomp P _ _
    ((MorphismProperty.cancel_right_of_respectsIso P.diagonal
      (terminal.from F) (terminalIsTerminal.uniqueUpToIso hH).hom).1 h')

/-- An algebraic space is separated over `S` if and only if its morphism to a terminal presheaf is
separated. -/
theorem isSeparatedOver_iff_isSeparated_of_isTerminal
    {F H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hH : IsTerminal H) (t : F ⟶ H) :
    IsSeparatedOver B S hS F ↔ IsSeparated B S hS t := by
  refine ⟨fun h => isSeparated_of_isSeparatedOver B S hS h t, fun h => ?_⟩
  exact diag_of_diagonal_of_isTerminal B S hS hH t h

/-- The morphism of presheaves represented by a morphism `m` of the site is separated if and only
if the underlying morphism of schemes is separated. -/
theorem isSeparated_yoneda_map_iff {a b : BigFppfOver B S hS} (m : a ⟶ b) :
    IsSeparated B S hS (yoneda.map m) ↔
      _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map m) := by
  have hyoneda : IsSeparated B S hS (yoneda.map m) ↔
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (pullback.diagonal m)) := by
    rw [← MorphismProperty.cancel_right_of_respectsIso
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf _
      (PreservesPullback.iso (yoneda (C := BigFppfOver B S hS)) m m).hom,
      map_pullback_diagonal]
  have hscheme : _root_.AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map (pullback.diagonal m)) ↔
      _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map m) := by
    rw [← MorphismProperty.cancel_right_of_respectsIso
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) _
      (PreservesPullback.iso (BigFppfOver.toScheme B S hS) m m).hom,
      map_pullback_diagonal, _root_.AlgebraicGeometry.isSeparated_iff]
  exact hyoneda.trans ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (pullback.diagonal m)).trans hscheme)

/-- A morphism of the site between objects with affine underlying schemes is separated. -/
theorem isSeparated_yoneda_map_of_isAffine {a b : BigFppfOver B S hS} (m : a ⟶ b)
    (ha : IsAffine ((BigFppfOver.toScheme B S hS).obj a))
    (hb : IsAffine ((BigFppfOver.toScheme B S hS).obj b)) :
    IsSeparated B S hS (yoneda.map m) :=
  (isSeparated_yoneda_map_iff B S hS m).2 <|
    have : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map m) :=
      @_root_.AlgebraicGeometry.isAffineHom_of_isAffine _ _ _ ha hb
    _root_.AlgebraicGeometry.IsSeparated.of_isAffineHom _

/-- Local separatedness of morphisms of algebraic spaces is stable under composition. -/
@[stacks 03KQ "locally separated"]
theorem isLocallySeparated_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : F ⟶ G) (q : G ⟶ H)
    (hp : IsLocallySeparated B S hS p) (hq : IsLocallySeparated B S hS q) :
    IsLocallySeparated B S hS (p ≫ q) :=
  MorphismProperty.comp_mem (immersionPresheafProperty B S hS).diagonal p q hp hq

/-- An isomorphism of presheaves on the big fppf site of `S` is a locally separated morphism:
its relative diagonal is an isomorphism. -/
theorem isLocallySeparated_of_isIso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ⟶ G)
    [IsIso e] : IsLocallySeparated B S hS e := by
  have : IsIso (pullback.diagonal e) := (pullback.isIso_diagonal_iff e).2 inferInstance
  exact MorphismProperty.of_isIso (immersionPresheafProperty B S hS) (pullback.diagonal e)

/-- Every morphism out of an algebraic space which is locally separated over `S` is locally
separated. -/
@[stacks 04ZI "part (5)"]
theorem isLocallySeparated_of_isLocallySeparatedOver {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsLocallySeparatedOver B S hS F) (p : F ⟶ G) : IsLocallySeparated B S hS p :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := immersionPresheafProperty B S hS)
    (Stacks.SeparationLocal.isPullback_diagonal_diag p).flip hF

/-- An algebraic space is locally separated over `S` if and only if its morphism to a terminal
presheaf is locally separated. -/
theorem isLocallySeparatedOver_iff_isLocallySeparated_of_isTerminal
    {F H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hH : IsTerminal H) (t : F ⟶ H) :
    IsLocallySeparatedOver B S hS F ↔ IsLocallySeparated B S hS t := by
  refine ⟨fun h => isLocallySeparated_of_isLocallySeparatedOver B S hS h t, fun h => ?_⟩
  exact diag_of_diagonal_of_isTerminal B S hS hH t h

/-- A morphism of the site between objects with affine underlying schemes is locally separated. -/
theorem isLocallySeparated_yoneda_map_of_isAffine {a b : BigFppfOver B S hS} (m : a ⟶ b)
    (ha : IsAffine ((BigFppfOver.toScheme B S hS).obj a))
    (hb : IsAffine ((BigFppfOver.toScheme B S hS).obj b)) :
    IsLocallySeparated B S hS (yoneda.map m) :=
  isLocallySeparated_of_isSeparated B S hS (isSeparated_yoneda_map_of_isAffine B S hS m ha hb)

/-! #### Relocalization to a larger base -/

section Relocalize

variable {S' : Scheme.{u}} (hS' : B.Contains S') (k : B.obj hS ⟶ B.obj hS')

/-- A closed immersion stays a closed immersion after relocalization to a larger base. -/
theorem isClosedImmersion_relocalize {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : F ⟶ G}
    (h : IsClosedImmersion B S hS p) :
    IsClosedImmersion B S' hS' ((OverShriek.relocalizePresheafFunctor k).map p) :=
  OverShriek.presheaf_map_relocalize _ (fun _ hk => hk) h

/-- A representable morphism which becomes a closed immersion after relocalization to a larger base
is a closed immersion. -/
theorem isClosedImmersion_of_relocalize {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : F ⟶ G}
    (hrep : yoneda.relativelyRepresentable p)
    (h : IsClosedImmersion B S' hS' ((OverShriek.relocalizePresheafFunctor k).map p)) :
    IsClosedImmersion B S hS p :=
  OverShriek.presheaf_of_presheaf_map_relocalize _ (fun _ hk => hk) hrep h

/-- A separated morphism stays separated after relocalization to a larger base. -/
theorem isSeparated_relocalize {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : F ⟶ G}
    (h : IsSeparated B S hS p) :
    IsSeparated B S' hS' ((OverShriek.relocalizePresheafFunctor k).map p) := by
  have h1 := isClosedImmersion_relocalize B S hS hS' k (p := pullback.diagonal p) h
  change IsClosedImmersion B S' hS'
    (pullback.diagonal ((OverShriek.relocalizePresheafFunctor k).map p))
  rw [← OverShriek.relocalize_map_diagonal]
  exact MorphismProperty.RespectsIso.postcomp (closedImmersionPresheafProperty B S' hS') _ _ h1

/-- A morphism with representable relative diagonal which becomes separated after relocalization to
a larger base is separated. -/
theorem isSeparated_of_relocalize {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : F ⟶ G}
    (hrep : yoneda.relativelyRepresentable (pullback.diagonal p))
    (h : IsSeparated B S' hS' ((OverShriek.relocalizePresheafFunctor k).map p)) :
    IsSeparated B S hS p := by
  have h1 : IsClosedImmersion B S' hS'
      (pullback.diagonal ((OverShriek.relocalizePresheafFunctor k).map p)) := h
  rw [← OverShriek.relocalize_map_diagonal] at h1
  exact isClosedImmersion_of_relocalize B S hS hS' k hrep
    ((MorphismProperty.cancel_right_of_respectsIso
      (closedImmersionPresheafProperty B S' hS') _ _).1 h1)

/-- An immersion stays an immersion after relocalization to a larger base. -/
theorem isImmersion_relocalize {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : F ⟶ G}
    (h : IsImmersion B S hS p) :
    IsImmersion B S' hS' ((OverShriek.relocalizePresheafFunctor k).map p) :=
  OverShriek.presheaf_map_relocalize _ (fun _ hk => hk) h

/-- A representable morphism which becomes an immersion after relocalization to a larger base is an
immersion. -/
theorem isImmersion_of_relocalize {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : F ⟶ G}
    (hrep : yoneda.relativelyRepresentable p)
    (h : IsImmersion B S' hS' ((OverShriek.relocalizePresheafFunctor k).map p)) :
    IsImmersion B S hS p :=
  OverShriek.presheaf_of_presheaf_map_relocalize _ (fun _ hk => hk) hrep h

/-- A locally separated morphism stays locally separated after relocalization to a larger base. -/
theorem isLocallySeparated_relocalize {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : F ⟶ G}
    (h : IsLocallySeparated B S hS p) :
    IsLocallySeparated B S' hS' ((OverShriek.relocalizePresheafFunctor k).map p) := by
  have h1 := isImmersion_relocalize B S hS hS' k (p := pullback.diagonal p) h
  change IsImmersion B S' hS'
    (pullback.diagonal ((OverShriek.relocalizePresheafFunctor k).map p))
  rw [← OverShriek.relocalize_map_diagonal]
  exact MorphismProperty.RespectsIso.postcomp (immersionPresheafProperty B S' hS') _ _ h1

/-- A morphism with representable relative diagonal which becomes locally separated after
relocalization to a larger base is locally separated. -/
theorem isLocallySeparated_of_relocalize {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : F ⟶ G}
    (hrep : yoneda.relativelyRepresentable (pullback.diagonal p))
    (h : IsLocallySeparated B S' hS' ((OverShriek.relocalizePresheafFunctor k).map p)) :
    IsLocallySeparated B S hS p := by
  have h1 : IsImmersion B S' hS'
      (pullback.diagonal ((OverShriek.relocalizePresheafFunctor k).map p)) := h
  rw [← OverShriek.relocalize_map_diagonal] at h1
  exact isImmersion_of_relocalize B S hS hS' k hrep
    ((MorphismProperty.cancel_right_of_respectsIso
      (immersionPresheafProperty B S' hS') _ _).1 h1)

end Relocalize

section Absolute

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- If the source of `f` is an algebraic space, the relative diagonal of each base change
`pullback.snd f g` is representable. -/
private theorem relativelyRepresentable_diagonal_pullbackSnd
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : Z ⟶ Y) : yoneda.relativelyRepresentable (pullback.diagonal (pullback.snd f g)) :=
  (Functor.relativelyRepresentable.isStableUnderBaseChange
    (yoneda (C := BigFppfOver B S hS))).of_isPullback
      (isPullback_diagonal_pullbackSnd f g) (relativelyRepresentable_diagonal B S hS hX f)

/-- For an affine test object `T` of the big fppf site of `S` and `g : h_T ⟶ Y`, the base change
`X ×_Y h_T ⟶ h_T` of `f` is separated if and only if the algebraic space `X ×_Y h_T`, viewed over
the terminal scheme, is separated. -/
theorem isSeparated_pullbackSnd_iff_isAbsolutelySeparated
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (g : yoneda.obj T ⟶ Y) :
    IsSeparated B S hS (pullback.snd f g) ↔
      IsAbsolutelySeparated B S hS hZ (pullback f g) := by
  have hterm : IsTerminal (Over.mk (𝟙 (B.obj hZ))) := Over.mkIdTerminal
  have haffT : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj
      ((Over.map (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ)).obj T)) := hT
  have haff0 : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj
      (Over.mk (𝟙 (B.obj hZ)))) := inferInstanceAs (IsAffine (⊤_ Scheme.{u}))
  have hm : IsSeparated B (⊤_ Scheme.{u}) hZ (yoneda.map (hterm.from
      ((Over.map (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ)).obj T))) :=
    isSeparated_yoneda_map_of_isAffine B (⊤_ Scheme.{u}) hZ _ haffT haff0
  have hiso := (OverShriek.relocalizeYonedaIso
    (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ)).app T
  have hterm' :=
    IsTerminal.isTerminalObj (yoneda (C := BigFppfOver B (⊤_ Scheme.{u}) hZ)) _ hterm
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 := isSeparated_relocalize B S hS hZ
      (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) h
    have h2 := isSeparated_comp B (⊤_ Scheme.{u}) hZ _ _ h1
      (isSeparated_of_isIso B (⊤_ Scheme.{u}) hZ hiso.hom)
    have h3 := isSeparated_comp B (⊤_ Scheme.{u}) hZ _ _ h2 hm
    exact (isSeparatedOver_iff_isSeparated_of_isTerminal B (⊤_ Scheme.{u}) hZ hterm' _).2 h3
  · exact isSeparated_of_relocalize B S hS hZ
      (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ)
      (relativelyRepresentable_diagonal_pullbackSnd B S hS hX f g)
      (isSeparated_of_isSeparatedOver B (⊤_ Scheme.{u}) hZ h _)

/-- For an affine test object `T` of the big fppf site of `S` and `g : h_T ⟶ Y`, the base change
`X ×_Y h_T ⟶ h_T` of `f` is locally separated if and only if the algebraic space `X ×_Y h_T`,
viewed over the terminal scheme, is locally separated. -/
theorem isLocallySeparated_pullbackSnd_iff_isAbsolutelyLocallySeparated
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (g : yoneda.obj T ⟶ Y) :
    IsLocallySeparated B S hS (pullback.snd f g) ↔
      IsAbsolutelyLocallySeparated B S hS hZ (pullback f g) := by
  have hterm : IsTerminal (Over.mk (𝟙 (B.obj hZ))) := Over.mkIdTerminal
  have haffT : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj
      ((Over.map (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ)).obj T)) := hT
  have haff0 : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj
      (Over.mk (𝟙 (B.obj hZ)))) := inferInstanceAs (IsAffine (⊤_ Scheme.{u}))
  have hm : IsLocallySeparated B (⊤_ Scheme.{u}) hZ (yoneda.map (hterm.from
      ((Over.map (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ)).obj T))) :=
    isLocallySeparated_yoneda_map_of_isAffine B (⊤_ Scheme.{u}) hZ _ haffT haff0
  have hiso := (OverShriek.relocalizeYonedaIso
    (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ)).app T
  have hterm' :=
    IsTerminal.isTerminalObj (yoneda (C := BigFppfOver B (⊤_ Scheme.{u}) hZ)) _ hterm
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 := isLocallySeparated_relocalize B S hS hZ
      (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) h
    have h2 := isLocallySeparated_comp B (⊤_ Scheme.{u}) hZ _ _ h1
      (isLocallySeparated_of_isIso B (⊤_ Scheme.{u}) hZ hiso.hom)
    have h3 := isLocallySeparated_comp B (⊤_ Scheme.{u}) hZ _ _ h2 hm
    exact (isLocallySeparatedOver_iff_isLocallySeparated_of_isTerminal
      B (⊤_ Scheme.{u}) hZ hterm' _).2 h3
  · exact isLocallySeparated_of_relocalize B S hS hZ
      (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ)
      (relativelyRepresentable_diagonal_pullbackSnd B S hS hX f g)
      (isLocallySeparated_of_isLocallySeparatedOver B (⊤_ Scheme.{u}) hZ h _)

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` the following are equivalent:
`f` is separated; the base change of `f` along every morphism from a representable presheaf is
separated; the same for the test objects with affine underlying scheme; for every affine test
object the fibre product is a separated algebraic space over the terminal scheme; there is a
surjective étale scheme chart of the target along which the base change of `f` is separated; and
there is a Zariski covering of the target over whose members the base changes of `f` are
separated. -/
@[stacks 03KM "separated"]
theorem isSeparated_tfae (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) :
    List.TFAE [
      IsSeparated B S hS f,
      (∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
        IsSeparated B S hS (pullback.snd f g)),
      (∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
        IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
          IsSeparated B S hS (pullback.snd f g)),
      (∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
        IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
          IsAbsolutelySeparated B S hS hZ (pullback f g)),
      (∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        IsSeparated B S hS (pullback.snd f g)),
      (∃ (I : Type u) (U : I → Subfunctor Y),
        IsZariskiCover B S hS I U ∧
        ∀ i, IsSeparated B S hS (pullback.snd f (U i).ι))
    ] := by
  tfae_have 1 → 2 := fun h T g => isSeparated_pullbackSnd B S hS g h
  tfae_have 2 → 3 := fun h T g _ => h T g
  tfae_have 3 → 4 := fun h T g hT =>
    (isSeparated_pullbackSnd_iff_isAbsolutelySeparated B S hS hZ hX f T hT g).1 (h T g hT)
  tfae_have 4 → 3 := fun h T g hT =>
    (isSeparated_pullbackSnd_iff_isAbsolutelySeparated B S hS hZ hX f T hT g).2 (h T g hT)
  tfae_have 3 → 1 := fun h =>
    (isSeparated_iff_affine B S hS hX f).2 fun T hT g => h T g hT
  tfae_have 1 → 5 := isSeparated_exists_etaleChart B S hS hY
  tfae_have 5 → 1 := fun ⟨_, _, hsurj, hetale, h⟩ =>
    isSeparated_of_etaleChart B S hS hX hsurj hetale h
  tfae_have 1 → 6 := isSeparated_exists_zariskiCover B S hS hY
  tfae_have 6 → 1 := fun ⟨_, _, hU, h⟩ => isSeparated_of_zariskiCover B S hS hX hU h
  tfae_finish

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` the following are equivalent:
`f` is locally separated; the base change of `f` along every morphism from a representable presheaf
is locally separated; the same for the test objects with affine underlying scheme; for every affine
test object the fibre product is a locally separated algebraic space over the terminal scheme;
there is a surjective étale scheme chart of the target along which the base change of `f` is
locally separated; and there is a Zariski covering of the target over whose members the base
changes of `f` are locally separated. -/
@[stacks 03KM "locally separated"]
theorem isLocallySeparated_tfae (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    List.TFAE [
      IsLocallySeparated B S hS f,
      (∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
        IsLocallySeparated B S hS (pullback.snd f g)),
      (∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
        IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
          IsLocallySeparated B S hS (pullback.snd f g)),
      (∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
        IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
          IsAbsolutelyLocallySeparated B S hS hZ (pullback f g)),
      (∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        IsLocallySeparated B S hS (pullback.snd f g)),
      (∃ (I : Type u) (U : I → Subfunctor Y),
        IsZariskiCover B S hS I U ∧
        ∀ i, IsLocallySeparated B S hS (pullback.snd f (U i).ι))
    ] := by
  tfae_have 1 → 2 := fun h T g => isLocallySeparated_pullbackSnd B S hS g h
  tfae_have 2 → 3 := fun h T g _ => h T g
  tfae_have 3 → 4 := fun h T g hT =>
    (isLocallySeparated_pullbackSnd_iff_isAbsolutelyLocallySeparated
      B S hS hZ hX f T hT g).1 (h T g hT)
  tfae_have 4 → 3 := fun h T g hT =>
    (isLocallySeparated_pullbackSnd_iff_isAbsolutelyLocallySeparated
      B S hS hZ hX f T hT g).2 (h T g hT)
  tfae_have 3 → 1 := fun h =>
    (isLocallySeparated_iff_affine B S hS hX f).2 fun T hT g => h T g hT
  tfae_have 1 → 5 := isLocallySeparated_exists_etaleChart B S hS hY
  tfae_have 5 → 1 := fun ⟨_, _, hsurj, hetale, h⟩ =>
    isLocallySeparated_of_etaleChart B S hS hX hsurj hetale h
  tfae_have 1 → 6 := isLocallySeparated_exists_zariskiCover B S hS hY
  tfae_have 6 → 1 := fun ⟨_, _, hU, h⟩ => isLocallySeparated_of_zariskiCover B S hS hX hU h
  tfae_finish

end Absolute

end AlgebraicGeometry.Space

end
