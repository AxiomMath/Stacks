module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiSeparatedVeryReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeDecency
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonableImpliesReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreDiscreteDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreEquivalences
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreFiniteDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteProperQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# A finite closed image near a fibre of a proper morphism (Stacks 0AEJ)

Let `S` be a scheme contained in a big fppf site `B`, and let

```
X --h--> Y
 \      /
  f    g
   \  /
    T
```

be a commutative triangle of algebraic spaces over `S`, so `h ≫ g = f`, with `f` proper and
`g` separated and locally of finite type. Let `b` be a point of `|T|`, represented by a
field-valued point `p` with field of definition `k`. **Stacks 0AEJ** says that if the image of
`|X_k|` in `|Y_k|` is finite — or, with `T` decent, if the image in `|Y|` of the set-theoretic
fibre `f^{-1}({b})` is finite — then `b` has an open neighbourhood `U ⊆ T` and there is a closed
subspace `Z ⊆ Y ×_T U`, finite over `U`, through which `X ×_T U ⟶ Y ×_T U` factors.

The proof replaces `Y` by the scheme-theoretic image `I` of `h` (Stacks 082X). By Stacks 0AGD
the structure morphism `q : I ⟶ T` is proper and `X ⟶ I` is surjective, so `I` absorbs both
finiteness hypotheses: the point set of the field fibre `I_k` is finite, in the first case
because `|X_k| ↠ |I_k| ↪ |Y_k|`, and in the second because the set-theoretic fibre of `q` over
`b` is finite and Stacks 0AC9 converts that into finiteness of `|I_k|` for a decent base. By
Stacks 0ACK, finiteness of `|I_k|` makes `q` quasi-finite at every point above `b`, so
Stacks 0A4Y produces an open `U ∋ b` over which `q` becomes finite. For `Z` one takes the
inverse image of `I` in `Y ×_T U`, which is closed (Stacks 083Q) and is exactly the base change
of `I` along `U ⟶ T`, hence finite over `U`; and `X ×_T U ⟶ Y ×_T U` factors through it because
`h` factors through `I`.

## Main results

* `AlgebraicGeometry.Space.exists_isOpenSubspace_isClosedSubspace_isFinite_of_isProper` is
  **Stacks 0AEJ**, with both forms of the finiteness hypothesis offered as a disjunction.

## Implementation notes

The induced morphism between the two base changes is Mathlib's `CategoryTheory.Limits.pullback.map`
for the comparison data `(h, 𝟙, 𝟙)`; no auxiliary definition is needed. Both base-changed fibres
are taken along the morphism `AlgebraicGeometry.Space.fieldMorphism` presented by the chosen
field-valued representative `p` of `b`, which is also what `AlgebraicGeometry.Space.fieldFibre`
uses.

## References

* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 0A4Y](https://stacks.math.columbia.edu/tag/0A4Y)
* [Stacks Project, Tag 0AC9](https://stacks.math.columbia.edu/tag/0AC9)
* [Stacks Project, Tag 0ACK](https://stacks.math.columbia.edu/tag/0ACK)
* [Stacks Project, Tag 0AEJ](https://stacks.math.columbia.edu/tag/0AEJ)
* [Stacks Project, Tag 0AGD](https://stacks.math.columbia.edu/tag/0AGD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_ProperFiniteImageNearFibre :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Cospans of presheaves on the big fppf site over `S` have limits (a fast path for instance
search). -/
local instance (priority := high) hasPullback_presheaf_ProperFiniteImageNearFibre
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Set-theoretic preliminaries -/

/-- If `f` is surjective, `g` is injective and `g ∘ f` has finite range, then the codomain of
`f` is finite: the range of `g` is contained in the range of `g ∘ f`, and `g` is injective. -/
private theorem finite_univ_of_surjective_of_injective_of_finite_range
    {A D E : Type*} (f : A → D) (g : D → E) (hf : Function.Surjective f)
    (hg : Function.Injective g) (hfin : (Set.range (g ∘ f)).Finite) :
    (Set.univ : Set D).Finite := by
  have hrange : (Set.range g).Finite := hfin.subset (by
    rintro y ⟨d, rfl⟩
    obtain ⟨a, rfl⟩ := hf d
    exact ⟨a, rfl⟩)
  simpa only [Set.preimage_range] using Set.Finite.preimage hg.injOn hrange

/-- If every element of `D` satisfying `Q` is the image under `f` of an element satisfying `P`,
`g` is injective, and `(g ∘ f) '' {P}` is finite, then `{Q}` is finite: it embeds into the
preimage under `g` of that finite image. -/
private theorem finite_setOf_of_injective_of_finite_image
    {A D E : Type*} (f : A → D) (g : D → E) (P : A → Prop) (Q : D → Prop)
    (hpre : ∀ d, Q d → ∃ a, P a ∧ f a = d) (hg : Function.Injective g)
    (hfin : ((g ∘ f) '' {a | P a}).Finite) :
    ({d | Q d} : Set D).Finite := by
  refine (hfin.preimage hg.injOn).subset fun d hd ↦ ?_
  obtain ⟨a, ha, rfl⟩ := hpre d hd
  exact ⟨a, ha, rfl⟩

/-- The base change along `k` of the first leg of a commutative triangle `hz ≫ q = f` is
cartesian over `hz`: the square whose legs are `X ×_T K ⟶ X` and the induced map
`X ×_T K ⟶ Z ×_T K` is a pullback square. -/
private theorem isPullback_fst_pullbackMap {X Z T K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hz : X ⟶ Z) (q : Z ⟶ T) (k : K ⟶ T) {f : X ⟶ T} (comm : hz ≫ q = f) :
    IsPullback (pullback.fst f k)
      (pullback.map f k q k hz (𝟙 _) (𝟙 _) (by simp [comm]) (by simp))
      hz (pullback.fst q k) := by
  cases comm
  refine IsPullback.of_iso_pullback ⟨by simp [pullback.map, pullback.lift_fst]⟩
    (pullbackRightPullbackFstIso q k hz).symm
    (pullbackRightPullbackFstIso_inv_fst q k hz) ?_
  apply pullback.hom_ext
  · simpa only [Iso.symm_hom, Category.assoc, pullback.map, pullback.lift_fst] using
      pullbackRightPullbackFstIso_inv_snd_fst q k hz
  · simpa only [Iso.symm_hom, Category.assoc, pullback.map, pullback.lift_snd,
      Category.comp_id] using pullbackRightPullbackFstIso_inv_snd_snd q k hz

/-- Finiteness of a morphism of algebraic spaces over `S` is unchanged by precomposition with
an isomorphism: an affine representative of a base change of the morphism becomes one of the
precomposition after transporting the cartesian square along the isomorphism. -/
private theorem isFinite_isoHom_comp {X X' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : X ≅ X')
    (f : X' ⟶ Y) (hf : IsFinite B S hS f) : IsFinite B S hS (e.hom ≫ f) := by
  intro U hU ξ
  obtain ⟨V, pr, i, hV, hfin, hpb⟩ := hf U hU ξ
  exact ⟨V, pr, i ≫ e.inv, hV, hfin, hpb.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)⟩

/-- A separated morphism of algebraic spaces is decent. -/
private theorem isDecent_of_isSeparated {I T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hI : IsAlgebraicSpace B S hS I) (hT : IsAlgebraicSpace B S hS T) (q : I ⟶ T)
    (hq : IsSeparated B S hS q) : IsDecent B S hS q :=
  isDecent_of_isReasonable B S hS hI hT q
    (isReasonable_of_isVeryReasonable B S hS hI hT
      (isVeryReasonable_of_isQuasiSeparated B S hS hI hT
        (isQuasiSeparated_of_isSeparated B S hS hq)))

/-! ### Stacks 0AEJ -/

variable {X Y T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- If the scheme-theoretic image `I` of `h : X ⟶ Y` is finite over `U ⊆ T` after base change,
then `X ×_T U ⟶ Y ×_T U` factors through a closed subspace of `Y ×_T U` finite over `U`, namely
the inverse image of `I`. -/
theorem exists_isClosedSubspace_isFinite_of_isFinite_schemeTheoreticImage
    (hY : IsAlgebraicSpace B S hS Y) (hT : IsAlgebraicSpace B S hS T) (h : X ⟶ Y) (f : X ⟶ T)
    (g : Y ⟶ T) (comm : h ≫ g = f) {U : Subfunctor T} (hU : IsAlgebraicSpace B S hS U.toFunctor)
    (hfiniteU :
      IsFinite B S hS (pullback.snd ((schemeTheoreticImageSubfunctor B S hS h).ι ≫ g) U.ι)) :
    ∃ Z : Subfunctor (pullback g U.ι),
      IsClosedSubspace B S hS Z ∧
      (∃ m : pullback f U.ι ⟶ Z.toFunctor, m ≫ Z.ι =
        pullback.map f U.ι g U.ι h (𝟙 _) (𝟙 _) (by simp [comm]) (by simp)) ∧
      IsFinite B S hS (Z.ι ≫ pullback.snd g U.ι) := by
  let I : Subfunctor Y := schemeTheoreticImageSubfunctor B S hS h
  have hIclosed : IsClosedSubspace B S hS I :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS h hY
  have hYU : IsAlgebraicSpace B S hS (pullback g U.ι) :=
    isAlgebraicSpace_pullback B S hS g U.ι hY hU hT
  let fstYU : pullback g U.ι ⟶ Y := pullback.fst g U.ι
  let Zc : Subfunctor (pullback g U.ι) := I.preimage fstYU
  let uMap : pullback f U.ι ⟶ pullback g U.ι :=
    pullback.map f U.ι g U.ι h (𝟙 _) (𝟙 _) (by simp [comm]) (by simp)
  have huMapFst : pullback.fst f U.ι ≫ h = uMap ≫ fstYU := by
    simp [uMap, fstYU, pullback.map, pullback.lift_fst]
  have huMapRange : Subfunctor.range uMap ≤ Zc := by
    rintro V _ ⟨x, rfl⟩
    show fstYU.app V (uMap.app V x) ∈ I.obj V
    apply range_le_schemeTheoreticImageSubfunctor B S hS h V
    refine ⟨(pullback.fst f U.ι).app V x, ?_⟩
    simpa only [NatTrans.comp_app, CategoryTheory.comp_apply] using
      congrArg (fun α ↦ α.app V x) huMapFst
  refine ⟨Zc, isClosedSubspace_preimage B S hS fstYU I hY hYU hIclosed,
    ⟨Subfunctor.lift uMap huMapRange, Subfunctor.lift_ι uMap huMapRange⟩, ?_⟩
  have hpbZ : IsPullback (I.fromPreimage fstYU) (Zc.ι ≫ pullback.snd g U.ι) (I.ι ≫ g) U.ι :=
    (Subfunctor.isPullback_preimage fstYU I).paste_vert (IsPullback.of_hasPullback g U.ι)
  rw [← hpbZ.isoPullback_hom_snd]
  exact isFinite_isoHom_comp B S hS hpbZ.isoPullback (pullback.snd (I.ι ≫ g) U.ι) hfiniteU

/-- In the setting of Stacks 0AEJ, if the image of `|X_k|` in `|Y_k|` is finite, then the field
fibre over `k` of the scheme-theoretic image of `h` has finitely many points. -/
theorem finite_univ_points_pullback_schemeTheoreticImage_of_finite_range
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hT : IsAlgebraicSpace B S hS T) (h : X ⟶ Y) (f : X ⟶ T) (g : Y ⟶ T)
    (comm : h ≫ g = f) (p : FieldValuedPoint B S hS T) (hf : IsProper B S hS f)
    (hg_sep : IsSeparated B S hS g)
    (hfin : Set.Finite (Set.range (pointsMap B S hS (pullback f (fieldMorphism B S hS T p))
      (pullback.map f (fieldMorphism B S hS T p) g (fieldMorphism B S hS T p) h
        (𝟙 _) (𝟙 _) (by simp [comm]) (by simp))))) :
    (Set.univ : Set (points B S hS (pullback ((schemeTheoreticImageSubfunctor B S hS h).ι ≫ g)
      (fieldMorphism B S hS T p)))).Finite := by
  let I : Subfunctor Y := schemeTheoreticImageSubfunctor B S hS h
  have hIclosed : IsClosedSubspace B S hS I :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS h hY
  have hI : IsAlgebraicSpace B S hS I.toFunctor := hIclosed.1
  let q : I.toFunctor ⟶ T := I.ι ≫ g
  let w : X ⟶ I.toFunctor := toSchemeTheoreticImage B S hS h
  have hwι : w ≫ I.ι = h := toSchemeTheoreticImage_ι B S hS h
  have hwq : w ≫ q = f := by rw [show q = I.ι ≫ g from rfl, ← Category.assoc, hwι, comm]
  let k : yoneda.obj p.siteObject ⟶ T := fieldMorphism B S hS T p
  have hK : IsAlgebraicSpace B S hS (yoneda.obj p.siteObject) :=
    isAlgebraicSpace_yoneda B S hS p.siteObject
  have hIk : IsAlgebraicSpace B S hS (pullback q k) :=
    isAlgebraicSpace_pullback B S hS q k hI hK hT
  have hYk : IsAlgebraicSpace B S hS (pullback g k) :=
    isAlgebraicSpace_pullback B S hS g k hY hK hT
  let xk : pullback f k ⟶ pullback q k :=
    pullback.map f k q k w (𝟙 _) (𝟙 _) (by simp [hwq]) (by simp)
  let zk : pullback q k ⟶ pullback g k :=
    pullback.map q k g k I.ι (𝟙 _) (𝟙 _) (by simp [q]) (by simp)
  let xy : pullback f k ⟶ pullback g k :=
    pullback.map f k g k h (𝟙 _) (𝟙 _) (by simp [comm]) (by simp)
  have hxy : xk ≫ zk = xy := by
    apply pullback.hom_ext
    · simp [xk, zk, xy, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc, hwι]
    · simp [xk, zk, xy, pullback.map, pullback.lift_snd]
  have hxksurj : IsSurjective B S hS xk :=
    isSurjective_of_isPullback B S hS
      (isPullback_homMk B S hS hX hIk hI (isAlgebraicSpace_pullback B S hS f k hX hK hT)
        (isPullback_fst_pullbackMap B S hS w q k hwq))
      (isSurjective_toSchemeTheoreticImage_of_isProper B S hS hX hY hT h f g comm hf hg_sep)
  have hzkImm : IsImmersion B S hS zk :=
    isImmersion_of_isPullback B S hS
      (isPullback_homMk B S hS hI hYk hY hIk
        (isPullback_fst_pullbackMap B S hS I.ι g k rfl))
      (isImmersion_of_isClosedImmersion B S hS hIclosed.2)
  have hcomp : pointsMap B S hS (pullback f k) xy =
      pointsMap B S hS (pullback q k) zk ∘ pointsMap B S hS (pullback f k) xk := by
    rw [← hxy, pointsMap_comp]
  refine finite_univ_of_surjective_of_injective_of_finite_range
    (pointsMap B S hS (pullback f k) xk) (pointsMap B S hS (pullback q k) zk) hxksurj
    (isEmbedding_pointsMap_of_isImmersion B S hS hYk zk hzkImm).injective ?_
  rw [← hcomp]
  exact hfin

/-- In the setting of Stacks 0AEJ, if `T` is decent and the image in `|Y|` of the set-theoretic
fibre of `f` over `b` is finite, then the field fibre over a representative of `b` of the
scheme-theoretic image of `h` has finitely many points. -/
theorem finite_univ_points_pullback_schemeTheoreticImage_of_finite_image_fibre
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hT : IsAlgebraicSpace B S hS T) (h : X ⟶ Y) (f : X ⟶ T) (g : Y ⟶ T)
    (comm : h ≫ g = f) (b : points B S hS T) (p : FieldValuedPoint B S hS T)
    (hp : p.class B S hS T = b) (hf : IsProper B S hS f)
    (hg_sep : IsSeparated B S hS g) (hg_lft : IsLocallyOfFiniteType B S hS g)
    (hfinSet : Set.Finite (pointsMap B S hS X h ''
      {x : points B S hS X | pointsMap B S hS X f x = b}))
    (hTdecent : IsDecentSpace B S hS T) :
    (Set.univ : Set (points B S hS (pullback ((schemeTheoreticImageSubfunctor B S hS h).ι ≫ g)
      (fieldMorphism B S hS T p)))).Finite := by
  let I : Subfunctor Y := schemeTheoreticImageSubfunctor B S hS h
  have hIclosed : IsClosedSubspace B S hS I :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS h hY
  have hI : IsAlgebraicSpace B S hS I.toFunctor := hIclosed.1
  let q : I.toFunctor ⟶ T := I.ι ≫ g
  let w : X ⟶ I.toFunctor := toSchemeTheoreticImage B S hS h
  have hwι : w ≫ I.ι = h := toSchemeTheoreticImage_ι B S hS h
  have hwq : w ≫ q = f := by rw [show q = I.ι ≫ g from rfl, ← Category.assoc, hwι, comm]
  have hqProper : IsProper B S hS q :=
    isProper_schemeTheoreticImageSubfunctor_inclusion_comp B S hS hX hY hT h f g comm hf
      hg_sep hg_lft
  have hqdecent : IsDecent B S hS q := isDecent_of_isSeparated B S hS hI hT q hqProper.1
  have hwsurj : IsSurjective B S hS w :=
    isSurjective_toSchemeTheoreticImage_of_isProper B S hS hX hY hT h f g comm hf hg_sep
  have hglobal : pointsMap B S hS X f =
      pointsMap B S hS I.toFunctor q ∘ pointsMap B S hS X w := by
    rw [← hwq, pointsMap_comp]
  have himage : pointsMap B S hS X h =
      pointsMap B S hS I.toFunctor I.ι ∘ pointsMap B S hS X w := by
    rw [← hwι, pointsMap_comp]
  have hfibre : ({z : points B S hS I.toFunctor |
      pointsMap B S hS I.toFunctor q z = b}).Finite := by
    refine finite_setOf_of_injective_of_finite_image (pointsMap B S hS X w)
      (pointsMap B S hS I.toFunctor I.ι) (fun x ↦ pointsMap B S hS X f x = b)
      (fun z ↦ pointsMap B S hS I.toFunctor q z = b) (fun z' hz' ↦ ?_)
      (isEmbedding_pointsMap_of_isImmersion B S hS hY I.ι
        (isImmersion_of_isClosedImmersion B S hS hIclosed.2)).injective
      (by simpa [Function.comp_def, himage] using hfinSet)
    obtain ⟨x, hx⟩ := hwsurj z'
    exact ⟨x, by simpa only [hglobal, Function.comp_apply, hx] using hz', hx⟩
  exact finite_univ_points_fieldFibre_of_finite_setFibre_of_isDecent B S hS hI hT q p
    hqProper.2.1.1 (isDecentSpace_of_isDecent B S hS hI hT q hTdecent hqdecent) hTdecent
    (by simpa [setFibre, hp] using hfibre)

/-- **Stacks 0AEJ.** Let `h : X ⟶ Y`, `f : X ⟶ T` and `g : Y ⟶ T` be morphisms of algebraic
spaces over `S` with `h ≫ g = f`, with `f` proper and `g` separated and locally of finite type,
and let `b ∈ |T|` be represented by a field-valued point `p` with field of definition `k`. If
the image of `|X_k|` in `|Y_k|` is finite, or if `T` is decent and the image in `|Y|` of the
set-theoretic fibre of `f` over `b` is finite, then `b` has an open neighbourhood `U ⊆ T` and
`X ×_T U ⟶ Y ×_T U` factors through a closed subspace of `Y ×_T U` which is finite over `U`. -/
@[stacks 0AEJ]
theorem exists_isOpenSubspace_isClosedSubspace_isFinite_of_isProper
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hT : IsAlgebraicSpace B S hS T) (h : X ⟶ Y) (f : X ⟶ T) (g : Y ⟶ T)
    (comm : h ≫ g = f) (b : points B S hS T) (p : FieldValuedPoint B S hS T)
    (hp : p.class B S hS T = b) (hf : IsProper B S hS f)
    (hg_sep : IsSeparated B S hS g) (hg_lft : IsLocallyOfFiniteType B S hS g)
    (hfinite :
      Set.Finite (Set.range (pointsMap B S hS (pullback f (fieldMorphism B S hS T p))
        (pullback.map f (fieldMorphism B S hS T p) g (fieldMorphism B S hS T p) h
          (𝟙 _) (𝟙 _) (by simp [comm]) (by simp)))) ∨
      (Set.Finite (pointsMap B S hS X h ''
          {x : points B S hS X | pointsMap B S hS X f x = b}) ∧
        IsDecentSpace B S hS T)) :
    ∃ U : Subfunctor T,
      IsOpenSubspace B S hS U ∧
      b ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) ∧
      ∃ Z : Subfunctor (pullback g U.ι),
        IsClosedSubspace B S hS Z ∧
        (∃ m : pullback f U.ι ⟶ Z.toFunctor, m ≫ Z.ι =
          pullback.map f U.ι g U.ι h (𝟙 _) (𝟙 _) (by simp [comm]) (by simp)) ∧
        IsFinite B S hS (Z.ι ≫ pullback.snd g U.ι) := by
  classical
  let I : Subfunctor Y := schemeTheoreticImageSubfunctor B S hS h
  have hI : IsAlgebraicSpace B S hS I.toFunctor :=
    (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS h hY).1
  let q : I.toFunctor ⟶ T := I.ι ≫ g
  have hqProper : IsProper B S hS q :=
    isProper_schemeTheoreticImageSubfunctor_inclusion_comp B S hS hX hY hT h f g comm hf
      hg_sep hg_lft
  have hqdecent : IsDecent B S hS q := isDecent_of_isSeparated B S hS hI hT q hqProper.1
  have hfiniteField :
      (Set.univ : Set (points B S hS (pullback q (fieldMorphism B S hS T p)))).Finite := by
    rcases hfinite with hfin | ⟨hfinSet, hTdecent⟩
    · exact finite_univ_points_pullback_schemeTheoreticImage_of_finite_range B S hS hX hY hT
        h f g comm p hf hg_sep hfin
    · exact finite_univ_points_pullback_schemeTheoreticImage_of_finite_image_fibre B S hS hX hY
        hT h f g comm b p hp hf hg_sep hg_lft hfinSet hTdecent
  have hdisc : IsDiscreteFieldFibrePoints B S hS q p :=
    discreteTopology_points_fieldFibre_of_finite_of_isDecent B S hS hI hT q p hqProper.2.1.1
      hqdecent hfiniteField
  -- Stacks 0A4Y: `q` is finite over an open neighbourhood `U` of `b`.
  obtain ⟨U, hU, hbU, hfiniteU⟩ :=
    exists_isOpenSubspace_isFinite_pullback_snd_of_isProper B S hS hI hT q hqProper b
      fun z hz ↦ (isDiscreteFieldFibrePoints_iff_isQuasiFiniteAboveFieldValuedPoint B S hS hI hT
        hqProper.2.1.1 p).mp hdisc z (hz.trans hp.symm)
  exact ⟨U, hU, hbU,
    exists_isClosedSubspace_isFinite_of_isFinite_schemeTheoreticImage B S hS hY hT h f g comm hU.1
      hfiniteU⟩

end AlgebraicGeometry.Space

end
