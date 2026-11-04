module

public import StacksFrontier.AlgebraicGeometry.Scheme.Immersion.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFieldAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms

/-!
# Quasi-compact algebraic spaces étale over the spectrum of a field

An algebraic space over `S` which is quasi-compact and étale over a point of the site whose
underlying scheme is the spectrum of a field `k` is a scheme, and that scheme is a finite
disjoint union of spectra of finite separable extensions of `k`, compatibly with the map to
`Spec k`.

The same holds for the fibre of a quasi-compact étale morphism of algebraic spaces over a
field-valued point of its target.

## Main results

* `AlgebraicGeometry.Space.exists_iso_yoneda_of_isQuasiCompactSpace_etale_over_fieldSpec`:
  such a space is representable, with the representing object carrying the morphism to the
  field point.
* `AlgebraicGeometry.Space.exists_iso_finite_coproduct_spectra_of_isQuasiCompactSpace_etale`:
  the representing scheme is a finite disjoint union of spectra of finite separable extensions
  of `k`.
* `AlgebraicGeometry.Space.exists_finite_coproduct_spectra_fibre_of_isEtale_isQuasiCompact`:
  the same for the fibre of a quasi-compact étale morphism of algebraic spaces over a
  field-valued point of its target.

## References

* [Stacks Project, Tag 024X](https://stacks.math.columbia.edu/tag/024X)
* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 03DP](https://stacks.math.columbia.edu/tag/03DP)
* [Stacks Project, Tag 03DZ](https://stacks.math.columbia.edu/tag/03DZ)
* [Stacks Project, Tag 03KX](https://stacks.math.columbia.edu/tag/03KX)
* [Stacks Project, Tag 03PC](https://stacks.math.columbia.edu/tag/03PC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An isomorphism of presheaves on the big fppf site of `S` is étale after every
representable base change. -/
private theorem presheaf_etale_of_isIso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    [IsIso f] :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f := by
  have _ : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).ContainsIdentities :=
    ⟨fun T ↦ by
      show AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (𝟙 T))
      rw [CategoryTheory.Functor.map_id]
      infer_instance⟩
  exact MorphismProperty.presheaf_of_isIso _ f

/-- If `a : yoneda.obj A ⟶ Z` is étale and `p : Z ⟶ yoneda.obj V` is étale, then any `m : A ⟶ V`
with `yoneda.map m = a ≫ p` has étale underlying scheme morphism. -/
private theorem etale_map_of_yoneda_map_eq_comp {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {A V : BigFppfOver B S hS} (a : yoneda.obj A ⟶ Z) (p : Z ⟶ yoneda.obj V)
    (hp : IsEtale B S hS p)
    (ha : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (m : A ⟶ V) (hm : yoneda.map m = a ≫ p) :
    AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map m) :=
  (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ m).1
    (by rw [hm]; exact hp A a ha)

/-- **A quasi-compact algebraic space étale over the spectrum of a field is a scheme.**

The space `Z` is étale over an object `V` of the site whose underlying scheme is `Spec k`, and
quasi-compact; the conclusion is an object `U` of the site representing it, together with the
morphism `U ⟶ V` through which the structure morphism to the field point factors.

This is the quasi-compact case of Stacks 03KX. -/
theorem exists_iso_yoneda_of_isQuasiCompactSpace_etale_over_fieldSpec
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
    (k : Type u) [Field k] {V : BigFppfOver B S hS}
    (eV : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k))
    (p : Z ⟶ yoneda.obj V)
    (hp : IsEtale B S hS p)
    (hqc : IsQuasiCompactSpace B S hS Z) :
    ∃ (U : BigFppfOver B S hS) (e : Z ≅ yoneda.obj U) (n : U ⟶ V),
      e.inv ≫ p = yoneda.map n := by
  classical
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have _ : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ := isMultiplicative_presheaf_etale B S hS
  obtain ⟨A, a, hAcpt, hasurj, haet⟩ := hqc
  have haet' := presheaf_etale_of_isEtale B S hS haet
  obtain ⟨m, hm⟩ : ∃ m : A ⟶ V, yoneda.map m = a ≫ p :=
    ⟨yoneda.preimage (a ≫ p), yoneda.map_preimage _⟩
  have hmEt := etale_map_of_yoneda_map_eq_comp B S hS a p hp haet' m hm
  set w : (BigFppfOver.toScheme B S hS).obj A ⟶ Spec (CommRingCat.of k) :=
    (BigFppfOver.toScheme B S hS).map m ≫ eV.hom with hwdef
  have hwEt : AlgebraicGeometry.Etale w :=
    MorphismProperty.RespectsIso.postcomp
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) eV.hom _ hmEt
  have hwQC : AlgebraicGeometry.QuasiCompact w :=
    quasiCompact_of_compactSpace_of_isAffine w inferInstance hAcpt
  have hmQC : AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map m) :=
    (MorphismProperty.cancel_right_of_respectsIso
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u}) _ eV.hom).1 hwQC
  have hAff : ∀ {X : Scheme.{u}} (w : X ⟶ Spec (.of k)), AlgebraicGeometry.Etale w →
      CompactSpace X → IsAffine X := fun {X} w hw hX ↦ by
    have _ := quasiCompact_of_compactSpace_of_isAffine w inferInstance hX
    obtain ⟨hft, hur⟩ := (etale_iff_unramified_over_field k w).mp hw
    have _ := hft
    have _ : StalkwiseUnramified w := hur
    exact isAffine_of_unramified_quasiCompact k w
  have hAaff : IsAffine ((BigFppfOver.toScheme B S hS).obj A) := hAff w hwEt hAcpt
  have _ := hAaff
  have hrep : yoneda.relativelyRepresentable a := hasurj.rep
  set R : BigFppfOver B S hS := hrep.pullback a with hRdef
  set t : R ⟶ A := hrep.fst' a with htdef
  set s : R ⟶ A := hrep.snd a with hsdef
  have hR : IsPullback (yoneda.map t) (yoneda.map s) a a := hrep.isPullback' a
  have hts : t ≫ m = s ≫ m := by
    refine yoneda.map_injective ?_
    rw [Functor.map_comp, Functor.map_comp, hm, ← Category.assoc, ← Category.assoc, hR.w]
  set Q : BigFppfOver B S hS := Limits.pullback m m with hQdef
  set c : R ⟶ Q := Limits.pullback.lift t s hts with hcdef
  have hcmono : Mono c := by
    refine ⟨fun {W} x y hxy ↦ ?_⟩
    have hx : x ≫ t = y ≫ t := by
      simpa only [hcdef, Category.assoc, Limits.pullback.lift_fst] using
        congrArg (· ≫ Limits.pullback.fst m m) hxy
    have hy : x ≫ s = y ≫ s := by
      simpa only [hcdef, Category.assoc, Limits.pullback.lift_snd] using
        congrArg (· ≫ Limits.pullback.snd m m) hxy
    refine yoneda.map_injective (hR.hom_ext ?_ ?_)
    · rw [← Functor.map_comp, ← Functor.map_comp, hx]
    · rw [← Functor.map_comp, ← Functor.map_comp, hy]
  have _ := hcmono
  have hQsq : IsPullback ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst m m))
      ((BigFppfOver.toScheme B S hS).map (Limits.pullback.snd m m))
      ((BigFppfOver.toScheme B S hS).map m) ((BigFppfOver.toScheme B S hS).map m) :=
    (IsPullback.of_hasPullback m m).map (BigFppfOver.toScheme B S hS)
  have hQfstEt : AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst m m)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hQsq.flip hmEt
  have hQfstQC : AlgebraicGeometry.QuasiCompact
      ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst m m)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hQsq.flip hmQC
  have hQcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj Q) := by
    have _ := hQfstQC
    have _ := hAcpt
    exact AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
      ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst m m))
  set wQ : (BigFppfOver.toScheme B S hS).obj Q ⟶ Spec (CommRingCat.of k) :=
    (BigFppfOver.toScheme B S hS).map (Limits.pullback.fst m m) ≫ w with hwQdef
  have hwQEt : AlgebraicGeometry.Etale wQ := by
    have _ := hQfstEt
    have _ := hwEt
    rw [hwQdef]
    infer_instance
  have hwQQC : AlgebraicGeometry.QuasiCompact wQ :=
    quasiCompact_of_compactSpace_of_isAffine wQ inferInstance hQcpt
  obtain ⟨P, hPfin, K, hKfield, hKalg, hKfin, hKsep, eQ, -⟩ :=
    (unramified_quasiCompact_iff_iso_finite_coproduct_spectra_finite_separable k wQ).mp
      ⟨(etale_iff_unramified_over_field k wQ).mp hwQEt, hwQQC⟩
  have _ := hPfin
  let (i : P) : Field (K i) := hKfield i
  have hcSchemeMono : Mono ((BigFppfOver.toScheme B S hS).map c) :=
    Functor.map_mono (BigFppfOver.toScheme B S hS) c
  have _ := hcSchemeMono
  obtain ⟨J, eR, -⟩ := AlgebraicGeometry.exists_iso_coproduct_spec_of_mono K
    ((BigFppfOver.toScheme B S hS).map c ≫ eQ.hom)
  have hRcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj R) := by
    have _ : CompactSpace ↥(∐ fun j : J ↦ Spec (CommRingCat.of (K j.1))) :=
      (AlgebraicGeometry.sigmaMk fun j : J ↦ Spec (CommRingCat.of (K j.1))).compactSpace
    exact (Scheme.homeoOfIso eR.symm).compactSpace
  have hsE : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map s) :=
    haet'.property a (yoneda.map t) s hR
  have htE : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map t) :=
    haet'.property a (yoneda.map s) t hR.flip
  have hRaff : IsAffine ((BigFppfOver.toScheme B S hS).obj R) := by
    have _ := hsE
    have _ := hwEt
    exact hAff ((BigFppfOver.toScheme B S hS).map s ≫ w) inferInstance hRcpt
  have _ := hRaff
  have _ : AlgebraicGeometry.IsSeparated w :=
    AlgebraicGeometry.IsSeparated.of_isAffineHom w
  have hflf : ∀ r : R ⟶ A, AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map r) →
      Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map r) := by
    intro r hr
    have _ := hr
    have _ : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map r ≫ w) := by
      have _ := hwEt
      infer_instance
    have hfin : AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map r ≫ w) :=
      isFinite_of_isAffine_of_etale_over_field k ((BigFppfOver.toScheme B S hS).map r ≫ w)
    have _ := hfin
    rw [Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation]
    exact ⟨AlgebraicGeometry.IsFinite.of_comp ((BigFppfOver.toScheme B S hS).map r) w,
      inferInstance, inferInstance⟩
  have _ : IsAffine ((Over.post B.inclusion).obj A).left := hAaff
  have _ : IsAffine ((Over.post B.inclusion).obj R).left := hRaff
  have _ : Stacks.Morphisms.IsFiniteLocallyFree ((Over.post B.inclusion).map s).left :=
    hflf s hsE
  have _ : Stacks.Morphisms.IsFiniteLocallyFree ((Over.post B.inclusion).map t).left :=
    hflf t htE
  have _ : IsEquivalenceRelation ((Over.post B.inclusion).map t)
      ((Over.post B.inclusion).map s) :=
    isEquivalenceRelation_of_isPullback B S hS a t s hR
  obtain ⟨A₀, _, g, π, hsize, hflfπ, hsurjπ, hpb⟩ :=
    exists_quotient_of_isFiniteLocallyFree_relation S
      ((Over.post B.inclusion).map t) ((Over.post B.inclusion).map s)
  have hA₀ : B.Contains (Spec (CommRingCat.of A₀)) := lt_of_le_of_lt hsize A.left.2
  have _ := hflfπ
  obtain ⟨-, e, -, -⟩ :=
    exists_iso_yoneda_of_isPullback B S hS hZ a t s hR hasurj haet'
      (U' := (Over.mk (⟨g⟩ : B.obj hA₀ ⟶ B.obj hS) : BigFppfOver B S hS)) π
      (Stacks.Morphisms.IsFiniteLocallyFree.flat π.left)
      (Stacks.Morphisms.IsFiniteLocallyFree.locallyOfFinitePresentation π.left) hsurjπ hpb
  exact ⟨_, e, yoneda.preimage (e.inv ≫ p), (yoneda.map_preimage _).symm⟩

/-- **A quasi-compact algebraic space étale over the spectrum of a field is a finite disjoint
union of spectra of finite separable extensions of that field.** -/
theorem exists_iso_finite_coproduct_spectra_of_isQuasiCompactSpace_etale
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
    (k : Type u) [Field k] {V : BigFppfOver B S hS}
    (eV : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k))
    (p : Z ⟶ yoneda.obj V)
    (hp : IsEtale B S hS p)
    (hqc : IsQuasiCompactSpace B S hS Z) :
    ∃ (U : BigFppfOver B S hS) (e : Z ≅ yoneda.obj U) (n : U ⟶ V)
      (I : Type u) (_ : Finite I) (K : I → Type u) (_ : ∀ i, Field (K i))
      (_ : ∀ i, Algebra k (K i)) (_ : ∀ i, Module.Finite k (K i))
      (_ : ∀ i, Algebra.IsSeparable k (K i))
      (eU : (BigFppfOver.toScheme B S hS).obj U ≅ ∐ fun i ↦ Spec (.of (K i))),
      e.inv ≫ p = yoneda.map n ∧
        eU.hom ≫ Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap k (K i)))) =
          (BigFppfOver.toScheme B S hS).map n ≫ eV.hom := by
  classical
  have _ : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨U, e, n, hn⟩ :=
    exists_iso_yoneda_of_isQuasiCompactSpace_etale_over_fieldSpec B S hS hZ k eV p hp hqc
  have hnEt := etale_map_of_yoneda_map_eq_comp B S hS e.inv p hp
    (presheaf_etale_of_isIso B S hS e.inv) n hn.symm
  have hwEt : AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map n ≫ eV.hom) :=
    MorphismProperty.RespectsIso.postcomp
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) eV.hom _ hnEt
  have hUcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
      (IsQuasiCompactSpace.of_iso B S hS hqc e)
  obtain ⟨I, hI, K, hKfield, hKalg, hKfin, hKsep, eU, heU⟩ :=
    (unramified_quasiCompact_iff_iso_finite_coproduct_spectra_finite_separable k
        ((BigFppfOver.toScheme B S hS).map n ≫ eV.hom)).mp
      ⟨(etale_iff_unramified_over_field k _).mp hwEt,
        quasiCompact_of_compactSpace_of_isAffine _ inferInstance hUcpt⟩
  exact ⟨U, e, n, I, hI, K, hKfield, hKalg, hKfin, hKsep, eU, hn, heU⟩

/-- **The fibre of a quasi-compact étale morphism of algebraic spaces over a field-valued
point is a finite disjoint union of spectra of finite separable field extensions.**

Here the fibre is `F ×_G h_V` of `f : F ⟶ G` over a point `g : h_V ⟶ G` whose underlying scheme
is `Spec k`. The first equation identifies the representing morphism with the fibre projection,
the second the scheme decomposition with the map to the base field. -/
theorem exists_finite_coproduct_spectra_fibre_of_isEtale_isQuasiCompact
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (hf : IsEtale B S hS f)
    (hfc : IsQuasiCompact B S hS f) (k : Type u) [Field k] (V : BigFppfOver B S hS)
    (eV : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k)) (g : yoneda.obj V ⟶ G) :
    ∃ (U : BigFppfOver B S hS) (eU₀ : Limits.pullback g f ≅ yoneda.obj U) (v : U ⟶ V)
      (I : Type u) (_ : Finite I) (K : I → Type u) (_ : ∀ i, Field (K i))
      (_ : ∀ i, Algebra k (K i)) (_ : ∀ i, Module.Finite k (K i))
      (_ : ∀ i, Algebra.IsSeparable k (K i))
      (eU : (BigFppfOver.toScheme B S hS).obj U ≅ ∐ fun i ↦ Spec (.of (K i))),
      eU₀.hom ≫ yoneda.map v = Limits.pullback.fst g f ∧
        eU.hom ≫ Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap k (K i)))) =
          (BigFppfOver.toScheme B S hS).map v ≫ eV.hom := by
  classical
  have hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have hfibre : IsAlgebraicSpace B S hS (Limits.pullback g f) :=
    isAlgebraicSpace_pullback B S hS g f hV hF hG
  let F' : AlgebraicSpaces B S hS := ⟨F, hF⟩
  let G' : AlgebraicSpaces B S hS := ⟨G, hG⟩
  let V' : AlgebraicSpaces B S hS := ⟨yoneda.obj V, hV⟩
  let g' : V' ⟶ G' := ObjectProperty.homMk g
  let f' : F' ⟶ G' := ObjectProperty.homMk f
  let W : AlgebraicSpaces B S hS := AlgebraicSpaces.fiberProduct B S hS g' f'
  let fstHom : W ⟶ V' := ObjectProperty.homMk (Limits.pullback.fst g f)
  let sndHom : W ⟶ F' := ObjectProperty.homMk (Limits.pullback.snd g f)
  have hpb : IsPullback fstHom sndHom g' f' :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS g' f'
  have hfstEt : IsEtale B S hS (Limits.pullback.fst g f) :=
    isEtale_of_isPullback B S hS sndHom fstHom f' g' hpb.flip hf
  have hVcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj V) :=
    Stacks.Spaces.compactSpace_of_iso eV.symm inferInstance
  have hfibreqc : IsQuasiCompactSpace B S hS (Limits.pullback g f) :=
    hfc (yoneda.obj V) hV (isQuasiCompactSpace_yoneda_obj B S hS hVcpt) g
  obtain ⟨U, e, v, I, hI, K, hKfield, hKalg, hKfin, hKsep, eU, hv, heU⟩ :=
    exists_iso_finite_coproduct_spectra_of_isQuasiCompactSpace_etale B S hS hfibre k eV
      (Limits.pullback.fst g f) hfstEt hfibreqc
  refine ⟨U, e, v, I, hI, K, hKfield, hKalg, hKfin, hKsep, eU, ?_, heU⟩
  rw [← hv, ← Category.assoc, e.hom_inv_id, Category.id_comp]

end AlgebraicGeometry.Space

end
