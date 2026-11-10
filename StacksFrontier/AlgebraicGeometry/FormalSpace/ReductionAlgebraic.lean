module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Assembly.Relativize
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationSizeBounds
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ActionQuotientFieldPoints
public import StacksFrontier.CategoryTheory.Sites.LocallySurjectiveCoproduct

/-!
# The glued reduction is an algebraic space

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a formal algebraic space over
`S` with atlas `{X_i ⟶ X}` by affine formal algebraic spaces, and let `ι : R ⟶ X` be a
subobject whose base change along each `X_i` is the reduction of `X_i`, exhibited as the sheaf
of an *affine* object `U_i` of the site. Then `R` is an algebraic space over `S`.

## The argument

The one object of the site that the algebraic-space condition asks for is glued from the `U_i`:
the set-theoretic condition on `X` supplies an object `U` of the site surjecting onto it, whose
base change along the — now representable — inclusion `ι` is an object `U_R` of the site
surjecting onto `R`; each `U_i` is étale over `R`, so the base change of `U_i ⟶ R` along
`U_R ⟶ R` is an object of the site étale over `U_R`, and these jointly cover `U_R`. Choosing one
`U_i` through each point of `U_R` and taking the coproduct gives a single object of the site,
surjective and étale over `R`, and **Stacks 0BGR** then delivers the whole algebraic-space
condition.

The sizes stay below the cutoff because each `U_i` is affine and étale-locally dominated by
`U_R`: a locally surjective morphism of representable presheaves does not increase size, which
is `AlgebraicGeometry.Space.size_le_of_isLocallySurjective`, and there are at most
`2 ^ size U_R` points of `U_R`.

## Main results

* `AlgebraicGeometry.FormalSpace.relativelyRepresentable_diag_of_mono`: a subobject of a sheaf
  with representable diagonal has representable diagonal.
* `AlgebraicGeometry.FormalSpace.relativelyRepresentable_uliftYoneda_of_sheaf`: representability
  relative to the sheafified Yoneda embedding passes to the universe-lifted one.
* `AlgebraicGeometry.FormalSpace.relative_surjective_of_isLocallySurjective`: a representable
  locally surjective morphism of presheaves is relatively surjective.
* `AlgebraicGeometry.FormalSpace.size_le_of_affineChart_relative_etale`: an affine chart étale
  over a sheaf which receives a locally surjective morphism from `h_U` has size at most that of
  `U`.
* `AlgebraicGeometry.FormalSpace.relative_etale_of_isPullback`: a chart of a base change of a
  representable étale morphism along a monomorphism is étale.
* `AlgebraicGeometry.FormalSpace.relative_etale_of_openCover`: relative étaleness is Zariski
  local on the source of a representable morphism.
* `AlgebraicGeometry.FormalSpace.isAlgebraicSpaceULift_of_reduced_etale_cover_of_mono_sheafHom`:
  the subobject `R` above is an algebraic space over `S`.

## References

* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0BGR](https://stacks.math.columbia.edu/tag/0BGR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Diagonals and representability -/

/-- The big fppf site of `S` is subcanonical. -/
private instance : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS

/-- The big fppf site of `S` has binary products. -/
private instance : HasBinaryProducts (BigFppfOver B S hS) :=
  hasBinaryProducts_of_hasTerminal_and_pullbacks _

private instance : PreservesLimitsOfShape WalkingCospan
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) := by
  dsimp [Sheaf.sheafifiedYoneda]
  infer_instance

private instance : PreservesLimitsOfShape (Discrete WalkingPair)
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) := by
  dsimp [Sheaf.sheafifiedYoneda]
  infer_instance

/-- **A subobject of a sheaf with representable diagonal has representable diagonal.** A pair of
scheme-valued points of the subobject has the same fibre product over the subobject as over the
ambient sheaf, the inclusion being a monomorphism. -/
theorem relativelyRepresentable_diag_of_mono {X R : FppfSheaf B S hS} (ι : R ⟶ X) (hmono : Mono ι)
    (hX : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
      (diag X)) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable (diag R) := by
  apply Functor.relativelyRepresentable.diag_of_map_from_obj
  intro a g a' g'
  obtain ⟨b, snd, fst, hpb⟩ := Functor.relativelyRepresentable.of_diag hX (g ≫ ι) (g' ≫ ι)
  exact ⟨b, snd, fst, (isPullback_comp_mono_iff ι).1 hpb⟩

/-- **Representability relative to the sheafified Yoneda embedding passes to the universe-lifted
Yoneda embedding of presheaves.** The two embeddings agree after including sheaves into
presheaves, the big fppf site of `S` being subcanonical. -/
theorem relativelyRepresentable_uliftYoneda_of_sheaf {F G : FppfSheaf B S hS} (m : F ⟶ G)
    (hm : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable m) :
    (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).relativelyRepresentable m.hom := by
  let J := BigFppfOver.topology B S hS
  let Pf := sheafToPresheaf J (Type (u + 1))
  exact Space.relativelyRepresentable_of_iso_embedding' (sheafifiedYonedaCompForgetIso' B S hS)
    (Pf.map m) ((Space.relativelyRepresentable_comp_map_iff (Sheaf.sheafifiedYoneda J) Pf m).mpr hm)

/-! ### Local surjectivity and the two relative properties -/

/-- Local surjectivity of the universe-lifted Yoneda presheaf of a morphism of the site is local
surjectivity of its ordinary Yoneda presheaf: the two image sieves are the same. -/
private theorem isLocallySurjective_yoneda_map_of_uliftYoneda
    {V W : BigFppfOver B S hS} (f : V ⟶ W)
    (hf : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      ((uliftYoneda.{u + 1}).map f)) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (yoneda.map f) := by
  refine ⟨fun {T} s ↦ (BigFppfOver.topology B S hS).superset_covering ?_
    (hf.imageSieve_mem (ULift.up s))⟩
  rintro V' g ⟨z, hz⟩
  exact ⟨z.down, congrArg ULift.down hz⟩

/-- **A representable locally surjective morphism of presheaves is relatively surjective.**
Every represented base change of it is locally surjective, hence surjective on underlying
schemes. -/
theorem relative_surjective_of_isLocallySurjective
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (f : F ⟶ G)
    (hrep : (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).relativelyRepresentable f)
    (hf : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f) :
    (MorphismProperty.inverseImage (@Surjective : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) f :=
  ⟨hrep, fun _ _ _ _ p hp ↦ Space.surjective_of_isLocallySurjective B S hS p
    (isLocallySurjective_yoneda_map_of_uliftYoneda B S hS p
      (Presheaf.isLocallySurjective_of_isPullback (BigFppfOver.topology B S hS) hp.flip
        (hf := hf)))⟩

/-- **An affine chart étale over a sheaf which receives a locally surjective morphism from `h_U`
has size at most that of `U`.** The base change of the chart along the locally surjective
morphism is étale over `U`, hence locally of finite type, and maps locally surjectively onto the
chart; a locally surjective morphism of representable presheaves does not increase size. -/
theorem size_le_of_affineChart_relative_etale {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {Z : FppfSheaf B S hS}
    (U V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (eV : Z.obj ≅ (uliftYoneda.{u + 1}).obj V)
    (t : (uliftYoneda.{u + 1}).obj U ⟶ X)
    (ht : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) t)
    (f : Z.obj ⟶ X)
    (hf : (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) f) :
    ((BigFppfOver.toScheme B S hS).obj V).size ≤
      ((BigFppfOver.toScheme B S hS).obj U).size := by
  let Y := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)
  let W := hf.rep.pullback t
  let p : W ⟶ U := hf.rep.snd t
  let a : W ⟶ V := Y.preimage (hf.rep.fst t ≫ eV.hom)
  have hp : Etale ((BigFppfOver.toScheme B S hS).map p) := hf.property_snd t
  have _ : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map p) := inferInstance
  have _ : CompactSpace ((BigFppfOver.toScheme B S hS).obj V : Type u) :=
    Scheme.compactSpace_of_isAffine _
  have ha : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Y.map a) := by
    have hs : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (hf.rep.fst t) :=
      Presheaf.isLocallySurjective_of_isPullback (BigFppfOver.topology B S hS)
        (hf.rep.isPullback t) (hf := ht)
    have hae : Y.map a = hf.rep.fst t ≫ eV.hom := Y.map_preimage _
    rw [hae]
    infer_instance
  obtain ⟨E, hE⟩ := Space.exists_fppfCovering_of_isLocallySurjective B S hS a
    (isLocallySurjective_yoneda_map_of_uliftYoneda B S hS a ha)
  choose gg hgg using hE
  exact size_le_of_compact_of_fppf_factorsThrough
    ((BigFppfOver.toScheme B S hS).map p) ((BigFppfOver.toScheme B S hS).map a) E gg hgg

/-! ### Étaleness of a chart of a base change -/

/-- **Relative étaleness is Zariski local on the source of a representable morphism.** If a
representable morphism out of the universe-lifted Yoneda presheaf of an object of the site is
étale after restriction to each member of a jointly surjective family of open immersions into
that object, it is étale. -/
theorem relative_etale_of_openCover {I : Type u} {W : BigFppfOver B S hS}
    (V : I → BigFppfOver B S hS) (kk : ∀ i, V i ⟶ W)
    (hk : ∀ i, AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (kk i)))
    (hcov : ∀ z : (BigFppfOver.toScheme B S hS).obj W,
      ∃ i, z ∈ Set.range ((BigFppfOver.toScheme B S hS).map (kk i)))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (q : (uliftYoneda.{u + 1}).obj W ⟶ X)
    (hrep : (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).relativelyRepresentable q)
    (hf : ∀ i, (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1})
        ((uliftYoneda.{u + 1}).map (kk i) ≫ q)) :
    (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) q := by
  let H := BigFppfOver.toScheme B S hS
  let Y := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)
  refine ⟨hrep, fun T Z g a p hp ↦ ?_⟩
  let l : Z ⟶ W := Y.preimage a
  have hl : Y.map l = a := Y.map_preimage a
  let DW : (H.obj W).OpenCover :=
    { I₀ := I
      X i := H.obj (V i)
      f i := H.map (kk i)
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨hcov, hk⟩ }
  let pb (i : I) := (IsPullback.of_hasPullback (kk i) l).map H
  have hr (i : I) : AlgebraicGeometry.IsOpenImmersion (H.map (pullback.snd (kk i) l)) :=
    MorphismProperty.of_isPullback (pb i) (hk i)
  let E : (H.obj Z).OpenCover :=
    { I₀ := I
      X i := H.obj (pullback (kk i) l)
      f i := H.map (pullback.snd (kk i) l)
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun z ↦ ?_, hr⟩
        obtain ⟨i, y, hy⟩ := Scheme.Cover.exists_eq (DW.pullback₂ (H.map l)) z
        refine ⟨i, (pb i).isoPullback.inv y, ?_⟩
        exact (congrArg (fun b : pullback (H.map (kk i)) (H.map l) ⟶ H.obj Z ↦ b y)
          (pb i).isoPullback_inv_snd).trans hy }
  have _ : IsZariskiLocalAtSource (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u})
  change Etale (H.map p)
  refine IsZariskiLocalAtSource.of_openCover (P := @Etale.{u}) E (fun i ↦ ?_)
  have hp' : IsPullback a (Y.map p) q g := hp
  have hs := (IsPullback.of_hasPullback (kk i) l).map Y
  rw [hl] at hs
  have hc := hs.paste_vert hp'
  rw [← Y.map_comp] at hc
  change Etale (H.map (pullback.snd (kk i) l) ≫ H.map p)
  rw [← Functor.map_comp]
  exact (hf i).property g (Y.map (pullback.fst (kk i) l)) (pullback.snd (kk i) l ≫ p) hc

/-! ### The glued reduction is an algebraic space -/

/-- **The glued reduction is an algebraic space.** Let `X` be a formal algebraic space over `S`
with atlas `{X_i ⟶ X}` by affine formal algebraic spaces and let `ι : R ⟶ X` be a representable
thickening whose base change along each `X_i` is the sheaf of an *affine* object `U_i` of the
site, with the `U_i` jointly covering `R`. Then `R` is an algebraic space over `S`. -/
theorem isAlgebraicSpaceULift_of_reduced_etale_cover_of_mono_sheafHom
    [HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS)]
    {X R : FppfSheaf B S hS} (ι : R ⟶ X) (hmono : Mono ι)
    (hX : IsFormalAlgebraicSpace B S hS X) {I : Type (u + 1)}
    (Xi Ri : I → FppfSheaf B S hS) (Ui : I → BigFppfOver B S hS)
    (hUi : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (Ui i)))
    (eRi : ∀ i, (uliftYoneda.{u + 1}).obj (Ui i) ≅ (Ri i).obj)
    (f : ∀ i, Xi i ⟶ X) (k : ∀ i, Ri i ⟶ R) (j : ∀ i, Ri i ⟶ Xi i)
    (hsq : ∀ i, IsPullback (k i) (j i) ι (f i))
    (hf : ∀ i, ∃ hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f i).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ q ↦ Space.IsEtaleULift.{u + 1} B S hS q.hom) (f i).hom hfi)
    (hcoverR : Sheaf.IsLocallySurjective (Limits.Sigma.desc k))
    (hι : Space.IsRepresentableThickeningULift.{u + 1} B S hS ι.hom) :
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS R.obj := by
  classical
  let J := BigFppfOver.topology B S hS
  let C := BigFppfOver B S hS
  let H := BigFppfOver.toScheme B S hS
  let Y := uliftYoneda.{u + 1} (C := C)
  let P : MorphismProperty C :=
    MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u}) H
  let _ : MorphismProperty.RespectsIso (@Etale.{u}) := .mk _
    (fun e f hf ↦ by have _ := hf; infer_instance)
    (fun e f hf ↦ by have _ := hf; infer_instance)
  let _ : P.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  -- the diagonal of `R` is representable, being that of a subobject of `X`
  have hdiagR : (Sheaf.sheafifiedYoneda J).relativelyRepresentable (diag R) :=
    relativelyRepresentable_diag_of_mono B S hS ι hmono
      (relativelyRepresentable_diag_of_isFormalAlgebraicSpace B S hS hX)
  let e := sheafifiedYonedaCompForgetIso' B S hS
  -- every morphism from a universe-lifted representable into `R` is representable
  have hrepOf : ∀ (a : C) (t : Y.obj a ⟶ R.obj), Y.relativelyRepresentable t := by
    intro a t
    have h1 : Y.relativelyRepresentable ((⟨(e.app a).hom ≫ t⟩ :
        (Sheaf.sheafifiedYoneda J).obj a ⟶ R)).hom :=
      relativelyRepresentable_uliftYoneda_of_sheaf B S hS _
        (Functor.relativelyRepresentable.of_diag hdiagR _)
    exact ((Y.relativelyRepresentable).cancel_left_of_respectsIso (e.app a).hom t).mp h1
  -- the charts of the covering pieces, étale over `R`
  let gi (i : I) : Y.obj (Ui i) ⟶ R.obj := (eRi i).hom ≫ (k i).hom
  have hgi (i : I) : P.relative Y (gi i) :=
    relative_etale_of_isPullback B S hS ι (f i) (k i) (j i) (hsq i) (hf i)
      (Ui i) (eRi i) (hrepOf (Ui i) (gi i))
  have he (i : I) : P.relative Y (k i).hom :=
    ((P.relative Y).cancel_left_of_respectsIso (eRi i).hom (k i).hom).mp (hgi i)
  -- one object of the site mapping locally surjectively onto `R`
  obtain ⟨U, -, hU, -, ⟨eU⟩, -, t, ht, -⟩ := hX.1
  let t' : Y.obj U ⟶ X.obj := eU.inv ≫ t.hom
  have ht' : Presheaf.IsLocallySurjective J t' := by
    have _ : Sheaf.IsLocallySurjective t := (Sheaf.isLocallySurjective_iff_epi t).mpr ht
    have _ : Presheaf.IsLocallySurjective J t.hom := ‹Sheaf.IsLocallySurjective t›
    dsimp only [t']
    infer_instance
  let UR : C := hι.rep.pullback t'
  let tR : Y.obj UR ⟶ R.obj := hι.rep.fst t'
  have htR : Presheaf.IsLocallySurjective J tR :=
    Presheaf.isLocallySurjective_of_isPullback J (hι.rep.isPullback t') (hf := ht')
  have hsize (i : I) : (H.obj (Ui i)).size ≤ (H.obj UR).size := by
    have _ : IsAffine (H.obj (Ui i)) := hUi i
    exact size_le_of_affineChart_relative_etale B S hS UR (Ui i) (eRi i).symm tR htR
      (k i).hom (he i)
  -- the fibre of each chart over `UR`
  let Wi (i : I) : C := (hgi i).rep.pullback tR
  let pi (i : I) : Wi i ⟶ UR := (hgi i).rep.snd tR
  let ri (i : I) : Wi i ⟶ Ui i := Y.preimage ((hgi i).rep.fst tR)
  have hpi (i : I) : Etale (H.map (pi i)) := (hgi i).property_snd tR
  have hfacR (i : I) : Y.map (ri i) ≫ gi i = Y.map (pi i) ≫ tR := by
    rw [Y.map_preimage]
    exact ((hgi i).rep.isPullback tR).w
  have hpoint : ∀ x : H.obj UR, ∃ i, x ∈ Set.range (H.map (pi i)) := by
    intro x
    have hmem := Sheaf.iSup_imageSieve_mem_of_isLocallySurjective_sigmaDesc J Ri R k hcoverR UR
      (uliftYonedaEquiv tR)
    obtain ⟨T, b, y, hb, hy⟩ := exists_mem_sieve_point B S hS hmem x
    simp only [iSup, Sieve.sSup_apply, Set.mem_range] at hb
    obtain ⟨-, ⟨i, rfl⟩, z, hz⟩ := hb
    have hw : (uliftYonedaEquiv.symm z ≫ (eRi i).inv) ≫ gi i = Y.map b ≫ tR := by
      have h0 : uliftYonedaEquiv.symm z ≫ (k i).hom = Y.map b ≫ tR := by
        apply uliftYonedaEquiv.injective
        rw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
        exact hz.trans (uliftYonedaEquiv_naturality.{u + 1} tR b.op)
      simpa only [gi, Category.assoc, Iso.inv_hom_id_assoc] using h0
    let aa : T ⟶ Wi i := Y.preimage
      (((hgi i).rep.isPullback tR).lift (uliftYonedaEquiv.symm z ≫ (eRi i).inv) (Y.map b) hw)
    have hab : aa ≫ pi i = b := by
      apply Y.map_injective
      rw [Y.map_comp, Y.map_preimage]
      exact ((hgi i).rep.isPullback tR).lift_snd _ _ _
    refine ⟨i, H.map aa y, ?_⟩
    have h3 : H.map (aa ≫ pi i) y = H.map b y := by rw [hab]
    rw [Functor.map_comp] at h3
    exact h3.trans hy
  choose idx hidx using hpoint
  -- the coproduct of one chart through each point of `UR` is again an object of the site
  have hcoprod : B.Contains (∐ fun x : H.obj UR ↦ H.obj (Ui (idx x))) :=
    lt_of_le_of_lt (schemeSize_coproduct_le _ (2 ^ (H.obj UR).size)
      ((Scheme.aleph0_le_size _).trans (Cardinal.cantor _).le)
      (Scheme.mk_le_two_pow_size _)
      (fun x ↦ (hsize (idx x)).trans (Cardinal.cantor _).le))
      (B.cutoff_isStrongPrelimit UR.left.property)
  obtain ⟨W, kk, q, hkq, hkOI, hkcov, -⟩ :=
    Space.exists_map_from_coproduct B S hS R (fun x ↦ Ui (idx x))
      (fun x ↦ gi (idx x)) hcoprod
  have hqrep : Y.relativelyRepresentable q := hrepOf W q
  have hqet : P.relative Y q :=
    relative_etale_of_openCover B S hS _ kk hkOI hkcov q hqrep
      (fun x ↦ (hkq x).symm ▸ hgi (idx x))
  -- the glued chart is locally surjective
  have hqsurj : Presheaf.IsLocallySurjective J q := by
    have hmem : Sieve.ofArrows (fun x : H.obj UR ↦ Wi (idx x))
        (fun x ↦ pi (idx x)) ∈ J UR :=
      Space.sieve_ofArrows_mem_topology_of_etale B hS _ _
        (fun x ↦ ⟨x, hidx x⟩) (fun x ↦ hpi (idx x))
    have hu : Presheaf.IsLocallySurjective J
        (Sigma.desc fun x : H.obj UR ↦ Y.map (pi (idx x))) :=
      (GrothendieckTopology.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map J
        (fun x : H.obj UR ↦ pi (idx x))).mp hmem
    have hdesc : Presheaf.IsLocallySurjective J
        (Sigma.desc fun x : H.obj UR ↦ gi (idx x)) :=
      Presheaf.isLocallySurjective_sigmaDesc_of_fac J (fun x ↦ gi (idx x))
        (fun x ↦ Y.map (pi (idx x))) (fun x ↦ Y.map (ri (idx x))) tR hu htR
        (fun x ↦ hfacR (idx x))
    let aa : (∐ fun x : H.obj UR ↦ Y.obj (Ui (idx x))) ⟶ Y.obj W :=
      Sigma.desc fun x ↦ Y.map (kk x)
    have hafac : aa ≫ q = Sigma.desc fun x : H.obj UR ↦ gi (idx x) := by
      refine Sigma.hom_ext _ _ (fun x ↦ ?_)
      rw [← Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc]
      exact hkq x
    have _ := hdesc
    have _ : Presheaf.IsLocallySurjective J (aa ≫ q) := by rw [hafac]; infer_instance
    exact Presheaf.isLocallySurjective_of_isLocallySurjective J aa q
  refine Space.isAlgebraicSpaceULift_of_relative_surjective_etale B S hS R.property
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS W) q ?_ hqet
  exact relative_surjective_of_isLocallySurjective B S hS q hqrep hqsurj

end AlgebraicGeometry.FormalSpace

end
