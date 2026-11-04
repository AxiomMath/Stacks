module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.FiniteFactorization.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.FiniteCoproduct

/-!
# Extending a finite surjective morphism across a quasi-compact open

Let `S` be a quasi-compact quasi-separated scheme and let `U ⊆ S` be a quasi-compact open.
A finite surjective morphism `V ⟶ U` extends to a finite surjective morphism `V̄ ⟶ S` whose
base change along `U ⟶ S` recovers `V` as a scheme over `U`.  This is [Stacks, Tag 0CNY].

## Main results

* `Stacks.FiniteFactorization.exists_finite_surjective_extension`: the extension, together with
  the identification of its restriction to `U` with the given morphism.

## Implementation notes

The quasi-compact open is a `AlgebraicGeometry.Scheme.Opens` whose underlying set is assumed
compact, and the base change is the categorical pullback along its inclusion.  The conclusion
records the compatibility of the identifying isomorphism with the two maps to `U`, which is
what makes it an isomorphism of schemes over `U`.

## References

* [Stacks Project, Tag 0CNY](https://stacks.math.columbia.edu/tag/0CNY)
* [Stacks Project, Tag 05K0](https://stacks.math.columbia.edu/tag/05K0)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.FiniteFactorization

/-- Let `S` be a quasi-compact quasi-separated scheme and let `U ⊆ S` be a quasi-compact open.
A finite surjective morphism `f : V ⟶ U` extends to a finite surjective morphism `g : V̄ ⟶ S`:
there is an isomorphism `e : V̄ ×_S U ≅ V` identifying the projection `V̄ ×_S U ⟶ U` with `f`, so
that `e` is an isomorphism of schemes over `U`. -/
@[stacks 0CNY]
theorem exists_finite_surjective_extension {S V : Scheme.{u}}
    [CompactSpace S] [QuasiSeparatedSpace S]
    (U : S.Opens) (hU : IsCompact (U : Set S))
    (f : V ⟶ U.toScheme) [IsFinite f] [Surjective f] :
    ∃ (Vbar : Scheme.{u}) (g : Vbar ⟶ S),
      IsFinite g ∧ Surjective g ∧
        ∃ e : pullback g U.ι ≅ V,
          e.hom ≫ f = pullback.snd g U.ι := by
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace f
  let h : V ⟶ S := f ≫ U.ι
  have : LocallyOfFiniteType h := inferInstance
  have : LocallyQuasiFinite h := inferInstance
  have : QuasiCompact h := inferInstance
  have : IsSeparated h := inferInstance
  obtain ⟨T, j, π, hj, hjqc, hπ, hfac'⟩ := exists_isOpenImmersion_isFinite_factorization h
  have hfac : j ≫ π = f ≫ U.ι := hfac'.symm
  let I : Scheme := j.image
  have : QuasiCompact j := hjqc
  let πI : I ⟶ S := j.imageι ≫ π
  let C : TopologicalSpace.Closeds S := ⟨(U : Set S)ᶜ, U.2.isClosed_compl⟩
  let Z : Scheme := (Scheme.IdealSheafData.vanishingIdeal C).subscheme
  let k : Z ⟶ S := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  let Y : ULift.{u, 0} Bool → Scheme
    | .up true => I
    | .up false => Z
  let m : ∀ b, Y b ⟶ S
    | .up true => πI
    | .up false => k
  let Vbar := ∐ Y
  let g : Vbar ⟶ S := Sigma.desc m
  have hmap (b : ULift.{u, 0} Bool) : Sigma.ι Y b ≫ g = m b := by simp [g]
  have hk : Set.range k = (U : Set S)ᶜ := by
    change Set.range ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι) = _
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hcover : ⋃ b, Set.range (m b).base = Set.univ := by
    ext s
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    by_cases hs : s ∈ U
    · obtain ⟨v, hv⟩ := f.surjective ⟨s, hs⟩
      refine ⟨.up true, j.toImage.base v, ?_⟩
      change π (j v) = s
      rw [← Scheme.Hom.comp_apply, hfac]
      simp [hv]
    · obtain ⟨z, hz⟩ : s ∈ Set.range k := by rwa [hk]
      exact ⟨.up false, z, hz⟩
  have : IsFinite πI := inferInstance
  have : IsFinite k := inferInstance
  have : ∀ b, IsFinite (m b) := by
    rintro ⟨_ | _⟩ <;> dsimp [m, Y] <;> infer_instance
  have : IsFinite g := AlgebraicGeometry.isFinite_sigmaDesc
  have : Surjective g := Surjective.sigmaDesc_of_union_range_eq_univ hcover
  let W : T.Opens := π ⁻¹ᵁ U
  have hpre : j ⁻¹ᵁ W = ⊤ := by
    change j ⁻¹ᵁ (π ⁻¹ᵁ U) = ⊤
    rw [← Scheme.Hom.comp_preimage, hfac]
    simp
  have hjrange : Set.range j ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨v, rfl⟩
    change v ∈ j ⁻¹ᵁ W
    rw [hpre]
    trivial
  let jw : V ⟶ W.toScheme := IsOpenImmersion.lift W.ι j hjrange
  have hjwfac : jw ≫ W.ι = j := IsOpenImmersion.lift_fac W.ι j hjrange
  let πU : W.toScheme ⟶ U.toScheme := π ∣_ U
  have hjwcomp : jw ≫ πU = f := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hjwfac, hfac]
  have : IsFinite (jw ≫ πU) := hjwcomp ▸ inferInstance
  have : IsSeparated πU := inferInstance
  have : IsFinite jw := IsFinite.of_comp jw πU
  have : IsClosedImmersion jw :=
    (IsClosedImmersion.iff_isFinite_and_mono jw).2 ⟨inferInstance, inferInstance⟩
  let A : V.Opens := j ⁻¹ᵁ W
  let eA : A.toScheme ≅ V := V.isoOfEq hpre ≪≫ V.topIso
  have heA : eA.inv ≫ A.ι = 𝟙 V := by simp [eA]
  let jr : A.toScheme ⟶ W.toScheme := j ∣_ W
  have hjr : eA.inv ≫ jr = jw := by
    apply (cancel_mono W.ι).1
    calc
      (eA.inv ≫ jr) ≫ W.ι = eA.inv ≫ (jr ≫ W.ι) := by rw [Category.assoc]
      _ = eA.inv ≫ (A.ι ≫ j) := by rw [morphismRestrict_ι]
      _ = (eA.inv ≫ A.ι) ≫ j := by rw [Category.assoc]
      _ = j := by rw [heA]; simp
      _ = jw ≫ W.ι := hjwfac.symm
  have hjrclosed : IsClosedImmersion (eA.inv ≫ jr) := hjr ▸ inferInstance
  have : IsClosedImmersion jr := by
    rw [← MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion)
      (Arrow.isoMk' (eA.inv ≫ jr) jr eA.symm (Iso.refl W.toScheme) (by simp))]
    exact hjrclosed
  let jRestrImageIso := AlgebraicGeometry.imageMorphismRestrictIso j W
  let jOverUIso : V ≅ pullback W.ι j.imageι :=
    eA.symm ≪≫ asIso jr.toImage ≪≫ jRestrImageIso
  have hJhom : jOverUIso.hom = eA.inv ≫ jr.toImage ≫ jRestrImageIso.hom := by
    simp [jOverUIso]
  have hjOverUIso_snd : jOverUIso.hom ≫ pullback.snd W.ι j.imageι = j.toImage := by
    apply (cancel_mono j.imageι).1
    calc
      (jOverUIso.hom ≫ pullback.snd W.ι j.imageι) ≫ j.imageι =
          jOverUIso.hom ≫ (pullback.fst W.ι j.imageι ≫ W.ι) := by
        rw [Category.assoc, pullback.condition]
      _ = (eA.inv ≫ jr.toImage ≫
          (jRestrImageIso.hom ≫ pullback.fst W.ι j.imageι)) ≫ W.ι := by
        rw [hJhom]; simp only [Category.assoc]
      _ = (eA.inv ≫ jr.toImage ≫ jr.imageι) ≫ W.ι := by
        rw [AlgebraicGeometry.imageMorphismRestrictIso_hom_fst]
      _ = (eA.inv ≫ jr) ≫ W.ι := by rw [Scheme.Hom.toImage_imageι]
      _ = jw ≫ W.ι := by rw [hjr]
      _ = j := hjwfac
      _ = j.toImage ≫ j.imageι := (Scheme.Hom.toImage_imageι j).symm
  have hjImageRange : Set.range j.toImage = Set.range (pullback.snd W.ι j.imageι) := by
    rw [← hjOverUIso_snd]
    exact range_eq_range_of_surjective _ _ jOverUIso.hom rfl
  have hjImageRange' : Set.range j.toImage = (j.imageι ⁻¹ᵁ W : Set I) := by
    rw [hjImageRange, IsOpenImmersion.range_pullbackSnd, Scheme.Opens.opensRange_ι]
  have hcomp : (j.toImage ≫ Sigma.ι Y (.up true)) ≫ g = f ≫ U.ι := by
    rw [Category.assoc, hmap, ← hfac]
    exact Scheme.Hom.toImage_imageι_assoc j π
  have hrangeRestr : Set.range (j.toImage ≫ Sigma.ι Y (.up true)) = g ⁻¹ᵁ U := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      change g ((j.toImage ≫ Sigma.ι Y (.up true)) v) ∈ U
      rw [← Scheme.Hom.comp_apply, hcomp]
      exact (f v).2
    · intro hx
      change g x ∈ U at hx
      cases hxy : (sigmaMk Y).symm x with
      | mk b y =>
        have hy : Sigma.ι Y b y = x := by
          calc
            Sigma.ι Y b y = sigmaMk Y (Sigma.mk b y) := (sigmaMk_mk Y b y).symm
            _ = sigmaMk Y ((sigmaMk Y).symm x) := by rw [hxy]
            _ = x := (sigmaMk Y).apply_symm_apply x
        have hyU : (m b) y ∈ U := by rw [← hmap, Scheme.Hom.comp_apply, hy]; exact hx
        cases b with
        | up b => cases b with
          | false =>
            have hyC : k y ∈ Set.range k := ⟨y, rfl⟩
            rw [hk] at hyC
            exact (hyC hyU).elim
          | true =>
            have hyRange : y ∈ Set.range j.toImage := by
              rw [hjImageRange']
              exact hyU
            obtain ⟨v, hv⟩ := hyRange
            refine ⟨v, ?_⟩
            change Sigma.ι Y (.up true) (j.toImage v) = x
            rw [hv, hy]
  have hpullbackRange : Set.range (pullback.fst g U.ι) = g ⁻¹ᵁ U := by
    rw [IsOpenImmersion.range_pullbackFst, Scheme.Opens.opensRange_ι]
  have hrange : Set.range (pullback.fst g U.ι) =
      Set.range (j.toImage ≫ Sigma.ι Y (.up true)) := hpullbackRange.trans hrangeRestr.symm
  have : IsOpenImmersion (j.toImage ≫ Sigma.ι Y (.up true)) := inferInstance
  let e : pullback g U.ι ≅ V :=
    IsOpenImmersion.isoOfRangeEq (pullback.fst g U.ι) (j.toImage ≫ Sigma.ι Y (.up true)) hrange
  have hef : e.hom ≫ (j.toImage ≫ Sigma.ι Y (.up true)) = pullback.fst g U.ι :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange
  have he : e.hom ≫ f = pullback.snd g U.ι := by
    rw [← cancel_mono U.ι, Category.assoc, ← hcomp, ← Category.assoc, hef]
    exact pullback.condition
  exact ⟨Vbar, g, inferInstance, inferInstance, e, he⟩

end Stacks.FiniteFactorization

end
