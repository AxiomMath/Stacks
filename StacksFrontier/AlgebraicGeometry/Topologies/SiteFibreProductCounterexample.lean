module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Analysis.Real.Cardinality
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcCoveringPullbackSheaves

/-!
# Tag 03OJ is false when fibre products of the site are not fibre products of schemes

Tag 03OJ considers a site `C` whose underlying category is a full subcategory of `Sch/S`.  A site
in the sense of Stacks 00VH carries the fibre products `Uᵢ ×_U V` of its coverings, formed **in
`C`**.  The proof of the tag ("after some formal arguments this is exactly Theorem 03O8") reads the
sheaf condition on `C` as the fpqc sheaf condition on schemes, which needs those fibre products to
be the fibre products of schemes.  This file shows that this is not a formality: there is a site
satisfying the site axioms and the four conditions of the tag on which the presheaf `𝒪` is not a
sheaf, so the first assertion of the tag fails.

## The site

Let `S = Spec ℚ` and `X = Spec ℝ`, a scheme over `S`.  Let `C` be the full subcategory of `Sch/S`
on the two objects `S/S` and `X/S`.  Every ring endomorphism of `ℝ` is the identity
(`Real.RingHom.unique`), so `X/S` has no automorphism other than the identity and `C` is thin; it
is totally ordered, `X` lying over `S`.  Hence `C` has all fibre products: the fibre product of
`X` with itself over `S` **in `C`** is `X`, whereas the fibre product of schemes is
`Spec (ℝ ⊗_ℚ ℝ)`.  Take every nonempty family of arrows with a common target as a covering.  These
satisfy the site axioms (Stacks 00VH), and every covering is an fpqc covering of schemes: all
arrows are flat (their targets are spectra of fields), and each covering contains a surjective
quasi-compact arrow.  The Zariski coverings of the spectrum of a field are refined by the identity,
and `S/S` is an object.

On the covering `{X ⟶ S}` every section of `𝒪(X) = ℝ` is a compatible family, because `C` is thin,
but only the sections of `𝒪(S) = ℚ` glue; `ℝ` being uncountable, `𝒪` is not a sheaf.

## Main results

* `Stacks.Sites.not_isSheaf_structurePresheaf_counterexample`: on that site `𝒪` is not a sheaf.
* `Stacks.Sites.not_forall_isSheaf_structurePresheaf`: the first assertion of Tag 03OJ, with the
  site axioms and all four conditions but without the assumption that the fibre products along
  coverings are fibre products of schemes, is false — even with all fibre products in `C`.

The corrected form of the tag is
`Stacks.Sites.isSheaf_structurePresheaf_and_exists_iso_siteAssociatedModule`.

## References

* [Stacks Project, Tag 03OJ](https://stacks.math.columbia.edu/tag/03OJ)
* [Stacks Project, Tag 00VH](https://stacks.math.columbia.edu/tag/00VH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites

open _root_.AlgebraicGeometry

/-! ### A criterion for fpqc coverings -/

/-- **A family of flat morphisms containing a surjective quasi-compact member is an fpqc covering
family.** -/
theorem ofArrows_mem_fpqcPrecoverage {Y : Scheme.{0}} {ι : Type*} {X : ι → Scheme.{0}}
    (f : ∀ i, X i ⟶ Y) (hflat : ∀ i, Flat (f i)) (i₀ : ι) [Surjective (f i₀)]
    [QuasiCompact (f i₀)] : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage Y := by
  refine ⟨?_, (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun y => ⟨i₀, (f i₀).surjective y⟩, hflat⟩⟩
  change (PreZeroHypercover.mk ι X f).presieve₀ ∈ Scheme.qcPrecoverage Y
  rw [Scheme.presieve₀_mem_qcPrecoverage_iff]
  exact QuasiCompactCover.of_hom (𝒱 := PreZeroHypercover.singleton.{0} (f i₀))
    ⟨fun _ => i₀, fun _ => 𝟙 _, fun _ => Category.id_comp _⟩

/-! ### The site -/

/-- The base `S = Spec ℚ`. -/
noncomputable abbrev cexBase : Scheme.{0} := Spec (.of ℚ)

/-- The scheme `X = Spec ℝ` over `S`, as an object of `Sch/S`. -/
noncomputable abbrev cexX : Over cexBase := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℝ)))

/-- The base `S/S`, as an object of `Sch/S`. -/
noncomputable abbrev cexS : Over cexBase := Over.mk (𝟙 cexBase)

/-- The two objects of the site. -/
def cexProp : ObjectProperty (Over cexBase) := fun Y => Y = cexS ∨ Y = cexX

/-- **The underlying category of the site**: the full subcategory of `Sch/S` on `S/S` and
`X/S`. -/
abbrev CexSite : Type 1 := cexProp.FullSubcategory

/-- The canonical functor of the site, the inclusion into `Sch/S`. -/
noncomputable abbrev cexToOver : CexSite ⥤ Over cexBase := cexProp.ι

/-- The object `S/S` of the site. -/
noncomputable abbrev cexSObj : CexSite := ⟨cexS, Or.inl rfl⟩

/-- The object `X/S` of the site. -/
noncomputable abbrev cexXObj : CexSite := ⟨cexX, Or.inr rfl⟩

/-- An object of the site is `S/S` or `X/S`. -/
theorem cexSite_cases (A : CexSite) : A = cexSObj ∨ A = cexXObj := by
  obtain ⟨A, rfl | rfl⟩ := A
  exacts [Or.inl rfl, Or.inr rfl]

/-- Morphisms of schemes from the spectrum of a subring of `ℝ` to `Spec ℝ` are unique. -/
theorem subsingleton_hom_spec_real (A : CommRingCat.{0}) (j : A ⟶ CommRingCat.of ℝ)
    (hj : Function.Injective j) : Subsingleton (Spec A ⟶ Spec (.of ℝ)) := by
  refine ⟨fun f g => ?_⟩
  rw [← Spec.map_preimage f, ← Spec.map_preimage g]
  congr 1
  ext x
  apply hj
  change (Spec.preimage f ≫ j) x = (Spec.preimage g ≫ j) x
  rw [show Spec.preimage f ≫ j = Spec.preimage g ≫ j from
    CommRingCat.hom_ext (Subsingleton.elim _ _)]

/-- Morphisms of schemes over `S` into `X` are unique. -/
theorem subsingleton_hom_cexX (Y : Over cexBase) (hY : Y = cexS ∨ Y = cexX) :
    Subsingleton (Y ⟶ cexX) := by
  refine ⟨fun f g => Over.OverMorphism.ext ?_⟩
  rcases hY with rfl | rfl
  · exact (subsingleton_hom_spec_real _ (CommRingCat.ofHom (algebraMap ℚ ℝ))
      (algebraMap ℚ ℝ).injective).elim _ _
  · exact (subsingleton_hom_spec_real _ (𝟙 _) Function.injective_id).elim _ _

/-- Morphisms of schemes over `S` into `S/S` are unique. -/
theorem subsingleton_hom_cexS (Y : Over cexBase) : Subsingleton (Y ⟶ cexS) :=
  ⟨fun f g => Over.OverMorphism.ext (((Category.comp_id f.left).symm.trans (Over.w f)).trans
    ((Category.comp_id g.left).symm.trans (Over.w g)).symm)⟩

/-- **The site is thin.** -/
instance (A B : CexSite) : Subsingleton (A ⟶ B) := by
  refine ⟨fun f g => ObjectProperty.hom_ext _ ?_⟩
  obtain ⟨B, rfl | rfl⟩ := B
  · exact (subsingleton_hom_cexS A.obj).elim _ _
  · exact (subsingleton_hom_cexX A.obj A.property).elim _ _

/-- Every object maps to `S/S`. -/
noncomputable def toCexS (A : CexSite) : A ⟶ cexSObj :=
  ObjectProperty.homMk (Over.homMk A.obj.hom (Category.comp_id _))

/-- `X/S` maps to every object. -/
noncomputable def fromCexX (A : CexSite) : cexXObj ⟶ A := by
  classical
  refine if h : A = cexSObj then h ▸ toCexS cexXObj else ?_
  have hA : A = cexXObj := (cexSite_cases A).resolve_left h
  exact hA ▸ 𝟙 _

/-- **The site is totally ordered.** -/
theorem cexSite_total (A B : CexSite) : Nonempty (A ⟶ B) ∨ Nonempty (B ⟶ A) := by
  rcases cexSite_cases A with rfl | rfl
  · exact Or.inr ⟨toCexS B⟩
  · exact Or.inl ⟨fromCexX B⟩

/-- In a thin category, a commutative square is a pullback as soon as every pair of arrows to the
two sides factors through the corner. -/
theorem isPullback_of_thin {D : Type*} [Category D] [∀ A B : D, Subsingleton (A ⟶ B)]
    {P A B T : D} (fst : P ⟶ A) (snd : P ⟶ B) (f : A ⟶ T) (g : B ⟶ T)
    (h : ∀ (W : D), (W ⟶ A) → (W ⟶ B) → Nonempty (W ⟶ P)) : IsPullback fst snd f g :=
  IsPullback.of_isLimit (c := PullbackCone.mk fst snd (Subsingleton.elim _ _))
    (PullbackCone.IsLimit.mk _ (fun s => (h s.pt s.fst s.snd).some)
      (fun _ => Subsingleton.elim _ _) (fun _ => Subsingleton.elim _ _)
      (fun _ _ _ _ => Subsingleton.elim _ _))

/-- **The site has all fibre products.** -/
instance : HasPullbacks CexSite := by
  refine @hasPullbacks_of_hasLimit_cospan _ _ fun {A B T} f g => ?_
  rcases cexSite_total A B with ⟨⟨u⟩⟩ | ⟨⟨v⟩⟩
  · exact (isPullback_of_thin (𝟙 A) u f g fun _ a _ => ⟨a⟩).hasPullback
  · exact (isPullback_of_thin v (𝟙 B) f g fun _ _ b => ⟨b⟩).hasPullback

/-- The site is essentially small: it has two objects. -/
instance : EssentiallySmall.{0} CexSite := by
  have : Small.{0} CexSite := small_of_surjective (f := fun b : Bool =>
    if b then cexSObj else cexXObj) (fun A => by
      rcases cexSite_cases A with rfl | rfl
      exacts [⟨true, rfl⟩, ⟨false, rfl⟩])
  exact essentiallySmall_of_small_of_locallySmall _

/-- **The coverings of the site**: all nonempty families of arrows with a common target. -/
def cexK : Precoverage CexSite where
  coverings T := {R | ∃ (Y : CexSite) (f : Y ⟶ T), R f}

/-- Every isomorphism of the site is a covering. -/
instance : cexK.HasIsos where
  mem_coverings_of_isIso f _ := ⟨_, f, Presieve.singleton.mk⟩

/-- The coverings of the site are stable under composition. -/
instance : cexK.IsStableUnderComposition where
  comp_mem_coverings f hf σ Y g hg := by
    obtain ⟨_, _, ⟨i⟩⟩ := hf
    obtain ⟨_, _, ⟨j⟩⟩ := hg i
    exact ⟨_, _, Presieve.ofArrows.mk (⟨i, j⟩ : Σ i, σ i)⟩

/-- The coverings of the site are stable under base change. -/
instance : cexK.IsStableUnderBaseChange where
  mem_coverings_of_isPullback f hR := by
    intros
    obtain ⟨_, _, ⟨i⟩⟩ := hR
    exact ⟨_, _, Presieve.ofArrows.mk i⟩

/-- The fibre products along the coverings of the site exist. -/
instance : cexK.HasPullbacks where
  hasPullbacks_of_mem _ _ := inferInstance

/-- The underlying scheme of an object of the site is the spectrum of a field. -/
theorem cexSite_left (A : CexSite) :
    (cexToOver.obj A).left = Spec (.of ℚ) ∨ (cexToOver.obj A).left = Spec (.of ℝ) := by
  rcases cexSite_cases A with rfl | rfl
  exacts [Or.inl rfl, Or.inr rfl]

/-- The underlying scheme of an object of the site is affine, integral, nonempty and a point. -/
theorem cexSite_left_props (A : CexSite) :
    IsAffine (cexToOver.obj A).left ∧ IsIntegral (cexToOver.obj A).left ∧
      Subsingleton (cexToOver.obj A).left ∧ Nonempty (cexToOver.obj A).left := by
  rcases cexSite_cases A with rfl | rfl <;>
    exact ⟨(inferInstance : IsAffine (Spec _)), (inferInstance : IsIntegral (Spec _)),
      (inferInstance : Subsingleton (Spec _)), (inferInstance : Nonempty (Spec _))⟩

/-- **Condition (4) of Tag 03OJ for the site: every covering is an fpqc covering of schemes.** -/
theorem cex_fpqc (T : CexSite) (Q : Presieve T) (hQ : Q ∈ cexK T) :
    Presieve.map (cexToOver ⋙ Over.forget cexBase) Q ∈
      Scheme.fpqcPrecoverage ((cexToOver.obj T).left) := by
  obtain ⟨ι, Z, g, rfl⟩ := Q.exists_eq_ofArrows
  obtain ⟨_, _, ⟨i₀⟩⟩ := hQ
  rw [Presieve.map_ofArrows]
  obtain ⟨hTa, hTi, hTs, -⟩ := cexSite_left_props T
  obtain ⟨hYa, -, -, hYn⟩ := cexSite_left_props (Z i₀)
  have : IsAffine ((cexToOver ⋙ Over.forget cexBase).obj T) := hTa
  have : IsIntegral ((cexToOver ⋙ Over.forget cexBase).obj T) := hTi
  have : Subsingleton ((cexToOver ⋙ Over.forget cexBase).obj T) := hTs
  have : IsAffine ((cexToOver ⋙ Over.forget cexBase).obj (Z i₀)) := hYa
  have : Surjective ((cexToOver ⋙ Over.forget cexBase).map (g i₀)) :=
    ⟨fun y => ⟨Classical.choice hYn, Subsingleton.elim _ _⟩⟩
  exact ofArrows_mem_fpqcPrecoverage _ (fun i => inferInstance) i₀

/-- **Condition (2) of Tag 03OJ for the site: every Zariski covering is refined by a covering.** -/
theorem cex_zariski (T : CexSite) (R : Presieve ((cexToOver.obj T).left))
    (hR : R ∈ Scheme.zariskiPrecoverage ((cexToOver.obj T).left)) :
    ∃ Q : Presieve T, Q ∈ cexK T ∧
      Presieve.map (cexToOver ⋙ Over.forget cexBase) Q ≤ (Sieve.generate R).arrows := by
  obtain ⟨-, -, hTs, hTn⟩ := cexSite_left_props T
  refine ⟨Presieve.singleton (𝟙 T), ⟨T, 𝟙 T, Presieve.singleton.mk⟩, ?_⟩
  rw [Presieve.map_singleton, Presieve.singleton_le_iff, CategoryTheory.Functor.map_id]
  obtain ⟨ι, X, f, rfl⟩ := R.exists_eq_ofArrows
  rw [Scheme.zariskiPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hR
  obtain ⟨i, x, -⟩ := hR.1 (Classical.choice hTn)
  have : IsOpenImmersion (f i) := hR.2 i
  have : Surjective (f i) := ⟨fun y => ⟨x, Subsingleton.elim _ _⟩⟩
  have : IsIso (f i) :=
    (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, inferInstance⟩
  exact ⟨_, inv (f i), f i, Presieve.ofArrows.mk i, IsIso.inv_hom_id _⟩

/-- **Condition (3) of Tag 03OJ for the site: `S/S` is an object.** -/
theorem cex_terminal : ∃ T : CexSite, Nonempty (cexToOver.obj T ≅ Over.mk (𝟙 cexBase)) :=
  ⟨cexSObj, ⟨Iso.refl _⟩⟩

/-! ### `𝒪` is not a sheaf -/

/-- The arrow `X ⟶ S` of the site. -/
noncomputable abbrev cexπ : cexXObj ⟶ cexSObj := toCexS cexXObj

/-- **On the site, `𝒪` is not a sheaf.** -/
theorem not_isSheaf_structurePresheaf_counterexample :
    ¬ Presheaf.IsSheaf cexK.toGrothendieck (structurePresheaf cexBase cexToOver) := by
  intro h
  let E : RingCat.{0} := RingCat.of (Polynomial ℤ)
  let P := structurePresheaf cexBase cexToOver ⋙ coyoneda.obj (op E)
  have hsing : (Presieve.singleton cexπ).IsSheafFor P :=
    (Presieve.isSheafFor_iff_generate _).2
      (h E _ (Precoverage.generate_mem_toGrothendieck ⟨_, cexπ, Presieve.singleton.mk⟩))
  rw [← Presieve.ofArrows_pUnit.{0}, Presieve.isSheafFor_arrows_iff] at hsing
  have hsurj : Function.Surjective (P.map cexπ.op) := fun s => by
    obtain ⟨t, ht, -⟩ := hsing (fun _ => s) fun _ _ _ gi gj _ => by
      rw [Subsingleton.elim gi gj]
    exact ⟨t, ht PUnit.unit⟩
  have hinj : ∀ R : RingCat.{0}, Function.Injective fun φ : E ⟶ R => φ.hom Polynomial.X :=
    fun R φ ψ hφψ => RingCat.hom_ext (Polynomial.ringHom_ext
      (fun a => RingHom.congr_fun (Subsingleton.elim (φ.hom.comp Polynomial.C)
        (ψ.hom.comp Polynomial.C)) a) hφψ)
  have hev : ∀ R : RingCat.{0}, Function.Surjective fun φ : E ⟶ R => φ.hom Polynomial.X :=
    fun R r => ⟨RingCat.ofHom (Polynomial.eval₂RingHom' (Int.castRingHom R) r
      (fun a => Int.cast_commute a r)), Polynomial.eval₂_X _ _⟩
  have hQ : Countable (P.obj (op cexSObj)) := by
    have : Countable ((structurePresheaf cexBase cexToOver).obj (op cexSObj)) :=
      (Scheme.ΓSpecIso (.of ℚ)).commRingCatIsoToRingEquiv.toEquiv.countable_iff.2 inferInstance
    exact (hinj _).countable
  have : Countable (E ⟶ (structurePresheaf cexBase cexToOver).obj (op cexXObj)) :=
    hsurj.countable
  have hR : Countable ((structurePresheaf cexBase cexToOver).obj (op cexXObj)) :=
    (hev _).countable
  exact Cardinal.not_countable_real (Set.countable_univ_iff.2
    ((Scheme.ΓSpecIso (.of ℝ)).commRingCatIsoToRingEquiv.toEquiv.countable_iff.1 hR))

/-- **The first assertion of Tag 03OJ fails without the assumption on fibre products.** There is a
scheme `S`, a site of schemes over `S` satisfying the site axioms of Stacks 00VH, having all fibre
products, and satisfying the four conditions of the tag — (1) a full subcategory of `Sch/S`,
essentially small; (2) Zariski coverings are refined by coverings; (3) `S/S` is an object; (4)
every covering is an fpqc covering of schemes — on which the presheaf `𝒪` is not a sheaf. What
fails is that the fibre products of the site along coverings are fibre products of schemes. -/
theorem not_forall_isSheaf_structurePresheaf :
    ¬ ∀ (S : Scheme.{0}) (C : Type 1) [Category.{0} C] (toOver : C ⥤ Over S) [HasPullbacks C]
      [toOver.Full] [toOver.Faithful] [EssentiallySmall.{0} C] (K : Precoverage C) [K.HasIsos]
      [K.IsStableUnderComposition] [K.HasPullbacks] [K.IsStableUnderBaseChange],
      (∀ (T : C) (Q : Presieve T), Q ∈ K T →
        Presieve.map (toOver ⋙ Over.forget S) Q ∈ Scheme.fpqcPrecoverage ((toOver.obj T).left)) →
      (∀ (T : C) (R : Presieve ((toOver.obj T).left)),
        R ∈ Scheme.zariskiPrecoverage ((toOver.obj T).left) →
          ∃ Q : Presieve T, Q ∈ K T ∧
            Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows) →
      (∃ T : C, Nonempty (toOver.obj T ≅ Over.mk (𝟙 S))) →
      Presheaf.IsSheaf K.toGrothendieck (structurePresheaf S toOver) :=
  fun h => not_isSheaf_structurePresheaf_counterexample
    (h cexBase CexSite cexToOver cexK cex_fpqc cex_zariski cex_terminal)

/-- The fibre products of the site along its coverings are not fibre products of schemes. -/
theorem not_preservesCoveringFibreProducts_counterexample :
    ¬ PreservesCoveringFibreProducts cexK (cexToOver ⋙ Over.forget cexBase) := fun h =>
  not_isSheaf_structurePresheaf_counterexample
    (isSheaf_structurePresheaf_of_preservesCoveringFibreProducts cexK cexToOver cex_fpqc h)

end Stacks.Sites

end
