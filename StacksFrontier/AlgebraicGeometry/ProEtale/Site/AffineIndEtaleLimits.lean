module

public import Mathlib.Algebra.Category.Ring.Under.Limits
public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Sites.Preserves
public import Mathlib.RingTheory.Etale.Pi
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AffineIndEtaleDense
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.AffineIndEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.Subcanonical
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible

/-!
# Finite coproducts and covering families in the affine ind-étale site

Let `S` be an affine object of a chosen big pro-étale site. The affine ind-étale site `S_app`
of `S` is closed under finite disjoint unions: a finite disjoint union of affine schemes
weakly étale over `S` is affine, is weakly étale over `S`, and has ind-étale ring of global
sections because a finite product of étale algebras is étale. Together with the fibre products
already available on the site this makes `S_app` finitary extensive, and makes its topology
subcanonical, since the inclusion into the small pro-étale site is fully faithful and
continuous and that site is subcanonical.

The covering families of `S_app` are the finite standard pro-étale coverings. They are stable
under base change and under refinement, from which every covering sieve of the generated
topology is shown to contain one. At a weakly contractible object that gives a section of the
total map `∐ Uᵢ → V` of any standard covering, which is the computational input to the
description of pro-étale inverse image along a closed immersion.

## Main results

* `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.hasFiniteCoproducts` and
  `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.toScheme_preservesFiniteCoproducts`: the
  affine ind-étale site has finite coproducts, computed on underlying schemes.
* `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.finitaryExtensive`: the affine ind-étale
  site is finitary extensive, so its finite coproducts are disjoint and universal.
* `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.topology_subcanonical`: the affine ind-étale
  topology is subcanonical.
* `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.isCovering_pullback₂`,
  `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.isCovering_bind` and
  `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.isCovering_singleton`: the standard pro-étale
  coverings are stable under base change, under refinement, and contain the isomorphisms.
* `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.exists_isCovering_presieve₀_le`: every
  covering sieve of the affine ind-étale topology contains a standard pro-étale covering family.
* `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.sheaf_preservesProduct`: a sheaf of sets
  takes a finite coproduct of the site to a product.
* `AffineIndEtaleProetale.exists_section_sigmaDesc_of_isWeaklyContractible`, in the same
  namespace: at a weakly contractible object the total map of a standard pro-étale covering has
  a section.

## Implementation notes

The index types of the chosen covering families of a big pro-étale site live in `Type (u + 1)`
while the coproducts constructed here are indexed by `Type u`; the two are reconciled by
`CategoryTheory.Limits.HasFiniteCoproducts`, which is a statement about `Discrete (Fin n)` and
therefore transports to a finite index type in any universe.

Finitary extensivity is obtained by transport along the functor to schemes rather than proved:
that functor preserves fibre products and finite coproducts and reflects isomorphisms, which
is what `CategoryTheory.finitaryExtensive_of_preserves_and_reflects_isomorphism` consumes.

The affine ind-étale precoverage is *not* stable under base change in the sense of
`CategoryTheory.Precoverage.IsStableUnderBaseChange`, whose index type is unconstrained: a
covering presieve of the site is one presented by a *finite* family, and an arbitrary pullback
family indexed by an infinite type need not have finite image. Stability is therefore recorded
at the level of covering families, `isCovering_pullback₂`, and
`exists_isCovering_presieve₀_le` is proved by induction over the generated topology rather
than by `CategoryTheory.Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition`.

No declaration here is tagged: these are structural statements about the site of Stacks 098X
which the source makes only in passing.

## References

* [Stacks Project, Tag 098X](https://stacks.math.columbia.edu/tag/098X)
* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.ProEtale

/-! ### Finite products of étale algebras -/

/-- A finite product of étale algebras over `R` is étale over `R`. -/
private lemma etale_piFan (R : CommRingCat.{u}) {I : Type u} [Finite I]
    (A : I → Under R) (hA : ∀ i, (A i).hom.hom.Etale) :
    (CommRingCat.Under.piFan A).pt.hom.hom.Etale := by
  let (i : I) : Algebra R (A i).right := (A i).hom.hom.toAlgebra
  have (i : I) : Algebra.Etale R (A i).right := (hA i).toAlgebra
  exact RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale R (∀ i, (A i).right))

/-- A finite product of ind-étale algebras over `R` is ind-étale over `R`: a map from an
algebra of finite presentation into the product factors through a finite product of étale
stages, one for each factor. -/
private lemma indEtale_pi (R : CommRingCat.{u}) {I : Type u} [Finite I]
    (A : I → Under R)
    (hA : ∀ i, ObjectProperty.ind.{u} (fun D : Under R ↦ D.hom.hom.Etale) (A i)) :
    ObjectProperty.ind.{u} (fun D : Under R ↦ D.hom.hom.Etale) (∏ᶜ A) := by
  classical
  let P : ObjectProperty (Under R) := fun D ↦ D.hom.hom.Etale
  have hP : P ≤ fun D : Under R ↦ D.hom.hom.FinitePresentation := fun _ h ↦ h.finitePresentation
  rw [CommRingCat.ind_under_iff_exists_factorization _ hP]
  intro T hT f
  choose D g h hgh hD using fun i ↦
    (CommRingCat.ind_under_iff_exists_factorization (A i) hP).mp (hA i) T hT (f ≫ Pi.π A i)
  let c := CommRingCat.Under.piFan D
  let hc := CommRingCat.Under.piFanIsLimit D
  let g' : T ⟶ c.pt := hc.lift (Fan.mk T g)
  let h' : c.pt ⟶ ∏ᶜ A := Pi.lift (fun i ↦ c.π.app ⟨i⟩ ≫ h i)
  refine ⟨c.pt, g', h', ?_, etale_piFan R D hD⟩
  refine Pi.hom_ext _ _ fun i ↦ ?_
  simp only [Category.assoc, h', Pi.lift_comp_π]
  rw [← Category.assoc, show g' ≫ c.π.app ⟨i⟩ = g i from hc.fac (Fan.mk T g) ⟨i⟩]
  exact hgh i

/-- If each member of a finite family of schemes over `S` is ind-étale over `S` on global
sections, so is their disjoint union: global sections take the disjoint union to the product.
-/
private lemma indEtale_appTop_sigmaDesc {I : Type u} [Finite I]
    {S : Scheme.{u}} (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ S)
    (hf : ∀ i, ObjectProperty.ind.{u} (fun D : Under Γ(S, ⊤) ↦ D.hom.hom.Etale)
      (Under.mk (f i).appTop)) :
    ObjectProperty.ind.{u} (fun D : Under Γ(S, ⊤) ↦ D.hom.hom.Etale)
      (Under.mk (Sigma.desc f).appTop) := by
  let A := fun i ↦ Under.mk (f i).appTop
  let c : Fan A := Fan.mk (Under.mk (Sigma.desc f).appTop)
    (fun i ↦ Under.homMk (Sigma.ι X i).appTop (by
      show (Sigma.desc f).appTop ≫ (Sigma.ι X i).appTop = (f i).appTop
      rw [← Scheme.Hom.comp_appTop, Sigma.ι_desc]))
  have hc : IsLimit c := by
    apply isLimitOfReflects (Under.forget Γ(S, ⊤))
    refine (isLimitMapConeFanMkEquiv (Under.forget Γ(S, ⊤)) A _).symm ?_
    exact (isLimitMapConeFanMkEquiv Scheme.Γ _ _)
      (isLimitOfPreserves Scheme.Γ (Cofan.IsColimit.op (coproductIsCoproduct X)))
  exact (ObjectProperty.ind.{u} (fun D : Under Γ(S, ⊤) ↦ D.hom.hom.Etale)).prop_of_iso
    (hc.conePointUniqueUpToIso (productIsProduct A)).symm (indEtale_pi _ A hf)

/-- A finite family of schemes presenting a colimit cofan is a pro-étale covering family of
its coproduct: it is a Zariski covering, and Zariski coverings are pro-étale. -/
theorem mem_proetalePrecoverage_of_isColimit {I : Type (u + 1)} [Finite I]
    {A : I → Scheme.{u}} (c : Cofan A) (hc : IsColimit c) :
    Presieve.ofArrows A c.inj ∈ Scheme.proetalePrecoverage c.pt := by
  let e : (∐ A) ≅ c.pt := (coproductIsCoproduct A).coconePointUniqueUpToIso hc
  have h := ((sigmaOpenCover A).pushforwardIso e.hom).mem₀
  have he (j : I) : Sigma.ι A j ≫ e.hom = c.inj j :=
    (coproductIsCoproduct A).comp_coconePointUniqueUpToIso_hom hc ⟨j⟩
  change Presieve.ofArrows A (fun j ↦ Sigma.ι A j ≫ e.hom) ∈
    Scheme.zariskiPrecoverage c.pt at h
  have : MorphismProperty.ContainsIdentities (@WeaklyEtale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ ↦ inferInstance⟩
  exact Scheme.zariskiPrecoverage_le_propQCPrecoverage _ (by simpa only [he] using h)

namespace AffineIndEtaleProetale

variable (B : BigProetaleSite.{u}) (S : B.Scheme)

/-! ### Finite coproducts -/

/-- The disjoint union of a finite family of affine ind-étale objects over `S`, as a cofan in
the affine ind-étale site. -/
private def coproductCofan {I : Type u} [Finite I] (A : I → AffineIndEtaleProetale B S) :
    Cofan A := by
  let X := fun i ↦ (A i).obj.obj.left.obj
  let f := fun i ↦ B.inclusion.map (A i).obj.obj.hom
  have hX (i : I) : (X i).size < B.cutoff := (A i).obj.obj.left.property
  have hsize : (∐ X).size < B.cutoff := Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff
    B.aleph0_lt_cutoff_cof Cardinal.mk_le_aleph0 X hX
  let Y : B.Scheme := ⟨∐ X, hsize⟩
  let g : Y ⟶ S := ObjectProperty.homMk (Sigma.desc f)
  have hweak : WeaklyEtale (B.inclusion.map g) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @WeaklyEtale) (fun i ↦ (A i).obj.property)
  have hind : ObjectProperty.ind.{u} (fun D : Under Γ(S.obj, ⊤) ↦ D.hom.hom.Etale)
      (Under.mk (B.inclusion.map g).appTop) :=
    indEtale_appTop_sigmaDesc X f (fun i ↦ (A i).property.2)
  let T : AffineIndEtaleProetale B S := ⟨⟨Over.mk g, hweak⟩, (inferInstance : IsAffine Y.obj), hind⟩
  exact Cofan.mk T fun i ↦ ObjectProperty.homMk (ObjectProperty.homMk (Over.homMk
    (ObjectProperty.homMk (Sigma.ι X i)) (B.inclusion.map_injective (Sigma.ι_desc f i))))

/-- The disjoint union of affine ind-étale objects is their coproduct: the functor to schemes
is fully faithful onto a subcategory closed under the construction, so it reflects the
colimit. -/
private def coproductCofanIsColimit {I : Type u} [Finite I] (A : I → AffineIndEtaleProetale B S) :
    IsColimit (coproductCofan B S A) :=
  isColimitOfReflects (toScheme B S)
    ((isColimitMapCoconeCofanMkEquiv (toScheme B S) A _).symm (coproductIsCoproduct _))

/-- The affine ind-étale site has finite coproducts: a finite disjoint union of affine schemes
ind-étale over `S` is again one. -/
instance hasFiniteCoproducts : HasFiniteCoproducts (AffineIndEtaleProetale B S) := by
  have H (I : Type u) [Finite I] : HasColimitsOfShape (Discrete I) (AffineIndEtaleProetale B S) :=
    { has_colimit := fun F ↦ ⟨⟨
        (Cocone.precompose Discrete.natIsoFunctor.hom).obj
          (coproductCofan B S (fun j ↦ F.obj ⟨j⟩)),
        (IsColimit.precomposeHomEquiv _ _).symm (coproductCofanIsColimit B S _)⟩⟩ }
  exact ⟨fun n ↦ @hasColimitsOfShape_of_equivalence (Discrete (ULift.{u} (Fin n)))
    _ _ _ _ _ (Discrete.equivalence Equiv.ulift) (H _)⟩

/-- The underlying scheme of a finite disjoint union in the affine ind-étale site is the
disjoint union of the underlying schemes. -/
instance toScheme_preservesFiniteCoproducts : PreservesFiniteCoproducts (toScheme B S) := by
  have H (I : Type u) [Finite I] : PreservesColimitsOfShape (Discrete I) (toScheme B S) := by
    have (A : I → AffineIndEtaleProetale B S) :
        PreservesColimit (Discrete.functor A) (toScheme B S) :=
      preservesColimit_of_preserves_colimit_cocone (coproductCofanIsColimit B S A)
        ((isColimitMapCoconeCofanMkEquiv (toScheme B S) A _).symm (coproductIsCoproduct _))
    exact preservesColimitsOfShape_of_discrete _
  refine ⟨fun n ↦ ?_⟩
  have := H (ULift.{u} (Fin n))
  exact preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _

/-- The affine ind-étale site of an affine object is finitary extensive: its finite coproducts
are disjoint and universal. -/
instance finitaryExtensive [IsAffine S.obj] : FinitaryExtensive (AffineIndEtaleProetale B S) :=
  finitaryExtensive_of_preserves_and_reflects_isomorphism (toScheme B S)

/-! ### Covering families -/

/-- A fibre product square of the affine ind-étale site is a fibre product square of schemes.
-/
private lemma isPullback_map_toScheme [IsAffine S.obj]
    {A D T P : AffineIndEtaleProetale B S} {f : A ⟶ T} {g : D ⟶ T}
    {a : P ⟶ A} {d : P ⟶ D} (h : IsPullback a d f g) :
    IsPullback (B.inclusion.map a.hom.hom.left) (B.inclusion.map d.hom.hom.left)
      (B.inclusion.map f.hom.hom.left) (B.inclusion.map g.hom.hom.left) :=
  h.map (toScheme B S)

/-- Standard pro-étale coverings are stable under base change. -/
theorem isCovering_pullback₂ [IsAffine S.obj] {U V : AffineIndEtaleProetale B S}
    (E : PreZeroHypercover.{u + 1} U) (hE : IsCovering B S ⟨U, E⟩) (f : V ⟶ U) :
    IsCovering B S ⟨V, E.pullback₂ f⟩ := by
  refine ⟨⟨?_, hE.1.2⟩, hE.2⟩
  show Presieve.ofArrows _ _ ∈ Scheme.proetalePrecoverage _
  exact Precoverage.mem_coverings_of_isPullback
    (fun j ↦ B.inclusion.map (E.f j).hom.hom.left) hE.1.1
    (B.inclusion.map f.hom.hom.left)
    (fun j ↦ B.inclusion.map (pullback.snd (E.f j) f).hom.hom.left)
    (fun j ↦ B.inclusion.map (pullback.fst (E.f j) f).hom.hom.left)
    fun j ↦ isPullback_map_toScheme B S (IsPullback.of_hasPullback (E.f j) f).flip

/-- Refining each member of a standard pro-étale covering by a standard pro-étale covering
again gives one. -/
theorem isCovering_bind {U : AffineIndEtaleProetale B S} (E : PreZeroHypercover.{u + 1} U)
    (D : ∀ j, PreZeroHypercover.{u + 1} (E.X j)) (hE : IsCovering B S ⟨U, E⟩)
    (hD : ∀ j, IsCovering B S ⟨E.X j, D j⟩) :
    IsCovering B S ⟨U, E.bind D⟩ := by
  have : Finite E.I₀ := hE.2
  have : ∀ j, Finite (D j).I₀ := fun j ↦ (hD j).2
  refine ⟨?_, inferInstanceAs (Finite (Σ j, (D j).I₀))⟩
  let F := inclusion B S ⋙ SmallProetale.inclusion B S.obj S.property ⋙
    Over.forget (⟨S.obj, S.property⟩ : B.Scheme)
  have h := B.covering_isSite.2.1 ⟨F.obj U, E.map F⟩ hE.1
    (fun j ↦ ⟨F.obj (E.X j), (D j).map F⟩) (fun j ↦ (hD j).1) (fun _ ↦ rfl)
  simpa [F, PreZeroHypercover.map, PreZeroHypercover.bind, PreZeroHypercover.pushforward] using h

/-- An isomorphism is a standard pro-étale covering. -/
theorem isCovering_singleton {U V : AffineIndEtaleProetale B S} (f : V ⟶ U) [IsIso f] :
    IsCovering B S ⟨U, PreZeroHypercover.singleton.{u + 1} f⟩ := by
  let F := inclusion B S ⋙ SmallProetale.inclusion B S.obj S.property ⋙
    Over.forget (⟨S.obj, S.property⟩ : B.Scheme)
  have : IsIso f.hom.hom.left := inferInstanceAs (IsIso (F.map f))
  exact ⟨B.covering_isSite.1 f.hom.hom.left, inferInstance⟩

/-- The pullback of a covering presieve of the affine ind-étale site is a covering presieve.
-/
theorem pullbackArrows_mem_precoverage [IsAffine S.obj] {U V : AffineIndEtaleProetale B S}
    (f : V ⟶ U) (R : Presieve U) (hR : R ∈ precoverage B S U) :
    R.pullbackArrows f ∈ precoverage B S V := by
  obtain ⟨E, rfl, hE⟩ := hR
  exact ⟨E.pullback₂ f, (E.presieve₀_pullback₁ f).symm, isCovering_pullback₂ B S E hE f⟩

/-- Every covering sieve of the affine ind-étale topology contains a standard pro-étale
covering family. -/
theorem exists_isCovering_presieve₀_le [IsAffine S.obj] {U : AffineIndEtaleProetale B S}
    {R : Sieve U} (hR : R ∈ topology B S U) :
    ∃ E : PreZeroHypercover.{u + 1} U, IsCovering B S ⟨U, E⟩ ∧ E.presieve₀ ≤ R := by
  induction hR with
  | of U R hR =>
    obtain ⟨E, rfl, hE⟩ := hR
    exact ⟨E, hE, Sieve.le_generate _⟩
  | top U =>
    exact ⟨.singleton (𝟙 U), isCovering_singleton B S _, by simp⟩
  | pullback U R hR V f ih =>
    obtain ⟨E, hE, hle⟩ := ih
    refine ⟨E.pullback₂ f, isCovering_pullback₂ B S E hE f, ?_⟩
    rw [E.presieve₀_pullback₁, ← Sieve.generate_le_iff, Sieve.pullbackArrows_comm]
    exact Sieve.pullback_monotone f ((Sieve.generate_le_iff _ _).mpr hle)
  | transitive U R T hR hT ihR ihT =>
    obtain ⟨E, hE, hle⟩ := ihR
    choose D hD hleD using fun j : E.I₀ ↦ ihT (hle _ _ (Presieve.ofArrows.mk j))
    refine ⟨E.bind D, isCovering_bind B S E D hE hD, ?_⟩
    rw [Presieve.ofArrows_le_iff]
    intro j
    exact hleD j.1 _ _ (Presieve.ofArrows.mk j.2)

/-- A finite cofan of the affine ind-étale site whose index type is within the covering bound
of the ambient big site generates a covering sieve of its coproduct. -/
theorem sieve_ofArrows_mem_topology [IsAffine S.obj] {I : Type (u + 1)} [Finite I]
    {A : I → AffineIndEtaleProetale B S} (c : Cofan A) (hc : IsColimit c)
    (hI : Cardinal.mk I ≤ B.coveringBound) :
    Sieve.ofArrows A c.inj ∈ topology B S c.pt := by
  have hcs : IsColimit (Cofan.mk ((toScheme B S).obj c.pt)
      (fun j ↦ (toScheme B S).map (c.inj j))) :=
    (isColimitMapCoconeCofanMkEquiv (toScheme B S) A c.inj)
      (isColimitOfPreserves (toScheme B S) hc)
  exact Precoverage.generate_mem_toGrothendieck
    ⟨⟨I, A, c.inj⟩, rfl, ⟨⟨mem_proetalePrecoverage_of_isColimit _ hcs, hI⟩, inferInstance⟩⟩

/-! ### Subcanonicity -/

/-- The affine ind-étale topology of an affine object is subcanonical: representable presheaves
are sheaves. The inclusion into the small pro-étale site is fully faithful and continuous, and
that site is subcanonical. -/
instance topology_subcanonical [IsAffine S.obj] : (topology B S).Subcanonical :=
  GrothendieckTopology.subcanonical_of_full_of_faithful (inclusion B S) (topology B S)
    (SmallProetale.topology B S.obj S.property)

/-! ### Sections over a weakly contractible object -/

/-- A single morphism generating a covering sieve of a weakly contractible object has a
section: the induced map of representable sheaves is locally surjective, hence surjective on
sections over the object. -/
theorem exists_section_of_isWeaklyContractible [IsAffine S.obj] {V W : AffineIndEtaleProetale B S}
    (hV : (topology B S).IsWeaklyContractible V) (f : W ⟶ V)
    (hf : Sieve.generate (Presieve.singleton f) ∈ topology B S V) :
    ∃ s : V ⟶ W, s ≫ f = 𝟙 V := by
  let J := topology B S
  have hsurj : Sheaf.IsLocallySurjective (J.yoneda.map f) := by
    constructor
    intro T g
    apply J.superset_covering (S := (Sieve.generate (Presieve.singleton f)).pullback g)
      _ (J.pullback_stable g hf)
    rintro A a ⟨D, b, c, ⟨⟩, he⟩
    exact ⟨b, he⟩
  exact hV (J.yoneda.obj W) (J.yoneda.obj V) (J.yoneda.map f) hsurj (𝟙 V)

/-- At a weakly contractible object the total map `∐ Uᵢ → V` of a standard pro-étale covering
has a section. -/
theorem exists_section_sigmaDesc_of_isWeaklyContractible [IsAffine S.obj]
    {V : AffineIndEtaleProetale B S} (hV : (topology B S).IsWeaklyContractible V)
    (E : PreZeroHypercover.{u + 1} V) [Finite E.I₀] (hE : IsCovering B S ⟨V, E⟩) :
    ∃ s : V ⟶ ∐ E.X, s ≫ Sigma.desc E.f = 𝟙 V := by
  apply exists_section_of_isWeaklyContractible B S hV
  apply (topology B S).superset_covering (S := Sieve.generate E.presieve₀) _
    (Precoverage.generate_mem_toGrothendieck ⟨E, rfl, hE⟩)
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro j
  exact ⟨_, Sigma.ι E.X j, Sigma.desc E.f, Presieve.singleton_self _, Sigma.ι_desc E.f j⟩

/-- A sheaf of sets on the affine ind-étale site takes a finite coproduct, with index type
within the covering bound of the ambient big site, to a product. -/
theorem sheaf_preservesProduct [IsAffine S.obj]
    (F : Sheaf (topology B S) (Type (max (u + 1) v)))
    {I : Type (u + 1)} [Finite I] (A : I → AffineIndEtaleProetale B S)
    (hI : Cardinal.mk I ≤ B.coveringBound) :
    PreservesLimit (Discrete.functor (fun j ↦ op (A j))) F.obj := by
  have hF := (isSheaf_iff_isSheaf_of_type _ _).mp F.property
  have hempty : Sieve.ofArrows (fun j : PEmpty.{u + 2} ↦ PEmpty.elim j)
      (fun j ↦ PEmpty.elim j) ∈ topology B S (⊥_ (AffineIndEtaleProetale B S)) :=
    sieve_ofArrows_mem_topology B S (Cofan.mk _ (fun j ↦ PEmpty.elim j))
      ((isColimitEquivIsInitialOfIsEmpty _ _).symm initialIsInitial) (by simp)
  have (j : I) : Mono (Cofan.inj (Sigma.cocone (Discrete.functor A)) j) :=
    FinitaryExtensive.mono_ι (coproductIsCoproduct A) ⟨j⟩
  exact Presieve.preservesProduct_of_isSheafFor F.obj
    (by
      apply hF.isSheafFor
      convert hempty using 1
      simp [Sieve.ofArrows, Presieve.ofArrows_of_isEmpty])
    initialIsInitial (Sigma.cocone (Discrete.functor A)) (coproductIsCoproduct A)
    (fun j k hjk ↦ FinitaryExtensive.isPullback_initial_to_sigma_ι A j k hjk)
    (hF.isSheafFor _ (sieve_ofArrows_mem_topology B S _ (coproductIsCoproduct A) hI))

end AffineIndEtaleProetale

end AlgebraicGeometry.ProEtale

end
