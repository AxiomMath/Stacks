module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleProjOpenImmersion
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.LocalOnBase
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ContractExceptionalCurveAmple
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Contraction.ChartPushforward
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Contraction.GlueContraction
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveOpenImmersion
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Invertible

/-!
# Contracting an exceptional curve over a Noetherian base

**[Stacks, Tag 0C2N] (1).** Let `S` be a Noetherian scheme, `f : X ⟶ S` a morphism of finite type
and `E ⊆ X` an exceptional curve of the first kind lying in a fibre of `f`. If `X` is projective
over `S`, there is a contraction `b : X ⟶ X'` of `E`, and `X'` is projective over `S`.

The proof is the source's. The point `s` under `E` is closed, `f` being proper. Over an affine
open `U ∋ s` the contraction exists by [Stacks, Tag 0C2M], together with an ample invertible
module `ℒ'_U` whose pullback has the class of `ℒ(nE)`, where `ℒ` is `f`-ample and `n` is its
degree on `E`. Glueing that contraction with `X \ E`
(`AlgebraicGeometry.exists_isContractionOfExceptionalCurve_of_chart`) gives the contraction
`b : X ⟶ X'` of `E` and the structure morphism `g : X' ⟶ S`, which is proper because properness
descends along `b` and finite type may be checked on the two charts.

The source glues `ℒ'_U` with `ℒ|_{X \ E}`. Here the glued module is produced in one step, as the
direct image `ℒ' = b_* 𝓜` of an invertible module `𝓜` of class `ℒ(nE)`: over the chart `U` it is
`c_* c^* ℒ'_U ≅ ℒ'_U` ([Stacks, Tag 0C5L], first claim), and over `X \ E` it is `𝓜 ≅ ℒ`. It is
ample over `U`, and over every affine open of `S` avoiding `s`, so it is `g`-ample by
[Stacks, Tag 01VJ]; with properness this makes `g` projective ([Stacks, Tag 0BCL]).

## Main results

* `AlgebraicGeometry.exists_isContractionOfExceptionalCurve_isProjective`:
  **[Stacks, Tag 0C2N] (1)**.

## References

* [Stacks Project, Tag 0C2N](https://stacks.math.columbia.edu/tag/0C2N)
* [Stacks Project, Tag 0C2M](https://stacks.math.columbia.edu/tag/0C2M)
* [Stacks Project, Tag 01VJ](https://stacks.math.columbia.edu/tag/01VJ)
* [Stacks Project, Tag 0BCL](https://stacks.math.columbia.edu/tag/0BCL)
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

open ExceptionalCurveContraction

/-- A morphism is locally of finite type if it is so after composing with two open immersions
whose ranges cover the source. -/
private theorem locallyOfFiniteType_of_isOpenImmersion_cover {X Y Z S : Scheme.{u}} (g : Z ⟶ S)
    (j : X ⟶ Z) (k : Y ⟶ Z) [IsOpenImmersion j] [IsOpenImmersion k]
    (hj : LocallyOfFiniteType (j ≫ g)) (hk : LocallyOfFiniteType (k ≫ g))
    (hcov : j.opensRange ⊔ k.opensRange = ⊤) : LocallyOfFiniteType g := by
  have : MorphismProperty.RespectsIso (@LocallyOfFiniteType.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : IsZariskiLocalAtSource (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
  have key : ∀ {A : Scheme.{u}} (i : A ⟶ Z) [IsOpenImmersion i], LocallyOfFiniteType (i ≫ g) →
      LocallyOfFiniteType (i.opensRange.ι ≫ g) := fun i _ hi => by
    have hι : i.opensRange.ι = i.isoOpensRange.inv ≫ i := by
      rw [← cancel_epi i.isoOpensRange.hom, Iso.hom_inv_id_assoc, Scheme.Hom.isoOpensRange_hom_ι]
    rw [hι, Category.assoc]
    exact (MorphismProperty.cancel_left_of_respectsIso (@LocallyOfFiniteType.{u}) _ _).mpr hi
  let C : Bool → Z.Opens := fun t => cond t j.opensRange k.opensRange
  have hC : iSup C = ⊤ := by simpa [C, iSup_bool_eq] using hcov
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @LocallyOfFiniteType.{u}) C hC
    (fun t => by cases t with
      | false => exact key k hk
      | true => exact key j hj)

/-! ### Properness of the glued structure morphism -/

/-- **Properness descends along a contraction, given finite type on a cover.** Let `b : X ⟶ X'`
be a contraction of an exceptional curve of the first kind and `g : X' ⟶ S` a morphism with
`b ≫ g` proper. If `X'` is covered by the image of an open immersion `j` with `j ≫ g` locally of
finite type and an open `W` over which `b` is an isomorphism, then `g` is proper. -/
theorem isProper_of_isContractionOfExceptionalCurve_of_cover {X X' S V' : Scheme.{u}}
    (D : X.IdealSheafData) (k : Type u) [Field k] (e : projectiveLineProj k ≅ D.subscheme)
    {b : X ⟶ X'} (hb : IsContractionOfExceptionalCurve D b) (g : X' ⟶ S)
    (hf : IsProper (b ≫ g)) (j : V' ⟶ X') [IsOpenImmersion j] (hj : LocallyOfFiniteType (j ≫ g))
    (W : X'.Opens) (hW : IsIso (b ∣_ W)) (hcov : j.opensRange ⊔ W = ⊤) :
    IsProper g := by
  have := hb.isProper
  have : Surjective b := ⟨surjective_of_isContractionOfExceptionalCurve D k e b hb⟩
  have : UniversallyClosed g := UniversallyClosed.of_comp_surjective b g
  have : IsSeparated g := by
    let φ : (Over.mk (b ≫ g) : Over S) ⟶ Over.mk g := Over.homMk b rfl
    have : Surjective φ.left := show Surjective b from inferInstance
    have : UniversallyClosed φ.left := show UniversallyClosed b from inferInstance
    have : IsSeparated (Over.mk (b ≫ g) : Over S).hom := show IsSeparated (b ≫ g) from inferInstance
    exact isSeparated_of_surjective_universallyClosed φ
  have : MorphismProperty.RespectsIso (@LocallyOfFiniteType.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hW' : LocallyOfFiniteType (W.ι ≫ g) := by
    have hres : LocallyOfFiniteType ((b ∣_ W) ≫ W.ι ≫ g) := by
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
      infer_instance
    exact (MorphismProperty.cancel_left_of_respectsIso
      (@LocallyOfFiniteType.{u}) (b ∣_ W) (W.ι ≫ g)).mp hres
  have : LocallyOfFiniteType g :=
    locallyOfFiniteType_of_isOpenImmersion_cover g j W.ι hj hW'
      (by rwa [Scheme.Opens.opensRange_ι])
  exact (isProper_iff g).2 ⟨inferInstance, inferInstance, inferInstance⟩

/-! ### The glued invertible module -/

/-- **The direct image of an invertible module along a glued contraction.** Let `b : X ⟶ X'`
restrict over the image of an open immersion `j : V' ⟶ X'` to `c : U ⟶ V'` with `𝒪_{V'} ≅ c_*𝒪_U`,
and over the image of an open immersion `k : W ⟶ X'` to the identity of an open `W ⊆ X`, the two
images covering `X'`. If `𝓜` is invertible on `X` and `𝓜|_U ≅ c^* 𝒩` for an invertible `𝒩` on
`V'`, then `b_* 𝓜` is invertible, its restriction along `j` is `𝒩` and its restriction along `k`
is `𝓜|_W`. -/
theorem exists_pushforward_restrict_isos {X X' V' : Scheme.{u}} (b : X ⟶ X') (U₀ W₀ : X.Opens)
    (c : U₀.toScheme ⟶ V') [IsIso c.c] (j : V' ⟶ X') (k : W₀.toScheme ⟶ X') [IsOpenImmersion j]
    [IsOpenImmersion k] (hjc : U₀.ι ≫ b = c ≫ j) (hbk : W₀.ι ≫ b = k)
    (hpreJ : b ⁻¹ᵁ j.opensRange = U₀) (hpreK : b ⁻¹ᵁ k.opensRange = W₀)
    (hcov : j.opensRange ⊔ k.opensRange = ⊤) (M : X.Modules) (N : V'.Modules)
    [Stacks.Ample.IsInvertibleModule X M] [Stacks.Ample.IsInvertibleModule V' N]
    (eM : (Scheme.Modules.pullback U₀.ι).obj M ≅ (Scheme.Modules.pullback c).obj N) :
    Stacks.Ample.IsInvertibleModule X' ((Scheme.Modules.pushforward b).obj M) ∧
      Nonempty (((Scheme.Modules.pushforward b).obj M).restrict j ≅ N) ∧
      Nonempty (((Scheme.Modules.pushforward b).obj M).restrict k ≅ M.restrict W₀.ι) := by
  obtain ⟨iJ⟩ := Scheme.Modules.nonempty_restrict_pushforward_iso b U₀ c j hjc hpreJ M
  have := Scheme.Modules.isIso_unit_app_of_isIso_c c N
  have eJ : ((Scheme.Modules.pushforward b).obj M).restrict j ≅ N :=
    iJ ≪≫ (Scheme.Modules.pushforward c).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback U₀.ι).app M ≪≫ eM) ≪≫
      (asIso ((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app N)).symm
  obtain ⟨iK⟩ := Scheme.Modules.nonempty_restrict_pushforward_iso b W₀ (𝟙 _) k
    (by rw [hbk, Category.id_comp]) hpreK M
  have eK : ((Scheme.Modules.pushforward b).obj M).restrict k ≅ M.restrict W₀.ι :=
    iK ≪≫ (Scheme.Modules.pushforwardId _).app _
  refine ⟨?_, ⟨eJ⟩, ⟨eK⟩⟩
  let Y : Bool → Scheme.{u} := fun t => cond t V' W₀.toScheme
  let f : ∀ t, Y t ⟶ X' := fun t => match t with
    | true => j
    | false => k
  have : ∀ t, IsOpenImmersion (f t) := fun t => match t with
    | true => inferInstanceAs (IsOpenImmersion j)
    | false => inferInstanceAs (IsOpenImmersion k)
  refine Stacks.SheafOfModules.isInvertibleModule_of_restrict_openImmersions f
    _ (by rwa [iSup_bool_eq]) fun t => ?_
  cases t
  · have : Stacks.Ample.IsInvertibleModule W₀.toScheme (M.restrict W₀.ι) :=
      Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso
        ((Scheme.Modules.restrictFunctorIsoPullback W₀.ι).app M ≪≫
          (Stacks.ProjectiveBundleQuotients.pullbackIso W₀.ι).app M).symm
    exact Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso eK.symm
  · exact Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso eJ.symm

/-! ### Ampleness in the two spellings -/

/-- An invertible module whose pullback along a morphism is ample in the sense of
`AlgebraicGeometry.Scheme.Modules.IsAmple` restricts to an ample module in the sense of
`Stacks.Ample.IsAmple`, the spelling relative ampleness is stated with. -/
theorem isAmple_pullbackModule_of_isAmple_pullback {O Z : Scheme.{u}} (g : O ⟶ Z) (F : Z.Modules)
    [Stacks.Ample.IsInvertibleModule Z F]
    (h : haveI := Scheme.Modules.isInvertibleModule_pullback_obj g F
      Scheme.Modules.IsAmple O ((Scheme.Modules.pullback g).obj F)) :
    haveI := Stacks.InvertiblePullback.isInvertibleModule_pullback g F
    Stacks.Ample.IsAmple O (Stacks.AmpleLocallyClosed.pullbackModule g F) := by
  have := Scheme.Modules.isInvertibleModule_pullback_obj g F
  have := Stacks.InvertiblePullback.isInvertibleModule_pullback g F
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
    ((Stacks.ProjectiveBundleQuotients.pullbackIso g).app F)).mp
    (Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple _ _ h)

/-- The converse of `AlgebraicGeometry.isAmple_pullbackModule_of_isAmple_pullback`. -/
theorem isAmple_pullback_of_isAmple_pullbackModule {O Z : Scheme.{u}} (g : O ⟶ Z) (F : Z.Modules)
    [Stacks.Ample.IsInvertibleModule Z F]
    (h : haveI := Stacks.InvertiblePullback.isInvertibleModule_pullback g F
      Stacks.Ample.IsAmple O (Stacks.AmpleLocallyClosed.pullbackModule g F)) :
    haveI := Scheme.Modules.isInvertibleModule_pullback_obj g F
    Scheme.Modules.IsAmple O ((Scheme.Modules.pullback g).obj F) := by
  have := Scheme.Modules.isInvertibleModule_pullback_obj g F
  have := Stacks.InvertiblePullback.isInvertibleModule_pullback g F
  exact Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple _ _
    ((Stacks.RelativeVeryAmple.isAmple_congr _ _
      ((Stacks.ProjectiveBundleQuotients.pullbackIso g).app F)).mpr h)

/-! ### The engine: glueing a contraction with an ample module on a chart -/

/-- **A contraction near the curve with an ample module of the right class glues to a contraction
of the whole scheme with a module ample over the chart and away from the curve.** Let `S` be a
scheme, `f : X ⟶ S` locally of finite type with `X` Noetherian, `ℒ` an `f`-ample invertible
module, and `E ⊆ X` an exceptional curve of the first kind lying over `s`. Let `U ∋ s` be an affine
open of `S` and suppose the restriction of `E` to `f⁻¹(U)` has a contraction `c : f⁻¹(U) ⟶ V'`
over `S`, with `V' ⟶ S` locally of finite type, together with an ample invertible `𝒩` on `V'` whose
pullback has the class of `ℒ(nE)|_{f⁻¹(U)}`. Then there are a contraction `b : X ⟶ X'` of `E`, a
morphism `g : X' ⟶ S` locally of finite type with `b ≫ g = f`, and an invertible `ℒ'` on `X'`
which is ample over every affine open `V ⊆ U`, and over the complement of the contracted point in
the preimage of every affine open; if `f` is proper, so is `g`. This is the construction in the
proof of [Stacks, Tag 0C2N] (1), with
`ℒ' = b_* 𝓜` for `𝓜` of class `ℒ(nE)`. -/
theorem exists_contraction_of_ample_chart {X S V' : Scheme.{u}} [IsNoetherian X] (f : X ⟶ S)
    [LocallyOfFiniteType f] {D : X.IdealSheafData} {k : Type u} [Field k]
    {e : projectiveLineProj k ≅ D.subscheme} (hE : D.IsExceptionalCurveOfFirstKind k e) (s : S)
    (hs : ∀ x ∈ (D.support : Set X), f.base x = s) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    (U : S.Opens) (hsU : s ∈ U) (c : (f ⁻¹ᵁ U).toScheme ⟶ V')
    (hc : IsContractionOfExceptionalCurve (D.comap (f ⁻¹ᵁ U).ι) c) (gV : V' ⟶ S)
    [LocallyOfFiniteType gV] (hgV : c ≫ gV = (f ⁻¹ᵁ U).ι ≫ f) (n : ℤ) (N : V'.Modules)
    [Stacks.Ample.IsInvertibleModule V' N] (hN : Scheme.Modules.IsAmple V' N)
    (hNcl : haveI : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap (f ⁻¹ᵁ U).ι) :=
        Stacks.Divisors.isPullbackDefined_of_flat (f ⁻¹ᵁ U).ι D hE.isEffectiveCartierDivisor
      haveI := Scheme.Modules.isInvertibleModule_pullback_obj (f ⁻¹ᵁ U).ι L
      Stacks.Picard.schemePullbackClass c (cls N) =
        (D.comap (f ⁻¹ᵁ U).ι).exceptionalTwist n
          (cls ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj L))) :
    ∃ (X' : Scheme.{u}) (b : X ⟶ X') (g : X' ⟶ S) (L' : X'.Modules)
      (_ : Stacks.Ample.IsInvertibleModule X' L'),
      IsContractionOfExceptionalCurve D b ∧ b ≫ g = f ∧ LocallyOfFiniteType g ∧
        (IsProper f → IsProper g) ∧
        (∀ V : S.Opens, IsAffineOpen V → V ≤ U →
          Stacks.Ample.IsAmple (g ⁻¹ᵁ V).toScheme
            (Stacks.AmpleLocallyClosed.pullbackModule (g ⁻¹ᵁ V).ι L')) ∧
        ∃ R : X'.Opens, b ⁻¹ᵁ R = D.support.compl ∧ ∀ V : S.Opens, IsAffineOpen V →
          Stacks.Ample.IsAmple (g ⁻¹ᵁ V ⊓ R).toScheme
            (Stacks.AmpleLocallyClosed.pullbackModule (g ⁻¹ᵁ V ⊓ R).ι L') := by
  have := hE.isEffectiveCartierDivisor
  -- the curve is nonempty and lies over `s`
  have := isIntegral_subscheme_of_iso_projectiveLineProj D k e
  obtain ⟨d₀⟩ : Nonempty D.subscheme := inferInstance
  have hsubsupp : ∀ z : D.subscheme, D.subschemeι.base z ∈ (D.support : Set X) := fun z => by
    rw [← D.range_subschemeι]
    exact ⟨z, rfl⟩
  have hne : (D.support : Set X).Nonempty := ⟨_, hsubsupp d₀⟩
  have hsupp : (D.support : Set X) ⊆ (f ⁻¹ᵁ U) := fun x hx =>
    show f.base x ∈ U from hs x hx ▸ hsU
  have : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap (f ⁻¹ᵁ U).ι) :=
    Stacks.Divisors.isPullbackDefined_of_flat (f ⁻¹ᵁ U).ι D inferInstance
  let LY : (f ⁻¹ᵁ U).toScheme.Modules := (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj L
  have : Stacks.Ample.IsInvertibleModule (f ⁻¹ᵁ U).toScheme LY :=
    Scheme.Modules.isInvertibleModule_pullback_obj (f ⁻¹ᵁ U).ι L
  -- glue `c` with the complement of the curve
  set W₀ : X.Opens := D.support.compl
  obtain ⟨X', b, j, kk, hj, hk, hjc, hbk, hpreJ, hpreK, hcov, hbK, hb⟩ :=
    exists_isContractionOfExceptionalCurve_of_chart D inferInstance hne (f ⁻¹ᵁ U) hsupp c hc W₀ rfl
  have : Surjective b := ⟨surjective_of_isContractionOfExceptionalCurve D k e b hb⟩
  -- the structure morphism of the contraction
  obtain ⟨g, hg, -⟩ := existsUnique_comp_eq_of_isContractionOfExceptionalCurve D b hb f
    ⟨s, fun z => hs _ (hsubsupp z)⟩
  have hjg : j ≫ g = gV := by
    have hφ : ∃ y : S, ∀ z : (D.comap (f ⁻¹ᵁ U).ι).subscheme,
        ((f ⁻¹ᵁ U).ι ≫ f).base ((D.comap (f ⁻¹ᵁ U).ι).subschemeι.base z) = y := by
      refine ⟨s, fun z => ?_⟩
      rw [Scheme.Hom.comp_apply]
      refine hs _ ?_
      have hz : (D.comap (f ⁻¹ᵁ U).ι).subschemeι.base z ∈
          ((D.comap (f ⁻¹ᵁ U).ι).support : Set (f ⁻¹ᵁ U).toScheme) := by
        rw [← (D.comap (f ⁻¹ᵁ U).ι).range_subschemeι]
        exact ⟨z, rfl⟩
      rw [Scheme.IdealSheafData.support_comap] at hz
      exact hz
    obtain ⟨ψ, -, huniq⟩ :=
      existsUnique_comp_eq_of_isContractionOfExceptionalCurve _ c hc ((f ⁻¹ᵁ U).ι ≫ f) hφ
    have h₁ : c ≫ (j ≫ g) = (f ⁻¹ᵁ U).ι ≫ f := by rw [← Category.assoc, ← hjc, Category.assoc, hg]
    rw [huniq _ h₁, ← huniq _ hgV]
  -- `g` is locally of finite type, and proper if `f` is
  have hgft : LocallyOfFiniteType g := by
    have hkg : kk ≫ g = W₀.ι ≫ f := by rw [← hbk, Category.assoc, hg]
    exact locallyOfFiniteType_of_isOpenImmersion_cover g j kk (by rw [hjg]; infer_instance)
      (by rw [hkg]; infer_instance) hcov
  have hgprop : IsProper f → IsProper g := fun hf =>
    isProper_of_isContractionOfExceptionalCurve_of_cover D k e hb g (by rwa [hg])
      j (by rw [hjg]; infer_instance) kk.opensRange hbK hcov
  -- the invertible module `𝓜` of class `ℒ(nE)`, and `ℒ' = b_* 𝓜`
  let x : Stacks.Picard.ofScheme X := D.exceptionalTwist n (cls L)
  let M : X.Modules := (Stacks.Picard.picardRepresentative X.toRingedSpace x).obj
  have : Stacks.Ample.IsInvertibleModule X M :=
    (Stacks.Picard.picardRepresentative X.toRingedSpace x).property.toAlgebraicGeometry
  have hMcls : cls M = x := Stacks.Picard.classOf_picardRepresentative _ x
  have : IsIso c.c := hc.isIso_c
  have := Scheme.Modules.isInvertibleModule_pullback_obj (f ⁻¹ᵁ U).ι M
  have := Scheme.Modules.isInvertibleModule_pullback_obj c N
  have eM : Nonempty ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M ≅
      (Scheme.Modules.pullback c).obj N) := by
    refine nonempty_iso_of_cls_eq ?_
    rw [← schemePullbackClass_cls, ← schemePullbackClass_cls, hNcl, hMcls]
    change Stacks.Picard.schemePullbackClassHom (f ⁻¹ᵁ U).ι
        (cls L + n • Stacks.Divisors.picardClass D) =
      cls LY + n • Stacks.Divisors.picardClass (D.comap (f ⁻¹ᵁ U).ι)
    rw [map_add, map_zsmul]
    change Stacks.Picard.schemePullbackClass (f ⁻¹ᵁ U).ι (cls L) +
        n • Stacks.Picard.schemePullbackClass (f ⁻¹ᵁ U).ι (Stacks.Divisors.picardClass D) = _
    rw [schemePullbackClass_cls, Scheme.IdealSheafData.schemePullbackClass_picardClass]
  obtain ⟨hL'inv, ⟨eJ⟩, ⟨eK⟩⟩ := exists_pushforward_restrict_isos b (f ⁻¹ᵁ U) W₀ c j kk
    hjc hbk hpreJ hpreK hcov M N eM.some
  set L' : X'.Modules := (Scheme.Modules.pushforward b).obj M
  have : QuasiCompact g := by
    have : IsNoetherian X' := hb.isNoetherian
    infer_instance
  -- `ℒ'` is ample over `U`
  have hgU : (g ⁻¹ᵁ U : Set X') = Set.range j.base := by
    ext y
    obtain ⟨x, rfl⟩ := b.surjective y
    change g.base (b.base x) ∈ U ↔ b.base x ∈ (j.opensRange : Set X')
    rw [← Scheme.Hom.comp_apply, hg]
    change x ∈ (f ⁻¹ᵁ U) ↔ x ∈ b ⁻¹ᵁ j.opensRange
    rw [hpreJ]
  have hampU : Stacks.Ample.IsAmple (g ⁻¹ᵁ U).toScheme
      (Stacks.AmpleLocallyClosed.pullbackModule (g ⁻¹ᵁ U).ι L') := by
    have := Scheme.Modules.isInvertibleModule_pullback_obj j L'
    have hjamp : Scheme.Modules.IsAmple V' ((Scheme.Modules.pullback j).obj L') :=
      Scheme.Modules.isAmple_of_iso
        (eJ.symm ≪≫ (Scheme.Modules.restrictFunctorIsoPullback j).app L') hN
    refine isAmple_pullbackModule_of_isAmple_pullback _ L' ?_
    exact Scheme.Modules.isAmple_pullback_of_range_eq _ j
      (by rw [Scheme.Opens.range_ι]; exact hgU) L' hjamp
  refine ⟨X', b, g, L', hL'inv, hb, hg, hgft, hgprop, fun V hV hVU => ?_,
    kk.opensRange, hpreK, fun V hV => ?_⟩
  · -- affine opens inside `U`
    exact Stacks.RelativeAmpleComposition.isAmple_restrict_of_le
      ((Opens.map g.base).monotone hVU) L' hampU
      (Stacks.RelativeAmpleComposition.compactSpace_preimage_of_isCompact g V hV.isCompact)
  · -- the complement of the contracted point
    have : IsNoetherian X' := hb.isNoetherian
    set O : X'.Opens := g ⁻¹ᵁ V ⊓ kk.opensRange
    have hOk : (O : Set X') ⊆ Set.range kk.base := fun y hy => hy.2
    let q : (kk ⁻¹ᵁ O).toScheme ⟶ X' := (kk ⁻¹ᵁ O).ι ≫ kk
    have hq : Set.range O.ι.base = Set.range q.base := by
      rw [Scheme.Opens.range_ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Scheme.Opens.range_ι]
      ext y
      constructor
      · intro hy
        obtain ⟨w, rfl⟩ := hOk hy
        exact ⟨w, hy, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        exact hw
    let p' : (kk ⁻¹ᵁ O).toScheme ⟶ X := (kk ⁻¹ᵁ O).ι ≫ W₀.ι
    have hgk : ∀ w : W₀.toScheme, g.base (kk.base w) = f.base (W₀.ι.base w) := fun w =>
      congrArg (fun φ => φ.base w) (show kk ≫ g = W₀.ι ≫ f by rw [← hbk, Category.assoc, hg])
    set Of : X.Opens := f ⁻¹ᵁ V ⊓ W₀
    have hp' : Set.range p'.base = Set.range Of.ι.base := by
      rw [Scheme.Opens.range_ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Scheme.Opens.range_ι]
      ext x
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨?_, w.2⟩
        have hw' : g.base (kk.base w) ∈ V := hw.1
        rw [hgk] at hw'
        exact hw'
      · rintro ⟨hx, hxW⟩
        refine ⟨⟨x, hxW⟩, ⟨?_, ⟨⟨x, hxW⟩, rfl⟩⟩, rfl⟩
        change g.base (kk.base ⟨x, hxW⟩) ∈ V
        exact (hgk ⟨x, hxW⟩).symm ▸ hx
    have := Scheme.Modules.isInvertibleModule_pullback_obj Of.ι L
    have := Scheme.Modules.isInvertibleModule_pullback_obj p' L
    have := Scheme.Modules.isInvertibleModule_pullback_obj q L'
    have hLV : Scheme.Modules.IsAmple Of.toScheme ((Scheme.Modules.pullback Of.ι).obj L) := by
      refine isAmple_pullback_of_isAmple_pullbackModule _ L ?_
      have : IsNoetherian X := ‹IsNoetherian X›
      exact Stacks.RelativeAmpleComposition.isAmple_restrict_of_le inf_le_left L (hL.2 V hV)
        (isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact (Of : Set X)))
    have hp'amp : Scheme.Modules.IsAmple (kk ⁻¹ᵁ O).toScheme
        ((Scheme.Modules.pullback p').obj L) :=
      Scheme.Modules.isAmple_pullback_of_range_eq p' Of.ι hp' L hLV
    -- `𝓜` and `ℒ` agree off the curve
    have := Scheme.Modules.isInvertibleModule_pullback_obj W₀.ι M
    have := Scheme.Modules.isInvertibleModule_pullback_obj W₀.ι L
    have eW : Nonempty ((Scheme.Modules.pullback W₀.ι).obj M ≅
        (Scheme.Modules.pullback W₀.ι).obj L) := by
      refine nonempty_iso_of_cls_eq ?_
      rw [← schemePullbackClass_cls, ← schemePullbackClass_cls, hMcls]
      change Stacks.Picard.schemePullbackClassHom _
          (cls L + n • Stacks.Divisors.picardClass D) = _
      rw [map_add, map_zsmul]
      change Stacks.Picard.schemePullbackClass _ (cls L) +
          n • Stacks.Picard.schemePullbackClass _ (Stacks.Divisors.picardClass D) = _
      rw [Scheme.IdealSheafData.schemePullbackClass_picardClass]
      have : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap W₀.ι) :=
        Stacks.Divisors.isPullbackDefined_of_flat W₀.ι D inferInstance
      have htop : D.comap W₀.ι = ⊤ := by
        rw [← Scheme.IdealSheafData.support_eq_bot_iff]
        ext y
        simp only [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage,
          Closeds.coe_bot, Set.mem_empty_iff_false, iff_false]
        exact y.2
      rw [Stacks.Divisors.picardClass_congr htop, Stacks.Divisors.picardClass_top, smul_zero,
        add_zero]
    have eq : (Scheme.Modules.pullback p').obj L ≅ (Scheme.Modules.pullback q).obj L' :=
      ((Scheme.Modules.pullbackComp (kk ⁻¹ᵁ O).ι W₀.ι).app L).symm ≪≫
        (Scheme.Modules.pullback (kk ⁻¹ᵁ O).ι).mapIso
          (eW.some.symm ≪≫ ((Scheme.Modules.restrictFunctorIsoPullback _).app M).symm ≪≫
            eK.symm ≪≫ (Scheme.Modules.restrictFunctorIsoPullback kk).app L') ≪≫
        (Scheme.Modules.pullbackComp (kk ⁻¹ᵁ O).ι kk).app L'
    refine isAmple_pullbackModule_of_isAmple_pullback _ L' ?_
    exact Scheme.Modules.isAmple_pullback_of_range_eq O.ι q hq L'
      (Scheme.Modules.isAmple_of_iso eq hp'amp)

/-! ### Tag 0C2N (1) -/

/-- **[Stacks, Tag 0C2N] (1).** Let `S` be a Noetherian scheme and `f : X ⟶ S` a morphism of
finite type. Let `E ⊆ X` be an exceptional curve of the first kind, cut out by `D` and presented
as `𝐏¹_k` by `e`, which lies in the fibre of `f` over a point `s`. If `X` is projective over `S`,
then there exists a contraction `b : X ⟶ X'` of `E`, and `X'` is projective over `S`: the
structure morphism factors as `b ≫ g` with `g` projective. -/
@[stacks 0C2N "(1)"]
theorem exists_isContractionOfExceptionalCurve_isProjective {X S : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] {D : X.IdealSheafData} {k : Type u}
    [Field k] {e : projectiveLineProj k ≅ D.subscheme} (hE : D.IsExceptionalCurveOfFirstKind k e)
    (s : S) (hs : ∀ x ∈ (D.support : Set X), f.base x = s) (hf : IsProjective f) :
    ∃ (X' : Scheme.{u}) (b : X ⟶ X') (g : X' ⟶ S),
      IsContractionOfExceptionalCurve D b ∧ b ≫ g = f ∧ IsProjective g := by
  have := hE.isEffectiveCartierDivisor
  have : IsProper f := hf.isProper
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  -- the curve lies over a closed point
  have := isIntegral_subscheme_of_iso_projectiveLineProj D k e
  obtain ⟨d₀⟩ : Nonempty D.subscheme := inferInstance
  have hne : (D.support : Set X).Nonempty :=
    ⟨D.subschemeι.base d₀, by rw [← D.range_subschemeι]; exact ⟨d₀, rfl⟩⟩
  have hsc : IsClosed ({s} : Set S) := by
    have him : f.base '' (D.support : Set X) = {s} := by
      refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, hne.some_mem, hs _ hne.some_mem⟩, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact hs x hx
    rw [← him]
    exact f.isClosedMap _ D.support.isClosed
  -- a relatively ample invertible module
  obtain ⟨-, L, hLinv, hLamp⟩ := hf.isQuasiProjective
  have : Stacks.Ample.IsInvertibleModule X L := hLinv
  -- an affine open around `s`
  obtain ⟨-, ⟨U, hU, rfl⟩, hsU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  set U₀ : X.Opens := f ⁻¹ᵁ U
  have hsuppR : (D.support : Set X) ⊆ Set.range U₀.ι.base := by
    rw [Scheme.Opens.range_ι]
    exact fun x hx => show f.base x ∈ U from hs x hx ▸ hsU
  -- the contraction over `U`, by Tag 0C2M
  have : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let fY : U₀.toScheme ⟶ Spec (.of Γ(S, U)) := (f ∣_ U) ≫ hU.isoSpec.hom
  have : IsProper fY := by
    have : IsProper (f ∣_ U) := IsZariskiLocalAtTarget.restrict (P := @IsProper) ‹_› U
    infer_instance
  let LY : U₀.toScheme.Modules := (Scheme.Modules.pullback U₀.ι).obj L
  have : Stacks.Ample.IsInvertibleModule U₀.toScheme LY :=
    Scheme.Modules.isInvertibleModule_pullback_obj U₀.ι L
  have hLY : Scheme.Modules.IsAmple U₀.toScheme LY :=
    isAmple_pullback_of_isAmple_pullbackModule U₀.ι L (hLamp.2 U hU)
  have hEY := Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.comap U₀.ι D hE hsuppR
  obtain ⟨V', c, hc, ⟨fV, hfV, hfVp⟩, ⟨n, hn⟩, hL'⟩ :=
    exists_contraction_isProper_isAmple fY LY hLY hEY
  obtain ⟨⟨N, hNinv, hNcl⟩, hNamp⟩ := hL' n hn
  have hgV : c ≫ (fV ≫ hU.isoSpec.inv ≫ Scheme.Opens.ι U) = U₀.ι ≫ f := by
    rw [← Category.assoc, hfV]
    simp only [fY, Category.assoc, Iso.hom_inv_id_assoc, morphismRestrict_ι]
    rfl
  obtain ⟨X', b, g, L', hL'inv, hb, hg, -, hgprop, hampU, R, hR, hampR⟩ :=
    exists_contraction_of_ample_chart f hE s hs L hLamp U hsU c hc
      (fV ≫ hU.isoSpec.inv ≫ Scheme.Opens.ι U) hgV n N (hNamp N hNcl) hNcl
  have : Surjective b := ⟨surjective_of_isContractionOfExceptionalCurve D k e b hb⟩
  have : IsProper g := hgprop inferInstance
  -- `ℒ'` is `g`-ample: every point of `S` has an affine neighbourhood inside `U` or avoiding `s`
  have hrel : Stacks.RelativeAmple.IsRelativelyAmple g L' := by
    refine Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple g L'
      inferInstance fun t => ?_
    by_cases ht : t ∈ U
    · exact ⟨U, hU, ht, hampU U hU le_rfl⟩
    · have hts : t ∈ ({s} : Set S)ᶜ := fun h => ht (by rwa [h])
      obtain ⟨-, ⟨V, hV, rfl⟩, htV, hVs⟩ :=
        S.isBasis_affineOpens.exists_subset_of_mem_open hts hsc.isOpen_compl
      have hVR : g ⁻¹ᵁ V ⊓ R = g ⁻¹ᵁ V := by
        refine inf_eq_left.mpr fun y hy => ?_
        obtain ⟨x, rfl⟩ := b.surjective y
        have hxR : x ∈ b ⁻¹ᵁ R := by
          rw [hR]
          intro hx
          have hfx : f.base x ∈ V := by
            change g.base (b.base x) ∈ V at hy
            rwa [← Scheme.Hom.comp_apply, hg] at hy
          exact hVs hfx (hs x hx)
        exact hxR
      have h := hampR V hV
      rw [hVR] at h
      exact ⟨V, hV, htV, h⟩
  have hqp : IsQuasiProjective g := ⟨⟨inferInstance, inferInstance⟩, L', hL'inv, hrel⟩
  exact ⟨X', b, g, hb, hg, (isProjective_iff_isQuasiProjective_and_isProper g).2
    ⟨hqp, inferInstance⟩⟩

end AlgebraicGeometry

end
