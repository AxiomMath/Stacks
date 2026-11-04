module

public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.SliceTransport
public import StacksFrontier.AlgebraicGeometry.Cohomology.ProperOverBase.Functoriality
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceDerivedLimit
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Restriction
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ProperPartOverHenselianPair.Chow
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.RingTheory.Henselian.Pair.Criteria
public import StacksFrontier.RingTheory.Henselian.Pair.Nilpotent

/-!
# Shrinking the open of Grothendieck existence until the support is proper

In Situation [Stacks, Tag 0CTC], let `W ⊆ X` be an open containing the closed subschemes
`Xₙ ⊆ X` and let `G` be an `𝒪_X`-module whose restriction to `W` is of finite presentation and
whose pullback to `X₀` is `ℱ₀`. The proof of [Stacks, Tag 0CTI] shrinks `W` so that the support
of `G|_W` becomes proper over `A = lim Aₙ`: the support `Z` of `G|_W` is closed, its closed fibre
over `Spec(A₀)` is the support of `ℱ₀`, hence proper, so by [Stacks, Tag 0CT9] applied to the
henselian pair `(A, Ker(A → A₀))` of [Stacks, Tag 0CT7] it splits as `Z = Z₁ ⨿ Z₂` with `Z₁`
proper over `A` and `Z₂` missing the closed fibre; removing `Z₂` from `W` gives the open sought.
This file carries out that argument.

## Main results

* `AlgebraicGeometry.GrothendieckExistence.isProper_comp_iff_isProperOver_range`: a closed
  immersion is proper over the base exactly when its range is ([Stacks, Tag 0CYL]).
* `ExistenceSituation.range_closedImmersion_eq`: all the
  `Xₙ` have the same underlying set, the points over `Spec(A₁) = Spec(A₂) = …`.
* `ExistenceSituation.exists_le_isProperOver_supp`: the
  shrinking step of [Stacks, Tag 0CTI].

## Implementation notes

The source applies [Stacks, Tag 0CT9] to the support `Z` itself; here `Z` carries its reduced
induced closed subscheme structure, and the quasi-compactness that Tag 0CT9 asks of `Z ⟶ Spec A`
is obtained by first shrinking `W` to a quasi-compact open still containing `X₀`, which is
possible because `X₀` is closed in the quasi-compact scheme `X`. The closed fibre in Tag 0CT9 is
the base change along `Spec(A ⧸ I) ⟶ Spec A` for `I = Ker(A → A₀)`, which is identified with the
base change along `Spec(A₀) ⟶ Spec A` through `A ⧸ I ≅ A₀`.

As in Situation [Stacks, Tag 0CTC], the index `n : ℕ` stands for the level `n + 1` of the
source.

## References

* [Stacks Project, Tag 0CTI](https://stacks.math.columbia.edu/tag/0CTI)
* [Stacks Project, Tag 0CT9](https://stacks.math.columbia.edu/tag/0CT9)
* [Stacks Project, Tag 0CT7](https://stacks.math.columbia.edu/tag/0CT7)
* [Stacks Project, Tag 0CYL](https://stacks.math.columbia.edu/tag/0CYL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.GrothendieckExistence

section Generalities

/-- A closed immersion is proper over a base exactly when its range is. -/
theorem isProper_comp_iff_isProperOver_range {P Y S : Scheme.{u}} (c : P ⟶ Y) [IsClosedImmersion c]
    (g : Y ⟶ S) [LocallyOfFiniteType g] :
    IsProper (c ≫ g) ↔ IsProperOver g ⟨Set.range c, c.isClosedEmbedding.isClosed_range⟩ := by
  have hsupp : c.ker.support = ⟨Set.range c, c.isClosedEmbedding.isClosed_range⟩ :=
    Closeds.ext <| by
      rw [Scheme.Hom.support_ker]
      exact c.isClosedEmbedding.isClosed_range.closure_eq
  have h1 : IsProper (c ≫ g) ↔ IsProper (c.ker.subschemeι ≫ g) := by
    conv_lhs => rw [← show c.toImage ≫ c.ker.subschemeι = c from c.toImage_imageι,
      Category.assoc]
    exact MorphismProperty.cancel_left_of_respectsIso @IsProper c.toImage _
  rw [h1, isProperOver_iff_exists_isProper]
  exact ⟨fun h => ⟨c.ker, hsupp, h⟩, fun h =>
    (exists_isProper_iff_forall_isProper g _).1 h c.ker hsupp⟩

/-- A morphism factoring through an open computes its preimages inside that open. -/
theorem preimage_range_comp_ι {X Y P : Scheme.{u}} (W : X.Opens) (z : P ⟶ W.toScheme)
    (j : Y ⟶ X) (l : Y ⟶ W.toScheme) (hl : l ≫ W.ι = j) :
    j ⁻¹' Set.range (z ≫ W.ι) = l ⁻¹' Set.range z := by
  subst hl
  ext x
  simp only [Set.mem_preimage, Set.mem_range, Scheme.Hom.comp_apply]
  exact ⟨fun ⟨y, hy⟩ => ⟨y, W.ι.isOpenEmbedding.injective hy⟩, fun ⟨y, hy⟩ => ⟨y, by rw [hy]⟩⟩

/-- A morphism whose range lies in an open factors through that open. -/
private theorem exists_comp_ι_eq {X Y : Scheme.{u}} (W : X.Opens) (f : Y ⟶ X)
    (h : Set.range f ⊆ W) : ∃ l : Y ⟶ W.toScheme, l ≫ W.ι = f :=
  ⟨IsOpenImmersion.lift W.ι f (by rwa [Scheme.Opens.range_ι]), IsOpenImmersion.lift_fac _ _ _⟩

/-- Properness of a base change only depends on the image of the base morphism, in the form of an
isomorphism factoring one base morphism through the other. -/
theorem isProper_pullback_snd_of_isIso {P B T T' : Scheme.{u}} (f : P ⟶ B) (q : T ⟶ B)
    (q' : T' ⟶ B) (i : T' ⟶ T) [IsIso i] (hi : i ≫ q = q')
    (h : IsProper (pullback.snd f q')) : IsProper (pullback.snd f q) := by
  let g : pullback f q ⟶ pullback f q' :=
    pullback.map f q f q' (𝟙 _) (inv i) (𝟙 _) (by simp)
      (by rw [Category.comp_id, IsIso.eq_inv_comp, hi])
  have hg : pullback.snd f q = g ≫ pullback.snd f q' ≫ i := by
    simp only [g, pullback.map, pullback.lift_snd_assoc, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id]
  rw [hg]
  infer_instance

end Generalities

namespace ExistenceSituation

variable (S : ExistenceSituation.{u})

/-- The scheme of the situation is locally of finite presentation over the inverse-limit base. -/
instance instLocallyOfFinitePresentationXHom : LocallyOfFinitePresentation S.X.hom :=
  S.finitePresentation.1

/-- The consecutive transitions of the system of rings are surjective with kernels contained in
the nilradical, the form in which Stacks 0CT7 and 0CTJ take them. -/
theorem transition_surjective_ker_le_nilradical (n : ℕ) :
    Function.Surjective (S.system.map (homOfLE (Nat.le_succ n)).op).hom ∧
      RingHom.ker (S.system.map (homOfLE (Nat.le_succ n)).op).hom ≤
        nilradical (S.system.obj (op (n + 1))) :=
  ⟨S.transition_surjective n, fun x hx => mem_nilradical.2 (S.transition_locallyNilpotent n x hx)⟩

/-- The projection from the inverse limit to the zeroth ring of the system is surjective. -/
theorem surjective_limit_π_zero : Function.Surjective (limit.π S.system (op 0)).hom :=
  Concrete.surjective_π_app_zero_of_surjective_map (limit.isLimit S.system)
    fun k => S.transition_surjective k

/-- All the affine bases `Spec Aₙ` have the same image in `Spec A`. -/
theorem range_baseProjection_eq (n : ℕ) :
    Set.range (baseProjection S.system n) = Set.range (baseProjection S.system 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hsurj : Function.Surjective (baseTransition S.system n) :=
      IsHomeomorph.surjective <| by
        refine PrimeSpectrum.isHomeomorph_comap _ (fun x => ?_)
          (S.transition_surjective_ker_le_nilradical n).2
        obtain ⟨y, rfl⟩ := S.transition_surjective n x
        exact ⟨1, by lia, y, by simp⟩
    have hfac : baseTransition S.system n ≫ baseProjection S.system (n + 1) =
        baseProjection S.system n := by
      simp only [baseTransition, baseProjection, ← Spec.map_comp]
      exact congrArg Spec.map (limit.w S.system (homOfLE (Nat.le_succ n)).op)
    rw [← ih, ← hfac]
    exact (hsurj.range_comp _).symm

/-- The closed fibre `V(Ker(A → A₀))` of `Spec A` has the same image in `Spec A` as the affine
base `Spec A₀`. -/
theorem range_spec_map_quotientMk_eq :
    Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (RingHom.ker (limit.π S.system (op 0)).hom)))) =
      Set.range (baseProjection S.system 0) := by
  rw [range_spec_map_quotient_mk]
  show _ = Set.range (PrimeSpectrum.comap (limit.π S.system (op 0)).hom)
  rw [_root_.range_comap_of_surjective _ _ S.surjective_limit_π_zero]

/-- All the closed subschemes `Xₙ` have the same underlying set in `X`: the points of `X` lying
over the closed subset `Spec(A₁) = Spec(A₂) = …` of `Spec A`. -/
theorem range_closedImmersion_eq (n : ℕ) :
    Set.range (S.closedImmersion n) = Set.range (S.closedImmersion 0) := by
  simp only [closedImmersion, schemeProjection, Scheme.Pullback.range_fst,
    S.range_baseProjection_eq n]

/-- The restriction of a module to a smaller open is the restriction of its restriction. -/
def restrictRestrictIso {X : Scheme.{u}} (G : X.Modules) {W₂ W₁ : X.Opens} (h : W₂ ≤ W₁) :
    G.restrict W₂.ι ≅ (G.restrict W₁.ι).restrict (X.homOfLE h) :=
  (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h).symm).app G ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE h) W₁.ι).app G

/-- Finite presentation of a restriction passes to a smaller open. -/
theorem isFinitePresentation_restrict_of_le {X : Scheme.{u}} (G : X.Modules) {W₂ W₁ : X.Opens}
    (h : W₂ ≤ W₁) [(G.restrict W₁.ι).IsFinitePresentation] :
    (G.restrict W₂.ι).IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation.{u, u, u} _).prop_of_iso (restrictRestrictIso G h).symm
    (Stacks.AlgebraicGeometry.CoherentTFAE.isFinitePresentation_restrict _ _)

/-- The support of a restriction to a smaller open is the preimage of the support. -/
theorem supp_restrict_eq_preimage {X : Scheme.{u}} (G : X.Modules) {W₂ W₁ : X.Opens}
    (h : W₂ ≤ W₁) [(G.restrict W₁.ι).IsFiniteType] :
    SheafOfModules.supp (G.restrict W₂.ι) =
      X.homOfLE h ⁻¹' SheafOfModules.supp (G.restrict W₁.ι) := by
  rw [SheafOfModules.supp_eq_of_iso (restrictRestrictIso G h),
    SheafOfModules.supp_eq_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback (X.homOfLE h)).app (G.restrict W₁.ι)),
    Stacks.Modules.supp_pullback]

/-- The support of a module restricted to a closed fibre:  if `G` is of finite type on `W`, the
support of its pullback along `Xₙ ⟶ W` is the preimage of its support. -/
theorem supp_pullback_eq {X Y : Scheme.{u}} (W : X.Opens) (G : X.Modules)
    [(G.restrict W.ι).IsFiniteType] (j : Y ⟶ X) (l : Y ⟶ W.toScheme) (hl : l ≫ W.ι = j) :
    SheafOfModules.supp ((Scheme.Modules.pullback j).obj G) =
      l ⁻¹' SheafOfModules.supp (G.restrict W.ι) := by
  have e : (Scheme.Modules.pullback j).obj G ≅ (Scheme.Modules.pullback l).obj (G.restrict W.ι) :=
    (Scheme.Modules.pullbackCongr hl.symm).app G ≪≫
      ((Scheme.Modules.pullbackComp l W.ι).app G).symm ≪≫
      (Scheme.Modules.pullback l).mapIso ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app
          G).symm
  rw [SheafOfModules.supp_eq_of_iso e, Stacks.Modules.supp_pullback]

/-- The closed fibre over `Spec A₀` of a closed subscheme `z` carrying the support of `G|_{W₁}`
is proper: it is the support of `ℱ₀`, which has proper support by assumption. -/
theorem isProper_pullback_snd_baseProjection_zero (W₁ : S.X.left.Opens)
    (hW₁ : Set.range (S.closedImmersion 0) ⊆ W₁) (G : S.X.left.Modules)
    [(G.restrict W₁.ι).IsFiniteType]
    (e : (Scheme.Modules.pullback (S.closedImmersion 0)).obj G ≅ S.F 0) {P : Scheme.{u}}
    (z : P ⟶ W₁.toScheme) [IsClosedImmersion z]
    (hz : Set.range z = SheafOfModules.supp (G.restrict W₁.ι)) :
    IsProper (pullback.snd ((z ≫ W₁.ι) ≫ S.X.hom) (baseProjection S.system 0)) := by
  have := S.compactSpace
  have := S.quasiSeparatedSpace
  have : IsSeparated S.X.hom := S.separated
  have : IsClosedImmersion (S.closedImmersion 0) := S.closedSchemeProjection 0
  let c := pullback.snd (z ≫ W₁.ι) (S.closedImmersion 0)
  have hsnd : pullback.snd ((z ≫ W₁.ι) ≫ S.X.hom) (baseProjection S.system 0) =
      (pullbackRightPullbackFstIso S.X.hom (baseProjection S.system 0) (z ≫ W₁.ι)).inv ≫
        c ≫ pullback.snd S.X.hom (baseProjection S.system 0) := by
    rw [Iso.eq_inv_comp, pullbackRightPullbackFstIso_hom_snd]
  rw [hsnd]
  suffices IsProper (c ≫ pullback.snd S.X.hom (baseProjection S.system 0)) by infer_instance
  obtain ⟨l0, hl0⟩ := exists_comp_ι_eq W₁ (S.closedImmersion 0) hW₁
  have hrc : Set.range c = l0 ⁻¹' SheafOfModules.supp (G.restrict W₁.ι) := by
    rw [Scheme.Pullback.range_snd, ← hz]
    exact preimage_range_comp_ι W₁ z (S.closedImmersion 0) l0 hl0
  have : IsClosedImmersion c := IsClosedImmersion.of_isPreimmersion c
    (by rw [hrc]; exact (SheafOfModules.isClosed_supp _).preimage l0.continuous)
  rw [isProper_comp_iff_isProperOver_range c]
  obtain ⟨Z0, i0, hi0c, hi0r, hi0p⟩ := S.properSupport 0
  convert (isProper_comp_iff_isProperOver_range i0 _).1 hi0p using 2
  rw [hrc, hi0r, ← supp_pullback_eq W₁ G (S.closedImmersion 0) l0 hl0,
    SheafOfModules.supp_eq_of_iso e]
  rfl

/-- The closed fibre over `Spec(A ⧸ Ker(A → A₀))` of a closed subscheme `z` carrying the support
of `G|_{W₁}` is proper, the form in which [Stacks, Tag 0CT9] asks for it. -/
theorem isProper_pullback_snd_quotientMk (W₁ : S.X.left.Opens)
    (hW₁ : Set.range (S.closedImmersion 0) ⊆ W₁) (G : S.X.left.Modules)
    [(G.restrict W₁.ι).IsFiniteType]
    (e : (Scheme.Modules.pullback (S.closedImmersion 0)).obj G ≅ S.F 0) {P : Scheme.{u}}
    (z : P ⟶ W₁.toScheme) [IsClosedImmersion z]
    (hz : Set.range z = SheafOfModules.supp (G.restrict W₁.ι)) :
    IsProper (pullback.snd ((z ≫ W₁.ι) ≫ S.X.hom) (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (RingHom.ker (limit.π S.system (op 0)).hom))))) := by
  set I := RingHom.ker (limit.π S.system (op 0)).hom
  let φ : ↑(limit S.system) ⧸ I ≃+* S.system.obj (op 0) :=
    RingHom.quotientKerEquivOfSurjective S.surjective_limit_π_zero
  let eS : Spec (S.system.obj (op 0)) ⟶ Spec (.of (↑(limit S.system) ⧸ I)) :=
    Spec.map (CommRingCat.ofHom φ.toRingHom)
  have : IsIso (CommRingCat.ofHom φ.toRingHom) := (RingEquiv.toCommRingCatIso φ).isIso_hom
  have : IsIso eS := inferInstance
  have heS : eS ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
      baseProjection S.system 0 := by
    simp only [eS, baseProjection, ← Spec.map_comp]
    congr 1
  exact isProper_pullback_snd_of_isIso _ _ _ eS heS
    (S.isProper_pullback_snd_baseProjection_zero W₁ hW₁ G e z hz)

/-- Removing from `W₁` the image of the non-proper part `Z₂` of the support leaves an open which
still contains every `Xₙ`, because every `Xₙ` lies over the closed fibre. -/
theorem exists_le_forall_range_closedImmersion_subset (W₁ : S.X.left.Opens)
    (hW₁ : ∀ n, Set.range (S.closedImmersion n) ⊆ W₁) {P : Scheme.{u}} (z : P ⟶ W₁.toScheme)
    [IsClosedImmersion z] {Pc : Scheme.{u}} (w : Pc ⟶ P) [IsOpenImmersion w]
    (hmemw : ∀ t : P, ((z ≫ W₁.ι) ≫ S.X.hom) t ∈ Set.range (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (RingHom.ker (limit.π S.system (op 0)).hom)))) → t ∈ Set.range w) :
    ∃ W' : S.X.left.Opens, W' ≤ W₁ ∧ (∀ n, Set.range (S.closedImmersion n) ⊆ W') ∧
      ∀ y : W₁.toScheme, W₁.ι y ∈ W' ↔ y ∉ z '' (Set.range w)ᶜ := by
  let U' : W₁.toScheme.Opens := ⟨(z '' (Set.range w)ᶜ)ᶜ, (z.isClosedEmbedding.isClosedMap _
    w.isOpenEmbedding.isOpen_range.isClosed_compl).isOpen_compl⟩
  let W' : S.X.left.Opens := W₁.ι ''ᵁ U'
  have hW'W₁ : W' ≤ W₁ := by
    simpa [Scheme.Opens.opensRange_ι] using W₁.ι.image_le_opensRange U'
  have hmemW' : ∀ y : W₁.toScheme, W₁.ι y ∈ W' ↔ y ∉ z '' (Set.range w)ᶜ := fun y =>
    ⟨fun ⟨_, hy', hyy'⟩ => W₁.ι.isOpenEmbedding.injective hyy' ▸ hy', fun hy => ⟨y, hy, rfl⟩⟩
  refine ⟨W', hW'W₁, fun n => ?_, hmemW'⟩
  rintro _ ⟨p, rfl⟩
  obtain ⟨ln, hln⟩ := exists_comp_ι_eq W₁ (S.closedImmersion n) (hW₁ n)
  rw [← hln, Scheme.Hom.comp_apply, SetLike.mem_coe, hmemW']
  rintro ⟨t, ht, hzt⟩
  refine ht (hmemw t ?_)
  rw [S.range_spec_map_quotientMk_eq, ← S.range_baseProjection_eq n]
  refine ⟨pullback.snd S.X.hom (baseProjection S.system n) p, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
  show S.X.hom (S.closedImmersion n p) = S.X.hom (W₁.ι (z t))
  rw [hzt, ← hln, Scheme.Hom.comp_apply]

/-- On the open `W'` left after removing the non-proper part of the support, the support of `G`
is the image of the proper part `Z₁`. -/
theorem exists_lift_range_eq_supp_restrict (W₁ : S.X.left.Opens) (G : S.X.left.Modules)
    [(G.restrict W₁.ι).IsFiniteType] {P : Scheme.{u}} (z : P ⟶ W₁.toScheme) [IsClosedImmersion z]
    (hz : Set.range z = SheafOfModules.supp (G.restrict W₁.ι)) {Pc : Scheme.{u}} (w : Pc ⟶ P)
    (W' : S.X.left.Opens) (hW' : W' ≤ W₁)
    (hmemW' : ∀ y : W₁.toScheme, W₁.ι y ∈ W' ↔ y ∉ z '' (Set.range w)ᶜ) :
    ∃ k : Pc ⟶ W'.toScheme, k ≫ W'.ι = w ≫ z ≫ W₁.ι ∧
      Set.range k = SheafOfModules.supp (G.restrict W'.ι) := by
  let j := S.X.left.homOfLE hW'
  have hj : j ≫ W₁.ι = W'.ι := S.X.left.homOfLE_ι hW'
  have hk : Set.range (w ≫ z ≫ W₁.ι) ⊆ W' := by
    rintro _ ⟨a, rfl⟩
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, SetLike.mem_coe,
      hmemW']
    rintro ⟨t, ht, hzt⟩
    exact ht ⟨a, z.isClosedEmbedding.injective hzt.symm⟩
  obtain ⟨k, hkf⟩ := exists_comp_ι_eq W' (w ≫ z ≫ W₁.ι) hk
  refine ⟨k, hkf, ?_⟩
  rw [supp_restrict_eq_preimage G hW']
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    rw [Set.mem_preimage, ← hz]
    refine ⟨w a, W₁.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply j W₁.ι, hj, ← Scheme.Hom.comp_apply k W'.ι, hkf]
    rfl
  · rw [Set.mem_preimage, ← hz]
    rintro ⟨t, ht⟩
    have hyW' : z t ∉ z '' (Set.range w)ᶜ := by
      rw [ht, ← hmemW', ← Scheme.Hom.comp_apply, hj]
      exact y.2
    obtain ⟨a, rfl⟩ : t ∈ Set.range w := not_not.1 fun htw => hyW' ⟨t, htw, rfl⟩
    refine ⟨a, W'.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hkf, ← hj, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ht]
    rfl

/-- **The proper part of the support, by [Stacks, Tag 0CT9].** A closed subscheme `z` carrying
the support of `G|_{W₁}` splits, over the henselian pair `(A, Ker(A → A₀))` of
[Stacks, Tag 0CT7], into an open and closed part which is proper over `Spec A` and a part
missing the closed fibre. -/
theorem exists_isOpenImmersion_isProper_forall_mem_range (W₁ : S.X.left.Opens)
    [CompactSpace W₁.toScheme] (hW₁ : Set.range (S.closedImmersion 0) ⊆ W₁)
    (G : S.X.left.Modules) [(G.restrict W₁.ι).IsFiniteType]
    (e : (Scheme.Modules.pullback (S.closedImmersion 0)).obj G ≅ S.F 0) {P : Scheme.{u}}
    (z : P ⟶ W₁.toScheme) [IsClosedImmersion z]
    (hz : Set.range z = SheafOfModules.supp (G.restrict W₁.ι)) :
    ∃ (Pc : Scheme.{u}) (w : Pc ⟶ P), IsOpenImmersion w ∧
      IsProper (w ≫ (z ≫ W₁.ι) ≫ S.X.hom) ∧
      ∀ t : P, ((z ≫ W₁.ι) ≫ S.X.hom) t ∈ Set.range (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (RingHom.ker (limit.π S.system (op 0)).hom)))) → t ∈ Set.range w := by
  have : IsSeparated S.X.hom := S.separated
  let A := ↑(limit S.system)
  let f : P ⟶ Spec (.of A) := (z ≫ W₁.ι) ≫ S.X.hom
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace z
  have : QuasiCompact f := quasiCompact_of_compactSpace f
  let I := RingHom.ker (limit.π S.system (op 0)).hom
  have : HenselianRing A I :=
    henselianRing_ker_limit_π_of_surjective_of_ker_le_nilradical S.system (limit.cone S.system)
      (limit.isLimit S.system) S.transition_surjective_ker_le_nilradical 0
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have : IsProper (𝟙 (pullback f q) ≫ pullback.snd f q) := by
    simpa using S.isProper_pullback_snd_quotientMk W₁ hW₁ G e z hz
  obtain ⟨Pc, w, hwo, -, hwp, hwr⟩ := exists_isClopen_isProper_range_eq_of_henselianPair A I
    (henselianPair_of_henselianRing A I) f (𝟙 (pullback f q))
  refine ⟨Pc, w, hwo, hwp, fun t ht => ?_⟩
  obtain ⟨s, rfl⟩ : t ∈ Set.range (pullback.fst f q) := by
    rwa [Scheme.Pullback.range_fst]
  show s ∈ pullback.fst f q ⁻¹' Set.range w
  rw [hwr]
  exact ⟨s, rfl⟩

/-- **The shrinking step of [Stacks, Tag 0CTI].** In Situation [Stacks, Tag 0CTC], let `W` be an
open of `X` containing every `Xₙ`, and let `G` be an `𝒪_X`-module whose restriction to `W` is of
finite presentation and whose pullback to `X₀` is isomorphic to `ℱ₀`. Then there is a smaller
open `W' ⊆ W`, still containing every `Xₙ`, on which `G` is still of finite presentation and
whose support is proper over `Spec A`. -/
theorem exists_le_isProperOver_supp (W : S.X.left.Opens)
    (hW : ∀ n, Set.range (S.closedImmersion n) ⊆ W) (G : S.X.left.Modules)
    [hfp : (G.restrict W.ι).IsFinitePresentation]
    (e : (Scheme.Modules.pullback (S.closedImmersion 0)).obj G ≅ S.F 0) :
    ∃ W' : S.X.left.Opens, W' ≤ W ∧ (∀ n, Set.range (S.closedImmersion n) ⊆ W') ∧
      (G.restrict W'.ι).IsFinitePresentation ∧
      ∃ Z : Closeds W'.toScheme, (Z : Set W'.toScheme) = SheafOfModules.supp (G.restrict W'.ι) ∧
        IsProperOver (W'.ι ≫ S.X.hom) Z := by
  classical
  have := S.compactSpace
  have := S.quasiSeparatedSpace
  have : IsSeparated S.X.hom := S.separated
  have : IsClosedImmersion (S.closedImmersion 0) := S.closedSchemeProjection 0
  obtain ⟨V, hVc, hVo, hKV, hVW⟩ := PrespectralSpace.exists_isCompact_and_isOpen_between
    (S.closedImmersion 0).isClosedEmbedding.isClosed_range.isCompact W.2 (hW 0)
  let W₁ : S.X.left.Opens := ⟨V, hVo⟩
  have hW₁W : W₁ ≤ W := hVW
  have hW₁ : ∀ n, Set.range (S.closedImmersion n) ⊆ W₁ := fun n =>
    (S.range_closedImmersion_eq n).trans_subset hKV
  have : CompactSpace W₁.toScheme := isCompact_iff_compactSpace.mp hVc
  let G₁ := G.restrict W₁.ι
  have hG₁ft : G₁.IsFiniteType :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isFinitePresentation
      G₁ (isFinitePresentation_restrict_of_le G hW₁W)).2
  -- the reduced closed subscheme on the support of `G₁`
  let Z : Closeds W₁.toScheme := ⟨SheafOfModules.supp G₁, SheafOfModules.isClosed_supp G₁⟩
  let J := Scheme.IdealSheafData.vanishingIdeal Z
  let z := J.subschemeι
  have hzr : Set.range z = SheafOfModules.supp G₁ := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  -- the proper part of the support, and the points of the support lying in it
  obtain ⟨Pc, w, hwo, hwp, hmemw⟩ :=
    S.exists_isOpenImmersion_isProper_forall_mem_range W₁ (hW₁ 0) G e z hzr
  have : IsOpenImmersion w := hwo
  have : IsProper (w ≫ (z ≫ W₁.ι) ≫ S.X.hom) := hwp
  -- the complement of the proper part, and the open `W'` it leaves
  obtain ⟨W', hW'W₁, hW'n, hmemW'⟩ :=
    S.exists_le_forall_range_closedImmersion_subset W₁ hW₁ z w hmemw
  refine ⟨W', hW'W₁.trans hW₁W, hW'n,
    isFinitePresentation_restrict_of_le G (hW'W₁.trans hW₁W), ?_⟩
  -- the support of `G` on `W'` is the image of the proper part
  obtain ⟨k, hkf, hrk⟩ := S.exists_lift_range_eq_supp_restrict W₁ G z hzr w W' hW'W₁ hmemW'
  have hp : IsProperOver (w ≫ (z ≫ W₁.ι) ≫ S.X.hom) ⊤ := by
    convert (isProper_comp_iff_isProperOver_range (𝟙 Pc)
      (w ≫ (z ≫ W₁.ι) ≫ S.X.hom)).1 (by simpa using hwp)
    simp
  have hfg : k ≫ (W'.ι ≫ S.X.hom) = w ≫ (z ≫ W₁.ι) ≫ S.X.hom := by
    rw [← Category.assoc, hkf, Category.assoc]
  refine ⟨⟨k.base '' Set.univ, isClosed_image_of_isProperOver _ (W'.ι ≫ S.X.hom) k hfg ⊤ hp⟩,
    ?_, isProperOver_image _ (W'.ι ≫ S.X.hom) k hfg ⊤ hp⟩
  show k.base '' Set.univ = _
  rw [Set.image_univ, ← hrk]

end ExistenceSituation

end AlgebraicGeometry.GrothendieckExistence

end
