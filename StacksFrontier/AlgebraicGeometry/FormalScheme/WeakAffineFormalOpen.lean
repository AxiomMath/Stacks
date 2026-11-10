module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumGlobalSectionsIso
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumSheaf
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsAffine
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsFull
public import StacksFrontier.AlgebraicGeometry.FormalScheme.McQuillanFormalScheme
public import StacksFrontier.AlgebraicGeometry.FormalScheme.SchemeToFormalSchemeRestrict
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinition

/-!
# Points of McQuillan's formal spectrum killing a weak ideal of definition

Let `A` be a weakly admissible topological ring and `Spfw A` its formal spectrum taken along the
weak ideals of definition (Stacks 0AI3). A point `g : T → Spfw A` over a scheme `T` induces a ring
homomorphism `A → Γ(T, 𝒪_T)`. This file proves that `g` factors through the quotient point
`Spec (A/J) → Spfw A` of a weak ideal of definition `J` exactly when that homomorphism kills `J`,
and then the factorisation is unique; and that over a quasi-compact `T` the homomorphism kills
some weak ideal of definition. Both are statements about *all* schemes `T`, not only affine ones.

## Main results

* `AlgebraicGeometry.spfwPoint_hom_ext`: a point of `Spfw A` over a scheme is determined by the
  ring homomorphism it induces on global sections.
* `AlgebraicGeometry.existsUnique_spfwQuotientPoint_factor`: a point killing `J` factors uniquely
  through `Spec (A/J)`.
* `AlgebraicGeometry.exists_weakIdeal_kill_of_compactSpace`: over a quasi-compact scheme a point
  kills some weak ideal of definition.

## References

* [Stacks Project, Tag 0AI3](https://stacks.math.columbia.edu/tag/0AI3)
* [Stacks Project, Tag 0AIV](https://stacks.math.columbia.edu/tag/0AIV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

open TopologicalRing

/-! ### Weak affine formal opens -/

/-- An open `U` of an object `X` of `LTRS` is a *weak affine formal open subscheme* when the
locally topologically ringed space induced on `U` is isomorphic to McQuillan's formal spectrum of
a weakly admissible topological ring. This is exactly the condition that
`AlgebraicGeometry.IsMcQuillanFormalScheme` asks of a neighbourhood of every point, and it is the
class of opens on which Stacks 0AIV imposes its conditions: the affine formal open subschemes of a
formal scheme in the sense of McQuillan. -/
def IsWeakAffineFormalOpen (X : LTRS.{u}) (U : Opens X) : Prop :=
  ∃ A : TopCommRingCat.{u}, ∃ hlinear : IsLinearTopology A.α A.α,
    letI := hlinear
    IsWeaklyAdmissible A.α ∧
      Nonempty (X.toPresheafedSpace.restrict (f := U.inclusion') U.isOpenEmbedding' ≅ Spfw A.α)

/-- An object of `LTRS` is a formal scheme in the sense of McQuillan exactly when each of its
points has a weak affine formal open neighbourhood. -/
theorem isMcQuillanFormalScheme_iff_forall_isWeakAffineFormalOpen (X : LTRS.{u}) :
    IsMcQuillanFormalScheme X ↔ ∀ x : X, ∃ U : Opens X, x ∈ U ∧ IsWeakAffineFormalOpen X U where
  mp hX x := by
    obtain ⟨U, hxU, A, hlinear, hA⟩ := hX x
    exact ⟨U, hxU, A, hlinear, hA⟩
  mpr hX x := by
    obtain ⟨U, hxU, A, hlinear, hA⟩ := hX x
    exact ⟨U, hxU, A, hlinear, hA⟩

/-- A weak affine formal open is quasi-compact: it is homeomorphic to the space of open primes of
a weakly admissible topological ring. -/
theorem IsWeakAffineFormalOpen.isCompact {X : LTRS.{u}} {U : Opens X}
    (hU : IsWeakAffineFormalOpen X U) : IsCompact (U : Set X) := by
  obtain ⟨A, hlinear, hA, ⟨e⟩⟩ := hU
  have : CompactSpace ((PresheafedSpace.forget _).obj (Spfw A.α)) :=
    compactSpace_spfSpace_of_isWeaklyPreAdmissible A.α hA.1
  let h := TopCat.homeoOfIso ((PresheafedSpace.forget _).mapIso e)
  have : CompactSpace U := h.symm.compactSpace
  exact isCompact_iff_compactSpace.mpr this

namespace LocallyTopologicallyRingedSpace.IdealSheaf

variable {X : LTRS.{u}}

/-- An ideal sheaf `ℐ` on `X` is *cut out by its sections over the members of a class `𝒜` of
opens* when, for every `U ∈ 𝒜` and every open `V ≤ U`, a section of `𝒪_X` over `V` lies in `ℐ(V)`
exactly when it is killed by every point `f : T → X` of a scheme which lands in `U` and kills
`ℐ(U)`. Over an affine formal open `𝔘 ≅ Spfw A` this says that `ℐ|_𝔘` is the kernel ideal sheaf of
the quotient point `Spec (A/ℐ(𝔘)) → 𝔘`, through which the points of `𝔘` killing `ℐ(𝔘)` are exactly
those that factor: it is the condition, analogous to quasi-coherence, that singles out among the
weak ideals of definition the ones cut out by thickenings. -/
def IsCutOutOn (I : IdealSheaf X) (𝒜 : Opens X → Prop) : Prop :=
  ∀ U : Opens X, 𝒜 U → ∀ V : Opens X, V ≤ U → ∀ s : (X.presheaf.obj (op V)).α,
    s ∈ I.ideal V ↔ ∀ (T : Scheme.{u}) (f : schemeToLTRSObj T ⟶ X),
      Set.range f.toHom.base ⊆ (U : Set X) →
        (∀ t ∈ I.ideal U, (f.toHom.c.app (op U)).1 t = 0) → (f.toHom.c.app (op V)).1 s = 0

end LocallyTopologicallyRingedSpace.IdealSheaf

section Spfw

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] (hA : IsWeaklyAdmissible A)

/-- The quotient point `Spec (A/J) → Spfw A` attached to a weak ideal of definition. -/
noncomputable abbrev spfwQuotientPoint (J : WeakIdealsOfDefinition A) :
    schemeToLTRSObj (Spec (spfQuotientOn A J)) ⟶ spfwLTRS A hA.1 :=
  spfQuotientPointOn A (weaklyPreAdmissibleSpfIndex A hA.1) J

omit [IsLinearTopology A A] in
/-- The ring homomorphism `A → Γ(T, 𝒪_T)` of a point precomposed with a morphism of schemes is the
composite with the map that morphism induces on global sections. -/
theorem spfPointGammaHomOn_schemeToLTRS_map_comp (hA : IsWeaklyPreAdmissible A) {T T' : Scheme.{u}}
    (h : T' ⟶ T) (g : schemeToLTRSObj T ⟶ spfwLTRS A hA) :
    spfPointGammaHomOn A (schemeToLTRS.map h ≫ g) = spfPointGammaHomOn A g ≫ h.appTop :=
  rfl

/-- **A point of `Spfw A` over a scheme is determined by the ring homomorphism it induces on
global sections.** Over an affine scheme this is
`AlgebraicGeometry.schemeToLTRS_hom_ext_of_spfPointGammaHomOn_eq`, through Stacks 0AHY for a
weakly admissible ring; in general both points agree on every affine open, whose induced
homomorphisms are the restrictions, and morphisms out of a scheme glue along its affine opens. -/
theorem spfwPoint_hom_ext {T : Scheme.{u}} {u v : schemeToLTRSObj T ⟶ spfwLTRS A hA.1}
    (h : spfPointGammaHomOn A u = spfPointGammaHomOn A v) : u = v := by
  have hloc : ∀ V : T.affineOpens, schemeToLTRS.map V.1.ι ≫ u = schemeToLTRS.map V.1.ι ≫ v :=
    fun V => by
      have : IsAffine V.1.toScheme := V.2
      exact schemeToLTRS_hom_ext_of_spfPointGammaHomOn_eq A _ (isIso_spfwGammaHom A hA) _
        (congrArg (fun φ => φ ≫ V.1.ι.appTop) h)
  obtain ⟨f, -, huniq⟩ := existsUnique_ltrsHom_of_openCover_scheme
    (fun V : T.affineOpens => V.1) (iSup_affineOpens_eq_top T)
    (fun V => schemeToLTRS.map V.1.ι ≫ v) fun V W =>
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ v)
        ((schemeToLTRS.map_comp _ _).symm.trans (congrArg schemeToLTRS.map
          (T.homOfLE_ι _))))).trans
      ((congrArg (· ≫ v) ((schemeToLTRS.map_comp _ _).symm.trans (congrArg schemeToLTRS.map
          (T.homOfLE_ι _))).symm).trans (Category.assoc _ _ _))
  exact (huniq u hloc).trans (huniq v fun _ => rfl).symm

/-- The ring homomorphism induced by the quotient point `Spec (A/J) → Spfw A` precomposed with a
morphism of schemes `b : T → Spec (A/J)` is the quotient map followed by the map `b` induces on
global sections. -/
theorem spfPointGammaHomOn_comp_spfwQuotientPoint (J : WeakIdealsOfDefinition A) {T : Scheme.{u}}
    (b : T ⟶ Spec (spfQuotientOn A J)) :
    spfPointGammaHomOn A (schemeToLTRS.map b ≫ spfwQuotientPoint A hA J) =
      CommRingCat.ofHom (Ideal.Quotient.mk J.1) ≫ (Scheme.ΓSpecIso (spfQuotientOn A J)).inv ≫
        b.appTop :=
  spfPointGammaHomOn_comp_spfQuotientPointOn A _ J b

/-- A point that factors through the quotient point of `J` kills `J`. -/
theorem spfPointGammaHomOn_comp_spfwQuotientPoint_apply (J : WeakIdealsOfDefinition A)
    {T : Scheme.{u}} (b : T ⟶ Spec (spfQuotientOn A J)) {a : A} (ha : a ∈ J.1) :
    (spfPointGammaHomOn A (schemeToLTRS.map b ≫ spfwQuotientPoint A hA J)).hom a = 0 := by
  refine (congrArg (fun φ => φ.hom a) (spfPointGammaHomOn_comp_spfwQuotientPoint A hA J b)).trans ?_
  change b.appTop.hom ((Scheme.ΓSpecIso _).inv.hom (Ideal.Quotient.mk J.1 a)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero, map_zero]

/-- The quotient point of `J` is a monomorphism on points over schemes: two morphisms
`T → Spec (A/J)` with the same composite to `Spfw A` induce the same homomorphism `A → Γ(T, 𝒪_T)`,
hence, `A → A/J` being surjective, the same homomorphism `A/J → Γ(T, 𝒪_T)`. -/
theorem spfwQuotientPoint_cancel (J : WeakIdealsOfDefinition A) {T : Scheme.{u}}
    {b b' : T ⟶ Spec (spfQuotientOn A J)}
    (h : schemeToLTRS.map b ≫ spfwQuotientPoint A hA J =
      schemeToLTRS.map b' ≫ spfwQuotientPoint A hA J) : b = b' := by
  have hγ := (spfPointGammaHomOn_comp_spfwQuotientPoint A hA J b).symm.trans
    ((congrArg (spfPointGammaHomOn A) h).trans
      (spfPointGammaHomOn_comp_spfwQuotientPoint A hA J b'))
  refine ext_of_isAffine ((cancel_epi (Scheme.ΓSpecIso (spfQuotientOn A J)).inv).mp ?_)
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact congrArg (fun φ : CommRingCat.of A ⟶ Γ(T, ⊤) => φ.hom a) hγ

/-- **A point killing a weak ideal of definition factors through its quotient point.** If the
homomorphism `A → Γ(T, 𝒪_T)` induced by `g : T → Spfw A` kills `J`, then `g` factors as
`T → Spec (A/J) → Spfw A`, and uniquely. The factoring morphism is the one the induced
homomorphism `A/J → Γ(T, 𝒪_T)` corresponds to; both composites induce the same homomorphism on
global sections, so they agree by `AlgebraicGeometry.spfwPoint_hom_ext`. -/
theorem existsUnique_spfwQuotientPoint_factor (J : WeakIdealsOfDefinition A) {T : Scheme.{u}}
    (g : schemeToLTRSObj T ⟶ spfwLTRS A hA.1)
    (hg : ∀ a ∈ J.1, (spfPointGammaHomOn A g).hom a = 0) :
    ∃! b : T ⟶ Spec (spfQuotientOn A J), schemeToLTRS.map b ≫ spfwQuotientPoint A hA J = g := by
  set ψ : spfQuotientOn A J ⟶ Γ(T, ⊤) :=
    CommRingCat.ofHom (Ideal.Quotient.lift J.1 (spfPointGammaHomOn A g).hom hg) with hψ
  have key : schemeToLTRS.map ((ΓSpec.adjunction.homEquiv T (op (spfQuotientOn A J))) ψ.op) ≫
      spfwQuotientPoint A hA J = g := by
    refine spfwPoint_hom_ext A hA ((spfPointGammaHomOn_comp_spfwQuotientPoint A hA J _).trans ?_)
    rw [ΓSpecIso_inv_ΓSpec_adjunction_homEquiv]
    exact CommRingCat.hom_ext (Ideal.Quotient.lift_comp_mk J.1 _ hg)
  exact ⟨_, key, fun b' hb' => spfwQuotientPoint_cancel A hA J (hb'.trans key.symm)⟩

omit [IsLinearTopology A A] in
/-- **Over a quasi-compact scheme a point of `Spfw A` kills a weak ideal of definition.** The
global sections of the pseudo-discretised structure sheaf of a quasi-compact scheme are discrete,
so the continuous homomorphism `A → Γ(T, 𝒪_T)` has open kernel, and its meet with a weak ideal of
definition is one. -/
theorem exists_weakIdeal_kill_of_compactSpace (hA : IsWeaklyPreAdmissible A) {T : Scheme.{u}}
    [CompactSpace T] (g : schemeToLTRSObj T ⟶ spfwLTRS A hA) :
    ∃ J : WeakIdealsOfDefinition A, ∀ a ∈ J.1, (spfPointGammaHomOn A g).hom a = 0 := by
  set χ : TopCommRingCat.of A ⟶ (schemeToLTRSObj T).presheaf.obj (op ⊤) :=
    spfGammaHomOn A IsWeakIdealOfDefinition ≫ ltrsGlobalSectionsMap g with hχ
  have : DiscreteTopology ((schemeToLTRSObj T).presheaf.obj (op ⊤)).α :=
    isPseudoDiscrete_pseudoDiscrete T.presheaf ⊤ isCompact_univ
  have hker : IsOpen ((RingHom.ker χ.1 : Ideal A) : Set A) := by
    have hset : ((RingHom.ker χ.1 : Ideal A) : Set A) = χ.1 ⁻¹' {0} := by
      ext x; exact RingHom.mem_ker
    rw [hset]
    exact (isOpen_discrete _).preimage χ.2
  exact ⟨spfIndexMeetOpen A (weaklyPreAdmissibleSpfIndex A hA) hker,
    fun _ hx => RingHom.mem_ker.1 hx.2⟩

end Spfw

/-- A restriction map of a presheaf of rings between two opens that are equal is injective. -/
theorem injective_presheaf_map_of_eq {Z : TopCat.{u}} (F : Z.Presheaf CommRingCat.{u})
    {V W : Opens Z} (h : V = W) (i : op W ⟶ op V) : Function.Injective (F.map i).hom := by
  subst h
  rw [Subsingleton.elim i (𝟙 _), F.map_id]
  exact fun _ _ h => h

section Chart

variable {X : LTRS.{u}} {U : Opens X} (A : Type u) [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [IsLinearTopology A A] (hA : IsWeaklyAdmissible A)
  (χ : X.restrict U ≅ spfwLTRS A hA.1)

/-- The open embedding `Spfw A → X` of a weak affine formal chart `X|_U ≅ Spfw A`. -/
noncomputable def weakChartEmbedding : spfwLTRS A hA.1 ⟶ X :=
  χ.inv ≫ X.ofRestrict U

/-- The embedding `Spfw A → X` of a weak affine formal chart is an open immersion of presheafed
spaces. -/
instance isOpenImmersion_weakChartEmbedding :
    PresheafedSpace.IsOpenImmersion (weakChartEmbedding A hA χ).toHom := by
  have : PresheafedSpace.IsOpenImmersion (X.ofRestrict U).toHom :=
    PresheafedSpace.IsOpenImmersion.ofRestrict _ _
  have : PresheafedSpace.IsOpenImmersion χ.inv.toHom :=
    PresheafedSpace.IsOpenImmersion.ofIso
      ((LocallyTopologicallyRingedSpace.forgetToSheafedSpace ⋙
        SheafedSpace.forgetToPresheafedSpace).mapIso χ.symm)
  exact PresheafedSpace.IsOpenImmersion.comp (f := χ.inv.toHom) (X.ofRestrict U).toHom

/-- The image of the open embedding of a weak affine formal chart is the open of the chart. -/
theorem range_weakChartEmbedding :
    Set.range (weakChartEmbedding A hA χ).toHom.base = (U : Set X) := by
  have hsurj : Function.Surjective χ.inv.toHom.base :=
    (TopCat.homeoOfIso (LocallyTopologicallyRingedSpace.forgetToTop.mapIso χ.symm)).surjective
  ext x
  refine ⟨?_, fun hx => ?_⟩
  · rintro ⟨y, rfl⟩
    exact (χ.inv.toHom.base y).2
  · obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩

/-- The open embedding of a weak affine formal chart is a monomorphism of `LTRS`. -/
theorem weakChartEmbedding_cancel {Z : LTRS.{u}} {g₁ g₂ : Z ⟶ spfwLTRS A hA.1}
    (h : g₁ ≫ weakChartEmbedding A hA χ = g₂ ≫ weakChartEmbedding A hA χ) : g₁ = g₂ :=
  LocallyTopologicallyRingedSpace.Hom.ext'
    ((PresheafedSpace.IsOpenImmersion.mono (weakChartEmbedding A hA χ).toHom).right_cancellation
      g₁.toHom g₂.toHom (congrArg (fun g => g.toHom) h))

/-- The preimage of the open of a weak affine formal chart under its open embedding is
everything. -/
theorem preimage_weakChartEmbedding :
    (Opens.map (weakChartEmbedding A hA χ).toHom.base).obj U = ⊤ :=
  eq_top_iff.mpr fun y _ => by
    change (weakChartEmbedding A hA χ).toHom.base y ∈ (U : Set X)
    rw [← range_weakChartEmbedding A hA χ]
    exact Set.mem_range_self y

/-- The map on sections over `U` induced by the open embedding of a weak affine formal chart is an
isomorphism. -/
instance isIso_weakChartEmbedding_c_app :
    IsIso ((weakChartEmbedding A hA χ).toHom.c.app (op U)) :=
  PresheafedSpace.IsOpenImmersion.c_iso' _ ⊤ (by
    ext1
    change (U : Set X) = (weakChartEmbedding A hA χ).toHom.base '' Set.univ
    rw [Set.image_univ, range_weakChartEmbedding])

/-- The identification of `A` with the sections of `𝒪_X` over the open of a weak affine formal
chart: `A = Γ(Spfw A, 𝒪)` (`AlgebraicGeometry.isIso_spfwGammaHom`) transported along the chart. -/
noncomputable def weakChartSections : TopCommRingCat.of A ⟶ X.presheaf.obj (op U) :=
  spfGammaHomOn A IsWeakIdealOfDefinition ≫
    (spfwLTRS A hA.1).presheaf.map (homOfLE le_top : (Opens.map
      (weakChartEmbedding A hA χ).toHom.base).obj U ⟶ ⊤).op ≫
    inv ((weakChartEmbedding A hA χ).toHom.c.app (op U))

/-- The identification of `A` with the sections of `𝒪_X` over the open of a weak affine formal
chart is an isomorphism of topological rings. -/
instance isIso_weakChartSections : IsIso (weakChartSections A hA χ) := by
  have h1 := isIso_spfwGammaHom A hA
  have h2 := isIso_presheaf_map_of_opens_eq (spfwLTRS A hA.1).presheaf
    (preimage_weakChartEmbedding A hA χ).symm
    (homOfLE le_top : (Opens.map (weakChartEmbedding A hA χ).toHom.base).obj U ⟶ ⊤).op
  exact IsIso.comp_isIso' h1 (IsIso.comp_isIso' h2 inferInstance)

/-- The effect on the sections over `U` of a point of `X` factoring through the chart is the map
it induces on global sections, up to the restriction along the equality of `⊤` with the preimage
of `U`. -/
theorem weakChartEmbedding_comp_c_app_weakChartSections {T : Scheme.{u}}
    (g : schemeToLTRSObj T ⟶ spfwLTRS A hA.1) (a : A) :
    ((g ≫ weakChartEmbedding A hA χ).toHom.c.app (op U)).1 ((weakChartSections A hA χ).1 a) =
      (T.presheaf.map (homOfLE le_top : (Opens.map g.toHom.base).obj
        ((Opens.map (weakChartEmbedding A hA χ).toHom.base).obj U) ⟶ ⊤).op).hom
        ((spfPointGammaHomOn A g).hom a) := by
  set ψ := weakChartEmbedding A hA χ
  have hinv : weakChartSections A hA χ ≫ ψ.toHom.c.app (op U) =
      spfGammaHomOn A IsWeakIdealOfDefinition ≫
        (spfwLTRS A hA.1).presheaf.map (homOfLE le_top : (Opens.map
          ψ.toHom.base).obj U ⟶ ⊤).op := by
    change _ ≫ (_ ≫ inv (ψ.toHom.c.app (op U))) ≫ ψ.toHom.c.app (op U) = _
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rfl
  have h1 := congrArg (fun φ : TopCommRingCat.of A ⟶ _ => φ.1 a) hinv
  have hnat := congrArg (fun φ => φ.1 ((spfGammaHomOn A IsWeakIdealOfDefinition).1 a))
    (g.toHom.c.naturality (homOfLE le_top : (Opens.map ψ.toHom.base).obj U ⟶ ⊤).op)
  have hcomp : (g ≫ ψ).toHom.c.app (op U) =
      ψ.toHom.c.app (op U) ≫ g.toHom.c.app (op ((Opens.map ψ.toHom.base).obj U)) :=
    PresheafedSpace.comp_c_app g.toHom ψ.toHom (op U)
  rw [hcomp]
  change (g.toHom.c.app _).1 ((weakChartSections A hA χ ≫ ψ.toHom.c.app (op U)).1 a) = _
  exact (congrArg (g.toHom.c.app _).1 h1).trans hnat

/-- A point of `X` landing in the open of a weak affine formal chart, lifted to `Spfw A`. -/
noncomputable def weakChartLift {T : Scheme.{u}} (f : schemeToLTRSObj T ⟶ X)
    (hf : Set.range f.toHom.base ⊆ (U : Set X)) : schemeToLTRSObj T ⟶ spfwLTRS A hA.1 :=
  liftToRestrict U f (fun _ hx => ⟨⟨_, hf hx⟩, rfl⟩) ≫ χ.hom

/-- The lift to `Spfw A` of a morphism `T → X` landing in the open of a chart, composed with the
open embedding of the chart, is the original morphism. -/
theorem weakChartLift_comp {T : Scheme.{u}} (f : schemeToLTRSObj T ⟶ X)
    (hf : Set.range f.toHom.base ⊆ (U : Set X)) :
    weakChartLift A hA χ f hf ≫ weakChartEmbedding A hA χ = f := by
  simp only [weakChartLift, weakChartEmbedding, Category.assoc, Iso.hom_inv_id_assoc]
  exact liftToRestrict_comp_ofRestrict U f _

/-- A point of `X` factoring through a weak affine formal chart kills the image of an element of
`A` in `𝒪_X(U)` exactly when the factoring point of `Spfw A` kills the element. -/
private theorem c_app_comp_weakChartEmbedding_eq_zero_iff {T : Scheme.{u}}
    (g : schemeToLTRSObj T ⟶ spfwLTRS A hA.1) (a : A) :
    ((g ≫ weakChartEmbedding A hA χ).toHom.c.app (op U)).1 ((weakChartSections A hA χ).1 a) = 0 ↔
      (spfPointGammaHomOn A g).hom a = 0 := by
  rw [weakChartEmbedding_comp_c_app_weakChartSections]
  have hinj := injective_presheaf_map_of_eq T.presheaf
    (show (Opens.map g.toHom.base).obj
      ((Opens.map (weakChartEmbedding A hA χ).toHom.base).obj U) = ⊤ by
        rw [preimage_weakChartEmbedding]; rfl)
    (homOfLE le_top : (Opens.map g.toHom.base).obj
        ((Opens.map (weakChartEmbedding A hA χ).toHom.base).obj U) ⟶ ⊤).op
  exact ⟨fun h => hinj (h.trans (map_zero _).symm), fun h => by rw [h]; exact map_zero _⟩

/-- A point landing in the open of a chart kills the image of an element of `A` in `𝒪_X(U)` exactly
when its lift to `Spfw A` kills the element. -/
theorem c_app_weakChartSections_eq_zero_iff {T : Scheme.{u}} (f : schemeToLTRSObj T ⟶ X)
    (hf : Set.range f.toHom.base ⊆ (U : Set X)) (a : A) :
    (f.toHom.c.app (op U)).1 ((weakChartSections A hA χ).1 a) = 0 ↔
      (spfPointGammaHomOn A (weakChartLift A hA χ f hf)).hom a = 0 := by
  have := c_app_comp_weakChartEmbedding_eq_zero_iff A hA χ (weakChartLift A hA χ f hf) a
  rwa [weakChartLift_comp] at this

/-- A point of `X` factoring through a weak affine formal chart kills the image of an element of
`A` in `𝒪_X(U)` exactly when the factoring point of `Spfw A` kills the element. -/
theorem c_app_weakChartSections_eq_zero_iff_of_comp {T : Scheme.{u}}
    (g : schemeToLTRSObj T ⟶ spfwLTRS A hA.1) (f : schemeToLTRSObj T ⟶ X)
    (h : g ≫ weakChartEmbedding A hA χ = f) (a : A) :
    (f.toHom.c.app (op U)).1 ((weakChartSections A hA χ).1 a) = 0 ↔
      (spfPointGammaHomOn A g).hom a = 0 := by
  subst h
  exact c_app_comp_weakChartEmbedding_eq_zero_iff A hA χ g a

/-- A point of `X` factoring through a weak affine formal chart lands in its open. -/
theorem range_subset_of_comp_weakChartEmbedding {Z : LTRS.{u}} (g : Z ⟶ spfwLTRS A hA.1)
    (f : Z ⟶ X) (h : g ≫ weakChartEmbedding A hA χ = f) :
    Set.range f.toHom.base ⊆ (U : Set X) := by
  subst h
  rintro _ ⟨y, rfl⟩
  rw [← range_weakChartEmbedding A hA χ]
  exact Set.mem_range_self _

/-- The quotient point `Spec (A/J) → X` of a weak affine formal chart `X|_U ≅ Spfw A` at a weak
ideal of definition `J` of `A`. -/
noncomputable def weakChartPoint (J : WeakIdealsOfDefinition A) :
    schemeToLTRSObj (Spec (spfQuotientOn A J)) ⟶ X :=
  spfwQuotientPoint A hA J ≫ weakChartEmbedding A hA χ

/-- The quotient points of a chart are compatible with the transition maps of the quotients. -/
theorem schemeToLTRS_map_comp_weakChartPoint {J K : WeakIdealsOfDefinition A} (h : J.1 ≤ K.1) :
    schemeToLTRS.map (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) ≫
      weakChartPoint A hA χ J = weakChartPoint A hA χ K :=
  (Category.assoc _ _ _).symm.trans (congrArg (· ≫ weakChartEmbedding A hA χ)
    (spfQuotientTransitionOn_comp_spfQuotientPointOn A _ h))

/-- A quotient point of a chart lands in its open. -/
theorem range_weakChartPoint_subset (J : WeakIdealsOfDefinition A) :
    Set.range (weakChartPoint A hA χ J).toHom.base ⊆ (U : Set X) :=
  range_subset_of_comp_weakChartEmbedding A hA χ _ _ rfl

/-- **A point of `X` landing in a weak affine formal chart and killing the image of a weak ideal of
definition `J` of `A` factors uniquely through the quotient point `Spec (A/J) → X`.** -/
theorem existsUnique_weakChartPoint_factor (J : WeakIdealsOfDefinition A) {T : Scheme.{u}}
    (f : schemeToLTRSObj T ⟶ X) (hf : Set.range f.toHom.base ⊆ (U : Set X))
    (hkill : ∀ a ∈ J.1, (f.toHom.c.app (op U)).1 ((weakChartSections A hA χ).1 a) = 0) :
    ∃! b : T ⟶ Spec (spfQuotientOn A J), schemeToLTRS.map b ≫ weakChartPoint A hA χ J = f := by
  obtain ⟨b, hb, -⟩ := existsUnique_spfwQuotientPoint_factor A hA J
    (weakChartLift A hA χ f hf) fun a ha =>
      (c_app_weakChartSections_eq_zero_iff_of_comp A hA χ _ f (weakChartLift_comp A hA χ f hf)
        a).mp (hkill a ha)
  have hfirst : schemeToLTRS.map b ≫ weakChartPoint A hA χ J = f :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ weakChartEmbedding A hA χ) hb).trans (weakChartLift_comp A hA χ f hf))
  exact ⟨b, hfirst, fun b' hb' => spfwQuotientPoint_cancel A hA J
    (weakChartEmbedding_cancel A hA χ ((Category.assoc _ _ _).trans
      (hb'.trans (hfirst.symm.trans (Category.assoc _ _ _).symm))))⟩

/-- A point of `X` factoring through the quotient point of `J` kills the image of `J`. -/
theorem c_app_weakChartSections_of_comp_weakChartPoint (J : WeakIdealsOfDefinition A)
    {T : Scheme.{u}} (b : T ⟶ Spec (spfQuotientOn A J)) (f : schemeToLTRSObj T ⟶ X)
    (hf : schemeToLTRS.map b ≫ weakChartPoint A hA χ J = f) {a : A} (ha : a ∈ J.1) :
    (f.toHom.c.app (op U)).1 ((weakChartSections A hA χ).1 a) = 0 :=
  (c_app_weakChartSections_eq_zero_iff_of_comp A hA χ
    (schemeToLTRS.map b ≫ spfwQuotientPoint A hA J) f ((Category.assoc _ _ _).trans hf) a).mpr
    (spfPointGammaHomOn_comp_spfwQuotientPoint_apply A hA J b ha)

/-- The quotient point of `J` kills the image of an element of `A` exactly when the element lies in
`J`: the map it induces on global sections is the quotient map `A → A/J`. -/
theorem weakChartPoint_c_app_weakChartSections_eq_zero_iff (J : WeakIdealsOfDefinition A)
    (a : A) :
    ((weakChartPoint A hA χ J).toHom.c.app (op U)).1 ((weakChartSections A hA χ).1 a) = 0 ↔
      a ∈ J.1 := by
  refine (c_app_weakChartSections_eq_zero_iff_of_comp A hA χ _ _ rfl a).trans ?_
  have hid : schemeToLTRS.map (𝟙 (Spec (spfQuotientOn A J))) ≫ spfwQuotientPoint A hA J =
      spfwQuotientPoint A hA J :=
    (congrArg (· ≫ spfwQuotientPoint A hA J) (schemeToLTRS.map_id _)).trans (Category.id_comp _)
  have hγ := congrArg (fun φ : CommRingCat.of A ⟶ _ => φ.hom a)
    ((congrArg (spfPointGammaHomOn A) hid).symm.trans
      (spfPointGammaHomOn_comp_spfwQuotientPoint A hA J (𝟙 _)))
  simp only [Scheme.Hom.id_appTop, Category.comp_id] at hγ
  rw [hγ]
  change (Scheme.ΓSpecIso (spfQuotientOn A J)).inv.hom (Ideal.Quotient.mk J.1 a) = 0 ↔ _
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  exact (Scheme.ΓSpecIso (spfQuotientOn A J)).commRingCatIsoToRingEquiv.symm.injective
    (h.trans (map_zero _).symm)

/-- **Over a quasi-compact scheme a point of `X` landing in a weak affine formal chart kills the
image of some weak ideal of definition of `A`.** -/
theorem exists_weakIdeal_kill_weakChartSections {T : Scheme.{u}} [CompactSpace T]
    (f : schemeToLTRSObj T ⟶ X) (hf : Set.range f.toHom.base ⊆ (U : Set X)) :
    ∃ J : WeakIdealsOfDefinition A,
      ∀ a ∈ J.1, (f.toHom.c.app (op U)).1 ((weakChartSections A hA χ).1 a) = 0 := by
  obtain ⟨J, hJ⟩ := exists_weakIdeal_kill_of_compactSpace A hA.1 (weakChartLift A hA χ f hf)
  exact ⟨J, fun a ha => (c_app_weakChartSections_eq_zero_iff_of_comp A hA χ _ f
    (weakChartLift_comp A hA χ f hf) a).mpr (hJ a ha)⟩

/-- The identification of `A` with the sections over the open of a weak affine formal chart, as a
homeomorphism. -/
noncomputable def weakChartSectionsHomeomorph : A ≃ₜ (X.presheaf.obj (op U)).α :=
  TopCat.homeoOfIso ((forget₂ TopCommRingCat TopCat).mapIso (asIso (weakChartSections A hA χ)))

/-- The homeomorphism `A ≃ₜ 𝒪_X(U)` of a weak affine formal chart is given by
`weakChartSections`. -/
theorem weakChartSectionsHomeomorph_apply (a : A) :
    weakChartSectionsHomeomorph A hA χ a = (weakChartSections A hA χ).1 a := rfl

/-- The identification of `A` with the sections over the open of a weak affine formal chart, as a
ring isomorphism. -/
noncomputable def weakChartSectionsRingEquiv : A ≃+* (X.presheaf.obj (op U)).α :=
  TopCommRingCat.ringEquivOfIso (asIso (weakChartSections A hA χ))

/-- The ring isomorphism `A ≃+* 𝒪_X(U)` of a weak affine formal chart is given by
`weakChartSections`. -/
theorem weakChartSectionsRingEquiv_apply (a : A) :
    weakChartSectionsRingEquiv A hA χ a = (weakChartSections A hA χ).1 a := rfl

/-- The weak ideal of definition of `A` corresponding, along a weak affine formal chart, to a weak
ideal of definition of the ring of sections over its open. -/
noncomputable def weakChartIdeal (K : Ideal (X.presheaf.obj (op U)).α)
    (hK : TopologicalRing.IsWeakIdealOfDefinition K) : WeakIdealsOfDefinition A :=
  ⟨K.comap (weakChartSections A hA χ).1, by
    refine ⟨hK.1.preimage (weakChartSections A hA χ).2, fun a ha => ?_⟩
    have h := IsTopologicallyNilpotent.map (φ := (weakChartSectionsRingEquiv A hA χ).symm)
      (weakChartSectionsHomeomorph A hA χ).symm.continuous (hK.2 _ ha)
    rwa [show (weakChartSectionsRingEquiv A hA χ).symm ((weakChartSections A hA χ).1 a) = a from
      (weakChartSectionsRingEquiv A hA χ).symm_apply_apply a] at h⟩

/-- An element of `A` lies in `weakChartIdeal A hA χ K hK` exactly when its image in `𝒪_X(U)` lies
in `K`. -/
theorem mem_weakChartIdeal {K : Ideal (X.presheaf.obj (op U)).α}
    (hK : TopologicalRing.IsWeakIdealOfDefinition K) (a : A) :
    a ∈ (weakChartIdeal A hA χ K hK).1 ↔ (weakChartSections A hA χ).1 a ∈ K :=
  Iff.rfl

end Chart

end AlgebraicGeometry

end
