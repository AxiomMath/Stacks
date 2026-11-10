module

public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.DescentFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Groupoids.EquivalenceRelation.InvolutionGraph
public import StacksFrontier.AlgebraicGeometry.Groupoids.EquivalenceRelation.Slice
public import StacksFrontier.AlgebraicGeometry.Limits.GluedRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAbsolute
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.FppfMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringOfOpenCover

/-!
# The quotient of a scheme by the diagonal glued to the kernel pair of an étale chart

Let `U` be an algebraic space over `Spec ℤ`, let `w : W ⟶ U` be an étale morphism from an object
of the big fppf site, and let `W ⊆ V` be an open subscheme of another object `V`. The kernel pair
`Q = W ×_U W` is represented by an object of the site, its diagonal `W ⟶ Q` is an open immersion,
and glueing `V` to `Q` along `W` produces an étale equivalence relation `R` on `V`
(`AlgebraicGeometry.GluedRelation`). Its quotient `V/R` is an algebraic space (Stacks 02WW).

## Main definitions

* `AlgebraicGeometry.Space.GluedEtaleQuotient.relationObj`: the object `R` of the site.
* `AlgebraicGeometry.Space.GluedEtaleQuotient.src` and
  `AlgebraicGeometry.Space.GluedEtaleQuotient.tgt`: its two maps to `V`.

## Main results

* `AlgebraicGeometry.Space.GluedEtaleQuotient.isEtaleEquivalenceRelation`: the relation is an
  étale equivalence relation, so that its quotient is an algebraic space.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Descending a morphism along a surjective étale chart -/

section Descend

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U : BigFppfOver B S hS}
  (f : yoneda.obj U ⟶ F) (s t : R ⟶ U)
  (hR : IsPullback (yoneda.map s) (yoneda.map t) f f) (hF : IsAlgebraicSpace B S hS F)
  (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f)
  (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f)
  (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)

include hR hF hsurj hetale hG in
/-- **A morphism out of a surjective étale chart which equalizes the kernel pair descends.** This
is the coequalizer property of Stacks 0262, part (3), read on morphisms into a sheaf. -/
theorem exists_desc_of_surjectiveEtale (ψ : yoneda.obj U ⟶ G)
    (hψ : yoneda.map s ≫ ψ = yoneda.map t ≫ ψ) : ∃ φ : F ⟶ G, f ≫ φ = ψ := by
  obtain ⟨hRsh, hUsh, hc⟩ := isCoequalizer_of_surjectiveEtale B S hS f s t hR hF hsurj hetale
  let J := BigFppfOver.topology B S hS
  let GF : Sheaf J (Type u) := ⟨G, hG⟩
  let RF : Sheaf J (Type u) := ⟨yoneda.obj R, hRsh⟩
  let UF : Sheaf J (Type u) := ⟨yoneda.obj U, hUsh⟩
  let sf : RF ⟶ UF := ⟨yoneda.map s⟩
  let tf : RF ⟶ UF := ⟨yoneda.map t⟩
  let ψf : UF ⟶ GF := ⟨ψ⟩
  have hw : sf ≫ ψf = tf ≫ ψf := Sheaf.hom_ext hψ
  exact ⟨((Classical.choice hc).desc (Cofork.ofπ ψf hw)).hom,
    congrArg (fun z => z.hom)
      ((Classical.choice hc).fac (Cofork.ofπ ψf hw) WalkingParallelPair.one)⟩

include hR hF hsurj hetale hG in
/-- **Morphisms out of an algebraic space into a sheaf are determined on a surjective étale
chart.** -/
theorem hom_ext_of_surjectiveEtale {φ₁ φ₂ : F ⟶ G} (h : f ≫ φ₁ = f ≫ φ₂) : φ₁ = φ₂ := by
  obtain ⟨hRsh, hUsh, hc⟩ := isCoequalizer_of_surjectiveEtale B S hS f s t hR hF hsurj hetale
  let J := BigFppfOver.topology B S hS
  let GF : Sheaf J (Type u) := ⟨G, hG⟩
  exact congrArg (fun z => z.hom) (Cofork.IsColimit.hom_ext (Classical.choice hc) (W := GF)
    (k := ⟨φ₁⟩) (l := ⟨φ₂⟩) (Sheaf.hom_ext h))

end Descend

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.GluedEtaleQuotient

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}
  {U : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} {W V : BigFppfOver B (⊤_ Scheme.{u}) hZ}
  (w : yoneda.obj W ⟶ U)
  (hw : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf w)

/-- A morphism of schemes between objects of the site over `Spec ℤ` is a morphism of the site. -/
abbrev homOfScheme {X Y : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    (f : (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj X ⟶
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Y) :
    X ⟶ Y :=
  BigFppfOver.homOfCompEq B (⊤_ Scheme.{u}) hZ f (terminal.hom_ext _ _)

/-- The underlying morphism of schemes of `homOfScheme f` is `f`. -/
@[simp]
theorem toScheme_map_homOfScheme {X Y : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    (f : (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj X ⟶
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Y) :
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (homOfScheme f) = f :=
  BigFppfOver.toScheme_map_homOfCompEq B (⊤_ Scheme.{u}) hZ _ _

include hw in
/-- The kernel pair object `Q = W ×_U W`. -/
abbrev kernelObj : BigFppfOver B (⊤_ Scheme.{u}) hZ := hw.rep.pullback w

/-- The first projection `Q ⟶ W`. -/
abbrev kp₁ : kernelObj w hw ⟶ W := hw.rep.fst' w

/-- The second projection `Q ⟶ W`. -/
abbrev kp₂ : kernelObj w hw ⟶ W := hw.rep.snd w

/-- The square formed by the projections `kp₁, kp₂ : Q ⟶ W` and `w : W ⟶ U` is a pullback. -/
theorem isPullback_kernel :
    IsPullback (yoneda.map (kp₁ w hw)) (yoneda.map (kp₂ w hw)) w w :=
  hw.rep.isPullback' w

/-- The diagonal `W ⟶ Q`. -/
abbrev diag : W ⟶ kernelObj w hw := hw.rep.lift' (𝟙 W) (𝟙 W) rfl

/-- The diagonal followed by the first projection is the identity of `W`. -/
@[reassoc (attr := simp)]
theorem diag_kp₁ : diag w hw ≫ kp₁ w hw = 𝟙 W := hw.rep.lift'_fst _ _ _

/-- The diagonal followed by the second projection is the identity of `W`. -/
@[reassoc (attr := simp)]
theorem diag_kp₂ : diag w hw ≫ kp₂ w hw = 𝟙 W := hw.rep.lift'_snd _ _ _

/-- The second projection `Q ⟶ W` is étale. -/
instance etale_kp₂ : Etale ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (kp₂ w hw)) :=
  hw.property_snd w

/-- The first projection `Q ⟶ W` is étale. -/
instance etale_kp₁ : Etale ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (kp₁ w hw)) := by
  change Etale ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (hw.rep.fst' w))
  rw [← hw.rep.symmetry_snd hw.rep, CategoryTheory.Functor.map_comp]
  have : IsIso (hw.rep.symmetry hw.rep) := (hw.rep.symmetryIso hw.rep).isIso_hom
  have h2 : Etale ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (hw.rep.snd w)) :=
    hw.property_snd w
  infer_instance

/-- The diagonal `W ⟶ Q` is an open immersion. -/
instance isOpenImmersion_diag :
    AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (diag w hw)) :=
  isOpenImmersion_of_section_of_etale ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (kp₁ w hw))
    _
    (by rw [← CategoryTheory.Functor.map_comp, diag_kp₁, CategoryTheory.Functor.map_id])

/-- A scheme, as an object over the terminal scheme. -/
abbrev overTop (T : Scheme.{u}) : Over (⊤_ Scheme.{u}) := Over.mk (terminal.from T)

/-- A morphism of schemes into an object of the site, as a morphism over the terminal scheme. -/
abbrev overHom {T : Scheme.{u}} {X : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    (f : T ⟶ (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj X) :
    overTop T ⟶ (Over.post B.inclusion).obj X :=
  Over.homMk f (terminal.hom_ext _ _)

/-- **The kernel pair is an equivalence relation on points of every scheme**, and the two
projections are jointly monic. -/
theorem kernel_hom_ext {T : Scheme.{u}}
    (σ τ : T ⟶ (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (kernelObj w hw))
    (h₁ : σ ≫ (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (kp₁ w hw) =
      τ ≫ (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (kp₁ w hw))
    (h₂ : σ ≫ (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (kp₂ w hw) =
      τ ≫ (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (kp₂ w hw)) :
    σ = τ := by
  obtain ⟨e⟩ := (isEquivalenceRelation_of_isPullback B (⊤_ Scheme.{u}) hZ w (kp₁ w hw) (kp₂ w hw)
    (isPullback_kernel w hw)).nonempty_equivalenceRelation
  exact congrArg CommaMorphism.left (e.right_cancellation (overHom σ) (overHom τ)
    (Over.OverMorphism.ext h₁) (Over.OverMorphism.ext h₂))

/-- For every scheme `T`, the relation on `T`-points of `W` given by `x ∼ y` if some `T`-point of
`Q` projects to `x` and `y` is an equivalence relation. -/
theorem kernel_equivalence (T : Scheme.{u}) :
    _root_.Equivalence (fun x y : T ⟶ (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj W =>
      ∃ q : T ⟶ (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (kernelObj w hw),
        q ≫ (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (kp₁ w hw) = x ∧
          q ≫ (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (kp₂ w hw) = y) := by
  obtain ⟨e⟩ := (isEquivalenceRelation_of_isPullback B (⊤_ Scheme.{u}) hZ w (kp₁ w hw) (kp₂ w hw)
    (isPullback_kernel w hw)).nonempty_equivalenceRelation
  have h := Stacks.Groupoids.equivalence_of_equivalenceRelation_hom e (overTop T)
  have hrel : ∀ x y : T ⟶ (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj W,
      (∃ q : T ⟶ (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (kernelObj w hw),
        q ≫ (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (kp₁ w hw) = x ∧
          q ≫ (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (kp₂ w hw) = y) ↔
      ∃ r : overTop T ⟶ (Over.post B.inclusion).obj (kernelObj w hw),
        r ≫ (Over.post B.inclusion).map (kp₁ w hw) = overHom x ∧
          r ≫ (Over.post B.inclusion).map (kp₂ w hw) = overHom y := by
    intro x y
    constructor
    · rintro ⟨q, h₁, h₂⟩
      exact ⟨overHom q, Over.OverMorphism.ext h₁, Over.OverMorphism.ext h₂⟩
    · rintro ⟨r, h₁, h₂⟩
      exact ⟨r.left, congrArg CommaMorphism.left h₁, congrArg CommaMorphism.left h₂⟩
  exact ⟨fun x => (hrel x x).mpr (h.refl (overHom x)),
    fun {x y} hxy => (hrel y x).mpr (h.symm ((hrel x y).mp hxy)),
    fun {x y z} hxy hyz => (hrel x z).mpr (h.trans ((hrel x y).mp hxy) ((hrel y z).mp hyz))⟩

variable (ι : W ⟶ V)
  [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ι)]

/-- The glued scheme `R = V ⊔_W Q`. -/
abbrev relationScheme : Scheme.{u} :=
  pushout ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ι)
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (diag w hw))

/-- The open subscheme cut out by the range of an open immersion has the size of its source. -/
theorem _root_.AlgebraicGeometry.Scheme.size_opensRange {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsOpenImmersion f] :
    Scheme.size (f.opensRange : Scheme.{u}) = Scheme.size X := by
  rw [← Scheme.size_congr (AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq f (Scheme.Opens.ι _)
    (congr_arg TopologicalSpace.Opens.carrier f.opensRange.opensRange_ι.symm))]

/-- The glued scheme `R` is an object of the site. -/
theorem contains_relationScheme : B.Contains (relationScheme w hw ι) := by
  have hcov := GluedRelation.iSup_opensRange ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ι)
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (diag w hw))
  let O : Bool → (relationScheme w hw ι).Opens := fun b =>
    if b then (pushout.inl ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ι)
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (diag w hw))).opensRange
    else (pushout.inr ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ι)
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (diag w hw))).opensRange
  have hO : ⨆ b, O b = ⊤ := by
    rw [iSup_bool_eq]
    exact hcov
  let O' : ULift.{u} Bool → (relationScheme w hw ι).Opens := fun c => O c.down
  have hO' : ⨆ c, O' c = ⊤ := by
    rw [← hO]
    exact le_antisymm (iSup_le fun c => le_iSup O c.down)
      (iSup_le fun b => le_iSup O' (ULift.up b))
  refine (Scheme.size_le_of_iSup_eq_top O' hO').trans_lt (max_lt ?_ ?_)
  · exact (Cardinal.lt_aleph0_of_finite _).trans B.aleph0_lt_cutoff
  · refine (ciSup_le' fun b => ?_).trans_lt
      (max_lt V.left.property (kernelObj w hw).left.property)
    rcases b with ⟨_ | _⟩
    · change Scheme.size ((pushout.inr ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ι)
          ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (diag w hw))).opensRange :
        Scheme.{u}) ≤ _
      rw [Scheme.size_opensRange]
      exact le_max_right _ _
    · change Scheme.size ((pushout.inl ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ι)
          ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (diag w hw))).opensRange :
        Scheme.{u}) ≤ _
      rw [Scheme.size_opensRange]
      exact le_max_left _ _

/-- **The relation object `R`** of the site. -/
abbrev relationObj : BigFppfOver B (⊤_ Scheme.{u}) hZ :=
  Over.mk (⟨terminal.from _⟩ : B.obj (contains_relationScheme w hw ι) ⟶ B.obj hZ)

/-- The source map `R ⟶ V`: the identity on `V` and the first projection on `Q`. -/
abbrev src : relationObj w hw ι ⟶ V :=
  homOfScheme (GluedRelation.fst ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ι)
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (diag w hw))
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (kp₁ w hw))
    (by rw [← CategoryTheory.Functor.map_comp, diag_kp₁, CategoryTheory.Functor.map_id]))

/-- The target map `R ⟶ V`: the identity on `V` and the second projection on `Q`. -/
abbrev tgt : relationObj w hw ι ⟶ V :=
  homOfScheme (GluedRelation.snd ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ι)
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (diag w hw))
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (kp₂ w hw))
    (by rw [← CategoryTheory.Functor.map_comp, diag_kp₂, CategoryTheory.Functor.map_id]))

/-- **The glued relation is an étale equivalence relation on `V`.** -/
instance isEtaleEquivalenceRelation :
    Stacks.Groupoids.IsEtaleEquivalenceRelation
      (relation B (⊤_ Scheme.{u}) hZ (src w hw ι) (tgt w hw ι)) where
  isEquivalenceRelation := by
    apply Stacks.Groupoids.isEquivalenceRelation_of_left
    simp only [Stacks.Groupoids.PreRelation.target, Stacks.Groupoids.PreRelation.source,
      prod.lift_fst, prod.lift_snd]
    change IsEquivalenceRelation ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (tgt w hw ι))
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (src w hw ι))
    rw [toScheme_map_homOfScheme, toScheme_map_homOfScheme]
    exact GluedRelation.isEquivalenceRelation _ _
      (kernel_hom_ext w hw) (kernel_equivalence w hw)
  etale_source := by
    simp only [Stacks.Groupoids.PreRelation.source, prod.lift_snd]
    change Etale ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (src w hw ι))
    rw [toScheme_map_homOfScheme]
    exact GluedRelation.etale_fst _ _
  etale_target := by
    simp only [Stacks.Groupoids.PreRelation.target, prod.lift_fst]
    change Etale ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (tgt w hw ι))
    rw [toScheme_map_homOfScheme]
    exact GluedRelation.etale_snd _ _

/-! ### The two charts of the relation, and the quotient -/

/-- The chart `V ⟶ R` of the relation: the diagonal copy of `V`. -/
abbrev inlV : V ⟶ relationObj w hw ι :=
  homOfScheme (pushout.inl ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ι)
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (diag w hw)))

/-- The chart `Q ⟶ R` of the relation. -/
abbrev inrQ : kernelObj w hw ⟶ relationObj w hw ι :=
  homOfScheme (pushout.inr ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ι)
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (diag w hw)))

/-- The chart `V ⟶ R` followed by the source map is the identity of `V`. -/
@[reassoc (attr := simp)]
theorem inlV_src : inlV w hw ι ≫ src w hw ι = 𝟙 V := by
  apply (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map_injective
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, toScheme_map_homOfScheme,
    toScheme_map_homOfScheme, GluedRelation.inl_fst]

/-- The chart `V ⟶ R` followed by the target map is the identity of `V`. -/
@[reassoc (attr := simp)]
theorem inlV_tgt : inlV w hw ι ≫ tgt w hw ι = 𝟙 V := by
  apply (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map_injective
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, toScheme_map_homOfScheme,
    toScheme_map_homOfScheme, GluedRelation.inl_snd]

/-- The chart `Q ⟶ R` followed by the source map is the first projection followed by `W ⟶ V`. -/
@[reassoc (attr := simp)]
theorem inrQ_src : inrQ w hw ι ≫ src w hw ι = kp₁ w hw ≫ ι := by
  apply (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map_injective
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, toScheme_map_homOfScheme,
    toScheme_map_homOfScheme, GluedRelation.inr_fst]

/-- The chart `Q ⟶ R` followed by the target map is the second projection followed by
`W ⟶ V`. -/
@[reassoc (attr := simp)]
theorem inrQ_tgt : inrQ w hw ι ≫ tgt w hw ι = kp₂ w hw ≫ ι := by
  apply (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map_injective
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, toScheme_map_homOfScheme,
    toScheme_map_homOfScheme, GluedRelation.inr_snd]

/-- **The quotient `V/R`**, an algebraic space over `Spec ℤ` by Stacks 02WW. -/
abbrev quotient : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u :=
  (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ)
    (Over.post B.inclusion)
    (relation B (⊤_ Scheme.{u}) hZ (src w hw ι) (tgt w hw ι))).obj

/-- The quotient `V/R` is an algebraic space. -/
theorem isAlgebraicSpace_quotient :
    IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (quotient w hw ι) :=
  isAlgebraicSpace_quotient_unconditional B (⊤_ Scheme.{u}) hZ _ _

/-- The quotient map `V ⟶ V/R`. -/
abbrev qmap : yoneda.obj V ⟶ quotient w hw ι :=
  quotientMap B (⊤_ Scheme.{u}) hZ (src w hw ι) (tgt w hw ι)

/-- The quotient map `V ⟶ V/R` is surjective. -/
theorem qmap_surjective : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)))
    (qmap w hw ι) :=
  quotientMap_surjective_unconditional B (⊤_ Scheme.{u}) hZ _ _

/-- The quotient map `V ⟶ V/R` is étale. -/
theorem qmap_etale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)))
    (qmap w hw ι) :=
  quotientMap_etale_unconditional B (⊤_ Scheme.{u}) hZ _ _

/-- The relation `R` is the fibre product `V ×_{V/R} V`, with the target and source maps as its
projections. -/
theorem isPullback_qmap : IsPullback (yoneda.map (tgt w hw ι)) (yoneda.map (src w hw ι))
    (qmap w hw ι) (qmap w hw ι) :=
  quotientMap_isPullback B (⊤_ Scheme.{u}) hZ _ _

/-- The source and target maps `R ⟶ V` agree after composing with the quotient map. -/
theorem src_qmap :
    yoneda.map (src w hw ι) ≫ qmap w hw ι = yoneda.map (tgt w hw ι) ≫ qmap w hw ι :=
  (isPullback_qmap w hw ι).w.symm

/-- The kernel pair `Q` of the chart is identified in the quotient. -/
theorem kp_qmap : yoneda.map (kp₁ w hw) ≫ yoneda.map ι ≫ qmap w hw ι =
    yoneda.map (kp₂ w hw) ≫ yoneda.map ι ≫ qmap w hw ι := by
  rw [← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp_assoc,
    ← inrQ_src, ← inrQ_tgt, CategoryTheory.Functor.map_comp_assoc,
    CategoryTheory.Functor.map_comp_assoc, src_qmap]

/-- The two charts of the glued relation form an fppf covering of it. -/
theorem relation_isFppfCovering :
    IsFppfCovering B (⊤_ Scheme.{u}) hZ
      (fun b : Bool => yoneda.obj (if b then V else kernelObj w hw))
      (fun b => yoneda.map (match b with
        | true => inlV w hw ι
        | false => inrQ w hw ι)) := by
  refine isFppfCovering_yoneda_of_openCover B (⊤_ Scheme.{u}) hZ
    (fun b : Bool => if b then V else kernelObj w hw)
    (fun b => match b with | true => inlV w hw ι | false => inrQ w hw ι) ?_ ?_
  · intro b
    cases b <;> simp only [toScheme_map_homOfScheme] <;> infer_instance
  · intro z
    rcases GluedRelation.mem_range_inl_or_inr ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ι)
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (diag w hw)) z with h | h
    · exact ⟨true, by simpa only [toScheme_map_homOfScheme] using h⟩
    · exact ⟨false, by simpa only [toScheme_map_homOfScheme] using h⟩

/-- Two morphisms out of the glued relation into a sheaf agree once they agree on the charts. -/
theorem relation_yoneda_hom_ext {Z : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hZs : Presheaf.IsSheaf (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ) Z)
    {a b : yoneda.obj (relationObj w hw ι) ⟶ Z}
    (hl : yoneda.map (inlV w hw ι) ≫ a = yoneda.map (inlV w hw ι) ≫ b)
    (hr : yoneda.map (inrQ w hw ι) ≫ a = yoneda.map (inrQ w hw ι) ≫ b) : a = b :=
  hom_ext_of_isFppfCovering B (⊤_ Scheme.{u}) hZ _ _ (relation_isFppfCovering w hw ι) hZs
    fun c => by
      cases c
      · exact hr
      · exact hl

/-- **The two maps of the glued relation are jointly monic in presheaves.** -/
theorem relation_yoneda_jointlyMono {T : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (α β : T ⟶ yoneda.obj (relationObj w hw ι))
    (h₁ : α ≫ yoneda.map (src w hw ι) = β ≫ yoneda.map (src w hw ι))
    (h₂ : α ≫ yoneda.map (tgt w hw ι) = β ≫ yoneda.map (tgt w hw ι)) : α = β := by
  ext T' x
  have key (g : relationObj w hw ι ⟶ V) (h : α.app T' x ≫ g = β.app T' x ≫ g) :
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (α.app T' x) ≫
          (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map g =
        (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (β.app T' x) ≫
          (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map g := by
    rw [← Functor.map_comp, ← Functor.map_comp, h]
  apply (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map_injective
  refine GluedRelation.hom_ext ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ι)
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (diag w hw))
    (p₁ := (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (kp₁ w hw))
    (p₂ := (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (kp₂ w hw))
    (h₁ := by rw [← CategoryTheory.Functor.map_comp, diag_kp₁, CategoryTheory.Functor.map_id])
    (h₂ := by rw [← CategoryTheory.Functor.map_comp, diag_kp₂, CategoryTheory.Functor.map_id])
    (kernel_hom_ext w hw) _ _ ?_ ?_
  · have := key _ (congrArg (fun m => m.app T' x) h₁)
    rw [toScheme_map_homOfScheme] at this
    exact this
  · have := key _ (congrArg (fun m => m.app T' x) h₂)
    rw [toScheme_map_homOfScheme] at this
    exact this


variable (hU : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ U)
  (hws : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf w)

include hU hws in
/-- **The base `U` of the chart maps to the quotient**: the composite `W ⟶ V ⟶ V/R` identifies
the kernel pair `Q` of `W ⟶ U`, so it descends along the surjective étale chart `W ⟶ U`. -/
theorem exists_baseMap : ∃ φ : U ⟶ quotient w hw ι, w ≫ φ = yoneda.map ι ≫ qmap w hw ι :=
  exists_desc_of_surjectiveEtale w (kp₁ w hw) (kp₂ w hw) (isPullback_kernel w hw) hU hws hw
    (isAlgebraicSpace_quotient w hw ι).isSheaf _ (kp_qmap w hw ι)

/-- The map from the base `U` of the chart to the quotient. -/
noncomputable def baseMap : U ⟶ quotient w hw ι := (exists_baseMap w hw ι hU hws).choose

/-- The map `baseMap : U ⟶ V/R` precomposed with `w : W ⟶ U` is the composite `W ⟶ V ⟶ V/R`. -/
@[reassoc (attr := simp)]
theorem w_baseMap : w ≫ baseMap w hw ι hU hws = yoneda.map ι ≫ qmap w hw ι :=
  (exists_baseMap w hw ι hU hws).choose_spec

/-! ### Quasi-separatedness of the quotient -/

set_option synthInstance.maxHeartbeats 400000 in
-- the `inferInstance` search for pullbacks of presheaves on the big fppf site times out
/-- Pullbacks of presheaves on the big fppf site over `Spec ℤ` (instance search times out
without this shortcut). -/
instance hasPullbacks_presheaf_GluedEtaleQuotient :
    HasPullbacks ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) := inferInstance

instance (priority := high) hasPullback_presheaf_GluedEtaleQuotient
    {X Y Z : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **The quotient is quasi-separated** (Stacks 07S4) as soon as `V` is quasi-separated and the
target map `R ⟶ V` of the relation is quasi-compact. -/
theorem isAbsolutelyQuasiSeparated_quotient
    (hVqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V))
    (hqc : QuasiCompact ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (tgt w hw ι))) :
    IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (quotient w hw ι) := by
  have hbc := inverseImage_isStableUnderBaseChange B (⊤_ Scheme.{u}) hZ
    (P := @QuasiCompact.{u}) inferInstance
  have hfst : pullback.fst (qmap w hw ι) (qmap w hw ι) =
      (isPullback_qmap w hw ι).isoPullback.inv ≫ yoneda.map (tgt w hw ι) := by
    rw [IsPullback.isoPullback_inv_fst]
  have hrel : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@QuasiCompact.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ))) (yoneda.map (tgt w hw ι)) :=
    (MorphismProperty.relative_map_iff (F := yoneda)
      (P := MorphismProperty.inverseImage (@QuasiCompact.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ))).mpr hqc
  refine isQuasiSeparated_of_etaleAtlas_quasiCompact_projection B (⊤_ Scheme.{u}) hZ hZ _
    (isAlgebraicSpace_quotient w hw ι) ⟨V, qmap w hw ι, hVqs, qmap_surjective w hw ι,
      qmap_etale w hw ι, Or.inl ?_⟩
  rw [hfst]
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@QuasiCompact.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ))).RespectsIso :=
    MorphismProperty.relative_respectsIso _
  exact MorphismProperty.RespectsIso.precomp _ _ _ hrel

/-- **The glued scheme is quasi-compact** when `V` and `Q` are. -/
theorem compactSpace_relationScheme
    [CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V)]
    [CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (kernelObj w hw))] :
    CompactSpace (relationScheme w hw ι) := by
  rw [← isCompact_univ_iff]
  convert (isCompact_range (pushout.inl ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ι)
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (diag w hw))).continuous).union
    (isCompact_range (pushout.inr ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ι)
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (diag w hw))).continuous) using 1
  ext z
  simp only [Set.mem_univ, Set.mem_union, true_iff]
  exact GluedRelation.mem_range_inl_or_inr _ _ z

/-- **The target map of the relation is quasi-compact** when `V` and `Q` are quasi-compact and
`V` is quasi-separated. -/
theorem quasiCompact_tgt [CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V)]
    [QuasiSeparatedSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V)]
    [CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (kernelObj w hw))] :
    QuasiCompact ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (tgt w hw ι)) := by
  have := compactSpace_relationScheme w hw ι
  have : CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (relationObj w hw ι)) := this
  infer_instance

include hw in
/-- **The kernel pair `Q = W ×_U W` is quasi-compact** when `W` is and `U` is quasi-separated. -/
theorem compactSpace_kernelObj (hU : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ U)
    (hUqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ U)
    [hW : CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj W)] :
    CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (kernelObj w hw)) := by
  apply compactSpace_of_isQuasiCompactSpace_yoneda_obj
  have hWqc := isQuasiCompactSpace_yoneda_obj B (⊤_ Scheme.{u}) hZ hW
  exact isQuasiCompactSpace_of_iso B (⊤_ Scheme.{u}) hZ (isPullback_kernel w hw).isoPullback.symm
    (isQuasiCompactSpace_pullback B (⊤_ Scheme.{u}) hZ hZ w w
      (isAlgebraicSpace_yoneda B (⊤_ Scheme.{u}) hZ W) hU hWqc hWqc hUqs)

end AlgebraicGeometry.Space.GluedEtaleQuotient

end
