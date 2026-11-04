module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Limits.ChowLemma
public import StacksFrontier.AlgebraicGeometry.Limits.ClosedImmersionModel
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.Absolute
public import StacksFrontier.AlgebraicGeometry.Morphisms.DimensionFormula.FunctionField
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Examples
public import StacksFrontier.AlgebraicGeometry.NormalizationMono.Basic
public import StacksFrontier.AlgebraicGeometry.NormalProperModel.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.UniversalProperty

/-!
# Normal integral Noetherian approximation

A quasi-compact and quasi-separated integral normal scheme `S` is the limit of a cofiltered
system of integral normal Noetherian schemes with affine transition morphisms, whose projections
from `S` are dominant. This is the first paragraph of the proof of [Stacks, Tag 0EZJ].

## Main results

* `AlgebraicGeometry.exists_isLimit_isNoetherian_isIntegral_isNormal`: the approximation.
* `AlgebraicGeometry.NormalApproximation.isLimit_of_finitePresentation_refinement`: a cone over a
  system mapping to a limit system by finitely presented separated morphisms, with reduced stages
  and dominant projections, is a limit cone.

## Implementation notes

Write `S = lim Sᵢ` with `Sᵢ` of finite type over `ℤ` (Tag 01ZA,
`AlgebraicGeometry.Scheme.exists_isLimit_affine_locallyOfFiniteType`). Replacing each `Sᵢ` by the
scheme-theoretic image of `S ⟶ Sᵢ` keeps the limit and makes the stages integral and the
projections dominant. The normalization `Sᵢ'` of the integral scheme `Sᵢ` is finite over `Sᵢ`,
because a scheme of finite type over `ℤ` is Nagata; it is integral, normal and Noetherian, and
`S ⟶ Sᵢ` lifts through it uniquely because `S` is normal (Tag 035Q). The uniqueness of the lifts
makes `i ↦ Sᵢ'` a functor.

The source proof normalizes `Sᵢ` *in `S`*, that is, takes the integral closure of `𝒪_{Sᵢ}` in
the pushforward of `𝒪_S`. That scheme is in general neither of finite type over `ℤ` nor
Noetherian: for `S = Spec(Q̄)` and `Sᵢ = Spec(ℤ)` it is the spectrum of the ring of algebraic
integers. The normalization of `Sᵢ` in its own function field is used instead; it sits between
`Sᵢ` and the normalization in `S`, and the limit of these is still `S`.

That `S` is the limit of the normalized stages is a rigidity statement about any refinement
`E ⟶ D` of a limit system by finitely presented separated morphisms with reduced stages and
dominant projections: each projection `S ⟶ Eᵢ` factors through a stage `D j ⟶ Eᵢ` (Mathlib's
`AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`), and two
morphisms out of a reduced scheme into a separated one agree once they agree on a dense subset.

## References

* [Stacks Project, Tag 0EZJ](https://stacks.math.columbia.edu/tag/0EZJ)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 035Q](https://stacks.math.columbia.edu/tag/035Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace NormalApproximation

variable {I : Type u} [Category.{u} I]

/-! ### Factoring a projection through a stage -/

/-- A morphism from the limit of a cofiltered system of quasi-compact and quasi-separated
schemes with affine transition morphisms to a scheme locally of finite presentation over a
stage factors through a later stage. -/
theorem exists_factor_from_stage [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (i : I) {T : Scheme.{u}} (ν : T ⟶ D.obj i) [LocallyOfFinitePresentation ν]
    (a : c.pt ⟶ T) (ha : a ≫ ν = c.π.app i) :
    ∃ (j : I) (e : j ⟶ i) (b : D.obj j ⟶ T), c.π.app j ≫ b = a ∧ b ≫ ν = D.map e := by
  let D' := Over.forget i ⋙ D
  let c' := c.whisker (Over.forget i)
  let t : D' ⟶ (Functor.const (Over i)).obj (D.obj i) :=
    { app := fun j ↦ D.map j.hom
      naturality := fun j k f ↦ by simp [D', ← D.map_comp] }
  have haff {j k : Over i} (g : j ⟶ k) : IsAffineHom (D'.map g) :=
    inferInstanceAs (IsAffineHom (D.map g.left))
  have hqc (j : Over i) : CompactSpace (D'.obj j) := inferInstanceAs (CompactSpace (D.obj j.left))
  have hqs (j : Over i) : QuasiSeparatedSpace (D'.obj j) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj j.left))
  obtain ⟨j, b, hb, hbν⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    D' t ν c' ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc)
    a (by ext j; simpa [t, c'] using (c.w j.hom).trans ha.symm)
  exact ⟨j.left, j.hom, b, hb, hbν⟩

/-- **A refinement of a limit system is a limit system.** Let `c` be a limit cone over a
cofiltered system `D` of quasi-compact and quasi-separated schemes with affine transition
morphisms, and let `ν : E ⟶ D` be a natural transformation whose components are locally of
finite presentation and separated. A cone `e` over `E` with the same vertex as `c`, lying over
`c`, whose stages are reduced and whose projections are dominant, is a limit cone. -/
def isLimit_of_finitePresentation_refinement [IsCofiltered I]
    (D E : I ⥤ Scheme.{u}) (ν : E ⟶ D) (c : Cone D) (e : Cone E)
    (hc : IsLimit c) (hpt : e.pt = c.pt)
    (hπ : ∀ i, e.π.app i ≫ ν.app i = eqToHom hpt ≫ c.π.app i)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ i, LocallyOfFinitePresentation (ν.app i)] [∀ i, IsSeparated (ν.app i)]
    [∀ i, IsReduced (E.obj i)] [∀ i, IsDominant (e.π.app i)] : IsLimit e := by
  have hf (i) : ∃ (j : I) (g : j ⟶ i) (b : D.obj j ⟶ E.obj i),
      (eqToHom hpt ≫ c.π.app j) ≫ b = e.π.app i ∧ b ≫ ν.app i = D.map g := by
    obtain ⟨j, g, b, hb, hbν⟩ := exists_factor_from_stage D c hc i (ν.app i)
      (eqToHom hpt.symm ≫ e.π.app i) (by simp [Category.assoc, hπ])
    exact ⟨j, g, b, by simp [Category.assoc, hb], hbν⟩
  have hmap (i j) (g : j ⟶ i) (b : D.obj j ⟶ E.obj i)
      (hb : (eqToHom hpt ≫ c.π.app j) ≫ b = e.π.app i)
      (hbν : b ≫ ν.app i = D.map g) : E.map g = ν.app j ≫ b := by
    apply ext_of_isDominant_of_isSeparated (ν.app i)
      (by rw [Category.assoc, hbν, ν.naturality]) (e.π.app j)
    rw [← Category.assoc, hπ, hb, e.w]
  refine
    { lift := fun s ↦ hc.lift ((Cone.postcompose ν).obj s) ≫ eqToHom hpt.symm
      fac := ?_
      uniq := ?_ }
  · intro s i
    obtain ⟨j, g, b, hb, hbν⟩ := hf i
    rw [← hb]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc, hc.fac]
    change (s.π.app j ≫ ν.app j) ≫ b = s.π.app i
    rw [Category.assoc, ← hmap i j g b hb hbν, s.w]
  · intro s m hm
    apply (cancel_mono (eqToHom hpt)).1
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    apply hc.uniq ((Cone.postcompose ν).obj s) (m ≫ eqToHom hpt)
    intro i
    rw [Category.assoc, ← hπ, ← Category.assoc, hm]
    rfl

/-! ### The scheme-theoretic images of the vertex in the stages -/

/-- The scheme-theoretic images of the vertex of a cone in the stages, as a system. -/
def imageDiagram (D : I ⥤ Scheme.{u}) (c : Cone D) : I ⥤ Scheme.{u} where
  obj i := (c.π.app i).image
  map {i j} f := (c.π.app i).ker.subschemeMap (c.π.app j).ker (D.map f)
    (by rw [← Scheme.Hom.ker_comp, c.w f])
  map_id i := by
    apply (cancel_mono (c.π.app i).imageι).1
    simp
  map_comp f g := by
    apply (cancel_mono (c.π.app _).imageι).1
    simp

/-- The inclusions of the scheme-theoretic images into the stages. -/
def imageDiagramι (D : I ⥤ Scheme.{u}) (c : Cone D) : imageDiagram D c ⟶ D where
  app i := (c.π.app i).imageι
  naturality i j f := by simp [imageDiagram]

/-- The cone from the vertex to its scheme-theoretic images in the stages. -/
def imageCone (D : I ⥤ Scheme.{u}) (c : Cone D) : Cone (imageDiagram D c) where
  pt := c.pt
  π :=
    { app := fun i ↦ (c.π.app i).toImage
      naturality := fun i j f ↦ by
        apply (cancel_mono (c.π.app j).imageι).1
        simp [imageDiagram] }

/-- The vertex of a limit cone is the limit of its scheme-theoretic images in the stages. -/
def imageConeIsLimit (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) :
    IsLimit (imageCone D c) where
  lift s := hc.lift ((Cone.postcompose (imageDiagramι D c)).obj s)
  fac s i := by
    apply (cancel_mono (c.π.app i).imageι).1
    change (hc.lift _ ≫ (c.π.app i).toImage) ≫ (c.π.app i).imageι = _
    rw [Category.assoc, Scheme.Hom.toImage_imageι]
    exact hc.fac ((Cone.postcompose (imageDiagramι D c)).obj s) i
  uniq s m hm := by
    apply hc.uniq ((Cone.postcompose (imageDiagramι D c)).obj s) m
    intro i
    refine (congrArg (m ≫ ·) (Scheme.Hom.toImage_imageι (c.π.app i))).symm.trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (c.π.app i).imageι) (hm i))

/-- The transition morphisms of the system of scheme-theoretic images are affine when those of
the original system are. -/
instance imageDiagram_map_isAffineHom (D : I ⥤ Scheme.{u}) (c : Cone D)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] {i j : I} (f : i ⟶ j) :
    IsAffineHom ((imageDiagram D c).map f) := by
  have hi : IsClosedImmersion (c.π.app i).imageι :=
    inferInstanceAs (IsClosedImmersion (c.π.app i).ker.subschemeι)
  have hj : IsSeparated (c.π.app j).imageι :=
    inferInstanceAs (IsSeparated (c.π.app j).ker.subschemeι)
  have hc : IsAffineHom ((imageDiagram D c).map f ≫ (c.π.app j).imageι) := by
    simpa [imageDiagram] using
      (inferInstance : IsAffineHom ((c.π.app i).imageι ≫ D.map f))
  exact MorphismProperty.of_postcomp (W := @IsAffineHom) (W' := @IsSeparated) _
    (c.π.app j).imageι hj hc

/-- The scheme-theoretic images of an integral vertex are integral. -/
private instance imageDiagram_obj_isIntegral (D : I ⥤ Scheme.{u}) (c : Cone D) [IsIntegral c.pt]
    [∀ i, QuasiCompact (c.π.app i)] (i : I) : IsIntegral ((imageDiagram D c).obj i) :=
  isIntegral_image_of_isIntegral (X := c.pt) (c.π.app i)

/-- The quasi-compact projections of the vertex to its scheme-theoretic images are dominant. -/
private instance imageCone_π_app_isDominant (D : I ⥤ Scheme.{u}) (c : Cone D)
    [∀ i, QuasiCompact (c.π.app i)] (i : I) :
    IsDominant ((imageCone D c).π.app i) :=
  inferInstanceAs (IsDominant (c.π.app i).toImage)

/-- The transition morphisms of the system of scheme-theoretic images of quasi-compact
projections are dominant. -/
private instance imageDiagram_map_isDominant (D : I ⥤ Scheme.{u}) (c : Cone D)
    [∀ i, QuasiCompact (c.π.app i)] {i j : I} (g : i ⟶ j) :
    IsDominant ((imageDiagram D c).map g) := by
  have : IsDominant ((imageCone D c).π.app i ≫ (imageDiagram D c).map g) := by
    rw [(imageCone D c).w g]
    exact imageCone_π_app_isDominant D c j
  exact IsDominant.of_comp ((imageCone D c).π.app i) ((imageDiagram D c).map g)

/-- A property stable under composition holds for the structure morphism of a scheme-theoretic
image in a stage if it holds for the inclusion and for the structure morphism of the stage. -/
private theorem terminal_from_imageDiagram_obj_mem (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderComposition] (D : I ⥤ Scheme.{u}) (c : Cone D) (i : I)
    (hι : P (c.π.app i).imageι) (h : P (terminal.from (D.obj i))) :
    P (terminal.from ((imageDiagram D c).obj i)) := by
  rw [show terminal.from ((imageDiagram D c).obj i) =
    (c.π.app i).imageι ≫ terminal.from (D.obj i) from terminal.hom_ext _ _]
  exact P.comp_mem _ _ hι h

/-! ### Normalizing integral stages -/

/-- The normalization of an integral scheme. -/
def integralNormalization (T : Scheme.{u}) [IsIntegral T] : Scheme.{u} :=
  T.normalizationScheme (finite_irreducibleComponents_of_isIntegral T)

/-- The normalization morphism of an integral scheme. -/
def integralNormalizationMap (T : Scheme.{u}) [IsIntegral T] :
    integralNormalization T ⟶ T :=
  T.normalization (finite_irreducibleComponents_of_isIntegral T)

/-- The normalization of an integral scheme is integral. -/
instance (T : Scheme.{u}) [IsIntegral T] : IsIntegral (integralNormalization T) :=
  Scheme.isIntegral_normalizationScheme T (finite_irreducibleComponents_of_isIntegral T)

/-- The normalization of an integral scheme is normal. -/
instance (T : Scheme.{u}) [IsIntegral T] : IsNormal (integralNormalization T) :=
  Scheme.isNormal_normalizationScheme T (finite_irreducibleComponents_of_isIntegral T)

/-- The normalization morphism of an integral scheme is dominant. -/
instance (T : Scheme.{u}) [IsIntegral T] : IsDominant (integralNormalizationMap T) := by
  have h₁ := Scheme.quasiCompactFromGenericPointResidueFields T
    (finite_irreducibleComponents_of_isIntegral T)
  have h₂ := Scheme.quasiSeparatedFromGenericPointResidueFields T
  exact Stacks.AlgebraicGeometry.Normalization.isDominant_fromNormalization _

/-- The normalization of an integral Nagata scheme is finite over it. -/
theorem isFinite_integralNormalizationMap (T : Scheme.{u}) [IsIntegral T]
    (hT : IsNagataScheme T) : IsFinite (integralNormalizationMap T) :=
  Scheme.isFinite_normalization hT (finite_irreducibleComponents_of_isIntegral T)

/-- A scheme locally of finite type over `ℤ` is a Nagata scheme. -/
private theorem isNagataScheme_of_locallyOfFiniteType_terminal_from (T : Scheme.{u})
    [LocallyOfFiniteType (terminal.from T)] : IsNagataScheme T :=
  isNagataScheme_of_locallyOfFiniteType_over_uliftInt
    (terminal.from T ≫ (terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal).hom)

/-- The normalization of an integral Noetherian scheme is Noetherian when it is finite. -/
private theorem isNoetherian_integralNormalization (T : Scheme.{u}) [IsIntegral T] [IsNoetherian T]
    [hfin : IsFinite (integralNormalizationMap T)] : IsNoetherian (integralNormalization T) := by
  have : IsLocallyNoetherian (integralNormalization T) :=
    LocallyOfFiniteType.isLocallyNoetherian (integralNormalizationMap T)
  have : CompactSpace (integralNormalization T) :=
    QuasiCompact.compactSpace_of_compactSpace (integralNormalizationMap T)
  exact {}

/-- A dominant morphism between irreducible schemes maps generic points to generic points. -/
theorem mapsTo_genericPoints_of_isDominant {T U : Scheme.{u}} (g : T ⟶ U)
    [IsIntegral T] [IsIntegral U] [IsDominant g] :
    Set.MapsTo g (genericPoints T) (genericPoints U) := by
  rw [genericPoints_eq_singleton, genericPoints_eq_singleton]
  intro x hx
  simpa only [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff] using
    genericPoint_eq_of_isDominant g

/-- The lift of a dominant morphism from an integral normal scheme to an integral scheme
through the normalization of the target (Tag 035Q). -/
def liftToIntegralNormalization {T U : Scheme.{u}} [IsIntegral T] [IsIntegral U] [IsNormal T]
    (g : T ⟶ U) [IsDominant g] : T ⟶ integralNormalization U :=
  (Scheme.existsUnique_lift_normalization (finite_irreducibleComponents_of_isIntegral U) g
    (fun η ↦ mapsTo_genericPoints_of_isDominant g η.2)).choose

/-- The lift `liftToIntegralNormalization g` composed with the normalization morphism is `g`. -/
@[reassoc (attr := simp)]
theorem liftToIntegralNormalization_fac {T U : Scheme.{u}} [IsIntegral T] [IsIntegral U]
    [IsNormal T] (g : T ⟶ U) [IsDominant g] :
    liftToIntegralNormalization g ≫ integralNormalizationMap U = g :=
  (Scheme.existsUnique_lift_normalization (finite_irreducibleComponents_of_isIntegral U) g
    (fun η ↦ mapsTo_genericPoints_of_isDominant g η.2)).choose_spec.1

/-- A morphism to the normalization whose composite with the normalization morphism is `g`
equals `liftToIntegralNormalization g`. -/
theorem liftToIntegralNormalization_unique {T U : Scheme.{u}} [IsIntegral T] [IsIntegral U]
    [IsNormal T] (g : T ⟶ U) [IsDominant g] (h : T ⟶ integralNormalization U)
    (hh : h ≫ integralNormalizationMap U = g) : h = liftToIntegralNormalization g :=
  (Scheme.existsUnique_lift_normalization (finite_irreducibleComponents_of_isIntegral U) g
    (fun η ↦ mapsTo_genericPoints_of_isDominant g η.2)).choose_spec.2 h hh

/-- A morphism of irreducible schemes followed by a locally quasi-finite morphism is dominant
only if it is dominant itself. -/
theorem isDominant_of_comp_of_locallyQuasiFinite {T U V : Scheme.{u}} (g : T ⟶ U) (h : U ⟶ V)
    [IsIntegral T] [IsIntegral U] [IsIntegral V] [LocallyQuasiFinite h] [IsDominant (g ≫ h)] :
    IsDominant g := by
  have : IsDominant h := IsDominant.of_comp g h
  have heq : genericPoint U = g (genericPoint T) :=
    (h.isDiscrete_preimage_singleton (genericPoint V)).eq_of_specializes
      ((genericPoint_spec U).specializes (Set.mem_univ _))
      (genericPoint_eq_of_isDominant h)
      (genericPoint_eq_of_isDominant (g ≫ h))
  constructor
  intro x
  have : closure ({genericPoint U} : Set U) ⊆ closure (Set.range g) :=
    closure_mono (Set.singleton_subset_iff.mpr ⟨genericPoint T, heq.symm⟩)
  exact this ((genericPoint_spec U).symm ▸ Set.mem_univ x)

/-- The lift of a dominant morphism through a finite normalization of the target is
dominant. -/
private theorem isDominant_liftToIntegralNormalization {T U : Scheme.{u}} [IsIntegral T]
    [IsIntegral U] [IsNormal T] (g : T ⟶ U) [IsDominant g]
    [hfin : IsFinite (integralNormalizationMap U)] :
    IsDominant (liftToIntegralNormalization g) := by
  have : IsDominant (liftToIntegralNormalization g ≫ integralNormalizationMap U) := by
    rwa [liftToIntegralNormalization_fac]
  exact isDominant_of_comp_of_locallyQuasiFinite _ (integralNormalizationMap U)

/-- The normalizations of the stages of a system of integral schemes with dominant transition
morphisms. -/
def normalizedDiagram (D : I ⥤ Scheme.{u}) [∀ i, IsIntegral (D.obj i)]
    [∀ {i j : I} (g : i ⟶ j), IsDominant (D.map g)] : I ⥤ Scheme.{u} where
  obj i := integralNormalization (D.obj i)
  map {i j} g := liftToIntegralNormalization (T := integralNormalization (D.obj i))
    (integralNormalizationMap (D.obj i) ≫ D.map g)
  map_id i := (liftToIntegralNormalization_unique _ (𝟙 _) (by simp)).symm
  map_comp {i j k} f g := by
    apply (liftToIntegralNormalization_unique _ _ ?_).symm
    rw [Category.assoc, liftToIntegralNormalization_fac, ← Category.assoc,
      liftToIntegralNormalization_fac, Category.assoc, D.map_comp]

/-- The stages of `normalizedDiagram D` are integral. -/
instance normalizedDiagram_obj_isIntegral (D : I ⥤ Scheme.{u}) [∀ i, IsIntegral (D.obj i)]
    [∀ {i j : I} (g : i ⟶ j), IsDominant (D.map g)] (i : I) :
    IsIntegral ((normalizedDiagram D).obj i) :=
  inferInstanceAs (IsIntegral (integralNormalization (D.obj i)))

/-- The stages of `normalizedDiagram D` are normal. -/
instance normalizedDiagram_obj_isNormal (D : I ⥤ Scheme.{u}) [∀ i, IsIntegral (D.obj i)]
    [∀ {i j : I} (g : i ⟶ j), IsDominant (D.map g)] (i : I) :
    IsNormal ((normalizedDiagram D).obj i) :=
  inferInstanceAs (IsNormal (integralNormalization (D.obj i)))

/-- The normalization morphisms of the stages, as a natural transformation. -/
def normalizedDiagramι (D : I ⥤ Scheme.{u}) [∀ i, IsIntegral (D.obj i)]
    [∀ {i j : I} (g : i ⟶ j), IsDominant (D.map g)] : normalizedDiagram D ⟶ D where
  app i := integralNormalizationMap (D.obj i)
  naturality _ _ g := liftToIntegralNormalization_fac (T := integralNormalization _)
    (integralNormalizationMap _ ≫ D.map g)

/-- The transition morphisms of `normalizedDiagram D` are affine when those of `D` are and the
normalization morphisms are finite. -/
private theorem normalizedDiagram_map_isAffineHom (D : I ⥤ Scheme.{u}) [∀ i, IsIntegral (D.obj i)]
    [∀ {i j : I} (g : i ⟶ j), IsDominant (D.map g)]
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i, IsFinite ((normalizedDiagramι D).app i)] {i j : I} (g : i ⟶ j) :
    IsAffineHom ((normalizedDiagram D).map g) := by
  have : IsAffineHom ((normalizedDiagram D).map g ≫ (normalizedDiagramι D).app j) := by
    rw [(normalizedDiagramι D).naturality]
    infer_instance
  exact IsAffineHom.of_comp _ ((normalizedDiagramι D).app j)

/-- The cone from an integral normal vertex to the normalized stages. -/
def normalizedCone (D : I ⥤ Scheme.{u}) [∀ i, IsIntegral (D.obj i)]
    [∀ {i j : I} (g : i ⟶ j), IsDominant (D.map g)]
    (c : Cone D) [IsIntegral c.pt] [IsNormal c.pt] [∀ i, IsDominant (c.π.app i)] :
    Cone (normalizedDiagram D) where
  pt := c.pt
  π :=
    { app := fun i ↦ liftToIntegralNormalization (T := c.pt) (c.π.app i)
      naturality := fun i j g ↦ by
        simp only [Functor.const_obj_map]
        symm
        apply liftToIntegralNormalization_unique (T := c.pt)
        change (liftToIntegralNormalization (T := c.pt) (c.π.app i) ≫
          liftToIntegralNormalization (integralNormalizationMap (D.obj i) ≫ D.map g)) ≫
            integralNormalizationMap (D.obj j) = _
        rw [Category.assoc, liftToIntegralNormalization_fac,
          liftToIntegralNormalization_fac_assoc, c.w] }

end NormalApproximation

open NormalApproximation in
/-- **Normal integral Noetherian approximation** (the first paragraph of the proof of
[Stacks, Tag 0EZJ]). A quasi-compact and quasi-separated integral normal scheme `S` is the limit
of a cofiltered system of integral normal Noetherian schemes with affine transition morphisms,
with dominant projections from `S`. -/
theorem exists_isLimit_isNoetherian_isIntegral_isNormal (S : Scheme.{u})
    [CompactSpace S] [QuasiSeparatedSpace S] [IsIntegral S] [IsNormal S] :
    ∃ (I : Type u) (_ : Category.{u} I) (_ : IsCofiltered I) (D : I ⥤ Scheme.{u})
      (π : (Functor.const I).obj S ⟶ D), Nonempty (IsLimit (Cone.mk S π)) ∧
      (∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)) ∧ (∀ i, IsNoetherian (D.obj i)) ∧
      (∀ i, IsIntegral (D.obj i)) ∧ (∀ i, IsNormal (D.obj i)) ∧ ∀ i, IsDominant (π.app i) := by
  obtain ⟨J, _, _, _, F, p, hFaff, hFlft, hFqc, ⟨hF⟩⟩ :=
    Scheme.exists_isLimit_affine_locallyOfFiniteType S
  let c := Cone.mk S p
  have : IsIntegral c.pt := inferInstanceAs (IsIntegral S)
  have : IsNormal c.pt := inferInstanceAs (IsNormal S)
  have : ∀ {i j : Jᵒᵈ} (g : i ⟶ j), IsAffineHom (F.map g) := hFaff
  have hπaff (i) : IsAffineHom (c.π.app i) := isAffineHom_π_app F c hF i
  have hπqc (i) : QuasiCompact (c.π.app i) := inferInstance
  let E := imageDiagram F c
  let e := imageCone F c
  have : IsIntegral e.pt := inferInstanceAs (IsIntegral S)
  have : IsNormal e.pt := inferInstanceAs (IsNormal S)
  have hEft (i) : LocallyOfFiniteType (terminal.from (E.obj i)) :=
    terminal_from_imageDiagram_obj_mem @LocallyOfFiniteType F c i inferInstance (hFlft i)
  have hEqc (i) : QuasiCompact (terminal.from (E.obj i)) :=
    terminal_from_imageDiagram_obj_mem @QuasiCompact F c i inferInstance (hFqc i)
  have hENoeth (i) : IsNoetherian (E.obj i) :=
    isNoetherian_of_locallyOfFiniteType_terminal_from (E.obj i)
  have hEint (i) : IsIntegral (E.obj i) := imageDiagram_obj_isIntegral F c i
  have hEdom (i) : IsDominant (e.π.app i) := imageCone_π_app_isDominant F c i
  have : ∀ {i j : Jᵒᵈ} (g : i ⟶ j), IsDominant (E.map g) := imageDiagram_map_isDominant F c
  have : ∀ {i j : Jᵒᵈ} (g : i ⟶ j), IsAffineHom (E.map g) := imageDiagram_map_isAffineHom F c
  have hνfin (i) : IsFinite ((normalizedDiagramι E).app i) :=
    isFinite_integralNormalizationMap _ (isNagataScheme_of_locallyOfFiniteType_terminal_from _)
  let N := normalizedDiagram E
  let n := normalizedCone E e
  have hndom (i) : IsDominant (n.π.app i) :=
    isDominant_liftToIntegralNormalization (T := e.pt) (e.π.app i) (hfin := hνfin i)
  have : ∀ i, CompactSpace (E.obj i) := fun _ ↦ inferInstance
  have : ∀ i, QuasiSeparatedSpace (E.obj i) := fun _ ↦ inferInstance
  have : ∀ i, LocallyOfFinitePresentation ((normalizedDiagramι E).app i) := fun _ ↦ inferInstance
  have : ∀ i, IsSeparated ((normalizedDiagramι E).app i) := fun _ ↦ inferInstance
  have hn : IsLimit n := isLimit_of_finitePresentation_refinement E N (normalizedDiagramι E) e n
    (imageConeIsLimit F c hF) rfl (fun i ↦
      (liftToIntegralNormalization_fac (T := e.pt) (e.π.app i)).trans (Category.id_comp _).symm)
  exact ⟨Jᵒᵈ, inferInstance, inferInstance, N, n.π, ⟨hn⟩, normalizedDiagram_map_isAffineHom E,
    fun i ↦ isNoetherian_integralNormalization (E.obj i) (hfin := hνfin i),
    fun i ↦ inferInstance, fun i ↦ inferInstance, hndom⟩

end AlgebraicGeometry

end
