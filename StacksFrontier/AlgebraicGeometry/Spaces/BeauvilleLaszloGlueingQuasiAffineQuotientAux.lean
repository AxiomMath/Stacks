module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingDataPullback
import all StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingQuasiAffineChart
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingPropertyTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineBasePullbackAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSheafSpaceCoverCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.PresentedObjectCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FlatChartQuotient

/-!
# Separated affine charts, fibre products and kernel pairs of algebraic spaces

Properties of separated affine charts of algebraic spaces, affineness of a fibre product of
affine algebraic spaces over a separated base, kernel pairs under a functor isomorphic to a
composite, and the universal property of a locally surjective morphism of sheaves among maps
out of its source.

## Main results

* `BeauvilleLaszlo.Space.IsSeparatedAffineChart.isFlat` and its companions: a separated affine
  chart is flat, locally of finite presentation and locally surjective, with separated target.
* `BeauvilleLaszlo.Space.isAffineSpace_of_isPullback_of_isSeparated`: a fibre product of affine
  algebraic spaces over a representable separated one is affine.
* `BeauvilleLaszlo.Space.isPullback_map_of_isPullback_of_iso`: a functor isomorphic to a
  composite carries a kernel pair, read through the composite, to a kernel pair.
* `AlgebraicGeometry.Space.existsUnique_desc_of_isLocallySurjective`: a locally surjective
  morphism of sheaves is the coequalizer, among sheaves, of any pair presenting its kernel pair.

## References

* [Stacks Project, Tag 0F9U](https://stacks.math.columbia.edu/tag/0F9U)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Separatedness is invariant under isomorphism.** -/
theorem isSeparatedOver_of_iso {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ F')
    (hF : IsSeparatedOver B S hS F) : IsSeparatedOver B S hS F' := by
  have hP : MorphismProperty.RespectsIso
      (MorphismProperty.inverseImage (@AlgebraicGeometry.IsClosedImmersion.{u})
        (BigFppfOver.toScheme B S hS)).presheaf :=
    MorphismProperty.relative_respectsIso _
  have h : diag F' = e.inv ≫ diag F ≫ prod.map e.hom e.hom := by
    ext <;> simp
  change (MorphismProperty.inverseImage (@AlgebraicGeometry.IsClosedImmersion.{u})
    (BigFppfOver.toScheme B S hS)).presheaf (diag F')
  rw [h]
  exact MorphismProperty.RespectsIso.precomp _ _ _
    (MorphismProperty.RespectsIso.postcomp _ (prod.map e.hom e.hom) _ hF)

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- **A locally surjective morphism of sheaves is the coequalizer, among sheaves, of any pair
presenting its kernel pair.** -/
theorem existsUnique_desc_of_isLocallySurjective {R U Q A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {t s : R ⟶ U} {q : U ⟶ Q} (hQ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Q)
    (hker : IsPullback t s q q)
    (hq : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) q)
    (hA : Presheaf.IsSheaf (BigFppfOver.topology B S hS) A) (k : U ⟶ A)
    (hk : t ≫ k = s ≫ k) : ∃! d : Q ⟶ A, q ≫ d = k := by
  let j := kernelPairRelation q
  have hj := isPullback_kernelPairRelation q
  let Qs : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨Q, hQ⟩
  let As : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨A, hA⟩
  have := isIso_quotientSheafDesc_of_isPullback j Qs q hj hq
  have hk' : j.target.left ≫ k = j.source.left ≫ k := by
    rw [kernelPairRelation_target_left, kernelPairRelation_source_left,
      show pullback.fst q q = hker.isoPullback.inv ≫ t by simp,
      show pullback.snd q q = hker.isoPullback.inv ≫ s by simp,
      Category.assoc, Category.assoc, hk]
  let D := quotientSheafDesc j Qs q hj.w
  let K := quotientSheafDesc j As k hk'
  have h1 : toQuotientSheaf j ≫ D.hom = q := toQuotientSheaf_quotientSheafDesc j Qs q hj.w
  have key : D.hom ≫ (inv D ≫ K).hom = K.hom :=
    congrArg (fun z : quotientSheaf j ⟶ As => z.hom) (IsIso.hom_inv_id_assoc D K)
  refine ⟨(inv D ≫ K).hom, ?_, fun d hd => ?_⟩
  · calc q ≫ (inv D ≫ K).hom = (toQuotientSheaf j ≫ D.hom) ≫ (inv D ≫ K).hom := by rw [h1]
      _ = toQuotientSheaf j ≫ K.hom := by rw [Category.assoc, key]
      _ = k := toQuotientSheaf_quotientSheafDesc j As k hk'
  · have hu := quotientSheafDesc_unique j As k hk' (D ≫ (⟨d⟩ : Qs ⟶ As))
      (show toQuotientSheaf j ≫ D.hom ≫ d = k by rw [← Category.assoc, h1, hd])
    exact congrArg (fun z : Qs ⟶ As => z.hom) ((IsIso.eq_inv_comp D).mpr hu)

end AlgebraicGeometry.Space

namespace BeauvilleLaszlo.Space

/-! ### Consequences of being a separated affine chart -/

section Chart

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The source of a separated affine chart is an affine algebraic space. -/
theorem IsSeparatedAffineChart.isAffineSpace_source {X Y : AlgebraicSpaces B S hS} {φ : X ⟶ Y}
    (hφ : IsSeparatedAffineChart φ) : AlgebraicGeometry.Space.IsAffineSpace B S hS X.obj := by
  obtain ⟨E, _, eE, _, _, -, hE, -⟩ := hφ
  exact ⟨E, hE, ⟨(ObjectProperty.ι _).mapIso eE⟩⟩

/-- The target of a separated affine chart is separated. -/
theorem IsSeparatedAffineChart.isSeparatedOver_target {X Y : AlgebraicSpaces B S hS}
    {φ : X ⟶ Y} (hφ : IsSeparatedAffineChart φ) :
    AlgebraicGeometry.Space.IsSeparatedOver B S hS Y.obj := by
  obtain ⟨_, V, _, eV, _, -, -, hV, -⟩ := hφ
  exact AlgebraicGeometry.Space.isSeparatedOver_of_iso ((ObjectProperty.ι _).mapIso eV.symm)
    (AlgebraicGeometry.Space.isSeparatedOver_yoneda_obj B S hS V hV)

/-- A separated affine chart satisfies every étale-local property its underlying morphism of
schemes has. -/
theorem IsSeparatedAffineChart.holdsOnEveryEtaleChart {X Y : AlgebraicSpaces B S hS}
    {φ : X ⟶ Y} (P : MorphismProperty Scheme.{u}) (hP : IsEtaleLocalOnSourceAndTarget P)
    (hφ : ∃ (E V : BigFppfOver B S hS) (eE : X ≅ schemeSpace E) (eV : Y ≅ schemeSpace V)
      (h : E ⟶ V), φ = eE.hom ≫ schemeSpaceMap h ≫ eV.inv ∧
        P ((BigFppfOver.toScheme B S hS).map h)) :
    AlgebraicGeometry.Space.HoldsOnEveryEtaleChart B S hS P φ.hom := by
  obtain ⟨E, V, eE, eV, h, rfl, hh⟩ := hφ
  refine AlgebraicGeometry.holdsOnEveryEtaleChart_of_prop_toScheme_map P hP B S hS h _
    ((ObjectProperty.ι _).mapIso eE) ((ObjectProperty.ι _).mapIso eV) ?_ hh
  change yoneda.map h = eE.inv.hom ≫ (eE.hom ≫ schemeSpaceMap h ≫ eV.inv).hom ≫ eV.hom.hom
  rw [← ObjectProperty.FullSubcategory.comp_hom, ← ObjectProperty.FullSubcategory.comp_hom]
  simp [schemeSpaceMap_hom]

/-- A separated affine chart is flat. -/
theorem IsSeparatedAffineChart.isFlat {X Y : AlgebraicSpaces B S hS} {φ : X ⟶ Y}
    (hφ : IsSeparatedAffineChart φ) : AlgebraicGeometry.Space.IsFlat B S hS φ.hom := by
  obtain ⟨E, V, eE, eV, h, hφ, -, -, hf, -⟩ := hφ
  exact IsSeparatedAffineChart.holdsOnEveryEtaleChart _ Flat.isEtaleLocalOnSourceAndTarget
    ⟨E, V, eE, eV, h, hφ, hf⟩

/-- A separated affine chart is locally of finite presentation. -/
theorem IsSeparatedAffineChart.isLocallyOfFinitePresentation {X Y : AlgebraicSpaces B S hS}
    {φ : X ⟶ Y} (hφ : IsSeparatedAffineChart φ) :
    AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS φ.hom := by
  obtain ⟨E, V, eE, eV, h, hφ, -, -, -, hl, -⟩ := hφ
  exact IsSeparatedAffineChart.holdsOnEveryEtaleChart _
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget ⟨E, V, eE, eV, h, hφ, hl⟩

/-- A separated affine chart is a surjection of fppf sheaves. -/
theorem IsSeparatedAffineChart.isLocallySurjective {X Y : AlgebraicSpaces B S hS} {φ : X ⟶ Y}
    (hφ : IsSeparatedAffineChart φ) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) φ.hom := by
  obtain ⟨E, V, eE, eV, h, rfl, -, -, hf, hl, hs⟩ := hφ
  have h3 : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (schemeSpaceMap h).hom :=
    AlgebraicGeometry.Stack.isLocallySurjective_yoneda_map_of_fppf B S hS h hf hl hs
  have h1 : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) eE.hom.hom :=
    Presheaf.isLocallySurjective_of_iso _ ((ObjectProperty.ι _).mapIso eE).hom
  have h2 : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) eV.inv.hom :=
    Presheaf.isLocallySurjective_of_iso _ ((ObjectProperty.ι _).mapIso eV.symm).hom
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom]
  exact Presheaf.isLocallySurjective_comp _ _ _

/-- **A fibre product of affine algebraic spaces over a representable separated one is
affine.** -/
theorem isAffineSpace_of_isPullback_of_isSeparated {P X Y Z : AlgebraicSpaces B S hS}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback fst snd f g)
    (hX : AlgebraicGeometry.Space.IsAffineSpace B S hS X.obj)
    (hY : AlgebraicGeometry.Space.IsAffineSpace B S hS Y.obj)
    {V : BigFppfOver B S hS} (eZ : Z ≅ schemeSpace V)
    (hV : ((BigFppfOver.toScheme B S hS).obj V).IsSeparated) :
    AlgebraicGeometry.Space.IsAffineSpace B S hS P.obj := by
  have := spaces_inclusion_preservesPullback B S hS f g
  obtain ⟨X₀, hX₀, ⟨eX⟩⟩ := hX
  obtain ⟨Y₀, hY₀, ⟨eY⟩⟩ := hY
  have : HasPullbacks (BigFppfOver B S hS) := AlgebraicGeometry.hasPullbacks_bigFppfOver B S hS
  let eZ' : Z.obj ≅ yoneda.obj V := (ObjectProperty.ι _).mapIso eZ
  let a : X₀ ⟶ V := Yoneda.fullyFaithful.preimage (eX.inv ≫ f.hom ≫ eZ'.hom)
  let b : Y₀ ⟶ V := Yoneda.fullyFaithful.preimage (eY.inv ≫ g.hom ≫ eZ'.hom)
  have : HasLimit (cospan a b) := HasLimitsOfShape.has_limit _
  have sq₀ : IsPullback fst.hom snd.hom f.hom g.hom := sq.map (ObjectProperty.ι _)
  have sq₁ : IsPullback (fst.hom ≫ eX.hom) (snd.hom ≫ eY.hom) (yoneda.map a) (yoneda.map b) :=
    IsPullback.of_iso sq₀ (Iso.refl _) eX eY eZ' (by simp) (by simp) (by simp [a]) (by simp [b])
  have sq₂ : IsPullback (yoneda.map (pullback.fst a b)) (yoneda.map (pullback.snd a b))
      (yoneda.map a) (yoneda.map b) := (IsPullback.of_hasPullback a b).map yoneda
  have hsch : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst a b))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd a b))
      ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b) :=
    (IsPullback.of_hasPullback a b).map (BigFppfOver.toScheme B S hS)
  have : IsAffine (pullback ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :=
    AlgebraicGeometry.isAffine_pullback_of_isSeparated_base _ _ hX₀ hY₀ hV
  exact ⟨pullback a b, IsAffine.of_isIso hsch.isoPullback.hom, ⟨sq₁.isoIsPullback _ _ sq₂⟩⟩

end Chart

/-! ### Kernel pairs through a natural isomorphism -/

/-- **A functor isomorphic to a composite carries a kernel pair read through the composite to a
kernel pair.** If the image under `G` of `p₀, p₁ : W ⟶ T` is, up to an isomorphism `e`, a pair
`pr₀, pr₁` whose image under `O` is the kernel pair of `O.map φ`, then `Bc ≅ G ⋙ O` carries
`p₀, p₁` to the kernel pair of the morphism `φ` read through the isomorphism. -/
theorem isPullback_map_of_isPullback_of_iso {C D E : Type*} [Category C] [Category D]
    [Category E] {G : C ⥤ D} {O : D ⥤ E} {Bc : C ⥤ E} (α : G ⋙ O ≅ Bc) {W T : C} {Z P : D}
    (φ : G.obj T ⟶ Z) (pr₀ pr₁ : P ⟶ G.obj T)
    (hP : IsPullback (O.map pr₀) (O.map pr₁) (O.map φ) (O.map φ)) (e : G.obj W ≅ P)
    (p₀ p₁ : W ⟶ T) (h₀ : G.map p₀ = e.hom ≫ pr₀) (h₁ : G.map p₁ = e.hom ≫ pr₁) :
    IsPullback (Bc.map p₀) (Bc.map p₁) (α.inv.app T ≫ O.map φ) (α.inv.app T ≫ O.map φ) := by
  have n₀ := α.hom.naturality p₀
  have n₁ := α.hom.naturality p₁
  simp only [Functor.comp_map, h₀, h₁, Functor.map_comp] at n₀ n₁
  refine IsPullback.of_iso hP (O.mapIso e.symm ≪≫ α.app W) (α.app T) (α.app T) (Iso.refl _)
    ?_ ?_ (by simp) (by simp) <;>
  · simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Category.assoc,
      ← n₀, ← n₁]
    simp

end BeauvilleLaszlo.Space

end
