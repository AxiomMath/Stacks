module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyPolarizedCharts
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesDiagonalReduction
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.EtaleCoverBoundedAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ProjectiveMorFunctorsBounded
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesEtaleLocallyProjective
public import StacksFrontier.AlgebraicGeometry.Quot.IsomorphismLocusBaseChange

/-!
# The relative morphism functors of families of curves, étale locally (towards Stacks 0D53)

Let `F` and `G` be families of curves over a common base `U`. Through every point of `U` there is
an affine étale neighbourhood `V ⟶ U` over which both families are H-projective schemes
(Stacks 0E6F from the smooth local polarizations of Stacks 0DQ0,
`AlgebraicGeometry.C1590Private.curvesSmoothLocallyPolarized`), and `Mor_V(F_V, G_V)` is the base
change of `Mor_U(F, G)` along `V ⟶ U` (Stacks 05Y4). So `Mor_U(F, G)` is an algebraic space as
soon as the relative morphism functors of H-projective schemes over affine bases are, with
atlases of uniformly bounded size (`AlgebraicGeometry.C1590Private.ProjectiveMorFunctorsBounded`):
the neighbourhoods, one per point of `U`, are glued by
`AlgebraicGeometry.C1590Private.isAlgebraicSpace_of_etaleCover_isPullback_of_size_le`.

## Main results

* `AlgebraicGeometry.C1590Private.exists_isPullback_relativeHom_of_isPullback`: Stacks 05Y4 along
  arbitrary cartesian squares.
* `AlgebraicGeometry.C1590Private.exists_affine_etale_isPullback_isProjectiveMorphism`: the common
  H-projective étale neighbourhoods of finitely many families, affine.
* `AlgebraicGeometry.C1590Private.isAlgebraicSpace_relativeHom_of_etaleLocal`: `Mor_U(Z, X)` is an
  algebraic space when `Z` and `X` are H-projective schemes étale locally on `U`.
* `AlgebraicGeometry.C1590Private.curveMorFunctorsAlgebraic_of_projectiveMorFunctorsBounded`: the
  relative morphism functors of families of curves are algebraic spaces.

## References

* [Stacks Project, Tag 0D53](https://stacks.math.columbia.edu/tag/0D53)
* [Stacks Project, Tag 05Y4](https://stacks.math.columbia.edu/tag/05Y4)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.C1590Private

section BaseChange

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Z X Q Z' X' Q' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 05Y4 along arbitrary cartesian squares.** Let `z : Z ⟶ Q`, `x : X ⟶ Q` and
`q : Q' ⟶ Q` be morphisms of algebraic spaces, and let `z' : Z' ⟶ Q'` and `x' : X' ⟶ Q'` be base
changes of `z` and `x` along `q`. Then the projection `Mor_{Q'}(Z', X') ⟶ Q'` is a base change
of the projection `Mor_Q(Z, X) ⟶ Q` along `q`. -/
theorem exists_isPullback_relativeHom_of_isPullback (z : Z ⟶ Q) (x : X ⟶ Q) (q : Q' ⟶ Q)
    (z' : Z' ⟶ Q') (x' : X' ⟶ Q') (a : Z' ⟶ Z) (c : X' ⟶ X)
    (ha : IsPullback a z' z q) (hc : IsPullback c x' x q)
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q) (hZ' : IsAlgebraicSpace B S hS Z')
    (hX' : IsAlgebraicSpace B S hS X') (hQ' : IsAlgebraicSpace B S hS Q') :
    ∃ g : Space.relativeHom B S hS Z' X' Q' z' x' hZ' hX' hQ' ⟶
        Space.relativeHom B S hS Z X Q z x hZ hX hQ,
      IsPullback g (Space.relativeHomProjection B S hS Z' X' Q' z' x' hZ' hX' hQ')
        (Space.relativeHomProjection B S hS Z X Q z x hZ hX hQ) q := by
  let e : Z' ≅ pullback q z := ha.flip.isoPullback
  have he : e.hom ≫ pullback.fst q z = z' := ha.flip.isoPullback_hom_fst
  let ε : X' ≅ pullback q x := hc.flip.isoPullback
  have hε : ε.hom ≫ pullback.fst q x = x' := hc.flip.isoPullback_hom_fst
  let H := Space.relativeHomData B S hS Z X Q z x hZ hX hQ
  let H' : Space.RelativeHomConstruction B S hS (pullback q z) (pullback q x) Q'
      (pullback.fst q z) (pullback.fst q x) :=
    { functor := Space.relativeHom B S hS Z' X' Q' z' x' hZ' hX' hQ'
      projection := Space.relativeHomProjection B S hS Z' X' Q' z' x' hZ' hX' hQ'
      sections T := (Space.relativeHomSections B S hS Z' X' Q' z' x' hZ' hX' hQ' T).trans
        (Space.RelativeMorphism.transportEquiv e he ε hε)
      projection_sections T p :=
        (Space.relativeHomData B S hS Z' X' Q' z' x' hZ' hX' hQ').projection_sections T p
      sections_map {T U} f p := Space.sections_map_of_eq_restrict f (by
        show Space.RelativeMorphism.transport e he ε hε
            (Space.relativeHomSections B S hS Z' X' Q' z' x' hZ' hX' hQ' U
              ((Space.relativeHom B S hS Z' X' Q' z' x' hZ' hX' hQ').map f.op p)) =
          Space.RelativeMorphism.restrict (yoneda.map f)
            (Space.RelativeMorphism.transport e he ε hε
              (Space.relativeHomSections B S hS Z' X' Q' z' x' hZ' hX' hQ' T p))
        rw [Space.relativeHomSections_map, Space.RelativeMorphism.transport_restrict]) }
  exact ⟨Space.relativeHomOfBaseChange q H H',
    (Space.isPullback_relativeHomOfBaseChange q H H').flip⟩

end BaseChange

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

open Stacks.Ample in
/-- **Common affine H-projective étale neighbourhoods of finitely many families of curves.** For
finitely many smooth locally polarized families of curves `X i` over a common base `S` and a point
`s` of `S`, there is an étale morphism `φ : U ⟶ S` of the site with `U` affine and `s` in its
image, along which the base change of every `X i` is a scheme, H-projective over `U`. This is
the pointwise form of Stacks 0E6F in
`StacksFrontier/AlgebraicGeometry/Quot/CurveFamiliesEtaleLocallyProjective.lean`, with the
affineness of the neighbourhood recorded. -/
theorem exists_affine_etale_isPullback_isProjectiveMorphism
    {ι : Type*} [Finite ι] {S : BigFppfOver B integerBase hZ} (X : ι → CurveFamily B hZ)
    (hX : ∀ i, (X i).base = S) (hpol : ∀ i, (X i).IsSmoothLocallyPolarized)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj S) :
    ∃ (U : BigFppfOver B integerBase hZ) (φ : U ⟶ S)
      (u : (BigFppfOver.toScheme B integerBase hZ).obj U),
      Etale ((BigFppfOver.toScheme B integerBase hZ).map φ) ∧
      IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj U) ∧
      (BigFppfOver.toScheme B integerBase hZ).map φ u = s ∧
      ∀ i, ∃ (Z : BigFppfOver B integerBase hZ) (p : schemeSpace Z ⟶ (X i).total) (q : Z ⟶ U),
        IsPullback p (schemeSpaceMap q) (X i).toBase
          (schemeSpaceMap (φ ≫ eqToHom (hX i).symm)) ∧
        IsProjectiveMorphism ((BigFppfOver.toScheme B integerBase hZ).map q) := by
  choose T' π hπ hs Z p q hsq L hL hamp using
    fun i => (hpol i).of_base_eq (hX i) s
  obtain ⟨U, φ, u, hφ, hU, hu, hg⟩ :=
    CurveFamily.exists_affine_etale_sections_of_smooth s T' π hπ hs
  refine ⟨U, φ, u, hφ, hU, hu, fun i => ?_⟩
  obtain ⟨g, hg⟩ := hg i
  have := hL i
  obtain ⟨Z', p', q', h1, h2⟩ :=
    CurveFamily.exists_isPullback_isProjectiveMorphism_of_polarizedChart (X i) (hsq i) (L i)
      (hamp i) g
  rw [← Category.assoc, hg] at h1
  exact ⟨Z', p', q', h1, h2⟩

variable (B hZ) in
/-- **`Mor_U(Z, X)` is an algebraic space when `Z` and `X` are H-projective schemes étale locally
on `U`.** Let `z : Z ⟶ U` and `x : X ⟶ U` be morphisms of algebraic spaces to an object `U` of
the big fppf site over `Spec ℤ`, with `z` flat, proper and of finite presentation and `x` proper
and of finite presentation. Suppose that through every point of `U` there is an étale morphism
`φ : V ⟶ U` from an affine `V` along which `Z` and `X` become H-projective schemes over `V`. Then
`Mor_U(Z, X)` is an algebraic space, provided the relative morphism functors of H-projective
schemes over affine bases are algebraic spaces with atlases of bounded size. -/
theorem isAlgebraicSpace_relativeHom_of_etaleLocal (hE : ProjectiveMorFunctorsBounded B hZ)
    {Z X : AlgebraicSpaces B integerBase hZ} {U : BigFppfOver B integerBase hZ}
    (z : Z ⟶ schemeSpace U) (x : X ⟶ schemeSpace U)
    (hzf : Space.IsFlat B integerBase hZ z.hom) (hzp : Space.IsProper B integerBase hZ z.hom)
    (hzfp : Space.IsFinitePresentation B integerBase hZ z.hom)
    (hxp : Space.IsProper B integerBase hZ x.hom)
    (hxfp : Space.IsFinitePresentation B integerBase hZ x.hom)
    (hloc : ∀ s : (BigFppfOver.toScheme B integerBase hZ).obj U,
      ∃ (V : BigFppfOver B integerBase hZ) (φ : V ⟶ U),
        Etale ((BigFppfOver.toScheme B integerBase hZ).map φ) ∧
        IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj V) ∧
        s ∈ Set.range ((BigFppfOver.toScheme B integerBase hZ).map φ) ∧
        ∃ (Z₁ Z₂ : BigFppfOver B integerBase hZ) (q₁ : Z₁ ⟶ V) (q₂ : Z₂ ⟶ V)
          (p₁ : schemeSpace Z₁ ⟶ Z) (p₂ : schemeSpace Z₂ ⟶ X),
          IsPullback p₁ (schemeSpaceMap q₁) z (schemeSpaceMap φ) ∧
          IsPullback p₂ (schemeSpaceMap q₂) x (schemeSpaceMap φ) ∧
          IsProjectiveMorphism ((BigFppfOver.toScheme B integerBase hZ).map q₁) ∧
          IsProjectiveMorphism ((BigFppfOver.toScheme B integerBase hZ).map q₂)) :
    IsAlgebraicSpace B integerBase hZ
      (Space.relativeHom B integerBase hZ Z.obj X.obj (schemeSpace U).obj z.hom x.hom
        Z.property X.property (schemeSpace U).property) := by
  classical
  choose V φ hφ hV hs Z₁ Z₂ q₁ q₂ p₁ p₂ hp₁ hp₂ hq₁ hq₂ using hloc
  -- the uniform bound: the neighbourhoods are étale over `U` and quasi-compact
  set μ : Cardinal.{u} := 2 ^ ((BigFppfOver.toScheme B integerBase hZ).obj U).size
  have hUc : ((BigFppfOver.toScheme B integerBase hZ).obj U).size < B.cutoff := U.left.property
  have hμ : μ < B.cutoff := B.cutoff_isStrongPrelimit hUc
  obtain ⟨κ, hκ, hEκ⟩ := hE μ hμ
  have hVsize : ∀ s, ((BigFppfOver.toScheme B integerBase hZ).obj (V s)).size ≤ μ := fun s => by
    have := hφ s
    have := hV s
    exact (Scheme.size_le_of_locallyOfFiniteType
      ((BigFppfOver.toScheme B integerBase hZ).map (φ s))).trans (cantor _).le
  -- the pieces are H-projective schemes with the properties of `z` and `x`
  have hpiece := fun s =>
    hEκ (V s) (Z₁ s) (Z₂ s) (q₁ s) (q₂ s) (hV s) (hVsize s) (hq₁ s) (hq₂ s)
      ((Space.isFlat_isStableUnderBaseChange B integerBase hZ).of_isPullback (hp₁ s) hzf)
      ((Space.isProper_isStableUnderBaseChange B integerBase hZ).of_isPullback (hp₁ s) hzp)
      ((Space.isFinitePresentation_isStableUnderBaseChange B integerBase hZ).of_isPullback
        (hp₁ s) hzfp)
      ((Space.isProper_isStableUnderBaseChange B integerBase hZ).of_isPullback (hp₂ s) hxp)
      ((Space.isFinitePresentation_isStableUnderBaseChange B integerBase hZ).of_isPullback
        (hp₂ s) hxfp)
  -- `Mor_V(Z_V, X_V)` is the base change of `Mor_U(Z, X)` along `V ⟶ U`
  choose g hg using fun s => exists_isPullback_relativeHom_of_isPullback z.hom x.hom
    (yoneda.map (φ s)) (yoneda.map (q₁ s)) (yoneda.map (q₂ s)) (p₁ s).hom (p₂ s).hom
    (AlgebraicSpaces.isPullback_hom B integerBase hZ (hp₁ s))
    (AlgebraicSpaces.isPullback_hom B integerBase hZ (hp₂ s)) Z.property X.property
    (schemeSpace U).property (isAlgebraicSpace_yoneda B integerBase hZ (Z₁ s))
    (isAlgebraicSpace_yoneda B integerBase hZ (Z₂ s))
    (isAlgebraicSpace_yoneda B integerBase hZ (V s))
  refine isAlgebraicSpace_of_etaleCover_isPullback_of_size_le
    (Space.isSheaf_relativeHom B integerBase hZ _ _ _ _ _ _ _ _)
    (Space.relativeHomProjection B integerBase hZ Z.obj X.obj (schemeSpace U).obj z.hom x.hom
      Z.property X.property (schemeSpace U).property)
    V φ hφ (fun s => ⟨s, hs s⟩) _ (fun s => (hpiece s).1) g _ hg
    (μ := max μ κ) (max_lt hμ hκ)
    ((Scheme.mk_le_two_pow_size _).trans (le_max_left _ _))
    (fun s => (hVsize s).trans (le_max_left _ _)) fun s => ?_
  obtain ⟨A, a, ha₁, ha₂, ha₃⟩ := (hpiece s).2
  exact ⟨A, a, ha₁, ha₂, ha₃.trans (le_max_right _ _)⟩

variable (B hZ) in
/-- **The relative morphism functors of families of curves are algebraic spaces**, given the
relative morphism functors of H-projective schemes over affine bases with atlases of bounded
size. Every family of curves is smooth locally polarized
(`AlgebraicGeometry.C1590Private.curvesSmoothLocallyPolarized`), so two families over a common
base are H-projective schemes over common affine étale neighbourhoods of the points of the base
(`AlgebraicGeometry.C1590Private.exists_affine_etale_isPullback_isProjectiveMorphism`), and
`AlgebraicGeometry.C1590Private.isAlgebraicSpace_relativeHom_of_etaleLocal` applies. -/
theorem curveMorFunctorsAlgebraic_of_projectiveMorFunctorsBounded
    (hE : ProjectiveMorFunctorsBounded B hZ) : CurveMorFunctorsAlgebraic B hZ := by
  intro F G h
  -- the transport along `h` is trivial once `h` is substituted
  have hcomp : ∀ (P : ∀ {Y Y' : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}, (Y ⟶ Y') → Prop)
      {b : BigFppfOver B integerBase hZ} (e : G.base = b), P G.toBase.hom →
        P (G.toBase.hom ≫ yoneda.map (eqToHom e)) := by
    rintro P b rfl hP
    rw [eqToHom_refl, CategoryTheory.Functor.map_id]
    exact (Category.comp_id G.toBase.hom).symm ▸ hP
  have hfp := fun {b} (e : G.base = b) =>
    hcomp (Space.IsFinitePresentation B integerBase hZ) e G.finitePresentation
  have hpr := fun {b} (e : G.base = b) =>
    hcomp (Space.IsProper B integerBase hZ) e G.proper
  have hsq : ∀ {b V Z : BigFppfOver B integerBase hZ} (e : G.base = b) (φ : V ⟶ b)
      (p : schemeSpace Z ⟶ G.total) (q : Z ⟶ V),
      IsPullback p (schemeSpaceMap q) G.toBase (schemeSpaceMap (φ ≫ eqToHom e.symm)) →
        IsPullback p (schemeSpaceMap q) (G.toBase ≫ schemeSpaceMap (eqToHom e))
          (schemeSpaceMap φ) := by
    rintro b V Z rfl φ p q hpq
    have hid : G.toBase ≫ schemeSpaceMap (eqToHom (rfl : G.base = G.base)) = G.toBase := by
      apply ObjectProperty.hom_ext
      show G.toBase.hom ≫ yoneda.map (𝟙 _) = _
      rw [CategoryTheory.Functor.map_id]
      exact Category.comp_id _
    rw [hid]
    simpa using hpq
  refine isAlgebraicSpace_relativeHom_of_etaleLocal B hZ hE F.toBase
    (G.toBase ≫ schemeSpaceMap (eqToHom h)) F.flat F.proper F.finitePresentation (hpr h)
    (hfp h) fun s => ?_
  obtain ⟨V, φ, u, hφ, hV, hu, hX⟩ := exists_affine_etale_isPullback_isProjectiveMorphism
    ![F, G] (fun i => by fin_cases i <;> simp [h])
    (fun _ => curvesSmoothLocallyPolarized B hZ _) s
  obtain ⟨Z₁, p₁, q₁, hp₁, hq₁⟩ := hX 0
  obtain ⟨Z₂, p₂, q₂, hp₂, hq₂⟩ := hX 1
  have hp₁' : IsPullback p₁ (schemeSpaceMap q₁) F.toBase
      (schemeSpaceMap (φ ≫ eqToHom (rfl : F.base = F.base))) := hp₁
  refine ⟨V, φ, hφ, hV, ⟨u, hu⟩, Z₁, Z₂, q₁, q₂, p₁, p₂, ?_, hsq h φ p₂ q₂ hp₂, hq₁, hq₂⟩
  simpa using hp₁'

end AlgebraicGeometry.C1590Private

end
