module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FiniteSchemeFiltration.ActionRelationDescent
import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.ResidueDegreeBound

/-!
# The degree filtration and the symmetric power of an étale chart

The groupoid of the permutation action on the distinct-tuple locus of a fibre power, the
degree property of a descending chain of open subspaces relative to an affine étale chart,
the degree filtration of a quasi-compact algebraic space by open subspaces, covered by
quotients of the distinct-tuple loci of the symmetric powers of the chart, and the
symmetric power of an affine étale chart. The groupoid is used by both the degree filtration
and the symmetric power, so they share this file.

## Main results

* `AlgebraicGeometry.Space.exists_symmetricPower_etaleChart`: the symmetric power
  of an affine étale chart, with its étale structure morphism, its coordinates, the
  permutation action, coordinatewise extensionality, and the lift of a pairwise
  distinct family of coordinates over a one-point test object.
* `AlgebraicGeometry.Space.isEtale_of_presheaf_inverseImage_etale`: a representably
  étale morphism of presheaves on the big fppf site is étale.
* `AlgebraicGeometry.Space.existsUnique_map_eq_of_surjective_flat_locallyOfFinitePresentation`:
  descent of sections of an fppf sheaf along a surjective flat morphism of finite
  presentation.
* `AlgebraicGeometry.Space.exists_comp_eq_of_isOpenImmersion_of_range_subset`: a
  morphism of the site whose image lies in the image of an open immersion factors
  through it.

This is the fourth part of
`StacksFrontier.AlgebraicGeometry.Spaces.Decent.FiniteSchemeFiltration`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v u₁ v₁

namespace AlgebraicGeometry.Space

private noncomputable def actionGroupoid
    {S : Scheme.{u}} (U : Over S) (G : Type v) [Group G] [Small.{u} G]
    (a : G →* Aut U)
    (ha : AlgebraicGeometry.Space.ActsNontriviallyOnFixedResidueFields U G a) :
    Stacks.Groupoids.GroupoidScheme S := by
  letI : Stacks.Groupoids.IsEtaleEquivalenceRelation
      (AlgebraicGeometry.Space.actionRelation U G a) :=
    AlgebraicGeometry.Space.actionRelation_isEtaleEquivalenceRelation U G a ha
  exact AlgebraicGeometry.groupoidSchemeOfIsEquivalenceRelation
    (AlgebraicGeometry.Space.actionRelation U G a)

private theorem actionGroupoid_extendsRelation
    {S : Scheme.{u}} (U : Over S) (G : Type v) [Group G] [Small.{u} G]
    (a : G →* Aut U)
    (ha : AlgebraicGeometry.Space.ActsNontriviallyOnFixedResidueFields U G a) :
    AlgebraicGeometry.ExtendsRelation (AlgebraicGeometry.Space.actionRelation U G a)
      (actionGroupoid U G a ha) := by
  let : Stacks.Groupoids.IsEtaleEquivalenceRelation
      (AlgebraicGeometry.Space.actionRelation U G a) :=
    AlgebraicGeometry.Space.actionRelation_isEtaleEquivalenceRelation U G a ha
  unfold actionGroupoid
  exact AlgebraicGeometry.groupoidSchemeOfIsEquivalenceRelation_extendsRelation _

/-- The finite locally free source and target of the action groupoid. -/
private theorem actionGroupoid_finiteLocallyFree
    {S : Scheme.{u}} (U : Over S) (G : Type v) [Group G] [Small.{u} G] [Finite G]
    (a : G →* Aut U)
    (ha : AlgebraicGeometry.Space.ActsNontriviallyOnFixedResidueFields U G a) :
    Stacks.Morphisms.IsFiniteLocallyFree (actionGroupoid U G a ha).source.left ∧
      Stacks.Morphisms.IsFiniteLocallyFree (actionGroupoid U G a ha).target.left :=
  finiteLocallyFree_of_extendsRelation (actionRelation U G a) _
    (actionGroupoid_extendsRelation U G a ha)
    (by
      simpa [actionRelation, Stacks.Groupoids.PreRelation.source] using
        actionRelationSource_isFiniteLocallyFree U G)
    (by
      simpa [actionRelation, Stacks.Groupoids.PreRelation.target] using
        actionRelationTarget_isFiniteLocallyFree U G a)

/-- The action groupoid is an equivalence relation. -/
private theorem actionGroupoid_isEquivalenceRelation
    {S : Scheme.{u}} (U : Over S) (G : Type v) [Group G] [Small.{u} G]
    (a : G →* Aut U)
    (ha : AlgebraicGeometry.Space.ActsNontriviallyOnFixedResidueFields U G a) :
    IsEquivalenceRelation (actionGroupoid U G a ha).target (actionGroupoid U G a ha).source := by
  let := actionRelation_isEtaleEquivalenceRelation U G a ha
  exact isEquivalenceRelation_of_extendsRelation (actionRelation U G a) _
    (actionGroupoid_extendsRelation U G a ha)

/-- The target map of the action groupoid is étale. -/
private theorem actionGroupoid_etale_target
    {S : Scheme.{u}} (U : Over S) (G : Type v) [Group G] [Small.{u} G]
    (a : G →* Aut U)
    (ha : AlgebraicGeometry.Space.ActsNontriviallyOnFixedResidueFields U G a) :
    Etale (actionGroupoid U G a ha).target.left := by
  let := actionRelation_isEtaleEquivalenceRelation U G a ha
  exact etale_target_of_extendsRelation (actionRelation U G a) _
    (actionGroupoid_extendsRelation U G a ha)

/-- The kernel pair of the quotient of the action groupoid, transported along an isomorphism. -/
private theorem actionGroupoid_isPullback_of_quotientMap
    {S : Scheme.{u}} (U : Over S) (G : Type v) [Group G] [Small.{u} G]
    (a : G →* Aut U)
    (ha : AlgebraicGeometry.Space.ActsNontriviallyOnFixedResidueFields U G a)
    (q : Stacks.Groupoids.FiniteFlatQuotient (actionGroupoid U G a ha)) {V : Over S}
    (j : V ≅ q.space) (f : U ⟶ V)
    (hf : f = eqToHom (actionGroupoid_extendsRelation U G a ha).objects_eq.symm ≫
      q.quotientMap ≫ j.inv) :
    IsPullback (actionRelationTarget U G a) (actionRelationSource U G) f f := by
  have hp := kernelPair_of_extendsRelation (actionRelation U G a) _
    (actionGroupoid_extendsRelation U G a ha) q.quotientMap q.kernelPair
  simp only [actionRelation, Stacks.Groupoids.PreRelation.target,
    Stacks.Groupoids.PreRelation.source, prod.lift_fst, prod.lift_snd] at hp
  rw [hf]
  exact hp.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) j.symm
    (by simp) (by simp) (by simp) (by simp)

/-- A quotient of a groupoid scheme with an object in the site lies in the site. -/
private theorem contains_space_of_finiteFlatQuotient
    (B : AlgebraicGeometry.BigFppfSite.{u}) {S : Scheme.{u}}
    {R : Stacks.Groupoids.GroupoidScheme S} (q : Stacks.Groupoids.FiniteFlatQuotient R)
    (hsource : B.Contains R.objects.left) : B.Contains q.space.left := by
  have hflf :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      q.quotientMap.left).mp q.finiteLocallyFree
  exact (size_le_of_surjective_flat_locallyOfFinitePresentation
    q.quotientMap.left hflf.2.1 hflf.2.2 q.surjective).trans_lt hsource

/-- The orbit-affine property of a groupoid scheme whose objects are étale and separated over an
affine scheme, and whose source map is finite locally free. -/
private theorem groupoid_exists_affineOpen_containing_orbit
    {S Y T : Scheme.{u}} [IsAffine Y] (R : Stacks.Groupoids.GroupoidScheme S)
    (e : R.objects.left ≅ T) (f : T ⟶ Y) [Etale f] [_root_.AlgebraicGeometry.IsSeparated f]
    (hs : Stacks.Morphisms.IsFiniteLocallyFree R.source.left) :
    ∀ Z : Set R.objects.left, IsClosed Z → Z.Nonempty →
      ∃ x ∈ Z, ∃ D : R.objects.left.Opens,
        IsAffineOpen D ∧ ∀ r : R.arrows.left,
          R.source.left.base r = x → R.target.left.base r ∈ D := by
  have : Etale (e.hom ≫ f) := inferInstance
  have : _root_.AlgebraicGeometry.IsSeparated (e.hom ≫ f) := inferInstance
  have := locallyQuasiFinite_of_etale (e.hom ≫ f)
  have : _root_.AlgebraicGeometry.IsFinite R.source.left :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mp
      hs).1
  intro Z _ ⟨x, hx⟩
  obtain ⟨D, hD, hcontains⟩ :=
    exists_isAffineOpen_containing_finite_of_locallyQuasiFinite (e.hom ≫ f)
      ((R.source.left.finite_preimage_singleton x).image R.target.left.base)
  exact ⟨x, hx, D, hD, fun r hr ↦ hcontains ⟨r, hr, rfl⟩⟩

/-- A morphism of the site whose image in `Over S` is a conjugate of `q` has property `P` as soon
as `q` does. -/
private theorem map_toScheme_of_post_map_eq
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {W V : AlgebraicGeometry.BigFppfOver B S hS} (f : W ⟶ V) {X Y : Over S} (q : X ⟶ Y)
    (i : (Over.post B.inclusion).obj W ≅ X) (j : Y ≅ (Over.post B.inclusion).obj V)
    (hf : (Over.post B.inclusion).map f = i.hom ≫ q ≫ j.hom) (hq : P q.left) :
    P ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f) := by
  change P ((Over.forget S).map ((Over.post B.inclusion).map f))
  rw [hf, Functor.map_comp, Functor.map_comp, P.cancel_left_of_respectsIso,
    P.cancel_right_of_respectsIso]
  exact hq

/-- The composite of the inclusion of an open of a site object with an étale separated morphism
is étale and separated. -/
private theorem etale_separated_map_opensSiteObjectInclusion_comp
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U A : AlgebraicGeometry.BigFppfOver B S hS}
    (L : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U).Opens) (p : U ⟶ A)
    (hp : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map p) ∧
      _root_.AlgebraicGeometry.IsSeparated
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map p)) :
    Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
        (opensSiteObjectInclusion B S hS U L ≫ p)) ∧
      _root_.AlgebraicGeometry.IsSeparated ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
        (opensSiteObjectInclusion B S hS U L ≫ p)) := by
  obtain ⟨h₁, h₂⟩ := hp
  have hι := map_opensSiteObjectInclusion B S hS U L
  have : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
      (opensSiteObjectInclusion B S hS U L)) := by
    rw [hι]
    exact (inferInstance : Etale L.ι)
  have : _root_.AlgebraicGeometry.IsSeparated ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
      (opensSiteObjectInclusion B S hS U L)) := by
    rw [hι]
    exact (inferInstance : _root_.AlgebraicGeometry.IsSeparated L.ι)
  rw [Functor.map_comp]
  constructor <;> infer_instance

/-- The degree property of a descending chain `D` of open subspaces of `X` relative
to a morphism `a : h_A ⟶ X`: a point of the `p`-th member of the chain, presented by
any field-valued point `z` of `X`, admits a field-valued extension `r` of `z` over
which `a` has at least `p + 1` distinct points. -/
def HasDistinctChartPoints
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {A : AlgebraicGeometry.BigFppfOver B S hS} (a : yoneda.obj A ⟶ X)
    (D : ℕ → Subfunctor X) : Prop :=
  ∀ (p : ℕ) (x : AlgebraicGeometry.Space.points B S hS X),
    x ∈ Set.range (AlgebraicGeometry.Space.pointsMap B S hS (D p).toFunctor (D p).ι) →
    ∀ z : AlgebraicGeometry.Space.FieldValuedPoint B S hS X,
      z.class B S hS X = x →
      ∃ (r : AlgebraicGeometry.Space.FieldValuedPoint B S hS X)
        (e : r.siteObject B S hS X ⟶ z.siteObject B S hS X)
        (c : Fin (p + 1) → (r.siteObject B S hS X ⟶ A)),
        AlgebraicGeometry.Space.fieldMorphism B S hS X r =
            yoneda.map e ≫ AlgebraicGeometry.Space.fieldMorphism B S hS X z ∧
          Function.Injective c ∧
          ∀ j, yoneda.map (c j) ≫ a = AlgebraicGeometry.Space.fieldMorphism B S hS X r

/-- The degree filtration of a quasi-compact algebraic space by the open
subspaces where the fibre of a fixed affine étale atlas has at least `p + 1`
points, together with the separated symmetric-power étale covers of its steps. -/
theorem exists_degreeFiltration_symmetricPower_cover_of_quasiCompact
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (A : AlgebraicGeometry.BigFppfOver B S hS) (a : yoneda.obj A ⟶ X)
    (hA : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj A))
    (haSurj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a)
    (haEtale : AlgebraicGeometry.Space.IsEtale B S hS a) :
    ∃ (D : ℕ → Subfunctor X)
      (V : ℕ → AlgebraicGeometry.BigFppfOver B S hS)
      (h : ∀ p, yoneda.obj (V p) ⟶ (D p).toFunctor),
      D 0 = ⊤ ∧
      (∀ p, D (p + 1) ≤ D p) ∧
      (∀ p, AlgebraicGeometry.Space.IsOpenSubspace B S hS (D p)) ∧
      (AlgebraicGeometry.Space.IsQuasiCompact B S hS a →
        ∀ p, CompactSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (V p))) ∧
      (∀ p, Scheme.IsSeparated
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (V p))) ∧
      (∀ p, (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf (h p)) ∧
      (∀ p, AlgebraicGeometry.Space.IsEtale B S hS (h p)) ∧
      (∀ (p : ℕ) (Z : Subfunctor (D p).toFunctor),
        AlgebraicGeometry.Space.IsClosedSubspace B S hS Z →
        AlgebraicGeometry.Space.HasEtaleLocalProperty B S hS Z.toFunctor
          (fun Y : Scheme.{u} => IsReduced Y) →
        Set.range (AlgebraicGeometry.Space.pointsMap B S hS Z.toFunctor (Z.ι ≫ (D p).ι)) =
          Set.range (AlgebraicGeometry.Space.pointsMap B S hS (D p).toFunctor (D p).ι) \
            Set.range (AlgebraicGeometry.Space.pointsMap B S hS (D (p + 1)).toFunctor
              (D (p + 1)).ι) →
        IsIso (pullback.fst Z.ι (h p))) ∧
      HasDistinctChartPoints B S hS a D := by
  have haRep := hX.diagonal_representable.of_diag a
  have haCompact : CompactSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj A) :=
    Scheme.compactSpace_of_isAffine _
  have haAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS A
  have haOpen :=
    AlgebraicGeometry.Space.isOpenImmersion_diagonal_of_isUnramified B S hS haAlg hX a
      (AlgebraicGeometry.Space.isUnramified_of_isEtale B S hS haEtale)
  have haClosed := AlgebraicGeometry.Space.isSeparated_of_isEtale_of_scheme_isSeparated
    B S hS X hX A (inferInstance) a haEtale
  have haRepresentablySeparated :
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsSeparated.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a :=
    (AlgebraicGeometry.Space.isSeparated_iff_presheaf
      B S hS a haAlg hX haRep).mp haClosed
  have hLoci (haQuasiCompact : AlgebraicGeometry.Space.IsQuasiCompact B S hS a) :=
    compact_distinctFiberPowerLocus B S hS a haRep haQuasiCompact
      haCompact haOpen haClosed
  have haRepresentablyEtale := presheaf_etale_of_isEtale B S hS haEtale
  have hPowerBase (n : ℕ) :=
    etale_separated_fiberPowerBaseProjection B S hS a haRep
      haRepresentablyEtale haRepresentablySeparated n
  have hPowerEtale := etale_fiberPower B S hS a haRep haRepresentablyEtale
  let W (n : ℕ) := opensSiteObject B S hS (fiberPower a haRep n).1
    (distinctFiberPowerLocus B S hS a haRep haOpen haClosed n)
  let w (n : ℕ) : yoneda.obj (W n) ⟶ X :=
    yoneda.map (opensSiteObjectInclusion B S hS (fiberPower a haRep n).1
      (distinctFiberPowerLocus B S hS a haRep haOpen haClosed n)) ≫
        (fiberPower a haRep n).2
  let toA (n : ℕ) : W n ⟶ A :=
    opensSiteObjectInclusion B S hS (fiberPower a haRep n).1
      (distinctFiberPowerLocus B S hS a haRep haOpen haClosed n) ≫
        fiberPowerBaseProjection a haRep n
  have hToA (n : ℕ) :
      Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (toA n)) ∧
      _root_.AlgebraicGeometry.IsSeparated
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (toA n)) :=
    etale_separated_map_opensSiteObjectInclusion_comp B S hS _ _ (hPowerBase n)
  have hWEtaleRepresentably (n : ℕ) :
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf (w n) :=
    etale_distinctFiberPowerLocus B S hS a haRep haOpen haClosed
      haRepresentablyEtale n
  have hWEtale (n : ℕ) : AlgebraicGeometry.Space.IsEtale B S hS (w n) :=
    isEtale_of_representablyEtale B S hS (w n) (hWEtaleRepresentably n)
  let action (n : ℕ) : Equiv.Perm (Fin (n + 1)) →* End (W n) :=
    distinctFiberPowerSiteAction B S hS a haRep haOpen haClosed n
  let actionAut (n : ℕ) : Equiv.Perm (Fin (n + 1)) →* Aut (W n) :=
    (Aut.unitsEndEquivAut (W n)).toMonoidHom.comp (action n).toHomUnits
  let schemeAction (n : ℕ) : Equiv.Perm (Fin (n + 1)) →*
      Aut ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (W n)) :=
    ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapAut (W n)).comp (actionAut n)
  have hWCompact (haQuasiCompact : AlgebraicGeometry.Space.IsQuasiCompact B S hS a) (n : ℕ) :
      CompactSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (W n)) :=
    hLoci haQuasiCompact n
  have hWSeparated (n : ℕ) :
      Scheme.IsSeparated ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (W n)) := by
    let q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
    let : Scheme.IsSeparated (q.obj A) := inferInstance
    let : _root_.AlgebraicGeometry.IsSeparated (q.map (toA n)) := (hToA n).2
    have h : _root_.AlgebraicGeometry.IsSeparated
      (q.map (toA n) ≫ terminal.from (q.obj A)) := inferInstance
    rw [terminal.comp_from] at h
    exact ⟨h⟩
  have hOrbitAffine (n : ℕ)
      (Z : Set ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (W n)))
      (hZnonempty : Z.Nonempty) :
      ∃ x ∈ Z, ∃ D : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (W n)).Opens,
        IsAffineOpen D ∧ ∀ σ : Equiv.Perm (Fin (n + 1)),
          ((schemeAction n σ).hom.base x) ∈ D := by
    let q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
    let : IsAffine (q.obj A) := hA
    let : Etale (q.map (toA n)) := (hToA n).1
    let : _root_.AlgebraicGeometry.IsSeparated (q.map (toA n)) := (hToA n).2
    let : LocallyOfFiniteType (q.map (toA n)) :=
      (AlgebraicGeometry.locallyQuasiFinite_of_etale
        (q.map (toA n))).1
    let : LocallyQuasiFinite (q.map (toA n)) :=
      (AlgebraicGeometry.locallyQuasiFinite_of_etale
        (q.map (toA n))).2
    exact exists_affineOpen_containing_finiteOrbit (schemeAction n)
      (q.map (toA n)) Z hZnonempty
  have hActionOver (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
      yoneda.map (action n σ) ≫ w n = w n :=
    distinctFiberPowerPermute_comp_structureMap B S hS a haRep haOpen haClosed n σ.symm
  have hFree (n : ℕ) (T : AlgebraicGeometry.BigFppfOver B S hS) (g : T ⟶ W n)
      (hT : Nonempty ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T)) :
      Function.Injective (fun σ ↦ g ≫ action n σ) :=
    injective_distinctFiberPowerSiteAction B S hS a haRep haOpen haClosed n g hT
  let overAction (n : ℕ) : Equiv.Perm (Fin (n + 1)) →*
      Aut ((Over.post B.inclusion).obj (W n)) :=
    ((Over.post B.inclusion).mapAut (W n)).comp (actionAut n)
  have hResidue (n : ℕ) :
      AlgebraicGeometry.Space.ActsNontriviallyOnFixedResidueFields
        ((Over.post B.inclusion).obj (W n)) (Equiv.Perm (Fin (n + 1)))
        (overAction n) :=
    residueFieldFaithful_of_siteFree B S hS (W n) (Equiv.Perm (Fin (n + 1))) (actionAut n)
      (hFree n)
  let groupoid (n : ℕ) : Stacks.Groupoids.GroupoidScheme S :=
    actionGroupoid ((Over.post B.inclusion).obj (W n))
      (Equiv.Perm (Fin (n + 1))) (overAction n) (hResidue n)
  have hGroupoidObjects (n : ℕ) :
      (groupoid n).objects = (Over.post B.inclusion).obj (W n) :=
    (actionGroupoid_extendsRelation ((Over.post B.inclusion).obj (W n))
      (Equiv.Perm (Fin (n + 1))) (overAction n) (hResidue n)).objects_eq
  have hGroupoidFiniteLocallyFree (n : ℕ) :
      Stacks.Morphisms.IsFiniteLocallyFree (groupoid n).source.left ∧
        Stacks.Morphisms.IsFiniteLocallyFree (groupoid n).target.left :=
    actionGroupoid_finiteLocallyFree _ _ _ (hResidue n)
  have hGroupoidRelation (n : ℕ) :
      IsEquivalenceRelation (groupoid n).target (groupoid n).source :=
    actionGroupoid_isEquivalenceRelation _ _ _ (hResidue n)
  have hGroupoidOrbitAffine (n : ℕ) :
      ∀ Z : Set (groupoid n).objects.left, IsClosed Z → Z.Nonempty →
        ∃ x ∈ Z, ∃ D : (groupoid n).objects.left.Opens,
          IsAffineOpen D ∧ ∀ r : (groupoid n).arrows.left,
            (groupoid n).source.left.base r = x →
              (groupoid n).target.left.base r ∈ D := by
    let : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj A) := hA
    have := (hToA n).1
    have := (hToA n).2
    exact groupoid_exists_affineOpen_containing_orbit (groupoid n)
      (T := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (W n))
      (eqToIso (congrArg Over.left (hGroupoidObjects n)))
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (toA n))
      (hGroupoidFiniteLocallyFree n).1
  have hGroupoidCompact (haQuasiCompact : AlgebraicGeometry.Space.IsQuasiCompact B S hS a)
      (n : ℕ) : CompactSpace (groupoid n).objects.left := by
    rw [hGroupoidObjects n]
    exact hWCompact haQuasiCompact n
  have hGroupoidSeparated (n : ℕ) : (groupoid n).objects.left.IsSeparated := by
    rw [hGroupoidObjects n]
    exact hWSeparated n
  let quotient (n : ℕ) : Stacks.Groupoids.FiniteFlatQuotient (groupoid n) := by
    have : Stacks.Morphisms.IsFiniteLocallyFree (groupoid n).source.left :=
      (hGroupoidFiniteLocallyFree n).1
    have : Stacks.Morphisms.IsFiniteLocallyFree (groupoid n).target.left :=
      (hGroupoidFiniteLocallyFree n).2
    exact finiteFlatQuotientOfAffineOrbits (groupoid n)
      (hGroupoidRelation n) (hGroupoidOrbitAffine n)
  have hGroupoidTargetEtale (n : ℕ) : Etale (groupoid n).target.left :=
    actionGroupoid_etale_target _ _ _ (hResidue n)
  have hQuotientMapEtale (n : ℕ) : Etale (quotient n).quotientMap.left :=
    etale_quotientMap_of_etale_target (quotient n) (hGroupoidTargetEtale n)
  have hQuotientCompact (haQuasiCompact : AlgebraicGeometry.Space.IsQuasiCompact B S hS a)
      (n : ℕ) : CompactSpace (quotient n).space.left :=
    compactSpace_of_finiteFlatQuotient (quotient n) (hGroupoidCompact haQuasiCompact n)
  have hQuotientSeparated (n : ℕ) : (quotient n).space.left.IsSeparated :=
    Stacks.Groupoids.FiniteFlatQuotient.isSeparated_space (quotient n) (hGroupoidSeparated n)
  have hQuotientSite (n : ℕ) : B.Contains (quotient n).space.left :=
    contains_space_of_finiteFlatQuotient B (quotient n) (by
      rw [hGroupoidObjects n]
      exact (W n).left.property)
  have hRelationSite (n : ℕ) : B.Contains (groupoid n).arrows.left := by
    let U : Over S := (Over.post B.inclusion).obj (W n)
    let G := Equiv.Perm (Fin (n + 1))
    have harrows : (groupoid n).arrows = AlgebraicGeometry.Space.actionRelationScheme U G :=
      (actionGroupoid_extendsRelation U G (overAction n) (hResidue n)).arrows_eq
    rw [congrArg Over.left harrows]
    exact actionRelationScheme_mem_site B S hS (W n) G
  let V (n : ℕ) : AlgebraicGeometry.BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (quotient n).space.hom :
      B.obj (hQuotientSite n) ⟶ B.obj hS)
  let quotientSiteIso (n : ℕ) : (Over.post B.inclusion).obj (V n) ≅
      (quotient n).space := Over.isoMk (Iso.refl _) (by
        show 𝟙 _ ≫ (quotient n).space.hom = (quotient n).space.hom
        exact Category.id_comp _)
  let quotientSiteMap (n : ℕ) : W n ⟶ V n :=
    (Over.post B.inclusion).preimage
      (eqToHom (hGroupoidObjects n).symm ≫ (quotient n).quotientMap ≫
        (quotientSiteIso n).inv)
  have hQuotientSiteMap (n : ℕ) :
      (Over.post B.inclusion).map (quotientSiteMap n) =
        eqToHom (hGroupoidObjects n).symm ≫ (quotient n).quotientMap ≫
          (quotientSiteIso n).inv :=
    (Over.post B.inclusion).map_preimage _
  have hQuotientSiteMapSurj (n : ℕ) :
      Surjective ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (quotientSiteMap n)) :=
    map_toScheme_of_post_map_eq B S hS (@Surjective.{u}) (quotientSiteMap n)
      (quotient n).quotientMap (eqToIso (hGroupoidObjects n).symm) (quotientSiteIso n).symm
      (hQuotientSiteMap n) (quotient n).surjective
  have hQuotientSiteMapEtale (n : ℕ) :
      Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (quotientSiteMap n)) :=
    map_toScheme_of_post_map_eq B S hS (@Etale.{u}) (quotientSiteMap n)
      (quotient n).quotientMap (eqToIso (hGroupoidObjects n).symm) (quotientSiteIso n).symm
      (hQuotientSiteMap n) (hQuotientMapEtale n)
  have hQuotientSiteKernelPair (n : ℕ) :
      IsPullback
        (AlgebraicGeometry.Space.actionRelationTarget ((Over.post B.inclusion).obj (W n))
          (Equiv.Perm (Fin (n + 1))) (overAction n))
        (AlgebraicGeometry.Space.actionRelationSource ((Over.post B.inclusion).obj (W n))
          (Equiv.Perm (Fin (n + 1))))
        ((Over.post B.inclusion).map (quotientSiteMap n))
        ((Over.post B.inclusion).map (quotientSiteMap n)) :=
    actionGroupoid_isPullback_of_quotientMap _ _ _ (hResidue n) (quotient n)
      (quotientSiteIso n) _ (hQuotientSiteMap n)
  have hDescend (n : ℕ) : ∃! g : yoneda.obj (V n) ⟶ X,
      yoneda.map (quotientSiteMap n) ≫ g = w n := by
    let G := Equiv.Perm (Fin (n + 1))
    have hR : B.Contains (AlgebraicGeometry.Space.actionRelationScheme
        ((Over.post B.inclusion).obj (W n)) G).left :=
      actionRelationScheme_mem_site B S hS (W n) G
    have : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
        (quotientSiteMap n)) := hQuotientSiteMapEtale n
    apply existsUnique_descent_of_actionRelation B S hS (W n) G hX.isSheaf
      (overAction n) hR (quotientSiteMap n) (hQuotientSiteMapSurj n)
      inferInstance inferInstance
      (fun p₁ p₂ hp ↦ exists_actionRelation_lift B S hS (W n) G
        (overAction n) hR (quotientSiteMap n) (hQuotientSiteKernelPair n) p₁ p₂ hp)
      (w n)
    intro σ
    have heq : (Over.post B.inclusion).preimage ((overAction n σ).hom) =
        action n σ := by
      apply (Over.post B.inclusion).map_injective
      rw [Functor.map_preimage]
      rfl
    rw [heq]
    exact hActionOver n σ
  choose g hg hgUnique using hDescend
  have hgEtale (n : ℕ) : AlgebraicGeometry.Space.IsEtale B S hS (g n) := by
    apply (AlgebraicGeometry.Space.isEtale_iff_exists_source_chart B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (V n)) hX (g n)).mpr
    refine ⟨W n, yoneda.map (quotientSiteMap n), ?_, ?_, ?_⟩
    · exact presheaf_yoneda_map_of_scheme_property B S hS _ _ (hQuotientSiteMapSurj n)
    · exact presheaf_yoneda_map_of_scheme_property B S hS _ _ (hQuotientSiteMapEtale n)
    · rw [hg]
      exact hWEtale n
  choose D hDopen hDimage using
    fun n ↦ exists_openSubspace_etaleImage B S hS X hX (V n) (g n) (hgEtale n)
  let h (n : ℕ) : yoneda.obj (V n) ⟶ (D n).toFunctor :=
    AlgebraicGeometry.Space.factorThroughEtaleImage B S hS hX (V n) (g n)
      (D n) (hDopen n) (hDimage n)
  have hh (n : ℕ) : h n ≫ (D n).ι = g n :=
    AlgebraicGeometry.Space.factorThroughEtaleImage_comp B S hS hX (V n) (g n)
      (D n) (hDopen n) (hDimage n)
  have hhSurj (n : ℕ) : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf (h n) :=
    AlgebraicGeometry.Space.surjective_factor_through_etaleImage B S hS (V n) (g n)
      (D n) (hDopen n) (hDimage n) (h n) (hh n)
  have hgRepresentablyEtale (n : ℕ) : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf (g n) := by
    apply hgEtale n (V n) (𝟙 _) ?_
    simpa only [CategoryTheory.Functor.map_id] using
      presheaf_yoneda_map_of_scheme_property B S hS (@Etale.{u}) (𝟙 (V n))
        (by rw [CategoryTheory.Functor.map_id]; infer_instance)
  have hhEtale (n : ℕ) : AlgebraicGeometry.Space.IsEtale B S hS (h n) :=
    isEtale_of_representablyEtale B S hS (h n)
      (AlgebraicGeometry.Space.etale_factor_through_etaleImage B S hS (V n) (g n)
        (hgRepresentablyEtale n) (D n) (hDopen n) (h n) (hh n))
  have hDimageW (n : ℕ) :
      Set.range (AlgebraicGeometry.Space.pointsMap B S hS (D n).toFunctor (D n).ι) =
        Set.range (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj (W n)) (w n)) := by
    have hs := (AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective_yoneda B S hS
      (yoneda.obj (V n)) (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (V n))
      (W n) (yoneda.map (quotientSiteMap n))).mp
      (presheaf_yoneda_map_of_scheme_property B S hS _ _ (hQuotientSiteMapSurj n))
    rw [hDimage n, ← hg n, pointsMap_comp, Set.range_comp, hs.range_eq, Set.image_univ]
  let forgetCoordinate (n : ℕ) : W (n + 1) ⟶ W n :=
    openSubschemeMap B S hS
      (distinctFiberPowerLocus B S hS a haRep haOpen haClosed (n + 1))
      (distinctFiberPowerLocus B S hS a haRep haOpen haClosed n)
      (haRep.snd (fiberPower a haRep n).2)
      (mapsTo_distinctFiberPowerLocus_snd B S hS a haRep haOpen haClosed n)
  have hForget (n : ℕ) : yoneda.map (forgetCoordinate n) ≫ w n = w (n + 1) :=
    openSubschemeMap_snd_comp B S hS a haRep haOpen haClosed n
  have hDmono (n : ℕ) : D (n + 1) ≤ D n := by
    apply openSubspace_le_of_range_subset B S hS hX (hDopen (n + 1)) (hDopen n)
    rw [hDimageW, hDimageW, ← hForget, pointsMap_comp]
    exact Set.range_comp_subset_range _ _
  have hLocusZero : distinctFiberPowerLocus B S hS a haRep haOpen haClosed 0 = ⊤ := by
    apply top_unique
    intro x _
    show x ∉ ⋃ ij : {ij : Fin 1 × Fin 1 // ij.1 ≠ ij.2},
      Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
        (haOpen.rep.snd (fiberPowerPair a haRep 0 ij.1.1 ij.1.2)))
    rintro h
    obtain ⟨ij, _⟩ := Set.mem_iUnion.mp h
    exact ij.2 (Subsingleton.elim _ _)
  have hWZeroSurj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf (w 0) := by
    let i := opensSiteObjectInclusion B S hS (fiberPower a haRep 0).1
      (distinctFiberPowerLocus B S hS a haRep haOpen haClosed 0)
    have hiL : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i =
        (distinctFiberPowerLocus B S hS a haRep haOpen haClosed 0).ι :=
      map_opensSiteObjectInclusion B S hS _ _
    have hi : IsIso ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i) := by
      rw [hiL, hLocusZero]
      show IsIso (Scheme.topIso _).hom
      infer_instance
    have hi' : IsIso i := isIso_of_reflects_iso i
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
    exact MorphismProperty.RespectsIso.precomp _ (yoneda.map i) a haSurj
  have hDzero : D 0 = ⊤ := by
    apply openSubspace_eq_top_of_surjective_pointsMap B S hS hX (D 0) (hDopen 0)
    apply Set.range_eq_univ.mp
    rw [hDimageW]
    exact ((AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective_yoneda B S hS X hX
      (W 0) (w 0)).mp hWZeroSurj).range_eq
  have hdegree : HasDistinctChartPoints B S hS a D := by
    intro p x hx z hz
    rw [hDimageW p] at hx
    obtain ⟨y, hy⟩ := hx
    obtain ⟨y, rfl⟩ := Quot.exists_rep y
    have hclass : (AlgebraicGeometry.Space.FieldValuedPoint.map B S hS
        (yoneda.obj (W p)) (w p) y).class B S hS X = z.class B S hS X := by
      rw [hz, ← hy]
      rfl
    obtain ⟨r, ⟨α, hα⟩, ⟨β, hβ⟩⟩ :=
      (AlgebraicGeometry.Space.FieldValuedPoint.class_eq_class_iff B S hS X _ z).mp hclass
    let i := opensSiteObjectInclusion B S hS (fiberPower a haRep p).1
      (distinctFiberPowerLocus B S hS a haRep haOpen haClosed p)
    have hsite : yoneda.map (y.siteHom B S hS ≫ i) ≫ (fiberPower a haRep p).2 =
        AlgebraicGeometry.Space.fieldMorphism B S hS X
          (AlgebraicGeometry.Space.FieldValuedPoint.map B S hS (yoneda.obj (W p)) (w p) y) :=
      AlgebraicGeometry.Space.yoneda_map_siteHom_comp B S hS X y i (fiberPower a haRep p).2
    let c : r.siteObject B S hS X ⟶ (fiberPower a haRep p).1 :=
      α ≫ y.siteHom B S hS ≫ i
    have hcrange : Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map c) ⊆
        distinctFiberPowerLocus B S hS a haRep haOpen haClosed p := by
      have hc : c = (α ≫ y.siteHom B S hS) ≫ i := (Category.assoc _ _ _).symm
      rw [hc]
      exact range_map_comp_opensSiteObjectInclusion B S hS _ (α ≫ y.siteHom B S hS)
    refine ⟨r, β, fun j ↦ c ≫ fiberPowerProjection a haRep p j,
      fieldMorphism_eq_yoneda_map_comp B S hS r z β hβ, ?_, fun j ↦ ?_⟩
    · exact injective_coordinates_of_mapsTo_distinctFiberPowerLocus B S hS a haRep
        haOpen haClosed p c
        (show Nonempty (Spec (.of r.carrier)) from inferInstance) hcrange
    · rw [Functor.map_comp, Category.assoc, fiberPowerProjection_comp,
        fieldMorphism_eq_yoneda_map_comp B S hS r
          (AlgebraicGeometry.Space.FieldValuedPoint.map B S hS (yoneda.obj (W p)) (w p) y)
          α hα,
        ← hsite]
      dsimp only [c]
      rw [Functor.map_comp, Category.assoc]
      rfl
  refine ⟨D, V, h, hDzero, hDmono, hDopen,
    hQuotientCompact, hQuotientSeparated, hhSurj, hhEtale, ?_, hdegree⟩
  intro p Z hZclosed hZreduced hZrange
  have hQAction (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
      action n σ ≫ quotientSiteMap n = quotientSiteMap n := by
    apply (Over.post B.inclusion).map_injective
    rw [Functor.map_comp]
    show (overAction n σ).hom ≫ (Over.post B.inclusion).map (quotientSiteMap n) = _
    have heq := congrArg (fun k ↦ Sigma.ι
      (fun _ : Equiv.Perm (Fin (n + 1)) ↦ (Over.post B.inclusion).obj (W n)) σ ≫ k)
      (hQuotientSiteKernelPair n).w
    simpa only [AlgebraicGeometry.Space.actionRelationTarget,
      AlgebraicGeometry.Space.actionRelationSource,
      ← Category.assoc, Sigma.ι_desc, Category.id_comp] using heq
  let P := pullback Z.ι (h p)
  let π : P ⟶ Z.toFunctor := pullback.fst Z.ι (h p)
  let v : P ⟶ yoneda.obj (V p) := pullback.snd Z.ι (h p)
  have hP : AlgebraicGeometry.IsAlgebraicSpace B S hS P :=
    AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Z.ι (h p) hZclosed.1
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (V p)) (hDopen p).1
  have hπetale : AlgebraicGeometry.Space.IsEtale B S hS π := by
    let Z' : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨Z.toFunctor, hZclosed.1⟩
    let V' : AlgebraicGeometry.AlgebraicSpaces B S hS :=
      ⟨yoneda.obj (V p), AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (V p)⟩
    let D' : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨(D p).toFunctor, (hDopen p).1⟩
    let j' : Z' ⟶ D' := ObjectProperty.homMk Z.ι
    let f' : V' ⟶ D' := ObjectProperty.homMk (h p)
    exact AlgebraicGeometry.Space.isEtale_of_isPullback B S hS _ _ f' j'
      (AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct B S hS j' f').flip (hhEtale p)
  have hπsurj : AlgebraicGeometry.Space.IsSurjective B S hS π := by
    let Q := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
    let := Q.relative_isStableUnderBaseChange (F := yoneda)
    have hs : Q.presheaf π := Q.presheaf.of_isPullback
      (IsPullback.of_hasPullback Z.ι (h p)).flip (hhSurj p)
    exact (AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective
      B S hS hP hZclosed.1 π hs.1).mp hs
  apply isIso_of_etale_surjective_of_fieldValuedPoint_lifts B S hS hP hZclosed.1
    π hπetale hπsurj
  intro z
  let K := pullback π π
  let β₁ : K ⟶ yoneda.obj (V p) := pullback.fst π π ≫ v
  let β₂ : K ⟶ yoneda.obj (V p) := pullback.snd π π ≫ v
  let κ : K ⟶ Z.toFunctor := pullback.fst π π ≫ π
  have hβZ : β₁ ≫ g p = κ ≫ Z.ι ≫ (D p).ι := by
    dsimp only [β₁, κ, v, π]
    simp only [← hh p, Category.assoc, ← pullback.condition_assoc]
  have hβ : β₁ ≫ g p = β₂ ≫ g p := by
    dsimp only [β₁, β₂, v, π]
    simp only [← hh p, Category.assoc, ← pullback.condition_assoc]
  let z₁ := AlgebraicGeometry.Space.FieldValuedPoint.map B S hS K β₁ z
  let z₂ := AlgebraicGeometry.Space.FieldValuedPoint.map B S hS K β₂ z
  have hqsurj : AlgebraicGeometry.Space.IsSurjective B S hS (yoneda.map (quotientSiteMap p)) :=
    (AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective_yoneda B S hS (yoneda.obj (V p))
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (V p))
      (W p) (yoneda.map (quotientSiteMap p))).mp
      (presheaf_yoneda_map_of_scheme_property B S hS _ _ (hQuotientSiteMapSurj p))
  obtain ⟨z₁', e₁, he₁⟩ := exists_fieldValuedPoint_lift_of_surjective B S hS
    (yoneda.map (quotientSiteMap p)) hqsurj z₁
  let z₂' : AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj (V p)) :=
    ⟨z₁'.carrier, z₁'.contained, z₁'.toBase, e₁ ≫ z₂.value⟩
  obtain ⟨z₂'', e₂, he₂⟩ := exists_fieldValuedPoint_lift_of_surjective B S hS
    (yoneda.map (quotientSiteMap p)) hqsurj z₂'
  let E := e₂ ≫ e₁
  let a' := e₂ ≫ z₁'.value
  let b' := z₂''.value
  let z' : AlgebraicGeometry.Space.FieldValuedPoint B S hS K :=
    ⟨z₂''.carrier, z₂''.contained, z₂''.toBase, K.map E.op z.value⟩
  have ha' : a' ≫ quotientSiteMap p = E ≫ z₁.value := by
    show (e₂ ≫ z₁'.value) ≫ quotientSiteMap p = (e₂ ≫ e₁) ≫ z₁.value
    change z₁'.value ≫ quotientSiteMap p = e₁ ≫ z₁.value at he₁
    rw [Category.assoc, he₁, Category.assoc]
  have hb' : b' ≫ quotientSiteMap p = E ≫ z₂.value := by
    change z₂''.value ≫ quotientSiteMap p = e₂ ≫ (e₁ ≫ z₂.value) at he₂
    exact he₂.trans (Category.assoc _ _ _).symm
  have hnat₁ : β₁.app (Opposite.op (z'.siteObject B S hS K)) (K.map E.op z.value) =
      (yoneda.obj (V p)).map E.op (β₁.app (Opposite.op (z.siteObject B S hS K)) z.value) :=
    NatTrans.naturality_apply β₁ E.op z.value
  have hnat₂ : β₂.app (Opposite.op (z'.siteObject B S hS K)) (K.map E.op z.value) =
      (yoneda.obj (V p)).map E.op (β₂.app (Opposite.op (z.siteObject B S hS K)) z.value) :=
    NatTrans.naturality_apply β₂ E.op z.value
  have hv₁ : β₁.app _ z'.value = a' ≫ quotientSiteMap p := by
    show β₁.app (Opposite.op (z'.siteObject B S hS K)) (K.map E.op z.value) = _
    refine hnat₁.trans ?_
    show E ≫ z₁.value = _
    exact ha'.symm
  have hv₂ : β₂.app _ z'.value = b' ≫ quotientSiteMap p := by
    show β₂.app (Opposite.op (z'.siteObject B S hS K)) (K.map E.op z.value) = _
    refine hnat₂.trans ?_
    show E ≫ z₂.value = _
    exact hb'.symm
  have hab : yoneda.map a' ≫ w p = yoneda.map b' ≫ w p := by
    simp only [← hg p, ← Category.assoc, ← Functor.map_comp]
    apply yonedaEquiv.injective
    simp only [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    rw [← hv₁, ← hv₂]
    exact congrArg (fun t ↦ t.app _ z'.value) hβ
  obtain hperm | ⟨l, hl⟩ := exists_perm_or_distinctFiberPower_succ B S hS
    (T := z₂''.siteObject B S hS _) a haRep haOpen haClosed p
    (show Subsingleton (Spec (.of z₂''.carrier)) from inferInstance)
    (show Nonempty (Spec (.of z₂''.carrier)) from inferInstance)
    a' b' (by simpa only [Functor.map_comp, Category.assoc] using hab)
  · obtain ⟨σ, hσ⟩ := hperm
    have hqeq : a' ≫ quotientSiteMap p = b' ≫ quotientSiteMap p := by
      change a' ≫ action p σ = b' at hσ
      rw [← hσ, Category.assoc a' (action p σ), hQAction]
    refine ⟨z', E, rfl, ?_⟩
    apply pullback.hom_ext
    · show (yonedaEquiv.symm z'.value ≫ pullback.fst π π) ≫ π =
        (yonedaEquiv.symm z'.value ≫ pullback.snd π π) ≫ π
      rw [Category.assoc, Category.assoc, pullback.condition]
    · apply yonedaEquiv.injective
      simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
      show β₁.app _ z'.value = β₂.app _ z'.value
      rw [hv₁, hv₂, hqeq]
  · let zZ := AlgebraicGeometry.Space.FieldValuedPoint.map B S hS K κ z'
    let zL : AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj (W (p + 1))) :=
      ⟨z₂''.carrier, z₂''.contained, z₂''.toBase, l⟩
    have hbaseZ : yoneda.map a' ≫ w p =
        (yonedaEquiv (X := z₂''.siteObject B S hS _) (F := Z.toFunctor)).symm zZ.value ≫
          Z.ι ≫ (D p).ι := by
      rw [← hg p, ← Category.assoc, ← Functor.map_comp]
      apply yonedaEquiv.injective
      simp only [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
      rw [← hv₁]
      simpa only [NatTrans.comp_app, types_comp_apply, Equiv.apply_symm_apply, zZ,
        AlgebraicGeometry.Space.FieldValuedPoint.map,
        AlgebraicGeometry.Space.FieldValuedPoint.siteObject]
        using congrArg (fun t ↦ t.app _ z'.value) hβZ
    have hl' : yoneda.map l ≫ w (p + 1) =
        (yonedaEquiv (X := z₂''.siteObject B S hS _) (F := Z.toFunctor)).symm zZ.value ≫
          Z.ι ≫ (D p).ι :=
      (show yoneda.map l ≫ w (p + 1) = yoneda.map a' ≫ w p by
        simpa only [Functor.map_comp, Category.assoc] using hl).trans hbaseZ
    have hpoints : AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj (W (p + 1)))
        (w (p + 1)) zL.class =
      AlgebraicGeometry.Space.pointsMap B S hS Z.toFunctor (Z.ι ≫ (D p).ι) zZ.class := by
      apply congrArg (fun t : X.obj (Opposite.op (z₂''.siteObject B S hS (yoneda.obj (W p)))) ↦
        (⟨z₂''.carrier, z₂''.contained, z₂''.toBase, t⟩ :
          AlgebraicGeometry.Space.FieldValuedPoint B S hS X).class)
      have hval := congrArg yonedaEquiv hl'
      simp only [yonedaEquiv_comp, yonedaEquiv_yoneda_map,
        Equiv.apply_symm_apply, zZ, z', AlgebraicGeometry.Space.FieldValuedPoint.map,
        AlgebraicGeometry.Space.FieldValuedPoint.siteObject] at hval
      exact hval
    have hx : AlgebraicGeometry.Space.pointsMap B S hS Z.toFunctor (Z.ι ≫ (D p).ι) zZ.class ∈
        Set.range (AlgebraicGeometry.Space.pointsMap B S hS (D p).toFunctor (D p).ι) \
        Set.range (AlgebraicGeometry.Space.pointsMap B S hS (D (p + 1)).toFunctor
          (D (p + 1)).ι) := by
      rw [← hZrange]
      exact ⟨zZ.class, rfl⟩
    exact (hx.2 (by rw [hDimageW]; exact ⟨zL.class, hpoints⟩)).elim

/-! ### Site-level facts and the symmetric power of an affine étale chart -/

/-- A morphism of presheaves on the big fppf site that is representably étale is étale. -/
alias isEtale_of_presheaf_inverseImage_etale := isEtale_of_representablyEtale

/-- A section of an fppf sheaf over the source of a surjective flat morphism of finite
presentation whose two pullbacks agree descends uniquely to the target. -/
alias existsUnique_map_eq_of_surjective_flat_locallyOfFinitePresentation := exists_unique_descent_along_fppf_cover

/-- A morphism of the site whose underlying image lies in the image of an open immersion of the
site factors through it. -/
alias exists_comp_eq_of_isOpenImmersion_of_range_subset := exists_lift_of_isOpenImmersion_range_subset

/-- Let `a : A ⟶ X` be an étale morphism from
an affine object of the site into an algebraic space `X` over `S`, and let `n : ℕ`. There are an
object `V` of the site, étale over `X` by a morphism `g`, and an object `W` of the site with a
morphism `π : W ⟶ V` and `n + 1` coordinate morphisms `pr i : W ⟶ A` such that:

* each coordinate lies over `π ≫ g`;
* the symmetric group on `n + 1` letters acts on `W` by permuting the coordinates, and `π` is
  invariant for that action;
* a morphism into `W` is determined by its coordinates;
* a family of `n + 1` pairwise distinct morphisms `T ⟶ A` lying over a single morphism
  `T ⟶ X`, with `T` of subsingleton underlying space, is the family of coordinates of a
  morphism `T ⟶ W`. -/
theorem exists_symmetricPower_etaleChart
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {A : BigFppfOver B S hS} (a : yoneda.obj A ⟶ X)
    (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj A))
    (haEtale : IsEtale B S hS a) (n : ℕ) :
    ∃ (V W : BigFppfOver B S hS) (π : W ⟶ V) (g : yoneda.obj V ⟶ X)
      (pr : Fin (n + 1) → (W ⟶ A)) (act : Equiv.Perm (Fin (n + 1)) → (W ⟶ W)),
      IsEtale B S hS g ∧
      (∀ i, yoneda.map (pr i) ≫ a = yoneda.map π ≫ g) ∧
      (∀ σ, act σ ≫ π = π) ∧
      (∀ σ i, act σ ≫ pr i = pr (σ i)) ∧
      (∀ (T : BigFppfOver B S hS) (s t : T ⟶ W),
        (∀ i, s ≫ pr i = t ≫ pr i) → s = t) ∧
      (∀ (T : BigFppfOver B S hS) (y : yoneda.obj T ⟶ X) (c : Fin (n + 1) → (T ⟶ A)),
        Subsingleton ((BigFppfOver.toScheme B S hS).obj T) → Function.Injective c →
        (∀ i, yoneda.map (c i) ≫ a = y) →
        ∃ t : T ⟶ W, ∀ i, t ≫ pr i = c i) := by
  classical
  let : IsAffine ((BigFppfOver.toScheme B S hS).obj A) := hA
  have haRep := hX.diagonal_representable.of_diag a
  have haAlg := isAlgebraicSpace_yoneda B S hS A
  have haOpen := isOpenImmersion_diagonal_of_isUnramified B S hS haAlg hX a
    (isUnramified_of_isEtale B S hS haEtale)
  have haClosed := isSeparated_of_isEtale_of_scheme_isSeparated B S hS X hX A
    inferInstance a haEtale
  have haRepresentablySeparated :
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsSeparated.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a :=
    (isSeparated_iff_presheaf B S hS a haAlg hX haRep).mp haClosed
  have haRepresentablyEtale := presheaf_etale_of_isEtale B S hS haEtale
  have hPowerBase := etale_separated_fiberPowerBaseProjection B S hS a haRep
    haRepresentablyEtale haRepresentablySeparated n
  set L := distinctFiberPowerLocus B S hS a haRep haOpen haClosed n with hLdef
  set W : BigFppfOver B S hS := opensSiteObject B S hS (fiberPower a haRep n).1 L with hWdef
  set incl : W ⟶ (fiberPower a haRep n).1 :=
    opensSiteObjectInclusion B S hS (fiberPower a haRep n).1 L with hincldef
  set w : yoneda.obj W ⟶ X := yoneda.map incl ≫ (fiberPower a haRep n).2 with hwdef
  set pr : Fin (n + 1) → (W ⟶ A) := fun i ↦ incl ≫ fiberPowerProjection a haRep n i with hprdef
  have hext (T : BigFppfOver B S hS) (s t : T ⟶ W) (h : ∀ i, s ≫ pr i = t ≫ pr i) : s = t := by
    have hmono : Mono incl := by
      refine (BigFppfOver.toScheme B S hS).mono_of_mono_map (f := incl) ?_
      rw [hincldef, map_opensSiteObjectInclusion]
      exact (inferInstance : Mono L.ι)
    refine (cancel_mono incl).mp (fiberPower_hom_ext a haRep n fun i ↦ ?_)
    simpa only [Category.assoc] using h i
  have hFree (T : BigFppfOver B S hS) (gT : T ⟶ W)
      (hT : Nonempty ((BigFppfOver.toScheme B S hS).obj T)) :
      Function.Injective fun σ ↦ gT ≫ distinctFiberPowerSiteAction B S hS a haRep
        haOpen haClosed n σ :=
    injective_distinctFiberPowerSiteAction B S hS a haRep haOpen haClosed n gT hT
  set action : Equiv.Perm (Fin (n + 1)) →* End W :=
    distinctFiberPowerSiteAction B S hS a haRep haOpen haClosed n with hactiondef
  set actionAut : Equiv.Perm (Fin (n + 1)) →* Aut W :=
    (Aut.unitsEndEquivAut W).toMonoidHom.comp action.toHomUnits with hactionAutdef
  set overAction : Equiv.Perm (Fin (n + 1)) →* Aut ((Over.post B.inclusion).obj W) :=
    ((Over.post B.inclusion).mapAut W).comp actionAut with hoverActiondef
  have hResidue : ActsNontriviallyOnFixedResidueFields ((Over.post B.inclusion).obj W)
      (Equiv.Perm (Fin (n + 1))) overAction :=
    residueFieldFaithful_of_siteFree B S hS W (Equiv.Perm (Fin (n + 1))) actionAut hFree
  set groupoid : Stacks.Groupoids.GroupoidScheme S :=
    actionGroupoid ((Over.post B.inclusion).obj W) (Equiv.Perm (Fin (n + 1)))
      overAction hResidue with hgroupoiddef
  have hGroupoidObjects : groupoid.objects = (Over.post B.inclusion).obj W :=
    (actionGroupoid_extendsRelation ((Over.post B.inclusion).obj W)
      (Equiv.Perm (Fin (n + 1))) overAction hResidue).objects_eq
  have hToA : Etale ((BigFppfOver.toScheme B S hS).map (incl ≫ fiberPowerBaseProjection a haRep n))
      ∧ _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map
        (incl ≫ fiberPowerBaseProjection a haRep n)) :=
    etale_separated_map_opensSiteObjectInclusion_comp B S hS L _ hPowerBase
  have hGroupoidFiniteLocallyFree :
      Stacks.Morphisms.IsFiniteLocallyFree groupoid.source.left ∧
        Stacks.Morphisms.IsFiniteLocallyFree groupoid.target.left :=
    actionGroupoid_finiteLocallyFree _ _ _ hResidue
  have hGroupoidRelation : IsEquivalenceRelation groupoid.target groupoid.source :=
    actionGroupoid_isEquivalenceRelation _ _ _ hResidue
  have hGroupoidOrbitAffine :
      ∀ Z : Set groupoid.objects.left, IsClosed Z → Z.Nonempty →
        ∃ x ∈ Z, ∃ D : groupoid.objects.left.Opens,
          IsAffineOpen D ∧ ∀ r : groupoid.arrows.left,
            groupoid.source.left.base r = x → groupoid.target.left.base r ∈ D := by
    have := hToA.1
    have := hToA.2
    exact groupoid_exists_affineOpen_containing_orbit groupoid
      (T := (BigFppfOver.toScheme B S hS).obj W)
      (eqToIso (congrArg Over.left hGroupoidObjects))
      ((BigFppfOver.toScheme B S hS).map (incl ≫ fiberPowerBaseProjection a haRep n))
      hGroupoidFiniteLocallyFree.1
  set quot : Stacks.Groupoids.FiniteFlatQuotient groupoid := by
    have : Stacks.Morphisms.IsFiniteLocallyFree groupoid.source.left :=
      hGroupoidFiniteLocallyFree.1
    have : Stacks.Morphisms.IsFiniteLocallyFree groupoid.target.left :=
      hGroupoidFiniteLocallyFree.2
    exact finiteFlatQuotientOfAffineOrbits groupoid hGroupoidRelation hGroupoidOrbitAffine
    with hquotdef
  have hGroupoidTargetEtale : Etale groupoid.target.left :=
    actionGroupoid_etale_target _ _ _ hResidue
  have hQuotientMapEtale : Etale quot.quotientMap.left :=
    etale_quotientMap_of_etale_target quot hGroupoidTargetEtale
  have hQuotientSite : B.Contains quot.space.left :=
    contains_space_of_finiteFlatQuotient B quot (by
      rw [hGroupoidObjects]
      exact W.left.property)
  set V : BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk quot.space.hom : B.obj hQuotientSite ⟶ B.obj hS) with hVdef
  set quotientSiteIso : (Over.post B.inclusion).obj V ≅ quot.space :=
    Over.isoMk (Iso.refl _) (by
      show 𝟙 _ ≫ quot.space.hom = quot.space.hom
      exact Category.id_comp _) with hqsIsodef
  set π : W ⟶ V := (Over.post B.inclusion).preimage
    (eqToHom hGroupoidObjects.symm ≫ quot.quotientMap ≫ quotientSiteIso.inv) with hpidef
  have hπ : (Over.post B.inclusion).map π =
      eqToHom hGroupoidObjects.symm ≫ quot.quotientMap ≫ quotientSiteIso.inv :=
    (Over.post B.inclusion).map_preimage _
  have hπSurj : Surjective ((BigFppfOver.toScheme B S hS).map π) :=
    map_toScheme_of_post_map_eq B S hS (@Surjective.{u}) π quot.quotientMap
      (eqToIso hGroupoidObjects.symm) quotientSiteIso.symm hπ quot.surjective
  have hπEtale : Etale ((BigFppfOver.toScheme B S hS).map π) :=
    map_toScheme_of_post_map_eq B S hS (@Etale.{u}) π quot.quotientMap
      (eqToIso hGroupoidObjects.symm) quotientSiteIso.symm hπ hQuotientMapEtale
  have hπKernelPair :
      IsPullback
        (actionRelationTarget ((Over.post B.inclusion).obj W)
          (Equiv.Perm (Fin (n + 1))) overAction)
        (actionRelationSource ((Over.post B.inclusion).obj W) (Equiv.Perm (Fin (n + 1))))
        ((Over.post B.inclusion).map π) ((Over.post B.inclusion).map π) :=
    actionGroupoid_isPullback_of_quotientMap _ _ _ hResidue quot quotientSiteIso _ hπ
  have hmapAction (τ : Equiv.Perm (Fin (n + 1))) :
      (Over.post B.inclusion).map (action τ) = (overAction τ).hom := rfl
  have hactionπ (τ : Equiv.Perm (Fin (n + 1))) : action τ ≫ π = π := by
    have hι := congrArg (fun k ↦ Sigma.ι (fun _ : Equiv.Perm (Fin (n + 1)) ↦
      (Over.post B.inclusion).obj W) τ ≫ k) hπKernelPair.w
    simp only [← Category.assoc, actionRelationTarget, actionRelationSource,
      Sigma.ι_desc] at hι
    apply (Over.post B.inclusion).map_injective
    rw [CategoryTheory.Functor.map_comp, hmapAction]
    simpa only [Category.id_comp] using hι
  have hactionincl (τ : Equiv.Perm (Fin (n + 1))) :
      action τ ≫ incl = incl ≫ fiberPowerPermute a haRep n τ.symm :=
    openSubschemeMap_inclusion B S hS L L (fiberPowerPermute a haRep n τ.symm)
      (mapsTo_distinctFiberPowerLocus B S hS a haRep haOpen haClosed n τ.symm)
  set act : Equiv.Perm (Fin (n + 1)) → (W ⟶ W) := fun σ ↦ action σ⁻¹ with hactdef
  have hsymmInv (σ : Equiv.Perm (Fin (n + 1))) : (σ⁻¹).symm = σ := by
    simp [Equiv.Perm.inv_def]
  have hactpr (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) : act σ ≫ pr i = pr (σ i) := by
    rw [hactdef, hprdef, ← Category.assoc, hactionincl, Category.assoc,
      fiberPowerPermute_projection, hsymmInv]
  have hwInvariant (τ : Equiv.Perm (Fin (n + 1))) : yoneda.map (action τ) ≫ w = w :=
    distinctFiberPowerPermute_comp_structureMap B S hS a haRep haOpen haClosed n τ.symm
  have hDescend : ∃! g : yoneda.obj V ⟶ X, yoneda.map π ≫ g = w := by
    have hR : B.Contains (actionRelationScheme ((Over.post B.inclusion).obj W)
        (Equiv.Perm (Fin (n + 1)))).left :=
      actionRelationScheme_mem_site B S hS W (Equiv.Perm (Fin (n + 1)))
    have : Etale ((BigFppfOver.toScheme B S hS).map π) := hπEtale
    apply existsUnique_descent_of_actionRelation B S hS W (Equiv.Perm (Fin (n + 1)))
      hX.isSheaf overAction hR π hπSurj inferInstance inferInstance
      (fun p₁ p₂ hp ↦ exists_actionRelation_lift B S hS W (Equiv.Perm (Fin (n + 1)))
        overAction hR π hπKernelPair p₁ p₂ hp) w
    intro τ
    have heq : (Over.post B.inclusion).preimage ((overAction τ).hom) = action τ := by
      apply (Over.post B.inclusion).map_injective
      rw [Functor.map_preimage]
      exact (hmapAction τ).symm
    rw [heq]
    exact hwInvariant τ
  obtain ⟨g, hg, -⟩ := hDescend
  have hgEtale : IsEtale B S hS g := by
    apply (isEtale_iff_exists_source_chart B S hS (isAlgebraicSpace_yoneda B S hS V) hX g).mpr
    refine ⟨W, yoneda.map π, ?_, ?_, ?_⟩
    · exact presheaf_yoneda_map_of_scheme_property B S hS _ _ hπSurj
    · exact presheaf_yoneda_map_of_scheme_property B S hS _ _ hπEtale
    · rw [hg]
      exact isEtale_of_representablyEtale B S hS w
        (etale_distinctFiberPowerLocus B S hS a haRep haOpen haClosed haRepresentablyEtale n)
  refine ⟨V, W, π, g, pr, act, hgEtale, ?_, fun σ ↦ hactionπ σ⁻¹, hactpr, hext, ?_⟩
  · intro i
    rw [hg, hwdef, hprdef, CategoryTheory.Functor.map_comp, Category.assoc]
    exact congrArg (fun k ↦ yoneda.map incl ≫ k) (fiberPowerProjection_comp a haRep n i)
  · intro T y c hT hcinj hcy
    obtain ⟨m, -, hmpr⟩ := fiberPowerLift a haRep n y c hcy
    have hrange : Set.range ((BigFppfOver.toScheme B S hS).map m) ⊆ L :=
      mapsTo_distinctFiberPowerLocus_of_injective_coordinates B S hS a haRep haOpen haClosed
        n m hT (by simpa only [hmpr] using hcinj)
    have hinclι : (BigFppfOver.toScheme B S hS).map incl = L.ι := by
      rw [hincldef, map_opensSiteObjectInclusion]
    obtain ⟨l, hl⟩ := exists_lift_of_isOpenImmersion_range_subset B S hS incl m
      (by rw [hinclι]; exact (inferInstance : _root_.AlgebraicGeometry.IsOpenImmersion L.ι))
      (by
        rw [hinclι]
        exact hrange.trans (Scheme.Opens.range_ι L).symm.subset)
    exact ⟨l, fun i ↦ by rw [hprdef, ← Category.assoc, hl]; exact hmpr i⟩

end AlgebraicGeometry.Space

end
