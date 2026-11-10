module

public import StacksFrontier.AlgebraicGeometry.Size.FiniteTypeCount
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSheafAtlasCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafRelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBase
public import StacksFrontier.Deformation.Artin.FunctorAxioms
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveTheoryGeometricReduction
public import StacksFrontier.Deformation.Artin.Versality.SmoothChartExistence

/-!
# Artin's criterion for a functor to be an algebraic space (Stacks 07Y1)

-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A smooth morphism of algebraic spaces whose image contains every finite type point of the
target is surjective.** Its image is open, smooth morphisms being universally open, so its
complement is a closed set of points without finite type points, hence empty by Stacks 06EK. -/
theorem isSurjective_of_isSmooth_of_finiteTypePoints_subset
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsSmooth B S hS f)
    (h : finiteTypePoints B S hS Y ⊆ Set.range (pointsMap B S hS X f)) :
    IsSurjective B S hS f := by
  let := pointTopology B S hS X
  let := pointTopology B S hS Y
  have hopen : IsOpenMorphism B S hS f :=
    isOpen_of_universallyOpen B S hS hY f (universallyOpen_of_isSmooth B S hS hX hY f hf)
  have hrange : IsOpen (Set.range (pointsMap B S hS X f)) := by
    rw [← Set.image_univ]
    exact hopen _ isOpen_univ
  intro y
  by_contra hy
  obtain ⟨w, hw, hwft⟩ := inter_finiteTypePoints_nonempty B S hS Y hY
    (T := (Set.range (pointsMap B S hS X f))ᶜ) hrange.isClosed_compl.isLocallyClosed
    ⟨y, fun ⟨x, hx⟩ => hy ⟨x, hx⟩⟩
  exact hw (h hwft)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.BigFppfOver

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An étale covering family of the underlying category of a big fppf site generates a covering
sieve of its étale topology, even when it is not one of the chosen families. -/
theorem generate_mem_etaleTopology {X : B.Schemes} (E : PreZeroHypercover.{u + 1} X)
    (hE : IsEtaleCovering (⟨X, E⟩ : Covering B.Schemes)) :
    Sieve.generate E.presieve₀ ∈ etaleTopology B X := by
  obtain ⟨E', hE', hEquiv⟩ := etaleCovering_has_representative B ⟨X, E⟩ hE
  have hpre : E.presieve₀ ∈ etalePrecoverage B X := by
    obtain ⟨hX, hComb⟩ := hEquiv
    cases hX
    rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hComb]
    exact ⟨E'.2, rfl, hE'⟩
  exact Precoverage.generate_mem_toGrothendieck hpre

/-- A jointly surjective family of open immersions of the big fppf category over `S` generates
a covering sieve of the étale topology. -/
theorem ofArrows_mem_etaleTopology_of_isOpenImmersion {T : BigFppfOver B S hS} {ι : Type u}
    {X : ι → BigFppfOver B S hS} (f : ∀ i, X i ⟶ T)
    (hf : ∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (f i)))
    (hcov : ∀ x : (BigFppfOver.toScheme B S hS).obj T,
      ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (f i))) :
    Sieve.ofArrows X f ∈ (etaleTopology B).over (B.obj hS) T := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  let E : PreZeroHypercover.{u + 1} T.left :=
    ⟨ULift.{u + 1} ι, fun i => (X i.down).left, fun i => (f i.down).left⟩
  have hE : IsEtaleCovering (⟨T.left, E⟩ : Covering B.Schemes) := by
    change Presieve.ofArrows (fun i => B.inclusion.obj (E.X i)) (fun i => B.inclusion.map (E.f i))
      ∈ Scheme.etalePrecoverage (B.inclusion.obj T.left)
    refine (Scheme.ofArrows_mem_precoverage_iff (P := @Etale.{u})).2 ⟨fun x => ?_, fun i => ?_⟩
    · obtain ⟨i, hi⟩ := hcov x
      exact ⟨⟨i⟩, hi⟩
    · have := hf i.down
      exact inferInstanceAs (Etale ((BigFppfOver.toScheme B S hS).map (f i.down)))
  refine (etaleTopology B).superset_covering ?_ (generate_mem_etaleTopology E hE)
  rw [Sieve.generate_le_iff]
  rintro Z g ⟨i⟩
  exact Sieve.ofArrows_mk _ _ i.down

/-- The empty sieve is a covering sieve of the étale topology of an object of the big fppf
category over `S` whose underlying scheme has no points. -/
theorem bot_mem_etaleTopology (Z : BigFppfOver B S hS)
    (hZ : IsEmpty ((BigFppfOver.toScheme B S hS).obj Z)) :
    (⊥ : Sieve Z) ∈ (etaleTopology B).over (B.obj hS) Z := by
  have hbot : (⊥ : Sieve Z) = Sieve.ofArrows (fun i : PEmpty.{u + 1} => Z) (fun i => i.elim) := by
    ext _ _
    exact ⟨fun h => h.elim, fun ⟨_, _, _, ⟨i⟩, _⟩ => i.elim⟩
  rw [hbot]
  exact ofArrows_mem_etaleTopology_of_isOpenImmersion _ (fun i => i.elim)
    fun x => (hZ.false x).elim

/-- **Sections of an étale sheaf glue along a family of pairwise disjoint open subobjects
covering the base**, with no compatibility hypothesis: two members of the family meet only in
an object with no points, over which an étale sheaf has a single section. -/
theorem exists_section_of_disjoint_openCover_etale
    {H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hH : Presieve.IsSheaf ((etaleTopology B).over (B.obj hS)) H)
    {K : Type u} {T : BigFppfOver B S hS} {W : K → BigFppfOver B S hS} (p : ∀ k, W k ⟶ T)
    (hoi : ∀ k, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (p k)))
    (hdisj : ∀ k k', k ≠ k' → ∀ (y : (BigFppfOver.toScheme B S hS).obj (W k))
      (y' : (BigFppfOver.toScheme B S hS).obj (W k')),
      (BigFppfOver.toScheme B S hS).map (p k) y ≠
        (BigFppfOver.toScheme B S hS).map (p k') y')
    (hcov : ∀ t : (BigFppfOver.toScheme B S hS).obj T,
      ∃ k, t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (p k)))
    (σ : ∀ k, H.obj (op (W k))) :
    ∃ τ : H.obj (op T), ∀ k, H.map (p k).op τ = σ k := by
  classical
  have hpmono : ∀ k, Mono (p k) := fun k =>
    have := hoi k
    (BigFppfOver.toScheme B S hS).mono_of_mono_map (IsOpenImmersion.mono _)
  have hindep : ∀ (T' : BigFppfOver B S hS) (k k' : K) (h : T' ⟶ W k) (h' : T' ⟶ W k'),
      h ≫ p k = h' ≫ p k' → H.map h.op (σ k) = H.map h'.op (σ k') := by
    intro T' k k' h h' hcomp
    by_cases hkk' : k = k'
    · subst hkk'
      have := hpmono k
      rw [(cancel_mono (p k)).1 hcomp]
    · have hempty : IsEmpty ((BigFppfOver.toScheme B S hS).obj T') := by
        refine ⟨fun y => ?_⟩
        have h1 := congrArg
          (fun m : (BigFppfOver.toScheme B S hS).obj T' ⟶
            (BigFppfOver.toScheme B S hS).obj T => m y)
          (congrArg (BigFppfOver.toScheme B S hS).map hcomp)
        simp only [Functor.map_comp, Scheme.Hom.comp_apply] at h1
        exact hdisj k k' hkk' _ _ h1
      exact (hH.subsingleton_obj_of_bot_mem _ (bot_mem_etaleTopology T' hempty)).elim _ _
  have hchoice : ∀ (T' : BigFppfOver B S hS) (g : T' ⟶ T), (Sieve.ofArrows W p).arrows g →
      ∃ y : H.obj (op T'), ∀ (k : K) (h : T' ⟶ W k), h ≫ p k = g →
        y = H.map h.op (σ k) := by
    rintro T' g ⟨Z, h, e, ⟨k⟩, hcomp⟩
    exact ⟨H.map h.op (σ k), fun k' h' hh' => hindep T' k k' h h' (hcomp.trans hh'.symm)⟩
  choose yy hyy using hchoice
  set fam : Presieve.FamilyOfElements H (Sieve.ofArrows W p).arrows :=
    fun T' g hg => yy T' g hg with hfamdef
  have hcompat : fam.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro T' T'' g u hg
    obtain ⟨Z, h, e, ⟨k⟩, hcomp⟩ := id hg
    simp only [hfamdef]
    rw [hyy T' g hg k h hcomp,
      hyy T'' (u ≫ g) ((Sieve.ofArrows W p).downward_closed hg u) k (u ≫ h)
        (by rw [Category.assoc, hcomp]),
      ← Functor.map_comp_apply, ← op_comp]
  obtain ⟨τ, hτ, -⟩ := hH _ (ofArrows_mem_etaleTopology_of_isOpenImmersion p hoi hcov) fam hcompat
  refine ⟨τ, fun k => ?_⟩
  refine (hτ (p k) ⟨W k, 𝟙 (W k), p k, ⟨k⟩, Category.id_comp _⟩).trans ?_
  simp only [hfamdef]
  exact (hyy (W k) (p k) _ k (𝟙 (W k)) (Category.id_comp _)).trans (by simp)

end AlgebraicGeometry.BigFppfOver

namespace Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Surjectivity of a chart over an affine test scheme of finite presentation.** Let
`a : h_V ⟶ F` have representable base changes which are smooth, and suppose that every element of
`F` over the spectrum of a field of finite type over `S` is the pullback of the universal element
along a morphism to `V`. Then for every `U` locally of finite presentation over `S` and every
`β : h_U ⟶ F` the base change `h_V ×_F h_U ⟶ h_U` is surjective: a finite type point of `U` is a
field-valued point `Spec K ⟶ U` locally of finite type, so `Spec K` is of finite type over `S`, and
the hypothesis provides the point of the base change over it. -/
theorem isSurjective_pullback_fst_of_cover {V : BigFppfOver B S hS} (a : yoneda.obj V ⟶ F)
    (ha : Space.IsRepresentableByAlgebraicSpaces B S hS a)
    (hsm : Space.HasProperty B S hS (Space.smoothMorphismProperty B S hS) a ha)
    (hcover : ∀ (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
      (toBase : Spec (.of K) ⟶ S), LocallyOfFiniteType toBase →
      ∀ x : F.obj (op (Over.mk (⟨toBase⟩ : B.obj hK ⟶ B.obj hS))),
      ∃ g : (Over.mk (⟨toBase⟩ : B.obj hK ⟶ B.obj hS) : BigFppfOver B S hS) ⟶ V,
        F.map g.op (yonedaEquiv a) = x)
    (U : BigFppfOver B S hS) (hU : LocallyOfFinitePresentation (B.inclusion.map U.hom))
    (β : yoneda.obj U ⟶ F) :
    Space.IsSurjective B S hS (pullback.fst β a) := by
  refine Space.isSurjective_of_isSmooth_of_finiteTypePoints_subset B S hS (ha U β)
    (isAlgebraicSpace_yoneda B S hS U) _ (hsm U β) ?_
  rintro _ ⟨p, rfl, hplft⟩
  let ψ : p.siteObject B S hS (yoneda.obj U) ⟶ U := p.value
  have hψ : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map ψ) :=
    (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget ψ).mp hplft
  have htoBase : p.toBase = (BigFppfOver.toScheme B S hS).map ψ ≫ B.inclusion.map U.hom := by
    have := congrArg B.inclusion.map (Over.w ψ)
    rw [Functor.map_comp] at this
    exact this.symm
  have hlft : LocallyOfFiniteType p.toBase := by
    rw [htoBase]
    infer_instance
  obtain ⟨g, hg⟩ := @hcover p.carrier p.field p.contained p.toBase hlft
    (F.map ψ.op (yonedaEquiv β))
  have hw : yoneda.map ψ ≫ β = yoneda.map g ≫ a := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map,
      ← map_yonedaEquiv, ← map_yonedaEquiv]
    exact hg.symm
  let z : Space.FieldValuedPoint B S hS (pullback β a) :=
    { carrier := p.carrier
      field := p.field
      contained := p.contained
      toBase := p.toBase
      value := yonedaEquiv (pullback.lift (yoneda.map ψ) (yoneda.map g) hw) }
  refine ⟨z.class B S hS (pullback β a), ?_⟩
  rw [Space.pointsMap_class]
  congr 1
  change Space.FieldValuedPoint.mk _ _ _ ((pullback.fst β a).app _ (yonedaEquiv
    (pullback.lift (yoneda.map ψ) (yoneda.map g) hw))) = p
  rw [← yonedaEquiv_comp, pullback.lift_fst, yonedaEquiv_yoneda_map]

/-- **From a smooth chart of `𝒮_F` covering the finite type points to an algebraic space.** Let
`F` be an étale sheaf whose diagonal is representable by algebraic spaces and whose category
fibred in sets `𝒮_F` is limit preserving, and let `t ∈ F(V)` be such that the 1-morphism
`t : (Sch/V)_{fppf} ⟶ 𝒮_F` is smooth and every element of `F` over the spectrum of a field of
finite type over `S` is the pullback of `t` along a morphism to `V`. Then `F` is an algebraic
space.

This is the end of the proof of Stacks 07Y1. By Stacks 0458 and an equivalence of sources, `t` is
the 1-morphism attached to `h_V ⟶ F`, which is therefore smooth (Stacks 045A). It is surjective:
by Stacks 07WI it suffices to test this over affine schemes `U` of finite presentation over `S`,
where it is `Deformation.Artin.isSurjective_pullback_fst_of_cover`. Stacks 07WF concludes. -/
theorem isAlgebraicSpace_of_isRelativelySmooth_objectMorphism_of_cover
    (hF : Presheaf.IsSheaf ((etaleTopology B).over (B.obj hS)) F)
    (hdiag : Space.IsRepresentableByAlgebraicSpaces B S hS (diag F))
    (hlim : IsLimitPreserving.{u, u, u, u + 1, u} B S hS (Stack.fibredCategory B S hS F))
    {V : BigFppfOver B S hS} (t : F.obj (op V))
    (hsm : Stack.IsRelativelySmooth B S hS
      (Stack.objectMorphism B S hS (Stack.fibredCategory B S hS F) (fibredCategoryFiberMk t)))
    (hcover : ∀ (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
      (toBase : Spec (.of K) ⟶ S), LocallyOfFiniteType toBase →
      ∀ x : F.obj (op (Over.mk (⟨toBase⟩ : B.obj hK ⟶ B.obj hS))),
      ∃ g : (Over.mk (⟨toBase⟩ : B.obj hK ⟶ B.obj hS) : BigFppfOver B S hS) ⟶ V,
        F.map g.op t = x) :
    IsAlgebraicSpace B S hS F := by
  let a : yoneda.obj V ⟶ F := yonedaEquiv.symm t
  let e := schemeToElements (B := B) (S := S) (hS := hS) V
  let g := (Stack.associatedMap B S hS a).1
  have ha := Space.isRepresentableByAlgebraicSpaces_of_diagonal B S hS hdiag
    (isAlgebraicSpace_yoneda B S hS V) a
  have hg := (Stack.isRepresentableByAlgebraicSpaces_iff_associatedMap B S hS a).mp ha
  have heq := objectMorphism_fibredCategoryFiberMk (B := B) (S := S) (hS := hS) t
  have := isEquivalence_schemeToElements (B := B) (S := S) (hS := hS) V
  have transfer : ∀ (P : MorphismProperty (AlgebraicSpaces B S hS))
      [P.IsStableUnderBaseChange] [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
      (hf : Stack.IsRepresentableByAlgebraicSpaces B S hS
        (Stack.objectMorphism B S hS (Stack.fibredCategory B S hS F)
          (fibredCategoryFiberMk t)).hom),
      Stack.HasRelativeProperty B S hS P
        (Stack.objectMorphism B S hS (Stack.fibredCategory B S hS F) (fibredCategoryFiberMk t))
        hf →
      Space.HasProperty B S hS P a ha := by
    intro P _ _ hf h
    rw [Stack.holdsOnEverySchemePoint_iff_hasRelativeProperty B S hS P a ha]
    have h' : ∀ (f : Stack.schemeFibredCategory B S hS V ⟶ Stack.fibredCategory B S hS F)
        (hf : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom), f = e ≫ g →
        Stack.HasRelativeProperty B S hS P f hf →
        Stack.HasRelativeProperty B S hS P
          (Bicategory.InducedBicategory.mkHom (BasedFunctor.comp e.hom g.hom))
          ((Stack.isRepresentableByAlgebraicSpaces_comp_iff B S hS
            (Stack.schemeFibredCategory B S hS V) (Stack.fibredCategory B S hS (yoneda.obj V))
            (Stack.fibredCategory B S hS F) g.hom e.hom inferInstance).mp hg) := by
      rintro f hf rfl hP
      exact hP
    exact (Stack.hasRelativeProperty_iff_of_equivalence_source B S hS P g.hom e.hom hg _).mp
      (h' _ hf heq h)
  have hsmF := transfer _ hsm.1 hsm.2
  have hsurj : Space.HasProperty B S hS (Space.surjectiveMorphismProperty B S hS) a ha := by
    rw [Stack.holdsOnEverySchemePoint_iff_hasRelativeProperty B S hS _ a ha]
    refine Stack.hasRelativeProperty_of_affine_locallyOfFinitePresentation.{u, u, u} B S hS _ g _
      (Stack.isLimitPreservingOnObjects_toTerminalCFG_of_isLimitPreserving B S hS _ hlim) ?_
    intro U _ hU y hy H hH ⟨eH⟩
    obtain ⟨β, hβ⟩ := PresheafOfCategories.exists_section_sectionOfBasedFunctor_eq U.hom y hy
    exact (Stack.prop_pullback_iff_prop_representative B S hS _ a ha U y hy H hH eH β hβ).1
      (isSurjective_pullback_fst_of_cover a ha hsmF
        (fun K _ hK toBase hlft x => by simpa [a] using hcover K hK toBase hlft x)
        (Over.mk U.hom) hU β)
  exact Space.isAlgebraicSpace_of_isSheaf_etale_of_smooth_scheme_atlas_unconditional B S hS F hF
    hdiag V a hsurj hsmF

/-- A morphism of schemes between the underlying schemes of two objects of the big fppf category
over `S`, compatible with their structure morphisms, as a morphism of the site. -/
def BigFppfOver.homOfComp {X Y : BigFppfOver B S hS}
    (φ : (BigFppfOver.toScheme B S hS).obj X ⟶ (BigFppfOver.toScheme B S hS).obj Y)
    (hφ : φ ≫ B.inclusion.map Y.hom = B.inclusion.map X.hom) : X ⟶ Y :=
  Over.homMk (B.inclusion.preimage φ) (B.inclusion.map_injective
    (by rwa [Functor.map_comp, B.inclusion.map_preimage]))

/-- The underlying morphism of schemes of `BigFppfOver.homOfComp φ hφ` is `φ`. -/
theorem BigFppfOver.toScheme_map_homOfComp {X Y : BigFppfOver B S hS}
    (φ : (BigFppfOver.toScheme B S hS).obj X ⟶ (BigFppfOver.toScheme B S hS).obj Y)
    (hφ : φ ≫ B.inclusion.map Y.hom = B.inclusion.map X.hom) :
    (BigFppfOver.toScheme B S hS).map (BigFppfOver.homOfComp φ hφ) = φ :=
  B.inclusion.map_preimage φ

/-- Two morphisms of the big fppf category over `S` with the same underlying morphism of schemes
are equal. -/
theorem BigFppfOver.hom_ext_of_toScheme {X Y : BigFppfOver B S hS} {f g : X ⟶ Y}
    (h : (BigFppfOver.toScheme B S hS).map f = (BigFppfOver.toScheme B S hS).map g) : f = g :=
  Over.OverMorphism.ext (B.inclusion.map_injective h)

/-- Composing the morphisms of the site attached to mutually inverse morphisms of underlying
schemes gives the identity. -/
private theorem BigFppfOver.homOfComp_comp_homOfComp {X Y : BigFppfOver B S hS}
    (φ : (BigFppfOver.toScheme B S hS).obj X ⟶ (BigFppfOver.toScheme B S hS).obj Y)
    (ψ : (BigFppfOver.toScheme B S hS).obj Y ⟶ (BigFppfOver.toScheme B S hS).obj X)
    (hφ : φ ≫ B.inclusion.map Y.hom = B.inclusion.map X.hom)
    (hψ : ψ ≫ B.inclusion.map X.hom = B.inclusion.map Y.hom) (h : φ ≫ ψ = 𝟙 _) :
    BigFppfOver.homOfComp φ hφ ≫ BigFppfOver.homOfComp ψ hψ = 𝟙 X := by
  apply BigFppfOver.hom_ext_of_toScheme
  rw [Functor.map_comp, BigFppfOver.toScheme_map_homOfComp, BigFppfOver.toScheme_map_homOfComp]
  exact h.trans ((BigFppfOver.toScheme B S hS).map_id X).symm

/-- **A smooth chart through a model of a field point.** Let `N` be an affine scheme of finite
type over an affine open `W` of `S` whose ring of global sections is a field, and let `x` be an
element of `F` over `N`. Under the hypotheses of Stacks 07Y1 on `𝒮_F`, there are an object `V`
of finite type over `S` and `t ∈ F(V)` such that `t : (Sch/V)_{fppf} ⟶ 𝒮_F` is smooth and `x` is
the pullback of `t` along a morphism `N ⟶ V`. This is Stacks 07XY for `𝒮_F` at the point `x`. -/
theorem exists_chart_of_model [IsLocallyNoetherian S]
    (hdiag : Space.IsRepresentableByAlgebraicSpaces B S hS (diag F))
    (hlim : IsLimitPreserving.{u, u, u, u + 1, u} B S hS (Stack.fibredCategory B S hS F))
    (hRS : SatisfiesRS B S hS (Stack.fibredCategory B S hS F).val.p
      (Stack.fibredCategory B S hS F).isFiberedInGroupoids)
    (htangent : ∀ {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
      (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
      (x₀ : (Stack.fibredCategory B S hS F).val.obj)
      (hx₀ : ((Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)),
      LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) →
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) →
      letI := (predeformationCategory iΛ ((Stack.fibredCategory B S hS F).val.p ⋙
        Over.post B.inclusion) x₀ hx₀).category
      ∀ hD : IsDeformationCategory (predeformationCategory iΛ
          ((Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion) x₀ hx₀).projection,
        letI : Fact (IsPredeformationCategory (BasedCategory.ofFunctor
            (predeformationCategory iΛ ((Stack.fibredCategory B S hS F).val.p ⋙
              Over.post B.inclusion) x₀ hx₀).projection).p) := ⟨hD.predeformation⟩
        letI : Fact (SchlessingerConditionS2 (Functor.Elements.π (isomorphismClasses
            (BasedCategory.ofFunctor (predeformationCategory iΛ
              ((Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion) x₀
                hx₀).projection)
            hD.predeformation.cofibered))) := ⟨tangentConditionS2 hD⟩
        FiniteDimensional k (tangentSpaceArtinian Λ k (isomorphismClasses
          (BasedCategory.ofFunctor (predeformationCategory iΛ
            ((Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion) x₀
              hx₀).projection)
          hD.predeformation.cofibered)))
    (heff : ∀ ξ : FormalObject B S hS (Stack.fibredCategory B S hS F).val.p,
      FormalObject.IsEffective B S hS (Stack.fibredCategory B S hS F).val.p
        (Stack.fibredCategory B S hS F).property ξ)
    (hopen : ∀ (U : Over S), LocallyOfFiniteType U.hom →
      ∀ (x : (Stack.fibredCategory B S hS F).val.obj)
        (hx : ((Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion).obj x = U)
        (u₀ : U.left), IsFiniteTypePoint u₀ →
        IsVersalAt U ((Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion) u₀ x hx →
        ∃ W : U.left.Opens, u₀ ∈ W.1 ∧ ∀ u : U.left, u ∈ W.1 → IsFiniteTypePoint u →
          IsVersalAt U ((Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion) u x hx)
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s))
    (W : S.affineOpens) (N : AffineFiniteTypeOver (W.1 : Scheme.{u}))
    (hN : B.Contains N.obj) (hfield : IsField Γ(N.obj, ⊤))
    (xM : F.obj (op (Over.mk (⟨N.hom ≫ W.1.ι⟩ : B.obj hN ⟶ B.obj hS)))) :
    ∃ (V : BigFppfOver B S hS) (t : F.obj (op V)),
      LocallyOfFiniteType (B.inclusion.map V.hom) ∧ QuasiCompact (B.inclusion.map V.hom) ∧
      Stack.IsRelativelySmooth B S hS
        (Stack.objectMorphism B S hS (Stack.fibredCategory B S hS F)
          (fibredCategoryFiberMk t)) ∧
      ∃ g : (Over.mk (⟨N.hom ≫ W.1.ι⟩ : B.obj hN ⟶ B.obj hS) : BigFppfOver B S hS) ⟶ V,
        F.map g.op t = xM := by
  let : Field Γ(N.obj, ⊤) := hfield.toField
  let k : Type u := Γ(N.obj, ⊤)
  let i₀ : Spec (.of k) ⟶ S := N.obj.isoSpec.inv ≫ N.hom ≫ W.1.ι
  have : IsOpenImmersion W.1.ι := W.1.instIsOpenImmersionι
  have hlft : LocallyOfFiniteType i₀ := by
    change LocallyOfFiniteType (N.obj.isoSpec.inv ≫ N.hom ≫ W.1.ι)
    infer_instance
  have hqc : QuasiCompact i₀ := inferInstance
  have hK : B.Contains (Spec (.of k)) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact i₀ hS
  let A : BigFppfOver B S hS := Over.mk (⟨i₀⟩ : B.obj hK ⟶ B.obj hS)
  let M : BigFppfOver B S hS := Over.mk (⟨N.hom ≫ W.1.ι⟩ : B.obj hN ⟶ B.obj hS)
  let isoSite : A ⟶ M := BigFppfOver.homOfComp (X := A) (Y := M) N.obj.isoSpec.inv rfl
  let invSite : M ⟶ A := BigFppfOver.homOfComp (X := M) (Y := A) N.obj.isoSpec.hom
    (by
      change N.obj.isoSpec.hom ≫ N.obj.isoSpec.inv ≫ N.hom ≫ W.1.ι = N.hom ≫ W.1.ι
      rw [Iso.hom_inv_id_assoc])
  have hinv : invSite ≫ isoSite = 𝟙 M :=
    BigFppfOver.homOfComp_comp_homOfComp _ _ _ _ N.obj.isoSpec.hom_inv_id
  let x' : F.obj (op A) := F.map isoSite.op xM
  let 𝒳 := Stack.fibredCategory B S hS F
  have hx₀ : (𝒳.val.p ⋙ Over.post B.inclusion).obj (fibredCategoryFiberMk x').1 =
      Over.mk i₀ := rfl
  have hs : IsFiniteTypePoint (i₀ (IsLocalRing.closedPoint k)) :=
    isFiniteTypePoint_of_locallyOfFiniteType_fieldPoint i₀ hlft
  obtain ⟨V, y, hV, hVqc, hsm, ⟨a⟩⟩ := exists_isRelativelySmooth_objectMorphism_of_fieldPoint B S hS
    𝒳 (fun V y => isRepresentableByAlgebraicSpaces_objectMorphism_of_diagonal hdiag y) hlim hRS
    htangent heff hopen i₀ (fibredCategoryFiberMk x').1 hx₀ hlft hqc (hG _ hs)
  obtain ⟨t, rfl⟩ := exists_eq_fibredCategoryFiberMk y
  refine ⟨V, t, hV, hVqc, hsm, invSite ≫ 𝒳.val.p.map a, ?_⟩
  have ha : x' = F.map (𝒳.val.p.map a).op t := fiber_as_eq_of_hom a
  have key : ∀ {X Y Z : BigFppfOver B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (s : F.obj (op Z)),
      F.map (f ≫ g).op s = F.map f.op (F.map g.op s) := fun f g s => by
    rw [op_comp, Functor.map_comp_apply]
  calc F.map (invSite ≫ 𝒳.val.p.map a).op t = F.map invSite.op (F.map (𝒳.val.p.map a).op t) :=
        key _ _ _
    _ = F.map invSite.op x' := by rw [← ha]
    _ = F.map (invSite ≫ isoSite).op xM := (key _ _ _).symm
    _ = xM := by rw [hinv, op_id, Functor.map_id_apply]

/-- Pullback along a composite of morphisms of the site. -/
theorem map_comp_op_apply {X Y Z : BigFppfOver B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (s : F.obj (op Z)) : F.map (f ≫ g).op s = F.map f.op (F.map g.op s) := by
  rw [op_comp, Functor.map_comp_apply]

/-- **The chart of Stacks 07Y1.** Under the hypotheses of Stacks 07Y1, there is an object `V` of
the site and `t ∈ F(V)` such that `t : (Sch/V)_{fppf} ⟶ 𝒮_F` is smooth and every element of `F`
over the spectrum of a field of finite type over `S` is a pullback of `t`.

The source takes `V = ∐ U_{k, x₀}` over all finite type fields `k` over `S` and all
`x₀ ∈ F(Spec k)`, with the charts of Stacks 07XY. Here the pairs `(k, x₀)` are indexed by the
affine opens `W` of `S`, the models of the affine schemes of finite type over `W` (whose number is
bounded by `AlgebraicGeometry.exists_index_affineFiniteTypeOver`) that are spectra of fields, and
the elements of `F` over them; axiom [-1] bounds the last factor, so the disjoint union of the
charts lies in the site. The charts glue to `t` because `F` is an étale sheaf, and `t` is smooth
because it is versal at every finite type point (Stacks 07XT, 07XX). -/
theorem exists_chart_of_artinAxioms [IsLocallyNoetherian S]
    (hF : Presheaf.IsSheaf ((etaleTopology B).over (B.obj hS)) F)
    (hsize : ∃ T₀ : BigFppfOver B S hS, ∀ (U : BigFppfOver B S hS) (k : Type u) [Field k],
      Nonempty ((BigFppfOver.toScheme B S hS).obj U ≅ Spec (.of k)) →
      LocallyOfFiniteType (B.inclusion.map U.hom) →
      Cardinal.mk (F.obj (op U)) ≤ ((BigFppfOver.toScheme B S hS).obj T₀).size)
    (hdiag : Space.IsRepresentableByAlgebraicSpaces B S hS (diag F))
    (hlim : IsLimitPreserving.{u, u, u, u + 1, u} B S hS (Stack.fibredCategory B S hS F))
    (hRS : SatisfiesRS B S hS (Stack.fibredCategory B S hS F).val.p
      (Stack.fibredCategory B S hS F).isFiberedInGroupoids)
    (htangent : ∀ {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
      (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
      (x₀ : (Stack.fibredCategory B S hS F).val.obj)
      (hx₀ : ((Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)),
      LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) →
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) →
      letI := (predeformationCategory iΛ ((Stack.fibredCategory B S hS F).val.p ⋙
        Over.post B.inclusion) x₀ hx₀).category
      ∀ hD : IsDeformationCategory (predeformationCategory iΛ
          ((Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion) x₀ hx₀).projection,
        letI : Fact (IsPredeformationCategory (BasedCategory.ofFunctor
            (predeformationCategory iΛ ((Stack.fibredCategory B S hS F).val.p ⋙
              Over.post B.inclusion) x₀ hx₀).projection).p) := ⟨hD.predeformation⟩
        letI : Fact (SchlessingerConditionS2 (Functor.Elements.π (isomorphismClasses
            (BasedCategory.ofFunctor (predeformationCategory iΛ
              ((Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion) x₀
                hx₀).projection)
            hD.predeformation.cofibered))) := ⟨tangentConditionS2 hD⟩
        FiniteDimensional k (tangentSpaceArtinian Λ k (isomorphismClasses
          (BasedCategory.ofFunctor (predeformationCategory iΛ
            ((Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion) x₀
              hx₀).projection)
          hD.predeformation.cofibered)))
    (heff : ∀ ξ : FormalObject B S hS (Stack.fibredCategory B S hS F).val.p,
      FormalObject.IsEffective B S hS (Stack.fibredCategory B S hS F).val.p
        (Stack.fibredCategory B S hS F).property ξ)
    (hopen : ∀ (U : Over S), LocallyOfFiniteType U.hom →
      ∀ (x : (Stack.fibredCategory B S hS F).val.obj)
        (hx : ((Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion).obj x = U)
        (u₀ : U.left), IsFiniteTypePoint u₀ →
        IsVersalAt U ((Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion) u₀ x hx →
        ∃ W : U.left.Opens, u₀ ∈ W.1 ∧ ∀ u : U.left, u ∈ W.1 → IsFiniteTypePoint u →
          IsVersalAt U ((Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion) u x hx)
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    ∃ (V : BigFppfOver B S hS) (t : F.obj (op V)),
      Stack.IsRelativelySmooth B S hS
        (Stack.objectMorphism B S hS (Stack.fibredCategory B S hS F)
          (fibredCategoryFiberMk t)) ∧
      ∀ (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
        (toBase : Spec (.of K) ⟶ S), LocallyOfFiniteType toBase →
        ∀ x : F.obj (op (Over.mk (⟨toBase⟩ : B.obj hK ⟶ B.obj hS))),
        ∃ g : (Over.mk (⟨toBase⟩ : B.obj hK ⟶ B.obj hS) : BigFppfOver B S hS) ⟶ V,
          F.map g.op t = x := by
  classical
  obtain ⟨T₀, hT₀⟩ := hsize
  let 𝒳 := Stack.fibredCategory B S hS F
  have hmodels : ∀ W : S.affineOpens, ∃ (I : Type u)
      (M : I → AffineFiniteTypeOver (W.1 : Scheme.{u})),
      Cardinal.mk I ≤ Cardinal.aleph0 * 2 ^ max Cardinal.aleph0
        (Cardinal.mk Γ((W.1 : Scheme.{u}), ⊤)) ∧
      ∀ N : AffineFiniteTypeOver (W.1 : Scheme.{u}),
        ∃ i, ∃ e : (M i).obj ≅ N.obj, e.hom ≫ N.hom = (M i).hom := by
    intro W
    have : IsAffine (W.1 : Scheme.{u}) := W.2
    exact exists_index_affineFiniteTypeOver _
  choose I M hIcard hM using hmodels
  have hMc : ∀ W i, B.Contains (M W i).obj := fun W i => by
    have : IsOpenImmersion W.1.ι := W.1.instIsOpenImmersionι
    exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact ((M W i).hom ≫ W.1.ι) hS
  let MO : ∀ W i, BigFppfOver B S hS := fun W i =>
    Over.mk (⟨(M W i).hom ≫ W.1.ι⟩ : B.obj (hMc W i) ⟶ B.obj hS)
  let J := Σ (W : S.affineOpens), Σ (i : I W),
    {x : F.obj (op (MO W i)) // IsField Γ((M W i).obj, ⊤)}
  have hchart : ∀ j : J, ∃ (V : BigFppfOver B S hS) (t : F.obj (op V)),
      LocallyOfFiniteType (B.inclusion.map V.hom) ∧ QuasiCompact (B.inclusion.map V.hom) ∧
      Stack.IsRelativelySmooth B S hS (Stack.objectMorphism B S hS 𝒳 (fibredCategoryFiberMk t)) ∧
      ∃ g : MO j.1 j.2.1 ⟶ V, F.map g.op t = j.2.2.1 := fun j =>
    exists_chart_of_model hdiag hlim hRS htangent heff hopen hG j.1 (M j.1 j.2.1) (hMc _ _)
      j.2.2.2 j.2.2.1
  choose V t hVlft hVqc hVsm g hg using hchart
  let κ₀ : Cardinal.{u} := max S.size ((BigFppfOver.toScheme B S hS).obj T₀).size
  let μ : Cardinal.{u} := 2 ^ κ₀
  have hκμ : κ₀ ≤ μ := (Cardinal.cantor κ₀).le
  have hSμ : S.size ≤ μ := (le_max_left _ _).trans hκμ
  have hℵ : Cardinal.aleph0 ≤ μ := S.aleph0_le_size.trans hSμ
  have hμ : μ < B.cutoff := B.cutoff_isStrongPrelimit (max_lt hS T₀.left.2)
  have hsizes : ∀ j, ((BigFppfOver.toScheme B S hS).obj (V j)).size ≤ μ := fun j => by
    have := hVlft j
    have := hVqc j
    exact (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact
      (B.inclusion.map (V j).hom)).trans hSμ
  have hsub : ∀ W i, Cardinal.mk {x : F.obj (op (MO W i)) // IsField Γ((M W i).obj, ⊤)} ≤ μ := by
    intro W i
    by_cases hf : IsField Γ((M W i).obj, ⊤)
    · let : Field Γ((M W i).obj, ⊤) := hf.toField
      have : IsOpenImmersion W.1.ι := W.1.instIsOpenImmersionι
      refine (Cardinal.mk_subtype_le _).trans ((hT₀ (MO W i) Γ((M W i).obj, ⊤)
        ⟨(M W i).obj.isoSpec⟩ ?_).trans ((le_max_right _ _).trans hκμ))
      change LocallyOfFiniteType ((M W i).hom ≫ W.1.ι)
      infer_instance
    · exact (Cardinal.mk_eq_zero_iff.mpr ⟨fun x => hf x.2⟩).le.trans (zero_le)
  have hI : ∀ W, Cardinal.mk (I W) ≤ μ := by
    intro W
    refine (hIcard W).trans ?_
    have h1 : max Cardinal.aleph0 (Cardinal.mk Γ((W.1 : Scheme.{u}), ⊤)) ≤ κ₀ := by
      refine max_le (S.aleph0_le_size.trans (le_max_left _ _)) ?_
      have : IsAffine (W.1 : Scheme.{u}) := W.2
      exact ((Scheme.mk_sections_le_size (W.1 : Scheme.{u}) ⟨⊤, isAffineOpen_top _⟩).trans
        (Scheme.size_coe_opens_le S W.1)).trans (le_max_left _ _)
    exact (mul_le_mul' hℵ (Cardinal.power_le_power_left two_ne_zero h1)).trans
      (Cardinal.mul_eq_self hℵ).le
  have hσ : ∀ {α : Type u} {β : α → Type u}, Cardinal.mk α ≤ μ →
      (∀ a, Cardinal.mk (β a) ≤ μ) → Cardinal.mk (Σ a, β a) ≤ μ := fun hα hβ => by
    rw [Cardinal.mk_sigma]
    exact (Cardinal.sum_le_mk_mul_iSup _).trans
      ((mul_le_mul' hα (ciSup_le' hβ)).trans (Cardinal.mul_eq_self hℵ).le)
  have hJ : Cardinal.mk J ≤ μ :=
    hσ ((Scheme.mk_affineOpens_le_size S).trans hSμ) fun W => hσ (hI W) (hsub W)
  obtain ⟨Z, c, hcoi, hcdisj, hccov⟩ :=
    BigFppfOver.exists_coproduct_of_size_le B S hS V hℵ hμ hJ hsizes
  obtain ⟨τ, hτ⟩ := BigFppfOver.exists_section_of_disjoint_openCover_etale
    ((isSheaf_iff_isSheaf_of_type _ _).mp hF) c hcoi hcdisj hccov t
  refine ⟨Z, τ, ?_, ?_⟩
  · let p := 𝒳.val.p
    let xZ : 𝒳.val.obj := (fibredCategoryFiberMk τ).1
    let q := p ⋙ Over.post B.inclusion
    have hZlft : LocallyOfFiniteType (q.obj xZ).hom := by
      let 𝒰 : ((BigFppfOver.toScheme B S hS).obj Z).OpenCover :=
        { I₀ := J
          X := fun j => (BigFppfOver.toScheme B S hS).obj (V j)
          f := fun j => (BigFppfOver.toScheme B S hS).map (c j)
          mem₀ := by
            rw [Scheme.presieve₀_mem_precoverage_iff]
            exact ⟨hccov, hcoi⟩ }
      have : IsZariskiLocalAtSource @LocallyOfFiniteType.{u} :=
        HasRingHomProperty.instIsZariskiLocalAtSource
      refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType.{u}) 𝒰 (fun j => ?_)
      change LocallyOfFiniteType (B.inclusion.map (c j).left ≫ B.inclusion.map Z.hom)
      rw [← Functor.map_comp, Over.w (c j)]
      exact hVlft j
    have hversal : ∀ z : (q.obj xZ).left, IsFiniteTypePoint z →
        IsVersalAt (q.obj xZ) q z xZ rfl := by
      intro z hz
      obtain ⟨j, v, rfl⟩ := hccov z
      obtain ⟨ρ, hρ⟩ := Stack.presheafFiberHom B S hS F (c j) (fibredCategoryFiberMk (t j))
        (fibredCategoryFiberMk τ) (hτ j)
      have hbase : p.map ρ = c j := base_eq_of_isHomLift (c j) ρ hρ
      have hj : IsOpenImmersion (B.inclusion.map (p.map ρ).left) := by
        rw [hbase]
        exact hcoi j
      have := hcoi j
      have hv : IsFiniteTypePoint v :=
        isFiniteTypePoint_of_isOpenImmersion ((BigFppfOver.toScheme B S hS).map (c j)) v hz
      have hft : LocallyOfFiniteType
          ((q.obj (fibredCategoryFiberMk (t j)).1).left.fromSpecResidueField v ≫
            (q.obj (fibredCategoryFiberMk (t j)).1).hom) :=
        @locallyOfFiniteType_comp _ _ _ _ _ hv.1 (hVlft j)
      have hvers := AlgebraicGeometry.Stack.isVersalAt_of_isRelativelySmooth_objectMorphism B S hS
        𝒳 (fibredCategoryFiberMk (t j)).1 (hVsm j) v hft
      have h := (isVersalAt_iff_of_isOpenImmersion_map B S hS 𝒳 ρ hj v).mp hvers
      rwa [hbase] at h
    have : LocallyOfFiniteType (B.inclusion.map Z.hom) := hZlft
    have : IsLocallyNoetherian (B.inclusion.obj (B.obj hS)) := ‹IsLocallyNoetherian S›
    exact Stack.isRelativelySmooth_of_isSmoothOnPredeformationCategories B S hS
      (Stack.objectMorphism B S hS 𝒳 (fibredCategoryFiberMk τ))
      (isRepresentableByAlgebraicSpaces_objectMorphism_of_diagonal hdiag _)
      (Stack.isLimitPreservingOnObjects_toTerminalCFG_schemeFibredCategory B S hS Z inferInstance)
      hlim (AlgebraicGeometry.Stack.isSmoothOnPredeformationCategories_objectMorphism_of_isVersalAt
        B S hS 𝒳 xZ hZlft hversal hRS)
  · intro K _ hK toBase hlft x
    obtain ⟨_, ⟨W₀, hW, rfl⟩, hsW, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (toBase (IsLocalRing.closedPoint K))) isOpen_univ
    let W : S.Opens := W₀
    have hrange : Set.range toBase.base ⊆ Set.range W.ι.base := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι, Subsingleton.elim z (IsLocalRing.closedPoint K)]
      exact hsW
    let l := IsOpenImmersion.lift W.ι toBase hrange
    have hl : l ≫ W.ι = toBase := IsOpenImmersion.lift_fac W.ι toBase hrange
    have hllft : LocallyOfFiniteType l :=
      LocallyOfFiniteType.of_comp (f := l) (g := W.ι) (by rwa [hl])
    let N : AffineFiniteTypeOver (W : Scheme.{u}) := ⟨Spec (.of K), l, inferInstance, hllft⟩
    obtain ⟨i, e, he⟩ := hM ⟨W, hW⟩ N
    have hfield : IsField Γ((M ⟨W, hW⟩ i).obj, ⊤) :=
      MulEquiv.isField (Field.toIsField K)
        ((Scheme.Γ.mapIso e.op).symm ≪≫
          Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv
    let Y : BigFppfOver B S hS := Over.mk (⟨toBase⟩ : B.obj hK ⟶ B.obj hS)
    let ψ : MO ⟨W, hW⟩ i ⟶ Y := BigFppfOver.homOfComp (X := MO ⟨W, hW⟩ i) (Y := Y) e.hom (by
      change e.hom ≫ toBase = (M ⟨W, hW⟩ i).hom ≫ W.ι
      rw [← hl, ← Category.assoc]
      exact congrArg (· ≫ W.ι) he)
    let φ : Y ⟶ MO ⟨W, hW⟩ i := BigFppfOver.homOfComp (X := Y) (Y := MO ⟨W, hW⟩ i) e.inv (by
      change e.inv ≫ (M ⟨W, hW⟩ i).hom ≫ W.ι = toBase
      rw [← he, Category.assoc, Iso.inv_hom_id_assoc, hl])
    have hφψ : φ ≫ ψ = 𝟙 Y := BigFppfOver.homOfComp_comp_homOfComp _ _ _ _ e.inv_hom_id
    let j : J := ⟨⟨W, hW⟩, i, ⟨F.map ψ.op x, hfield⟩⟩
    refine ⟨φ ≫ g j ≫ c j, ?_⟩
    rw [map_comp_op_apply, map_comp_op_apply, hτ j, hg j]
    change F.map φ.op (F.map ψ.op x) = x
    rw [← map_comp_op_apply, hφψ, op_id, Functor.map_id_apply]

/-- **Artin's criterion for a functor to be an algebraic space** (the statement of Stacks 07Y1,
used here without the tag). Let `S` be a
locally Noetherian scheme and `F : (Sch/S)_{fppf}^{opp} ⟶ Sets` a functor. Assume that
1. `Δ : F ⟶ F × F` is representable by algebraic spaces,
2. `F` satisfies the axioms of Section 07XZ:
   * [-1] the cardinalities `|F(Spec k)|`, `k` a field of finite type over `S`, are bounded by the
     size of an object of the site,
   * [0] `F` is a sheaf for the étale topology,
   * [1] `F` is limit preserving (Stacks 049J, along inverse systems indexed in the universe of
     the site),
   * [2] `F` satisfies (RS) in the form of Section 07XZ,
   * [3] every tangent space `TF_{k, x₀}` is finite dimensional, read on the predeformation
     category of the category fibred in sets `𝒮_F` over every affine open chart of Section 07T2,
   * [4] every formal object of `𝒮_F` is effective,
   * [5] `𝒮_F` satisfies openness of versality,
3. `𝒪_{S, s}` is a G-ring for all finite type points `s` of `S`.

Then `F` is an algebraic space.

Following Section 07XZ, axioms [3], [4] and [5] are stated on the category fibred in sets
`𝒮_F = AlgebraicGeometry.Stack.fibredCategory B S hS F` attached to `F`; the tangent space
hypothesis is required for every deformation-category structure, which holds under [2] by
Stacks 07WU, and openness of versality is the body of `Deformation.Artin.IsOpenVersality`,
whose fibred-in-groupoids argument for `𝒮_F ⟶ Over S` is not available (see
`StacksFrontier.Deformation.Artin.Obstruction.NaiveTheoryVersalityOpenness`). The proof is the
source's: the charts of Stacks 07XY at a set of representatives of the finite type points of `F`
form a smooth surjective atlas, and Stacks 07WF applies. -/
theorem isAlgebraicSpace_of_artinAxioms [IsLocallyNoetherian S]
    (hdiag : Space.IsRepresentableByAlgebraicSpaces B S hS (diag F))
    (hsize : ∃ T₀ : BigFppfOver B S hS, ∀ (U : BigFppfOver B S hS) (k : Type u) [Field k],
      Nonempty ((BigFppfOver.toScheme B S hS).obj U ≅ Spec (.of k)) →
      LocallyOfFiniteType (B.inclusion.map U.hom) →
      Cardinal.mk (F.obj (op U)) ≤ ((BigFppfOver.toScheme B S hS).obj T₀).size)
    (hF : Presheaf.IsSheaf ((etaleTopology B).over (B.obj hS)) F)
    (hlim : LimitPreserving.{u, u, u, u, u + 1} (BigFppfOver.toScheme B S hS) F)
    (hRS : SatisfiesRSFunctor B S hS F)
    (htangent : ∀ {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
      (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
      (x₀ : (Stack.fibredCategory B S hS F).val.obj)
      (hx₀ : ((Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)),
      LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) →
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) →
      letI := (predeformationCategory iΛ ((Stack.fibredCategory B S hS F).val.p ⋙
        Over.post B.inclusion) x₀ hx₀).category
      ∀ hD : IsDeformationCategory (predeformationCategory iΛ
          ((Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion) x₀ hx₀).projection,
        letI : Fact (IsPredeformationCategory (BasedCategory.ofFunctor
            (predeformationCategory iΛ ((Stack.fibredCategory B S hS F).val.p ⋙
              Over.post B.inclusion) x₀ hx₀).projection).p) := ⟨hD.predeformation⟩
        letI : Fact (SchlessingerConditionS2 (Functor.Elements.π (isomorphismClasses
            (BasedCategory.ofFunctor (predeformationCategory iΛ
              ((Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion) x₀
                hx₀).projection)
            hD.predeformation.cofibered))) := ⟨tangentConditionS2 hD⟩
        FiniteDimensional k (tangentSpaceArtinian Λ k (isomorphismClasses
          (BasedCategory.ofFunctor (predeformationCategory iΛ
            ((Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion) x₀
              hx₀).projection)
          hD.predeformation.cofibered)))
    (heff : ∀ ξ : FormalObject B S hS (Stack.fibredCategory B S hS F).val.p,
      FormalObject.IsEffective B S hS (Stack.fibredCategory B S hS F).val.p
        (Stack.fibredCategory B S hS F).property ξ)
    (hopen : ∀ (U : Over S), LocallyOfFiniteType U.hom →
      ∀ (x : (Stack.fibredCategory B S hS F).val.obj)
        (hx : ((Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion).obj x = U)
        (u₀ : U.left), IsFiniteTypePoint u₀ →
        IsVersalAt U ((Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion) u₀ x hx →
        ∃ W : U.left.Opens, u₀ ∈ W.1 ∧ ∀ u : U.left, u ∈ W.1 → IsFiniteTypePoint u →
          IsVersalAt U ((Stack.fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion) u x hx)
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    IsAlgebraicSpace B S hS F := by
  have hlim' := isLimitPreserving_fibredCategory_of_limitPreserving hlim
  have hRS' : SatisfiesRS B S hS (Stack.fibredCategory B S hS F).val.p
      (Stack.fibredCategory B S hS F).isFiberedInGroupoids :=
    satisfiesRS_fibredCategory_of_satisfiesRSFunctor hRS
  obtain ⟨V, t, hsm, hcover⟩ :=
    exists_chart_of_artinAxioms hF hsize hdiag hlim' hRS' htangent heff hopen hG
  exact isAlgebraicSpace_of_isRelativelySmooth_objectMorphism_of_cover hF hdiag hlim' t hsm hcover

end Deformation.Artin

end
