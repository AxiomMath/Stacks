module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Group.ULift
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.AlgebraicGeometry.Spaces.BigEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafCoproduct

/-!
# Coproducts in the spaces-étale site of an algebraic space

The spaces-étale site of an algebraic space `X` over `S` has binary coproducts, and they are
computed in the sheaves of sets on the big fppf site over `S`: the disjoint union of two
algebraic spaces étale over `X` is again an algebraic space étale over `X`. The two
inclusions of a binary coproduct are monomorphisms, they generate a covering sieve, and an
object mapping to both members over the coproduct has no points. Extension by zero of the
constant abelian sheaf turns a binary coproduct of the site into a direct sum.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.toSheaf` is the sheaf of sets on the big fppf site
  over `S` underlying an object of the spaces-étale site of `X`, as a functor.
* `AlgebraicGeometry.Space.SpacesEtale.freeAbelianRepresentableSheaf` is the sheafified free
  abelian group on the representable presheaf of an object of the site.
* `AlgebraicGeometry.Space.SpacesEtale.extensionByZero` is Mathlib's left adjoint to
  restriction of abelian sheaves to the slice site, and
  `AlgebraicGeometry.Space.SpacesEtale.extensionByZeroConstant` applies it to the constant
  integer sheaf.
* `AlgebraicGeometry.Space.SpacesEtale.extensionByZeroConstantMap` is the canonical map
  induced by a morphism of the site, defined through the two adjunctions.

## Main results

* `AlgebraicGeometry.relative_inverseImage_of_openCover_source`: a property of scheme
  morphisms which is Zariski local at the source may be checked, for a morphism of presheaves
  out of a representable one, after restricting to an open cover of the representing object.
  `AlgebraicGeometry.presheaf_inverseImage_of_openCover_source` is its instance at
  `CategoryTheory.yoneda`.
* `AlgebraicGeometry.Space.SpacesEtale.exists_isColimit_cofan_toSheaf` and
  `AlgebraicGeometry.Space.SpacesEtale.instHasBinaryCoproducts`: the spaces-étale site has
  binary coproducts, computed in the sheaves of sets on the big fppf site.
* `AlgebraicGeometry.Space.SpacesEtale.nonempty_isColimit_cofan_toSheaf`: conversely, a
  coproduct of the site is a coproduct of the underlying sheaves of sets.
* `AlgebraicGeometry.Space.SpacesEtale.mono_of_isColimit_cofan`,
  `AlgebraicGeometry.Space.SpacesEtale.ofArrows_mem_topology_of_isColimit_cofan` and
  `AlgebraicGeometry.Space.SpacesEtale.bot_mem_topology_of_isColimit_cofan`: the inclusions
  of a coproduct are monomorphisms, they generate a covering sieve, and an object mapping to
  two different members compatibly is covered by the empty sieve.
* `AlgebraicGeometry.Space.SpacesEtale.extensionByZeroConstant_preservesBinaryCoproduct`: the
  canonical maps induced by the inclusions of a binary coproduct exhibit the extension by zero
  of the constant sheaf on the coproduct as the direct sum of those on the two members.

## References

* [Stacks Project, Tag 0722](https://stacks.math.columbia.edu/tag/0722)
* [Stacks Project, Tag 02WO](https://stacks.math.columbia.edu/tag/02WO)
* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 03FS](https://stacks.math.columbia.edu/tag/03FS)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w t u

namespace AlgebraicGeometry

section Source

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A property of morphisms of schemes which is Zariski local at the source may be checked,
for a morphism of presheaves out of a representable one, after restricting to an open cover
of the representing object.**

The representable presheaves are those of a fully faithful functor `Y` from the site into its
presheaves of `Type t` which preserves fibre products, such as `CategoryTheory.yoneda` or
`CategoryTheory.uliftYoneda`.

The hypothesis is that each restriction `Y.map (p k) ≫ g` has the property after every
representable base change; the conclusion is the same statement for `g`. -/
theorem relative_inverseImage_of_openCover_source
    {P₀ : MorphismProperty Scheme.{u}} (hloc : IsZariskiLocalAtSource P₀)
    {Y : BigFppfOver B S hS ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type t)} [Y.Full] [Y.Faithful]
    [PreservesLimitsOfShape WalkingCospan Y]
    {V : BigFppfOver B S hS} {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type t} {g : Y.obj V ⟶ Z}
    (hrep : Y.relativelyRepresentable g)
    {K : Type w} {W : K → BigFppfOver B S hS} (p : ∀ k, W k ⟶ V)
    (hoi : ∀ k, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (p k)))
    (hcov : ∀ x : (BigFppfOver.toScheme B S hS).obj V,
      ∃ k, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (p k)))
    (h : ∀ k, (P₀.inverseImage (BigFppfOver.toScheme B S hS)).relative Y
      (Y.map (p k) ≫ g)) :
    (P₀.inverseImage (BigFppfOver.toScheme B S hS)).relative Y g := by
  have := hloc
  have hri : (P₀.inverseImage (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine MorphismProperty.relative_of_snd hrep fun c kk => ?_
  change P₀ ((BigFppfOver.toScheme B S hS).map (hrep.snd kk))
  set π : ∀ k, Limits.pullback (p k) (hrep.fst' kk) ⟶ hrep.pullback kk :=
    fun k => Limits.pullback.snd (p k) (hrep.fst' kk) with hπdef
  have hschpb : ∀ k, IsPullback
      ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst (p k) (hrep.fst' kk)))
      ((BigFppfOver.toScheme B S hS).map (π k))
      ((BigFppfOver.toScheme B S hS).map (p k))
      ((BigFppfOver.toScheme B S hS).map (hrep.fst' kk)) := fun k =>
    (IsPullback.of_hasPullback (p k) (hrep.fst' kk)).map (BigFppfOver.toScheme B S hS)
  have hπoi : ∀ k, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (π k)) := by
    intro k
    have := hoi k
    rw [← (hschpb k).isoPullback_hom_snd]
    infer_instance
  have hπcov : ∀ y : (BigFppfOver.toScheme B S hS).obj (hrep.pullback kk),
      ∃ k, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (π k)) := by
    intro y
    obtain ⟨k, hk⟩ := hcov ((BigFppfOver.toScheme B S hS).map (hrep.fst' kk) y)
    refine ⟨k, ?_⟩
    have h₁ := hoi k
    have hmem : y ∈ Set.range (Limits.pullback.snd
        ((BigFppfOver.toScheme B S hS).map (p k))
        ((BigFppfOver.toScheme B S hS).map (hrep.fst' kk))) := by
      rwa [IsOpenImmersion.range_pullbackSnd]
    obtain ⟨z, hz⟩ := hmem
    have key : ∀ w, Limits.pullback.snd ((BigFppfOver.toScheme B S hS).map (p k))
          ((BigFppfOver.toScheme B S hS).map (hrep.fst' kk)) ((hschpb k).isoPullback.hom w) =
        ((BigFppfOver.toScheme B S hS).map (π k)) w := by
      intro w
      rw [← Scheme.Hom.comp_apply, (hschpb k).isoPullback_hom_snd]
    have hz' : ((hschpb k).isoPullback.hom) (((hschpb k).isoPullback.inv) z) = z := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl
    exact ⟨((hschpb k).isoPullback.inv) z, by rw [← key, hz']; exact hz⟩
  have hPk : ∀ k, P₀ ((BigFppfOver.toScheme B S hS).map (π k) ≫
      (BigFppfOver.toScheme B S hS).map (hrep.snd kk)) := by
    intro k
    have hsq : IsPullback (Y.map (Limits.pullback.fst (p k) (hrep.fst' kk)))
        (Y.map (π k ≫ hrep.snd kk)) (Y.map (p k) ≫ g) kk := by
      have h₁ : IsPullback (Y.map (Limits.pullback.fst (p k) (hrep.fst' kk)))
          (Y.map (π k)) (Y.map (p k)) (Y.map (hrep.fst' kk)) :=
        (IsPullback.of_hasPullback (p k) (hrep.fst' kk)).map Y
      simpa only [Functor.map_comp] using h₁.paste_vert (hrep.isPullback' kk)
    rw [← Functor.map_comp]
    exact (h k).property kk _ (π k ≫ hrep.snd kk) hsq
  refine MorphismProperty.IsLocalAtSource.of_forall_comp (K := Scheme.zariskiPrecoverage)
    (R := Presieve.ofArrows
      (fun k => (BigFppfOver.toScheme B S hS).obj (Limits.pullback (p k) (hrep.fst' kk)))
      (fun k => (BigFppfOver.toScheme B S hS).map (π k))) ?_ ?_
  · rw [Scheme.zariskiPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨hπcov, hπoi⟩
  · rintro _ _ ⟨k⟩
    exact hPk k

/-- **A property of morphisms of schemes which is Zariski local at the source may be checked,
for a morphism of presheaves of `Type u` out of a representable one, after restricting to an
open cover of the representing object.** This is
`AlgebraicGeometry.relative_inverseImage_of_openCover_source` for `CategoryTheory.yoneda`. -/
theorem presheaf_inverseImage_of_openCover_source
    {P₀ : MorphismProperty Scheme.{u}} (hloc : IsZariskiLocalAtSource P₀)
    {V : BigFppfOver B S hS} {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {g : yoneda.obj V ⟶ Z}
    (hrep : yoneda.relativelyRepresentable g)
    {K : Type w} {W : K → BigFppfOver B S hS} (p : ∀ k, W k ⟶ V)
    (hoi : ∀ k, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (p k)))
    (hcov : ∀ x : (BigFppfOver.toScheme B S hS).obj V,
      ∃ k, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (p k)))
    (h : ∀ k, (P₀.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
      (yoneda.map (p k) ≫ g)) :
    (P₀.inverseImage (BigFppfOver.toScheme B S hS)).presheaf g :=
  relative_inverseImage_of_openCover_source hloc hrep p hoi hcov h

end Source

section Coproduct

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

namespace Space.SpacesEtale

/-- The sheaf of sets on the big fppf site over `S` underlying an object of the spaces-étale
site of `X`: an algebraic space is in particular a sheaf, and the morphisms of the
spaces-étale site are morphisms of the underlying presheaves. -/
noncomputable def toSheaf :
    SpacesEtale B S hS X ⥤ Sheaf (BigFppfOver.topology B S hS) (Type u) where
  obj W := ⟨((toSpaces B S hS X).obj W).obj, ((toSpaces B S hS X).obj W).property.isSheaf⟩
  map f := ⟨((toSpaces B S hS X).map f).hom⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The underlying presheaf of `toSheaf` applied to `W` is the underlying presheaf of the
algebraic space `W`. -/
@[simp]
lemma toSheaf_obj_obj (W : SpacesEtale B S hS X) :
    ((toSheaf B S hS X).obj W).obj = ((toSpaces B S hS X).obj W).obj := rfl

/-- The underlying morphism of presheaves of `toSheaf` applied to `f` is the underlying
morphism of the algebraic spaces. -/
@[simp]
lemma toSheaf_map_hom {W W' : SpacesEtale B S hS X} (f : W ⟶ W') :
    ((toSheaf B S hS X).map f).hom = ((toSpaces B S hS X).map f).hom := rfl

/-- **Two objects of the spaces-étale site of `X` have a coproduct, and it is the coproduct
of the underlying sheaves of sets on the big fppf site over `S`.** -/
theorem exists_isColimit_cofan_toSheaf (Y : WalkingPair → SpacesEtale B S hS X) :
    ∃ (P : SpacesEtale B S hS X) (c : ∀ p, Y p ⟶ P),
      Nonempty (IsColimit (Cofan.mk ((toSheaf B S hS X).obj P)
        (fun p => (toSheaf B S hS X).map (c p)))) := by
  classical
  have hsh := BigFppfOver.hasSheafify_type B S hS
  have _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  set Fsh : WalkingPair → Sheaf (BigFppfOver.topology B S hS) (Type u) :=
    fun p => (toSheaf B S hS X).obj (Y p) with hFshdef
  have hcol : HasColimit (Discrete.functor Fsh) :=
    HasColimit.mk ⟨Sheaf.sheafifyCocone (colimit.cocone _),
      Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩
  have hPsh : IsColimit (Cofan.mk (∐ Fsh) (Sigma.ι Fsh)) := coproductIsCoproduct Fsh
  have halgY : ∀ p, IsAlgebraicSpace B S hS (Fsh p).obj := fun p =>
    ((toSpaces B S hS X).obj (Y p)).property
  choose A a hasurj haetale using fun p => (halgY p).exists_atlas
  have hVcof : IsColimit (Cofan.mk (∐ A) (Sigma.ι A)) := coproductIsCoproduct A
  have halg : IsAlgebraicSpace B S hS (∐ Fsh).obj :=
    isAlgebraicSpace_coproduct B S hS (fun p => (Fsh p).obj) halgY (∐ Fsh) (Sigma.ι Fsh) hPsh
      A a hasurj haetale (∐ A) (Sigma.ι A) hVcof
  set fstr : (∐ Fsh) ⟶ (⟨X.obj, X.property.isSheaf⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) :=
    Cofan.IsColimit.desc hPsh (fun p => ⟨(Y p).obj.hom.hom⟩) with hfstrdef
  have hfstrfac : ∀ p, (Sigma.ι Fsh p).hom ≫ fstr.hom =
      (Y p).obj.hom.hom := by
    intro p
    have := Cofan.IsColimit.fac hPsh (fun p => (⟨(Y p).obj.hom.hom⟩ :
      Fsh p ⟶ (⟨X.obj, X.property.isSheaf⟩ :
        Sheaf (BigFppfOver.topology B S hS) (Type u)))) p
    exact congrArg (fun m => m.hom) this
  obtain ⟨v, hvfac⟩ := exists_hom_yoneda_of_isColimit_cofan (Sigma.ι Fsh) a hVcof
  have hvsurj := presheaf_inverseImage_of_isColimit_cofan (Sigma.ι Fsh) hPsh
    (fun p => (halgY p).diagonal_representable) hVcof hvfac inferInstance hasurj
  have hvetale := presheaf_inverseImage_of_isColimit_cofan (Sigma.ι Fsh) hPsh
    (fun p => (halgY p).diagonal_representable) hVcof hvfac
    (HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Etale) (Q := RingHom.Etale)) haetale
  have hrepvf : yoneda.relativelyRepresentable (v ≫ fstr.hom) :=
    Functor.relativelyRepresentable.of_diag X.property.diagonal_representable _
  have hvf : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (v ≫ fstr.hom) := by
    refine presheaf_inverseImage_of_openCover_source
      (HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale))
      hrepvf (Sigma.ι A) (fun p => isOpenImmersion_toScheme_map_cofan hVcof p) ?_ ?_
    · exact fun x => Set.mem_iUnion.1 (by rw [iUnion_range_toScheme_map_cofan hVcof]; trivial)
    · intro p
      rw [← Category.assoc, hvfac p, Category.assoc, hfstrfac p]
      exact (Y p).property (A p) (a p) (haetale p)
  have hetale : IsEtale B S hS fstr.hom :=
    isEtale_of_presheaf_etale_comp_chart B S hS X.property hvsurj hvetale fstr.hom hvf
  refine ⟨⟨Over.mk (ObjectProperty.homMk fstr.hom :
      (⟨(∐ Fsh).obj, halg⟩ : AlgebraicSpaces B S hS) ⟶ X), hetale⟩,
    fun p => ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk (Sigma.ι Fsh p).hom) ?_), ⟨?_⟩⟩
  · exact ObjectProperty.hom_ext _ (hfstrfac p)
  · exact hPsh

/-- Morphisms of the spaces-étale site of `X` are determined by the underlying morphism of
sheaves of sets on the big fppf site over `S`. -/
theorem toSheaf_map_injective {W W' : SpacesEtale B S hS X} {f g : W ⟶ W'}
    (h : (toSheaf B S hS X).map f = (toSheaf B S hS X).map g) : f = g :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _
    (congrArg (fun m => m.hom) h)))

/-- The functor `toSheaf` is faithful. -/
instance faithful_toSheaf : (toSheaf B S hS X).Faithful where
  map_injective h := toSheaf_map_injective B S hS X h

/-- The underlying morphism of sheaves of a morphism of the spaces-étale site of `X`
commutes with the structure morphisms to `X`. -/
theorem toSheaf_map_hom_comp {W W' : SpacesEtale B S hS X} (f : W ⟶ W') :
    ((toSheaf B S hS X).map f).hom ≫ W'.obj.hom.hom = W.obj.hom.hom := by
  rw [← Over.w f.hom]; rfl

/-- **A coproduct cocone of the underlying sheaves of a family of objects of the
spaces-étale site of `X` whose vertex comes from the site is a coproduct in the site.** -/
noncomputable def isColimit_cofan_of_isColimit_cofan_toSheaf
    {Y : WalkingPair → SpacesEtale B S hS X} {P : SpacesEtale B S hS X} (c : ∀ p, Y p ⟶ P)
    (hc : IsColimit (Cofan.mk ((toSheaf B S hS X).obj P)
      (fun p => (toSheaf B S hS X).map (c p)))) :
    IsColimit (Cofan.mk P c) := by
  classical
  set Xsh : Sheaf (BigFppfOver.topology B S hS) (Type u) :=
    ⟨X.obj, X.property.isSheaf⟩ with hXshdef
  set str : ∀ W : SpacesEtale B S hS X, (toSheaf B S hS X).obj W ⟶ Xsh :=
    fun W => ⟨W.obj.hom.hom⟩ with hstrdef
  have hstr : ∀ {W W' : SpacesEtale B S hS X} (f : W ⟶ W'),
      (toSheaf B S hS X).map f ≫ str W' = str W := fun f =>
    Sheaf.hom_ext (toSheaf_map_hom_comp B S hS X f)
  have hext : ∀ (T : SpacesEtale B S hS X) (m₁ m₂ : P ⟶ T),
      (∀ p, c p ≫ m₁ = c p ≫ m₂) → m₁ = m₂ := by
    intro T m₁ m₂ hm
    refine toSheaf_map_injective B S hS X (Cofan.IsColimit.hom_ext hc _ _ fun p => ?_)
    simp only [cofan_mk_inj, ← Functor.map_comp, hm p]
  have hdesc : ∀ (T : SpacesEtale B S hS X) (g : ∀ p, Y p ⟶ T),
      ∃ m : P ⟶ T, ∀ p, c p ≫ m = g p := by
    intro T g
    set d := Cofan.IsColimit.desc hc (fun p => (toSheaf B S hS X).map (g p)) with hddef
    have hdfac : ∀ p, (toSheaf B S hS X).map (c p) ≫ d = (toSheaf B S hS X).map (g p) := by
      intro p
      simpa only [cofan_mk_inj] using
        Cofan.IsColimit.fac hc (fun p => (toSheaf B S hS X).map (g p)) p
    have htri : d ≫ str T = str P :=
      Cofan.IsColimit.hom_ext hc _ _ fun p => by
        simp only [cofan_mk_inj, ← Category.assoc, hdfac p, hstr]
    refine ⟨ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk d.hom)
      (ObjectProperty.hom_ext _ (congrArg (fun m => m.hom) htri))), fun p => ?_⟩
    refine toSheaf_map_injective B S hS X (Sheaf.hom_ext ?_)
    rw [Functor.map_comp]
    exact congrArg (fun m => m.hom) (hdfac p)
  refine Cofan.IsColimit.mk _ (fun t => (hdesc t.pt (fun p => t.inj p)).choose)
    (fun t p => ?_) (fun t m hm => hext _ _ _ fun p => ?_)
  · simpa only [cofan_mk_inj] using (hdesc t.pt (fun p => t.inj p)).choose_spec p
  · rw [(hdesc t.pt (fun p => t.inj p)).choose_spec p]
    simpa only [cofan_mk_inj] using hm p

/-- **A coproduct in the spaces-étale site of `X` is a coproduct of the underlying sheaves of
sets on the big fppf site over `S`.** -/
theorem nonempty_isColimit_cofan_toSheaf {Y : WalkingPair → SpacesEtale B S hS X}
    {U : SpacesEtale B S hS X} (i : ∀ p, Y p ⟶ U) (hU : IsColimit (Cofan.mk U i)) :
    Nonempty (IsColimit (Cofan.mk ((toSheaf B S hS X).obj U)
      (fun p => (toSheaf B S hS X).map (i p)))) := by
  obtain ⟨P, c, ⟨hc⟩⟩ := exists_isColimit_cofan_toSheaf B S hS X Y
  have hcS : IsColimit (Cofan.mk P c) := isColimit_cofan_of_isColimit_cofan_toSheaf B S hS X c hc
  set e : P ≅ U := hcS.coconePointUniqueUpToIso hU with hedef
  have hefac : ∀ p, c p ≫ e.hom = i p := fun p =>
    hcS.comp_coconePointUniqueUpToIso_hom hU (j := (⟨p⟩ : Discrete WalkingPair))
  refine ⟨hc.ofIsoColimit (Cocone.ext ((toSheaf B S hS X).mapIso e) fun j => ?_)⟩
  obtain ⟨p⟩ := j
  simp only [Cofan.mk_ι_app, Functor.mapIso_hom, ← Functor.map_comp, hefac p]

/-- **The spaces-étale site of `X` has binary coproducts**, computed as coproducts of the
underlying sheaves of sets on the big fppf site over `S`. -/
noncomputable instance instHasBinaryCoproducts :
    HasBinaryCoproducts (SpacesEtale B S hS X) := by
  refine ⟨fun F => ?_⟩
  obtain ⟨P, c, ⟨hc⟩⟩ := exists_isColimit_cofan_toSheaf B S hS X (F.obj ∘ Discrete.mk)
  have : HasColimit (Discrete.functor (F.obj ∘ Discrete.mk)) :=
    HasColimit.mk ⟨Cofan.mk P c, isColimit_cofan_of_isColimit_cofan_toSheaf B S hS X c hc⟩
  exact hasColimit_of_iso Discrete.natIsoFunctor

/-- The two inclusions of a coproduct in the spaces-étale site of `X` are monomorphisms. -/
theorem mono_of_isColimit_cofan {Y : WalkingPair → SpacesEtale B S hS X}
    {U : SpacesEtale B S hS X} (i : ∀ p, Y p ⟶ U) (hU : IsColimit (Cofan.mk U i))
    (p : WalkingPair) : Mono (i p) := by
  obtain ⟨hsh⟩ := nonempty_isColimit_cofan_toSheaf B S hS X i hU
  exact (toSheaf B S hS X).mono_of_mono_map
    (Sheaf.mono_cofan_inj_bigFppfOver (fun p => (toSheaf B S hS X).map (i p)) hsh p)

/-- The empty sieve is a covering sieve of an object of the spaces-étale site of `X` with no
points. -/
theorem bot_mem_topology (W : SpacesEtale B S hS X)
    (hW : IsEmpty (points B S hS ((toSpaces B S hS X).obj W).obj)) :
    (⊥ : Sieve W) ∈ topology B S hS X W := by
  let E : PreZeroHypercover.{u + 1} W := ⟨PEmpty.{u + 2}, PEmpty.elim, fun k => k.elim⟩
  have hmem : E.presieve₀ ∈ precoverage B S hS X W := ⟨E, rfl, fun x => hW.elim x⟩
  have hgen : Sieve.generate E.presieve₀ = (⊥ : Sieve W) := by
    refine le_antisymm ?_ bot_le
    rintro V f ⟨Z, g, h, ⟨k⟩, -⟩
    exact k.elim
  exact hgen ▸ Precoverage.generate_mem_toGrothendieck hmem

/-- **An object of the spaces-étale site of `X` mapping to two different members of a
coproduct compatibly over the coproduct has no points, so the empty sieve covers it.** -/
theorem bot_mem_topology_of_isColimit_cofan {Y : WalkingPair → SpacesEtale B S hS X}
    {U : SpacesEtale B S hS X} (i : ∀ p, Y p ⟶ U) (hU : IsColimit (Cofan.mk U i))
    {W : SpacesEtale B S hS X} {p p' : WalkingPair} (hpp' : p ≠ p')
    (a : W ⟶ Y p) (b : W ⟶ Y p') (hab : a ≫ i p = b ≫ i p') :
    (⊥ : Sieve W) ∈ topology B S hS X W := by
  obtain ⟨hsh⟩ := nonempty_isColimit_cofan_toSheaf B S hS X i hU
  refine bot_mem_topology B S hS X W ⟨fun x => ?_⟩
  obtain ⟨q, rfl⟩ := Quot.exists_rep x
  have himg : ((toSpaces B S hS X).map (i p)).hom.app (op q.siteObject)
        (((toSpaces B S hS X).map a).hom.app (op q.siteObject) q.value) =
      ((toSpaces B S hS X).map (i p')).hom.app (op q.siteObject)
        (((toSpaces B S hS X).map b).hom.app (op q.siteObject) q.value) := by
    have hcongr := congrArg
      (fun f : W ⟶ U => ((toSpaces B S hS X).map f).hom.app (op q.siteObject) q.value) hab
    simpa only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app, types_comp_apply] using hcongr
  have hT : IsEmpty ((BigFppfOver.toScheme B S hS).obj q.siteObject) :=
    Sheaf.isEmpty_toScheme_of_eq_of_ne (fun p => (toSheaf B S hS X).map (i p)) hsh hpp'
      (((toSpaces B S hS X).map a).hom.app (op q.siteObject) q.value)
      (((toSpaces B S hS X).map b).hom.app (op q.siteObject) q.value) himg
  have huniqK : Unique ((BigFppfOver.toScheme B S hS).obj q.siteObject) :=
    inferInstanceAs (Unique (Spec (.of q.carrier)))
  exact hT.elim huniqK.default

/-- **The two inclusions of a coproduct in the spaces-étale site of `X` are jointly
surjective on points.** -/
theorem exists_pointsMap_eq_of_isColimit_cofan {Y : WalkingPair → SpacesEtale B S hS X}
    {U : SpacesEtale B S hS X} (i : ∀ p, Y p ⟶ U) (hU : IsColimit (Cofan.mk U i))
    (x : points B S hS ((toSpaces B S hS X).obj U).obj) :
    ∃ (p : WalkingPair) (y : points B S hS ((toSpaces B S hS X).obj (Y p)).obj),
      pointsMap B S hS ((toSpaces B S hS X).obj (Y p)).obj
        ((toSpaces B S hS X).map (i p)).hom y = x := by
  obtain ⟨hsh⟩ := nonempty_isColimit_cofan_toSheaf B S hS X i hU
  obtain ⟨q, rfl⟩ := Quot.exists_rep x
  obtain ⟨W', pr, hoi, hsec, hdisj, hcov, huniv⟩ :=
    Sheaf.exists_clopen_decomposition_of_isColimit_cofan
      (fun p => (toSheaf B S hS X).map (i p)) hsh q.siteObject q.value
  have huniqK : Unique ((BigFppfOver.toScheme B S hS).obj q.siteObject) :=
    inferInstanceAs (Unique (Spec (.of q.carrier)))
  obtain ⟨p₀, hp₀⟩ := hcov huniqK.default
  have hoi₀ := hoi p₀
  have hiso : IsIso ((BigFppfOver.toScheme B S hS).map (pr p₀)) := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ (TopologicalSpace.Opens.ext ?_)
    rw [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top]
    refine Set.eq_univ_of_forall fun w => ?_
    rw [Subsingleton.elim w huniqK.default]
    exact hp₀
  have hcomm : inv ((BigFppfOver.toScheme B S hS).map (pr p₀)) ≫
      B.inclusion.map (W' p₀).hom = B.inclusion.map q.siteObject.hom := by
    have h : (BigFppfOver.toScheme B S hS).map (pr p₀) ≫
        B.inclusion.map q.siteObject.hom = B.inclusion.map (W' p₀).hom := by
      rw [← Over.w (pr p₀), Functor.map_comp]
      rfl
    rw [← h, IsIso.inv_hom_id_assoc]
  obtain ⟨einv, heinv⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS
    (inv ((BigFppfOver.toScheme B S hS).map (pr p₀))) hcomm
  have heid : einv ≫ pr p₀ = 𝟙 q.siteObject :=
    (BigFppfOver.toScheme B S hS).map_injective (by
      rw [Functor.map_comp, heinv, IsIso.inv_hom_id,
        (BigFppfOver.toScheme B S hS).map_id])
  obtain ⟨z, hz⟩ := hsec p₀
  have hz' : ((toSpaces B S hS X).map (i p₀)).hom.app (op (W' p₀)) z =
      ((toSpaces B S hS X).obj U).obj.map (pr p₀).op q.value := hz
  have hval : ((toSpaces B S hS X).map (i p₀)).hom.app (op q.siteObject)
      ((((toSpaces B S hS X).obj (Y p₀)).obj).map einv.op z) = q.value := by
    rw [NatTrans.naturality_apply ((toSpaces B S hS X).map (i p₀)).hom einv.op z, hz',
      ← Functor.map_comp_apply, ← op_comp, heid, op_id, Functor.map_id_apply]
  refine ⟨p₀, Quot.mk _ (@FieldValuedPoint.mk B S hS ((toSpaces B S hS X).obj (Y p₀)).obj
    q.carrier q.field q.contained q.toBase
    ((((toSpaces B S hS X).obj (Y p₀)).obj).map einv.op z)), ?_⟩
  rw [pointsMap_class]
  exact congrArg (Quot.mk _) (congrArg (fun v =>
    @FieldValuedPoint.mk B S hS ((toSpaces B S hS X).obj U).obj
      q.carrier q.field q.contained q.toBase v) hval)

/-- **The two inclusions of a coproduct in the spaces-étale site of `X` generate a covering
sieve.** -/
theorem ofArrows_mem_topology_of_isColimit_cofan {Y : WalkingPair → SpacesEtale B S hS X}
    {U : SpacesEtale B S hS X} (i : ∀ p, Y p ⟶ U) (hU : IsColimit (Cofan.mk U i)) :
    Sieve.ofArrows (fun k : ULift.{u + 1} WalkingPair => Y k.down) (fun k => i k.down)
      ∈ topology B S hS X U := by
  refine Precoverage.generate_mem_toGrothendieck
    ⟨⟨ULift.{u + 1} WalkingPair, fun k => Y k.down, fun k => i k.down⟩, rfl, fun x => ?_⟩
  obtain ⟨p, y, hy⟩ := exists_pointsMap_eq_of_isColimit_cofan B S hS X i hU x
  exact ⟨⟨p⟩, y, hy⟩

/-! ### Extension by zero of the constant sheaf -/

/-- The free abelian sheaf on the representable presheaf of an object of the spaces-étale
site of `X`. -/
noncomputable def freeAbelianRepresentableSheaf :
    SpacesEtale B S hS X ⥤ Sheaf (topology B S hS X) AddCommGrpCat.{u + 1} :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf (topology B S hS X) _

/-- Restriction of abelian sheaves to a slice of the spaces-étale site has a left adjoint,
built from left Kan extension and sheafification; instance search does not find the
universally quantified Kan extension hypothesis on its own. -/
instance isRightAdjoint_sheafPushforwardContinuous_forget (U : SpacesEtale B S hS X) :
    ((Over.forget U).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      ((topology B S hS X).over U) (topology B S hS X)).IsRightAdjoint :=
  haveI : ∀ F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}, (Over.forget U).op.HasLeftKanExtension F :=
    fun _ => inferInstance
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _).isRightAdjoint

/-- Extension by zero of abelian sheaves on the spaces-étale site of `X`: the left adjoint
to restriction along the forgetful functor from the slice site. -/
noncomputable abbrev extensionByZero (U : SpacesEtale B S hS X) :=
  (Over.forget U).sheafPullback AddCommGrpCat.{u + 1}
    ((topology B S hS X).over U) (topology B S hS X)

/-- The defining adjunction of extension by zero with restriction. -/
noncomputable def extensionByZeroAdjunction (U : SpacesEtale B S hS X) :
    extensionByZero B S hS X U ⊣
      (topology B S hS X).overPullback AddCommGrpCat.{u + 1} U :=
  (Over.forget U).sheafAdjunctionContinuous _ _ _

/-- Extension by zero of the constant integer sheaf on the slice site. -/
noncomputable abbrev extensionByZeroConstant (U : SpacesEtale B S hS X) :=
  (extensionByZero B S hS X U).obj
    ((constantSheaf ((topology B S hS X).over U)
      AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))

/-- The extension-by-zero and constant-sheaf adjunctions identify maps from `j_{U!} ℤ` with
homomorphisms from `ℤ` to sections at `U`. -/
noncomputable def extensionByZeroConstantHomEquiv (U : SpacesEtale B S hS X)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    (extensionByZeroConstant B S hS X U ⟶ F) ≃
      (AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶ F.obj.obj (Opposite.op U)) :=
  ((extensionByZeroAdjunction B S hS X U).homEquiv _ _).trans
    ((constantSheafAdj ((topology B S hS X).over U)
      AddCommGrpCat.{u + 1} Over.mkIdTerminal).homEquiv _ _)

/-- The canonical covariant map of extensions by zero induced by `i : U ⟶ V`, whose adjoint is
the universal section at `V` restricted along `i`. -/
noncomputable def extensionByZeroConstantMap {U V : SpacesEtale B S hS X} (i : U ⟶ V) :
    extensionByZeroConstant B S hS X U ⟶ extensionByZeroConstant B S hS X V :=
  (extensionByZeroConstantHomEquiv B S hS X U _).symm
    ((extensionByZeroConstantHomEquiv B S hS X V _ (𝟙 _)) ≫
      (extensionByZeroConstant B S hS X V).obj.map i.op)

/-- The identification of maps out of `j_{U!} ℤ` with sections at `U` is natural in the
sheaf: composing with a morphism of sheaves corresponds to taking its component at `U`. -/
theorem extensionByZeroConstantHomEquiv_comp (U : SpacesEtale B S hS X)
    {F F' : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}}
    (h : extensionByZeroConstant B S hS X U ⟶ F) (k : F ⟶ F') :
    extensionByZeroConstantHomEquiv B S hS X U F' (h ≫ k) =
      extensionByZeroConstantHomEquiv B S hS X U F h ≫ k.hom.app (Opposite.op U) := by
  simp only [extensionByZeroConstantHomEquiv]
  rfl

/-- The identification of maps out of `j_{U!} ℤ` with sections at `U` turns the canonical map
induced by `i : U ⟶ V` into restriction of sections along `i`. -/
theorem extensionByZeroConstantHomEquiv_map {U V : SpacesEtale B S hS X} (i : U ⟶ V)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1})
    (g : extensionByZeroConstant B S hS X V ⟶ F) :
    extensionByZeroConstantHomEquiv B S hS X U F
        (extensionByZeroConstantMap B S hS X i ≫ g) =
      extensionByZeroConstantHomEquiv B S hS X V F g ≫ F.obj.map i.op := by
  rw [extensionByZeroConstantHomEquiv_comp, extensionByZeroConstantMap,
    Equiv.apply_symm_apply, Category.assoc, NatTrans.naturality,
    ← Category.assoc, ← extensionByZeroConstantHomEquiv_comp, Category.id_comp]

/-- **A section of an abelian sheaf over a coproduct of the spaces-étale site of `X` is the
same thing as a compatible family of sections over the members.** Precisely, every family of
maps `extensionByZeroConstant (Y p) ⟶ T` factors uniquely through the canonical maps into
`extensionByZeroConstant U`. -/
theorem existsUnique_hom_extensionByZeroConstant
    {Y : WalkingPair → SpacesEtale B S hS X} {U : SpacesEtale B S hS X} (i : ∀ p, Y p ⟶ U)
    (hU : IsColimit (Cofan.mk U i))
    (T : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1})
    (leg : ∀ p, extensionByZeroConstant B S hS X (Y p) ⟶ T) :
    ∃! m : extensionByZeroConstant B S hS X U ⟶ T,
      ∀ p, extensionByZeroConstantMap B S hS X (i p) ≫ m = leg p := by
  classical
  have hmono := mono_of_isColimit_cofan B S hS X i hU
  have hcov := ofArrows_mem_topology_of_isColimit_cofan B S hS X i hU
  have hx : ∀ ⦃W : SpacesEtale B S hS X⦄ ⦃k l : ULift.{u + 1} WalkingPair⦄
      (a : W ⟶ Y k.down) (b : W ⟶ Y l.down), a ≫ i k.down = b ≫ i l.down →
      extensionByZeroConstantHomEquiv B S hS X (Y k.down) T (leg k.down) ≫ T.obj.map a.op =
        extensionByZeroConstantHomEquiv B S hS X (Y l.down) T (leg l.down) ≫ T.obj.map b.op := by
    intro W k l a b hab
    by_cases hkl : k.down = l.down
    · obtain ⟨k⟩ := k
      obtain ⟨l⟩ := l
      subst hkl
      have := hmono k
      rw [(cancel_mono (i k)).1 hab]
    · have hbot := bot_mem_topology_of_isColimit_cofan B S hS X i hU hkl a b hab
      have hsub : Subsingleton (AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶
          T.obj.obj (Opposite.op W)) :=
        (T.property (AddCommGrpCat.of (ULift.{u + 1} ℤ))).subsingleton_obj_of_bot_mem _ hbot
      exact hsub.elim _ _
  obtain ⟨α, hα, hαuniq⟩ := Presheaf.IsSheaf.existsUnique_amalgamation_ofArrows
    (P := T.obj) T.property (fun k : ULift.{u + 1} WalkingPair => i k.down) hcov
    (fun k => extensionByZeroConstantHomEquiv B S hS X (Y k.down) T (leg k.down)) hx
  refine ⟨(extensionByZeroConstantHomEquiv B S hS X U T).symm α, fun p => ?_, fun m hm => ?_⟩
  · refine (extensionByZeroConstantHomEquiv B S hS X (Y p) T).injective ?_
    rw [extensionByZeroConstantHomEquiv_map, Equiv.apply_symm_apply]
    exact hα ⟨p⟩
  · refine (extensionByZeroConstantHomEquiv B S hS X U T).injective ?_
    rw [Equiv.apply_symm_apply]
    refine hαuniq _ fun k => ?_
    rw [← extensionByZeroConstantHomEquiv_map]
    exact congrArg _ (hm k.down)

/-- The two canonical maps induced by the inclusions into a binary coproduct of the
spaces-étale site give a direct-sum decomposition of extensions by zero. -/
@[stacks 0722 "coproduct_sum"]
theorem extensionByZeroConstant_preservesBinaryCoproduct
    (U₁ U₂ U : SpacesEtale B S hS X)
    (i₁ : U₁ ⟶ U) (i₂ : U₂ ⟶ U)
    (hU : IsColimit (BinaryCofan.mk i₁ i₂)) :
    Nonempty (IsColimit (BinaryCofan.mk
      (extensionByZeroConstantMap B S hS X i₁)
      (extensionByZeroConstantMap B S hS X i₂))) := by
  have hUcof : IsColimit (Cofan.mk
      (f := fun p : WalkingPair => WalkingPair.casesOn p U₁ U₂) U
      (fun p => WalkingPair.casesOn p i₁ i₂)) :=
    hU.ofIsoColimit (Cocone.ext (Iso.refl _) fun j => by
      rcases j with ⟨⟨⟩⟩ <;> exact Category.comp_id _)
  have key := fun s : BinaryCofan (extensionByZeroConstant B S hS X U₁)
      (extensionByZeroConstant B S hS X U₂) =>
    existsUnique_hom_extensionByZeroConstant B S hS X _ hUcof s.pt
      (fun p => WalkingPair.casesOn p s.inl s.inr)
  exact ⟨BinaryCofan.isColimitMk (fun s => (key s).choose)
    (fun s => (key s).choose_spec.1 WalkingPair.left)
    (fun s => (key s).choose_spec.1 WalkingPair.right)
    (fun s m h₁ h₂ => (key s).choose_spec.2 m fun p => by cases p; exacts [h₁, h₂])⟩

end Space.SpacesEtale

end Coproduct

end AlgebraicGeometry

end
