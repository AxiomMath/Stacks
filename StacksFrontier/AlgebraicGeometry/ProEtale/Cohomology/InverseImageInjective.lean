module

public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.EtaleCover
public import StacksFrontier.AlgebraicGeometry.ProEtale.FilteredColimitsOfProetaleCohomology
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.LimitPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ProetaleEtaleSheafPullbackAbelian
public import StacksFrontier.CategoryTheory.MorphismProperty.OverLimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.CofilteredLimitOfFamilies
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongAFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.InjectiveSheafVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingAlongAFunctorEssentiallySmall

/-!
# The pro-étale inverse image of an injective étale sheaf is acyclic on affines

Let `X` be a scheme and let `ε : X_proétale → X_étale` be the morphism of sites given by the
inclusion of the small étale site into the small pro-étale site.  For an injective abelian sheaf
`ℐ` on `X_étale` the pro-étale sheaf `ε⁻¹ℐ` has no higher cohomology over the affine objects of
`X_proétale` which are ind-étale over an affine object of `X_étale`; in particular, if `X` is
affine, `H^p(X_proétale, ε⁻¹ℐ) = 0` for `p > 0` (Stacks 099U).

## Main definitions

* `AlgebraicGeometry.ProEtale.IsAffineIndEtaleOverEtale`: the affine objects of `X_proétale`
  which are ind-étale over an affine object of `X_étale`.

## Main results

* `AlgebraicGeometry.ProEtale.exists_cofilteredSystem_of_indEtale`: a finite family of affine
  objects ind-étale over an affine object is a cofiltered limit of families of affine schemes
  étale over it.
* `AlgebraicGeometry.ProEtale.exists_indEtale_covering_le`: finite coverings by affine objects
  ind-étale over the base are cofinal among the coverings of an affine object.
* `AlgebraicGeometry.ProEtale.isAffine_left_prod` and
  `AlgebraicGeometry.ProEtale.isSeparated_left_prod`: iterated fibre products of affine objects
  over a separated, resp. quasi-separated, object are affine, resp. quasi-compact and separated.
* `AlgebraicGeometry.ProEtale.exists_isLimit_baseChange_of_isPullback`: a family base changed
  from a stage of a limit is the limit of its base changes to the later stages.
* `AlgebraicGeometry.ProEtale.isZero_cechCohomology_of_isPullback`: the Čech complex of `ε⁻¹ℐ`
  along such a family is acyclic in positive degrees, for a limit of quasi-compact and
  quasi-separated étale `X`-schemes with affine transition morphisms.
* `AlgebraicGeometry.ProEtale.isZero_cechCohomology_of_etale` and
  `AlgebraicGeometry.ProEtale.isZero_cechCohomology_of_indEtale`: the Čech complex of `ε⁻¹ℐ`
  along a finite family of affine schemes étale, resp. ind-étale, over an object which is a limit
  of affine étale `X`-schemes is acyclic in positive degrees.
* `AlgebraicGeometry.ProEtale.subsingleton_ext_proetaleInverseImage_of_injective`: the vanishing
  of the higher cohomology of `ε⁻¹ℐ` over an affine object of `X_proétale` ind-étale over an
  affine étale `X`-scheme, for an arbitrary scheme `X`.
* `AlgebraicGeometry.ProEtale.subsingleton_sheafH_proetaleInverseImage_of_injective`:
  **Stacks 099U**.

## Implementation notes

The proof is the source's.  Cohomology over an object is computed by the Čech criterion of
Stacks 03F9 for the collection of affine objects ind-étale over an affine étale `X`-scheme and
the finite pro-étale coverings of such objects by affine objects ind-étale over them, which are
cofinal by Proposition 097Z.  The source takes the affine objects ind-étale over `X` itself, for
`X` affine; allowing an arbitrary affine étale `X`-scheme in place of `X` gives the same proof
for an arbitrary scheme `X`, and contains the source's collection when `X` is affine.

The Čech complex of `ε⁻¹ℐ` along such a covering is the filtered colimit of the Čech complexes
along families of affine schemes étale over the base, because sections of `ε⁻¹ℐ` over a limit
are the colimit of sections over the stages (Stacks 099S).  Each of those is in turn a filtered
colimit of Čech complexes along families of affine étale `X`-schemes, which are the Čech
complexes of `ε_*ε⁻¹ℐ = ℐ` (Stacks 099T), and so are acyclic in positive degrees because `ℐ` is
injective.  The families need not be coverings: the higher Čech cohomology of an injective sheaf
vanishes along every family.

Pro-étale cohomology is `Ext` out of the constant sheaf `ℤ`, `CategoryTheory.Sheaf.H`, and
cohomology over an object `U` is `Ext` out of the free abelian sheaf on `U`.  The inverse image
`ε⁻¹` is an arbitrary left adjoint of `ε_*`.

## References

* [Stacks Project, Tag 099U](https://stacks.math.columbia.edu/tag/099U)
* [Stacks Project, Tag 099S](https://stacks.math.columbia.edu/tag/099S)
* [Stacks Project, Tag 099T](https://stacks.math.columbia.edu/tag/099T)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 097Z](https://stacks.math.columbia.edu/tag/097Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.CechSite

universe w v u

namespace AlgebraicGeometry.ProEtale

variable {X : Scheme.{u}}

/-- Affine morphisms of schemes are stable under composition. -/
local instance : MorphismProperty.IsStableUnderComposition
    (@IsAffineHom : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsMultiplicative.toIsStableUnderComposition

/-- Étale morphisms of schemes are stable under composition. -/
local instance : MorphismProperty.IsStableUnderComposition (@Etale : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsMultiplicative.toIsStableUnderComposition

/-- Weakly étale morphisms of schemes are stable under composition. -/
local instance : MorphismProperty.IsStableUnderComposition
    (@WeaklyEtale : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsMultiplicative.toIsStableUnderComposition

/-- The class of affine morphisms of schemes respects isomorphisms. -/
local instance : MorphismProperty.RespectsIso (@IsAffineHom : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

/-- The class of étale morphisms of schemes respects isomorphisms. -/
local instance : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

/-! ### Iterated fibre products in the small pro-étale site -/

/-- The forgetful functor from the small pro-étale site to schemes preserves iterated fibre
products of a family. -/
private lemma preservesLimit_overPost_forget {U : X.ProEt} (E : PreZeroHypercover.{w} U) :
    ∀ (n : ℕ) (t : Fin (n + 1) → E.I₀),
      PreservesLimit (Discrete.functor fun a ↦ Over.mk (E.f (t a)))
        (Over.post (Scheme.ProEt.forget X ⋙ Over.forget X)) :=
  Stacks.Sites.preservesLimit_fibreProducts_overPost _ E (fun _ _ _ ↦ inferInstance)
    (fun _ _ _ ↦ inferInstance)

/-- The underlying morphism of schemes of the structure morphism of an iterated fibre product of
a family in the small pro-étale site has every property of the underlying morphisms of the
members which is stable under base change and composition. -/
lemma prop_left_hom_prod (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition] [P.RespectsIso] {U : X.ProEt} (E : PreZeroHypercover.{w} U)
    (hE : ∀ k, P (E.f k).left) (n : ℕ) (t : Fin (n + 1) → E.I₀) :
    P (∏ᶜ fun a ↦ Over.mk (E.f (t a))).hom.left := by
  have := preservesLimit_overPost_forget E n t
  exact P.prop_hom_pt_of_isLimit_fan (isLimitFanMkObjOfIsLimit
    (Over.post (Scheme.ProEt.forget X ⋙ Over.forget X)) _ _ (productIsProduct _))
    fun a ↦ hE (t a)

/-- The projection of an iterated fibre product of a family in the small pro-étale site to its
first factor, on underlying schemes, has every property of the underlying morphisms of the members
which is stable under base change and composition and satisfies cancellation against the
underlying morphism of the first member. -/
lemma prop_left_π_zero (P W : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition] [P.RespectsIso] [P.HasOfPostcompProperty W] {U : X.ProEt}
    (E : PreZeroHypercover.{w} U) (hE : ∀ k, P (E.f k).left) (n : ℕ) (t : Fin (n + 1) → E.I₀)
    (hW : W (E.f (t 0)).left) :
    P (Pi.π (fun a ↦ Over.mk (E.f (t a))) 0).left.left := by
  have h := prop_left_hom_prod P E hE n t
  have hw : (Pi.π (fun a ↦ Over.mk (E.f (t a))) 0).left.left ≫ (E.f (t 0)).left =
      (∏ᶜ fun a ↦ Over.mk (E.f (t a))).hom.left :=
    congrArg (fun φ ↦ φ.left) (Over.w (Pi.π (fun a ↦ Over.mk (E.f (t a))) 0))
  rw [← hw] at h
  exact MorphismProperty.of_postcomp _ _ _ hW h

/-- An iterated fibre product of a family of objects of the small pro-étale site with affine
underlying schemes, over an object with separated underlying scheme, has affine underlying
scheme. -/
lemma isAffine_left_prod {U : X.ProEt} [U.left.IsSeparated] (E : PreZeroHypercover.{w} U)
    (hE : ∀ k, IsAffine (E.X k).left) (n : ℕ) (t : Fin (n + 1) → E.I₀) :
    IsAffine (∏ᶜ fun a ↦ Over.mk (E.f (t a))).left.left := by
  have hA (k : E.I₀) : IsAffineHom (E.f k).left := by
    have := hE k
    have : IsAffineHom ((E.f k).left ≫ terminal.from U.left) := by
      rw [terminal.comp_from]
      infer_instance
    exact IsAffineHom.of_comp _ (terminal.from U.left)
  have : IsAffine (Over.mk (E.f (t 0))).left.left := hE (t 0)
  have := prop_left_π_zero @IsAffineHom @IsSeparated E hA n t inferInstance
  exact isAffine_of_isAffineHom (Pi.π (fun a ↦ Over.mk (E.f (t a))) 0).left.left

/-- An iterated fibre product of a family of objects of the small pro-étale site with affine
underlying schemes, over an object with quasi-separated underlying scheme, has quasi-compact and
separated underlying scheme: its projection to the first factor is quasi-compact and
separated. -/
lemma isSeparated_left_prod {U : X.ProEt} [QuasiSeparatedSpace U.left]
    (E : PreZeroHypercover.{w} U) (hE : ∀ k, IsAffine (E.X k).left) (n : ℕ)
    (t : Fin (n + 1) → E.I₀) :
    (∏ᶜ fun a ↦ Over.mk (E.f (t a))).left.left.IsSeparated ∧
      CompactSpace (∏ᶜ fun a ↦ Over.mk (E.f (t a))).left.left := by
  have hS (k : E.I₀) : IsSeparated (E.f k).left := by
    have := hE k
    infer_instance
  have hC (k : E.I₀) : QuasiCompact (E.f k).left := by
    have := hE k
    have : QuasiCompact ((E.f k).left ≫ terminal.from U.left) := by
      rw [terminal.comp_from]
      infer_instance
    exact QuasiCompact.of_comp _ (terminal.from U.left)
  have : IsAffine (Over.mk (E.f (t 0))).left.left := hE (t 0)
  have : MorphismProperty.RespectsIso (@QuasiCompact : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : IsSeparated (Pi.π (fun a ↦ Over.mk (E.f (t a))) 0).left.left :=
    prop_left_π_zero @IsSeparated ⊤ E hS n t trivial
  have hπC := prop_left_π_zero @QuasiCompact @QuasiSeparated E hC n t inferInstance
  refine ⟨⟨?_⟩, @QuasiCompact.compactSpace_of_compactSpace _ _ _ hπC _⟩
  rw [← terminal.comp_from (Pi.π (fun a ↦ Over.mk (E.f (t a))) 0).left.left]
  infer_instance

/-! ### Affine objects ind-étale over an affine étale `X`-scheme -/

variable (X) in
/-- The objects `V` of the small pro-étale site of `X` with affine underlying scheme which are
ind-étale over an affine object `U₀` of the small étale site: `V` maps to `U₀` by a morphism
inducing an ind-étale ring map `Γ(U₀) → Γ(V)`.  If `X` is affine, `X` itself is one, and so is
every affine object of `X_étale`. -/
def IsAffineIndEtaleOverEtale : ObjectProperty X.ProEt := fun V ↦
  IsAffine V.left ∧ ∃ (U₀ : X.Etale) (g : V ⟶ X.etaleToProetale.obj U₀),
    IsAffine U₀.left ∧ MorphismProperty.ind.{u} CommRingCat.etale g.left.appTop

/-- An affine object of the small étale site is ind-étale over itself. -/
lemma isAffineIndEtaleOverEtale_etaleToProetale_obj (U₀ : X.Etale) [IsAffine U₀.left] :
    IsAffineIndEtaleOverEtale X (X.etaleToProetale.obj U₀) :=
  ⟨inferInstanceAs (IsAffine U₀.left), U₀, 𝟙 _, inferInstance, by
    show MorphismProperty.ind.{u} CommRingCat.etale (Scheme.Hom.appTop (𝟙 U₀.left))
    rw [Scheme.Hom.id_appTop]
    exact indEtale_of_isIso _⟩

/-- An affine object of the small pro-étale site which is ind-étale over one which is ind-étale
over an affine étale `X`-scheme is again ind-étale over that scheme (Stacks 097K). -/
lemma IsAffineIndEtaleOverEtale.of_hom {U V : X.ProEt} (hU : IsAffineIndEtaleOverEtale X U)
    [IsAffine V.left] (f : V ⟶ U) (hf : MorphismProperty.ind.{u} CommRingCat.etale f.left.appTop) :
    IsAffineIndEtaleOverEtale X V := by
  obtain ⟨-, U₀, g, hU₀, hg⟩ := hU
  refine ⟨inferInstance, U₀, f ≫ g, hU₀, ?_⟩
  show MorphismProperty.ind.{u} CommRingCat.etale (f.left ≫ g.left).appTop
  rw [Scheme.Hom.comp_appTop]
  exact CommRingCat.ind_etale_comp _ _ hg hf

/-- An object ind-étale over an affine étale `X`-scheme is the limit of a cofiltered system of
affine objects of the small étale site. -/
theorem IsAffineIndEtaleOverEtale.exists_isLimit {V : X.ProEt}
    (hV : IsAffineIndEtaleOverEtale X V) :
    ∃ (A : Type u) (_ : SmallCategory A) (_ : IsCofiltered A) (Ub : A ⥤ X.Etale)
      (πU : (Functor.const A).obj V ⟶ Ub ⋙ X.etaleToProetale),
      (∀ a, IsAffine (Ub.obj a).left) ∧
        Nonempty (IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone (Cone.mk V πU))) := by
  let : Category.{u} (MorphismProperty.Over (@Etale : MorphismProperty Scheme.{u}) ⊤ X) :=
    inferInstanceAs (Category X.Etale)
  obtain ⟨hVa, U₀, g, hU₀, hg⟩ := hV
  have : IsAffine (X.etaleToProetale.obj U₀).left := hU₀
  obtain ⟨A, _, _, D, d, p, hDa, hd, hpd, ⟨hc⟩⟩ := exists_isLimit_of_indEtale_appTop g.left hg
  let Ub : A ⥤ X.Etale := MorphismProperty.Over.systemOver (@Etale) U₀ D d hd
  let πU : (Functor.const A).obj V ⟶ Ub ⋙ X.etaleToProetale :=
    { app a := MorphismProperty.Over.homMk (p.app a) (by
          show p.app a ≫ d.app a ≫ U₀.hom = V.hom
          exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ U₀.hom) (hpd a))).trans
            (MorphismProperty.Over.w g)) trivial
      naturality {a b} f := MorphismProperty.Over.Hom.ext (by
          show 𝟙 _ ≫ p.app b = p.app a ≫ D.map f
          simpa using p.naturality f) }
  exact ⟨A, inferInstance, inferInstance, Ub, πU, hDa, ⟨hc⟩⟩

/-- A single morphism of the small pro-étale site which is surjective, quasi-compact and weakly
étale on underlying schemes generates a covering sieve. -/
private lemma generate_singleton_mem_topology {V W : X.ProEt} (qo : W ⟶ V)
    [Surjective ((Scheme.ProEt.forget X ⋙ Over.forget X).map qo)]
    [QuasiCompact ((Scheme.ProEt.forget X ⋙ Over.forget X).map qo)] (hqw : WeaklyEtale qo.left) :
    Sieve.generate (Presieve.singleton qo) ∈ Scheme.ProEt.topology X V := by
  refine Precoverage.generate_mem_toGrothendieck ?_
  change Presieve.map (Scheme.ProEt.forget X ⋙ Over.forget X) (Presieve.singleton qo) ∈
    Scheme.proetalePrecoverage _
  rw [Presieve.map_singleton]
  exact Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) hqw

variable (X) in
/-- **Every object of the small pro-étale site is covered by objects ind-étale over affine étale
`X`-schemes.** Cover the underlying scheme by affine opens mapping into affine opens of `X`, and
refine each of them by a single affine object ind-étale over that affine open (Stacks 097Z). -/
theorem generate_isAffineIndEtaleOverEtale_mem (V : X.ProEt) :
    Sieve.generate (fun (W : X.ProEt) (_ : W ⟶ V) ↦ IsAffineIndEtaleOverEtale X W) ∈
      Scheme.ProEt.topology X V := by
  let S := Sieve.generate (fun (W : X.ProEt) (_ : W ⟶ V) ↦
    IsAffineIndEtaleOverEtale X W)
  let 𝒰 : V.left.OpenCover := (X.affineCover.pullback₁ V.hom).bind
    fun i ↦ (pullback V.hom (X.affineCover.f i)).affineCover
  have hwe (k : 𝒰.I₀) : WeaklyEtale (𝒰.f k ≫ V.hom) :=
    have : WeaklyEtale V.hom := V.prop
    inferInstance
  let W (k : 𝒰.I₀) : X.ProEt := @Scheme.ProEt.mk _ _ (𝒰.f k ≫ V.hom) (hwe k)
  let ι (k : 𝒰.I₀) : W k ⟶ V := MorphismProperty.Over.homMk (𝒰.f k) rfl trivial
  have hT : Sieve.generate (Presieve.ofArrows W ι) ∈ Scheme.ProEt.topology X V := by
    refine Precoverage.generate_mem_toGrothendieck ?_
    show Presieve.map (Scheme.ProEt.forget X ⋙ Over.forget X) (Presieve.ofArrows W ι) ∈
      Scheme.proetalePrecoverage _
    rw [Presieve.map_ofArrows]
    have : MorphismProperty.ContainsIdentities (@WeaklyEtale : MorphismProperty Scheme.{u}) :=
      ⟨fun _ ↦ inferInstance⟩
    exact Scheme.zariskiPrecoverage_le_propQCPrecoverage _ 𝒰.mem₀
  refine (Scheme.ProEt.topology X).transitive hT S fun Y f hf ↦ ?_
  obtain ⟨Z, a, b, ⟨k⟩, rfl⟩ := hf
  rw [Sieve.pullback_comp]
  refine (Scheme.ProEt.topology X).pullback_stable a ?_
  obtain ⟨i, j⟩ := k
  have hXi : IsAffine (X.affineCover.X i) := inferInstanceAs (IsAffine (Spec _))
  have : IsOpenImmersion (X.affineCover.f i) := X.affineCover.map_prop i
  have hWk : IsAffine (W ⟨i, j⟩).left := inferInstanceAs (IsAffine (Spec _))
  let h : (W ⟨i, j⟩).left ⟶ X.affineCover.X i :=
    (pullback V.hom (X.affineCover.f i)).affineCover.f j ≫ pullback.snd _ _
  have hh : h ≫ X.affineCover.f i = (W ⟨i, j⟩).hom := by
    show _ = ((pullback V.hom (X.affineCover.f i)).affineCover.f j ≫ pullback.fst _ _) ≫ V.hom
    simp only [h, Category.assoc, pullback.condition]
    rfl
  have hhwe : WeaklyEtale h := by
    have h₁ : WeaklyEtale (h ≫ X.affineCover.f i) := hh ▸ (W ⟨i, j⟩).prop
    have h₂ : WeaklyEtale (X.affineCover.f i) := inferInstance
    exact MorphismProperty.of_postcomp (W := @WeaklyEtale) (W' := @WeaklyEtale) h
      (X.affineCover.f i) h₂ h₁
  obtain ⟨W', q, hW'a, hqs, hqwe, hind⟩ := exists_surjective_weaklyEtale_indEtale_appTop h
  have hqwe' : WeaklyEtale (q ≫ (W ⟨i, j⟩).hom) :=
    have : WeaklyEtale (W ⟨i, j⟩).hom := (W ⟨i, j⟩).prop
    inferInstance
  let W'' : X.ProEt := @Scheme.ProEt.mk _ _ (q ≫ (W ⟨i, j⟩).hom) hqwe'
  let qo : W'' ⟶ W ⟨i, j⟩ := MorphismProperty.Over.homMk q rfl trivial
  have hW'' : IsAffineIndEtaleOverEtale X W'' := by
    have : Etale (X.affineCover.f i) := inferInstance
    refine ⟨hW'a, Scheme.Etale.mk (X.affineCover.f i),
      MorphismProperty.Over.homMk (q ≫ h) (by
        show (q ≫ h) ≫ X.affineCover.f i = q ≫ (W ⟨i, j⟩).hom
        rw [Category.assoc, hh]) trivial, hXi, hind⟩
  refine (Scheme.ProEt.topology X).superset_covering ?_ (?_ : Sieve.generate
    (Presieve.singleton qo) ∈ Scheme.ProEt.topology X (W ⟨i, j⟩))
  · rw [Sieve.generate_le_iff]
    rintro _ _ ⟨⟩
    exact Sieve.le_generate _ _ _ hW''
  · have : Surjective ((Scheme.ProEt.forget X ⋙ Over.forget X).map qo) := hqs
    have : QuasiCompact ((Scheme.ProEt.forget X ⋙ Over.forget X).map qo) :=
      inferInstanceAs (QuasiCompact q)
    exact generate_singleton_mem_topology qo hqwe

/-! ### Families of affine objects ind-étale over the base as limits -/

/-- A finite family `{U_k → U}` of affine objects of the small pro-étale site, ind-étale over the
affine `U`, is the limit of a cofiltered system of families `{U_{k,λ} → U}` of affine schemes
étale over `U`: the index category is the product of index categories of limit presentations of
the members. -/
theorem exists_cofilteredSystem_of_indEtale {U : X.ProEt} (E : PreZeroHypercover.{u} U)
    [Finite E.I₀] [IsAffine U.left] [∀ k, IsAffine (E.X k).left]
    (hE : ∀ k, MorphismProperty.ind.{u} CommRingCat.etale (E.f k).left.appTop) :
    ∃ (Λ : Type u) (_ : SmallCategory Λ) (_ : IsCofiltered Λ) (M : E.I₀ → Λ ⥤ X.ProEt)
      (m : ∀ k, M k ⟶ (Functor.const Λ).obj U)
      (πM : ∀ k, (Functor.const Λ).obj (E.X k) ⟶ M k)
      (_ : ∀ k j, (πM k).app j ≫ (m k).app j =
        E.f k ≫ NatTrans.app (𝟙 ((Functor.const Λ).obj U)) j),
      Nonempty (IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone
          (Cone.mk U (𝟙 ((Functor.const Λ).obj U))))) ∧
        (∀ k, Nonempty (IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone
          (Cone.mk (E.X k) (πM k))))) ∧
        (∀ k j, IsAffine ((M k).obj j).left) ∧ (∀ k j, Etale ((m k).app j).left) := by
  let : Category.{u} (MorphismProperty.Over (@WeaklyEtale : MorphismProperty Scheme.{u}) ⊤ X) :=
    inferInstanceAs (Category X.ProEt)
  choose Ak hAk hAk' D d pk hDa hde hpd hlim using
    fun k ↦ exists_isLimit_of_indEtale_appTop (E.f k).left (hE k)
  let : ∀ k, SmallCategory (Ak k) := hAk
  have : ∀ k, IsCofiltered (Ak k) := hAk'
  have hdw (k : E.I₀) (a : Ak k) : WeaklyEtale ((d k).app a) :=
    have := hde k a
    inferInstance
  let N (k : E.I₀) : Ak k ⥤ X.ProEt :=
    MorphismProperty.Over.systemOver (@WeaklyEtale) U (D k) (d k) (hdw k)
  let Λ := ∀ k, Ak k
  let πN (k : E.I₀) : N k ⟶ (Functor.const (Ak k)).obj U :=
    MorphismProperty.Over.systemOverπ (@WeaklyEtale) U (D k) (d k) (hdw k)
  let cM (k : E.I₀) : (Functor.const (Ak k)).obj (E.X k) ⟶ N k :=
    (MorphismProperty.Over.systemOverCone (@WeaklyEtale) U (D k) (d k) (hdw k)
      (E.X k) (E.f k) (pk k) (hpd k)).π
  have : IsConnected Λ := IsCofiltered.isConnected Λ
  refine ⟨Λ, inferInstance, inferInstance, fun k ↦ Pi.eval Ak k ⋙ N k,
    fun k ↦ Functor.whiskerLeft (Pi.eval Ak k) (πN k),
    fun k ↦ Functor.whiskerLeft (Pi.eval Ak k) (cM k), fun k j ↦ ?_,
    ⟨isLimitConstCone Λ U.left⟩, fun k ↦ ⟨?_⟩, fun k j ↦ hDa k (j k), fun k j ↦ hde k (j k)⟩
  · refine MorphismProperty.Over.Hom.ext ?_
    show (pk k).app (j k) ≫ (d k).app (j k) = (E.f k).left ≫ 𝟙 U.left
    rw [hpd, Category.comp_id]
  · exact (Functor.Initial.isLimitWhiskerEquiv (Pi.eval Ak k)
      (Cone.mk (E.X k).left (pk k))).symm (hlim k).some

/-- An iterated fibre product of a finite family of affine objects ind-étale over an object which
is ind-étale over an affine étale `X`-scheme is again ind-étale over that scheme: it is the limit
of the iterated fibre products of affine schemes étale over the base. -/
lemma IsAffineIndEtaleOverEtale.prod {U : X.ProEt} (hU : IsAffineIndEtaleOverEtale X U)
    (E : PreZeroHypercover.{u} U) [Finite E.I₀] [∀ k, IsAffine (E.X k).left]
    (hE : ∀ k, MorphismProperty.ind.{u} CommRingCat.etale (E.f k).left.appTop) (n : ℕ)
    (t : Fin (n + 1) → E.I₀) :
    IsAffineIndEtaleOverEtale X (∏ᶜ fun a ↦ Over.mk (E.f (t a))).left := by
  have : IsAffine U.left := hU.1
  have := isAffine_left_prod E (fun k ↦ ‹∀ k, IsAffine (E.X k).left› k) n t
  refine hU.of_hom (∏ᶜ fun a ↦ Over.mk (E.f (t a))).hom ?_
  obtain ⟨Λ, _, _, M, m, πM, hπ, ⟨hB⟩, hM, hMa, hMe⟩ := exists_cofilteredSystem_of_indEtale E hE
  let q := Scheme.ProEt.forget X ⋙ Over.forget X
  let B : Λ ⥤ X.ProEt := (Functor.const Λ).obj U
  have := preservesLimit_overPost_forget E
  have := fun j ↦ preservesLimit_overPost_forget (stageFamily E B M m j)
  have hlim := isLimitMapConeStageFibreProductCone E B M m (𝟙 B) πM hπ q hB
    (fun k ↦ (hM k).some) n t
  have : ∀ j, IsAffine ((stageFibreProduct E B M m n t ⋙ q).obj j) := fun j ↦
    have : IsAffine (B.obj j).left := ‹IsAffine U.left›
    isAffine_left_prod (stageFamily E B M m j) (fun k ↦ hMa k j) n t
  let d : stageFibreProduct E B M m n t ⋙ q ⟶ (Functor.const Λ).obj U.left :=
    { app j := (∏ᶜ fun a ↦ Over.mk ((stageFamily E B M m j).f (t a))).hom.left
      naturality {j j'} g := congrArg (fun f ↦ f.left) (cechProductMap_comp_hom
        (stageFamily E B M m j) (stageFamily E B M m j') (stageFamilyHomOver E B M m g) n t) }
  exact indEtale_appTop_of_isLimit _ (stageFibreProduct E B M m n t ⋙ q) d _
    (fun j ↦ prop_left_hom_prod @Etale (stageFamily E B M m j) (fun k ↦ hMe k j) n t)
    (fun j ↦ (congrArg (fun f ↦ f.left) (cechProductMap_comp_hom E (stageFamily E B M m j)
      (toStageFamily E B M m (𝟙 B) πM hπ j) n t)).trans
        (Category.comp_id (∏ᶜ fun a ↦ Over.mk (E.f (t a))).hom.left)) hlim

/-- **Ind-étale coverings are cofinal.** Every covering sieve of an affine object of the small
pro-étale site is refined by a finite covering family of affine objects ind-étale over it: refine
it by a finite covering by affine objects, and each of those by a single affine object ind-étale
over the base, by Proposition 097Z. -/
theorem exists_indEtale_covering_le {U : X.ProEt} [IsAffine U.left] (R : Sieve U)
    (hR : R ∈ Scheme.ProEt.topology X U) :
    ∃ E : PreZeroHypercover.{u} U, Finite E.I₀ ∧ E.sieve₀ ∈ Scheme.ProEt.topology X U ∧
      E.sieve₀ ≤ R ∧ ∀ k, IsAffine (E.X k).left ∧
        MorphismProperty.ind.{u} CommRingCat.etale (E.f k).left.appTop := by
  obtain ⟨E', hfin, hcov, hle, haff⟩ := exists_finite_affine_covering_le U R hR
  have hw (j : E'.I₀) : WeaklyEtale (E'.f j).left :=
    MorphismProperty.of_postcomp _ _ U.hom U.prop (by
      rw [MorphismProperty.Over.w (E'.f j)]
      exact (E'.X j).prop)
  have := haff
  choose W qj hWa hsurj hqw hind using fun j ↦ exists_surjective_weaklyEtale_indEtale_appTop
    (E'.f j).left
  let σ : ULift.{u} (Fin (Nat.card E'.I₀)) ≃ E'.I₀ := Equiv.ulift.trans (Finite.equivFin E'.I₀).symm
  have hwq (i : ULift.{u} (Fin (Nat.card E'.I₀))) : WeaklyEtale (qj (σ i) ≫ (E'.X (σ i)).hom) :=
    have := hqw (σ i)
    have : WeaklyEtale (E'.X (σ i)).hom := (E'.X (σ i)).prop
    inferInstance
  let Y (i : ULift.{u} (Fin (Nat.card E'.I₀))) : X.ProEt :=
    @Scheme.ProEt.mk _ _ (qj (σ i) ≫ (E'.X (σ i)).hom) (hwq i)
  let qo (i : ULift.{u} (Fin (Nat.card E'.I₀))) : Y i ⟶ E'.X (σ i) :=
    MorphismProperty.Over.homMk (qj (σ i)) rfl trivial
  let E : PreZeroHypercover.{u} U :=
    ⟨ULift.{u} (Fin (Nat.card E'.I₀)), Y, fun i ↦ qo i ≫ E'.f (σ i)⟩
  have hqcov (i : ULift.{u} (Fin (Nat.card E'.I₀))) :
      Sieve.generate (Presieve.singleton (qo i)) ∈ Scheme.ProEt.topology X (E'.X (σ i)) := by
    have := hWa (σ i)
    have := haff (σ i)
    have : Surjective ((Scheme.ProEt.forget X ⋙ Over.forget X).map (qo i)) := hsurj (σ i)
    have : QuasiCompact ((Scheme.ProEt.forget X ⋙ Over.forget X).map (qo i)) :=
      inferInstanceAs (QuasiCompact (qj (σ i)))
    exact generate_singleton_mem_topology (qo i) (hqw (σ i))
  refine ⟨E, inferInstance, ?_, ?_, fun i ↦ ⟨hWa (σ i), hind (σ i)⟩⟩
  · refine (Scheme.ProEt.topology X).transitive (Precoverage.generate_mem_toGrothendieck hcov)
      _ fun Z f hf ↦ ?_
    obtain ⟨T, h, _, ⟨j⟩, rfl⟩ := hf
    obtain ⟨i, rfl⟩ := σ.surjective j
    rw [Sieve.pullback_comp]
    refine (Scheme.ProEt.topology X).pullback_stable h
      ((Scheme.ProEt.topology X).superset_covering ?_ (hqcov i))
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨⟩
    exact Sieve.le_generate _ _ _ (Presieve.ofArrows.mk i)
  · rw [Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    exact R.downward_closed (hle _ (Sieve.le_generate _ _ _ (Presieve.ofArrows.mk (σ i)))) (qo i)

/-! ### Čech complexes of families coming from the small étale site -/

section Composites

variable {C : Type*} [Category* C]

/- The three identities between composites below are stated with all objects as variables: their
instances in the proofs below involve the underlying schemes of objects of the small pro-étale
site, which are only definitionally equal to the schemes appearing in the pullback squares. -/

private lemma comp_comp_eq_of_eq {V P₁ P₂ W B Bu Z : C} (i : V ⟶ P₁) (t : P₁ ⟶ P₂)
    (s : P₂ ⟶ W) (w : W ⟶ B) (δ : B ⟶ Z) (s₀ : P₁ ⟶ W) (g : V ⟶ W) (e : V ⟶ Bu)
    (cπ : Bu ⟶ B) (η : Bu ⟶ Z) (hX : V ⟶ Z) (h₁ : t ≫ s = s₀) (h₂ : i ≫ s₀ = g)
    (h₃ : g ≫ w = e ≫ cπ) (h₄ : cπ ≫ δ = η) (h₅ : e ≫ η = hX) :
    (i ≫ t) ≫ (s ≫ w) ≫ δ = hX := by
  simp only [Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄, h₅]

private lemma id_comp_comp_eq_comp_comp {V P Q R : C} (i : V ⟶ P) (x : P ⟶ Q) (y : Q ⟶ R)
    (x' : P ⟶ R) (h : x ≫ y = x') : 𝟙 V ≫ i ≫ x' = (i ≫ x) ≫ y := by
  rw [Category.id_comp, Category.assoc, h]

private lemma comp_comp_eq_comp {V P Q R Bu : C} (i : V ⟶ P) (x : P ⟶ Q) (y : Q ⟶ R)
    (y₀ : P ⟶ Bu) (cπ : Bu ⟶ R) (e : V ⟶ Bu) (h₁ : x ≫ y = y₀ ≫ cπ) (h₂ : i ≫ y₀ = e) :
    (i ≫ x) ≫ y = e ≫ cπ := by
  rw [Category.assoc, h₁, reassoc_of% h₂]

end Composites

section Etale

variable {L : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
    Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}}
  (adj : L ⊣ X.etaleToProetale.sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
    X.smallEtaleTopology (Scheme.ProEt.topology X))
  (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) [Injective I]

include adj in
/-- The Čech complex of `ε⁻¹ℐ` along the image of a family of the small étale site is acyclic in
positive degrees, for an injective abelian sheaf `ℐ` on the small étale site: it is the Čech
complex of `ε_*ε⁻¹ℐ = ℐ` along the family (Stacks 099T). -/
lemma isZero_cechCohomology_map_etaleToProetale {V : X.Etale} (E : PreZeroHypercover.{u} V)
    (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology (E.map X.etaleToProetale) (L.obj I).obj p) := by
  have hcomp (n : ℕ) (i : Fin (n + 1) → E.I₀) :
      IsIso (cechProductMapOfFunctor X.etaleToProetale E n i) := by
    have := Stacks.Sites.preservesLimit_fibreProducts_overPost X.etaleToProetale E
      (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance) n i
    exact isIso_cechProductMapOfFunctor _ _ n i
  refine IsZero.of_iso ?_ (cechCohomologyIsoOfFunctor X.etaleToProetale E (L.obj I).obj hcomp p)
  have := Scheme.isIso_unit_of_etaleToProetale_addCommGrp.{u, v} X adj
  have e : I.obj ≅ X.etaleToProetale.op ⋙ (L.obj I).obj :=
    (sheafToPresheaf _ _).mapIso (asIso (adj.unit.app I))
  exact IsZero.of_iso (injective_sheaf_cechCohomology_isZero E I p hp)
    ((HomologicalComplex.homologyFunctor _ _ p).mapIso
      ((Stacks.CechSite.cechComplexFunctor E).mapIso e)).symm

include adj in
omit [Injective I] in
/-- **The Čech complex of `ε⁻¹ℐ` along a cofiltered limit of families.** Let a finite family
`{U_k → U}` of the small pro-étale site be the limit, on underlying schemes, of a cofiltered
system of families `{U_{k,λ} → U_λ}` whose iterated fibre products
`U_{k_0,λ} ×_{U_λ} ⋯ ×_{U_λ} U_{k_n,λ}` have quasi-compact and quasi-separated underlying
schemes and affine transition morphisms.  If the Čech complexes of `ε⁻¹ℐ` along the families
`{U_{k,λ} → U_λ}` are acyclic in degree `p`, so is the Čech complex along `{U_k → U}`: it is
their filtered colimit, by Stacks 099S. -/
theorem isZero_cechCohomology_of_isLimit {U : X.ProEt} (E : PreZeroHypercover.{u} U)
    [Finite E.I₀] {Λ : Type u} [SmallCategory Λ] [IsCofiltered Λ] (B : Λ ⥤ X.ProEt)
    (M : E.I₀ → Λ ⥤ X.ProEt) (m : ∀ k, M k ⟶ B) (πB : (Functor.const Λ).obj U ⟶ B)
    (πM : ∀ k, (Functor.const Λ).obj (E.X k) ⟶ M k)
    (hπ : ∀ k j, (πM k).app j ≫ (m k).app j = E.f k ≫ πB.app j)
    (hB : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone (Cone.mk U πB)))
    (hM : ∀ k, IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone
      (Cone.mk (E.X k) (πM k))))
    (hSc : ∀ n t j, CompactSpace ((stageFibreProduct E B M m n t).obj j).left)
    (hSq : ∀ n t j, QuasiSeparatedSpace ((stageFibreProduct E B M m n t).obj j).left)
    (hSa : ∀ n t {i j : Λ} (f : i ⟶ j),
      IsAffineHom ((stageFibreProduct E B M m n t).map f).left) (p : ℕ)
    (hp : ∀ j, IsZero (cechCohomology (stageFamily E B M m j) (L.obj I).obj p)) :
    IsZero (cechCohomology E (L.obj I).obj p) := by
  let q := Scheme.ProEt.forget X ⋙ Over.forget X
  have := preservesLimit_overPost_forget E
  have := fun j ↦ preservesLimit_overPost_forget (stageFamily E B M m j)
  refine isZero_cechCohomology_of_isColimit E B M m πB πM hπ (L.obj I).obj (fun n t ↦ ?_) p hp
  have hlim := isLimitMapConeStageFibreProductCone E B M m πB πM hπ q hB hM n t
  have : ∀ j, CompactSpace ((stageFibreProduct E B M m n t).obj j).left := hSc n t
  have : ∀ j, QuasiSeparatedSpace ((stageFibreProduct E B M m n t).obj j).left := hSq n t
  have : ∀ {i j : Λ} (f : i ⟶ j), IsAffineHom ((stageFibreProduct E B M m n t).map f).left :=
    hSa n t
  exact Scheme.proetaleInverseImageIsColimitForget.{u, v} X (stageFibreProduct E B M m n t)
    (stageFibreProductCone E B M m πB πM hπ n t) hlim adj I

end Etale

/-- **A family based changed from a stage is the limit of its base changes to the later
stages.** Let `U` be the limit, on underlying schemes, of a cofiltered system `U_b` of objects of
`X_étale` with affine transition morphisms, and let `{U_k → U}` be a family of the small
pro-étale site whose members are the base changes `U_k = W_k ×_{U_{b₀}} U` of affine schemes
`W_k` étale over one stage `U_{b₀}`.  Then the family is the limit, on underlying schemes, of the
families `{W_k ×_{U_{b₀}} U_b → U_b}` of affine objects of `X_étale` étale over the later stages
`U_b`, and the squares formed by their transition morphisms are cartesian. -/
theorem exists_isLimit_baseChange_of_isPullback {U : X.ProEt} {A : Type u} [SmallCategory A]
    [IsCofiltered A] (Ub : A ⥤ X.Etale) [∀ {a b : A} (f : a ⟶ b), IsAffineHom (Ub.map f).left]
    (πU : (Functor.const A).obj U ⟶ Ub ⋙ X.etaleToProetale)
    (hUlim : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone (Cone.mk U πU)))
    (E : PreZeroHypercover.{u} U) (b₀ : A) (W : E.I₀ → Scheme.{u}) [∀ k, IsAffine (W k)]
    (w : ∀ k, W k ⟶ (Ub.obj b₀).left) [∀ k, Etale (w k)] (g : ∀ k, (E.X k).left ⟶ W k)
    (hpb : ∀ k, IsPullback (g k) (E.f k).left (w k) (πU.app b₀).left) :
    ∃ (Met : E.I₀ → Over b₀ ⥤ X.Etale) (met : ∀ k, Met k ⟶ Over.forget b₀ ⋙ Ub)
      (πM : ∀ k, (Functor.const (Over b₀)).obj (E.X k) ⟶ Met k ⋙ X.etaleToProetale)
      (_ : ∀ k a, (πM k).app a ≫ (Functor.whiskerRight (met k) X.etaleToProetale).app a =
        E.f k ≫ (Functor.whiskerLeft (Over.forget b₀) πU).app a),
      (∀ k, Nonempty (IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone
        (Cone.mk (E.X k) (πM k))))) ∧
      (∀ k a, IsAffine ((Met k).obj a).left) ∧ (∀ k a, Etale ((met k).app a).left) ∧
      ∀ k {a a' : Over b₀} (f : a ⟶ a'), IsPullback ((Met k).map f).left ((met k).app a).left
        ((met k).app a').left (Ub.map f.left).left := by
  let q := Scheme.ProEt.forget X ⋙ Over.forget X
  let D : A ⥤ Scheme.{u} := Ub ⋙ X.etaleToProetale ⋙ q
  have : ∀ {a b : A} (f : a ⟶ b), IsAffineHom (D.map f) := fun f ↦
    inferInstanceAs (IsAffineHom (Ub.map f).left)
  let c := q.mapCone (Cone.mk U πU)
  let w' (k : E.I₀) : W k ⟶ D.obj b₀ := w k
  have : ∀ k, Etale (w' k) := fun k ↦ inferInstanceAs (Etale (w k))
  have hpb' (k : E.I₀) : IsPullback (g k) (E.f k).left (w' k) (c.π.app b₀) := hpb k
  let Y (k : E.I₀) : Over (D.obj b₀) := Over.mk (w' k)
  have hd (k : E.I₀) (a : Over b₀) : Etale ((baseChangeStructureMap D b₀ (Y k)).app a) := by
    have : Etale (D.map a.hom) := by
      have h := MorphismProperty.Over.w (Ub.map a.hom)
      have : Etale ((Ub.map a.hom).left ≫ (Ub.obj b₀).hom) := by
        rw [h]; exact (Ub.obj a.left).prop
      exact MorphismProperty.of_postcomp _ _ _ (Ub.obj b₀).prop this
    have : Etale (Y k).hom := inferInstanceAs (Etale (w' k))
    rw [baseChangeStructureMap_app]
    have : Etale (pullback.snd (D.map a.hom) (Y k).hom) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback (D.map a.hom) (Y k).hom) inferInstance
    exact MorphismProperty.comp_mem (@Etale) _ _ this ‹_›
  let Met (k : E.I₀) : Over b₀ ⥤ X.Etale := MorphismProperty.Over.systemOver (@Etale) (Ub.obj b₀)
    (baseChangeDiagram D b₀ (Y k)) (baseChangeStructureMap D b₀ (Y k)) (hd k)
  let met (k : E.I₀) : Met k ⟶ Over.forget b₀ ⋙ Ub :=
    { app a := MorphismProperty.Over.homMk (pullback.fst (D.map a.hom) (w' k)) (by
        show pullback.fst (D.map a.hom) (w' k) ≫ (Ub.obj a.left).hom =
          (pullback.snd (D.map a.hom) (w' k) ≫ w' k) ≫ (Ub.obj b₀).hom
        have h₁ : pullback.fst (D.map a.hom) (w' k) ≫ D.map a.hom =
            pullback.snd (D.map a.hom) (w' k) ≫ w' k := pullback.condition
        have h₂ : (Ub.map a.hom).left ≫ (Ub.obj b₀).hom = (Ub.obj a.left).hom :=
          MorphismProperty.Over.w _
        calc pullback.fst (D.map a.hom) (w' k) ≫ (Ub.obj a.left).hom
            = pullback.fst (D.map a.hom) (w' k) ≫ (D.map a.hom ≫ (Ub.obj b₀).hom) :=
              congrArg _ h₂.symm
          _ = (pullback.fst (D.map a.hom) (w' k) ≫ D.map a.hom) ≫ (Ub.obj b₀).hom :=
              (Category.assoc _ _ _).symm
          _ = _ := congrArg (· ≫ (Ub.obj b₀).hom) h₁) trivial
      naturality {a a'} f := MorphismProperty.Over.Hom.ext
        (baseChangeTransition_fst (D.map a'.hom) (D.map a.hom) (D.map f.left)
          (by rw [← D.map_comp, Over.w f]) (Y k)) }
  let iso (k : E.I₀) : (E.X k).left ≅ pullback (c.π.app b₀) (w' k) := (hpb' k).flip.isoPullback
  let δ (a : A) : D.obj a ⟶ X := (Ub.obj a).hom
  let ηU : c.pt ⟶ X := U.hom
  have hδ (a : A) : c.π.app a ≫ δ a = ηU := MorphismProperty.Over.w (πU.app a)
  have hηU (k : E.I₀) : (E.f k).left ≫ ηU = (E.X k).hom := MorphismProperty.Over.w (E.f k)
  let bc (k : E.I₀) := baseChangeCone D c b₀ (Y k)
  have hbc_snd (k : E.I₀) (a : Over b₀) :
      (bc k).π.app a ≫ pullback.snd (D.map a.hom) (w' k) = pullback.snd (c.π.app b₀) (w' k) :=
    baseChangeTransition_snd (D.map a.hom) (c.π.app b₀) (c.π.app a.left) (c.w a.hom) (Y k)
  have hbc_fst (k : E.I₀) (a : Over b₀) :
      (bc k).π.app a ≫ pullback.fst (D.map a.hom) (w' k) =
        pullback.fst (c.π.app b₀) (w' k) ≫ c.π.app a.left :=
    baseChangeTransition_fst (D.map a.hom) (c.π.app b₀) (c.π.app a.left) (c.w a.hom) (Y k)
  have hiso_snd (k : E.I₀) : (iso k).hom ≫ pullback.snd (c.π.app b₀) (w' k) = g k :=
    (hpb' k).flip.isoPullback_hom_snd
  have hiso_fst (k : E.I₀) : (iso k).hom ≫ pullback.fst (c.π.app b₀) (w' k) = (E.f k).left :=
    (hpb' k).flip.isoPullback_hom_fst
  let πM (k : E.I₀) : (Functor.const (Over b₀)).obj (E.X k) ⟶ Met k ⋙ X.etaleToProetale :=
    { app a := MorphismProperty.Over.homMk ((iso k).hom ≫ (bc k).π.app a) (by
          exact comp_comp_eq_of_eq _ _ _ _ (δ b₀) _ _ _ _ _ _ (hbc_snd k a) (hiso_snd k)
            (hpb' k).w (hδ b₀) (hηU k)) trivial
      naturality {a a'} f := MorphismProperty.Over.Hom.ext
        (id_comp_comp_eq_comp_comp _ _ _ _ ((bc k).w f)) }
  refine ⟨Met, met, πM, fun k a ↦ MorphismProperty.Over.Hom.ext
    (comp_comp_eq_comp _ _ _ _ _ _ (hbc_fst k a) (hiso_fst k)), fun k ↦ ⟨?_⟩,
    fun k a ↦ ?_, fun k a ↦ ?_, fun k a a' f ↦ ?_⟩
  · exact IsLimit.ofIsoLimit (baseChangeConeIsLimit D hUlim b₀ (Y k))
      (Cone.ext (iso k).symm fun a ↦ (Iso.inv_hom_id_assoc (iso k) _).symm)
  · have : IsAffine (Y k).left := inferInstanceAs (IsAffine (W k))
    exact isAffine_baseChangeDiagram_obj D b₀ (Y k) a
  · show Etale (pullback.fst (D.map a.hom) (w' k))
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (D.map a.hom) (w' k)).flip inferInstance
  · have hf : D.map f.left ≫ D.map a'.hom = D.map a.hom := by rw [← D.map_comp, Over.w f]
    have big : IsPullback (baseChangeTransition (D.map a'.hom) (D.map a.hom) (D.map f.left)
        hf (Y k) ≫ pullback.snd (D.map a'.hom) (Y k).hom)
        (pullback.fst (D.map a.hom) (Y k).hom) (Y k).hom (D.map f.left ≫ D.map a'.hom) := by
      rw [baseChangeTransition_snd, hf]
      exact (IsPullback.of_hasPullback (D.map a.hom) (Y k).hom).flip
    exact IsPullback.of_right big (baseChangeTransition_fst (D.map a'.hom) (D.map a.hom)
      (D.map f.left) hf (Y k)) (IsPullback.of_hasPullback (D.map a'.hom) (Y k).hom).flip

section Etale

variable {L : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
    Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}}
  (adj : L ⊣ X.etaleToProetale.sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
    X.smallEtaleTopology (Scheme.ProEt.topology X))
  (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) [Injective I]

include adj in
/-- **Čech acyclicity along a family base changed from a stage.** Let `U` be the limit, on
underlying schemes, of a cofiltered system `U_b` of quasi-compact and quasi-separated objects of
`X_étale` with affine transition morphisms, and let `{U_k → U}` be a finite family of the small
pro-étale site whose members are the base changes `W_k ×_{U_{b₀}} U` of affine schemes `W_k`
étale over one stage `U_{b₀}`.  Then the Čech complex of `ε⁻¹ℐ` along `{U_k → U}` is acyclic in
positive degrees.

It is the colimit of the Čech complexes along the families `{W_k ×_{U_{b₀}} U_b → U_b}`
(Stacks 099S): their iterated fibre products are quasi-compact and separated, with affine
transition morphisms because iterated fibre products of cartesian squares are cartesian; and these
are Čech complexes of families of the small étale site, acyclic because `ℐ` is injective. -/
theorem isZero_cechCohomology_of_isPullback {U : X.ProEt} {A : Type u} [SmallCategory A]
    [IsCofiltered A] (Ub : A ⥤ X.Etale) [∀ a, QuasiSeparatedSpace (Ub.obj a).left]
    [∀ {a b : A} (f : a ⟶ b), IsAffineHom (Ub.map f).left]
    (πU : (Functor.const A).obj U ⟶ Ub ⋙ X.etaleToProetale)
    (hUlim : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone (Cone.mk U πU)))
    (E : PreZeroHypercover.{u} U) [Finite E.I₀] (b₀ : A) (W : E.I₀ → Scheme.{u})
    [∀ k, IsAffine (W k)] (w : ∀ k, W k ⟶ (Ub.obj b₀).left) [∀ k, Etale (w k)]
    (g : ∀ k, (E.X k).left ⟶ W k) (hpb : ∀ k, IsPullback (g k) (E.f k).left (w k) (πU.app b₀).left)
    (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology E (L.obj I).obj p) := by
  obtain ⟨Met, met, πM, hπ, hM, hMa, -, hMpb⟩ :=
    exists_isLimit_baseChange_of_isPullback Ub πU hUlim E b₀ W w g hpb
  let q := Scheme.ProEt.forget X ⋙ Over.forget X
  let B : Over b₀ ⥤ X.ProEt := (Over.forget b₀ ⋙ Ub) ⋙ X.etaleToProetale
  let M (k : E.I₀) : Over b₀ ⥤ X.ProEt := Met k ⋙ X.etaleToProetale
  let m (k : E.I₀) : M k ⟶ B := Functor.whiskerRight (met k) X.etaleToProetale
  let πB : (Functor.const (Over b₀)).obj U ⟶ B := Functor.whiskerLeft (Over.forget b₀) πU
  have hB : IsLimit (q.mapCone (Cone.mk U πB)) :=
    IsLimit.ofIsoLimit ((Functor.Initial.isLimitWhiskerEquiv (Over.forget b₀)
      (q.mapCone (Cone.mk U πU))).symm hUlim)
      (Cone.ext (Iso.refl _) fun _ ↦ (Category.id_comp _).symm)
  have := fun j ↦ preservesLimit_overPost_forget (stageFamily E B M m j)
  have hS (n : ℕ) (t : Fin (n + 1) → E.I₀) (j : Over b₀) :=
    have : QuasiSeparatedSpace (B.obj j).left := inferInstanceAs
      (QuasiSeparatedSpace (Ub.obj j.left).left)
    isSeparated_left_prod (stageFamily E B M m j) (fun k ↦ hMa k j) n t
  refine isZero_cechCohomology_of_isLimit adj I E B M m πB πM hπ hB (fun k ↦ (hM k).some)
    (fun n t j ↦ (hS n t j).2) (fun n t j ↦ have := (hS n t j).1; inferInstance)
    (fun n t i j f ↦ ?_) p fun j ↦ ?_
  · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_map_cechProductMap q (stageFamily E B M m i) (stageFamily E B M m j)
        (stageFamilyHomOver E B M m f) n t fun a ↦ hMpb (t a) f).flip
      (inferInstanceAs (IsAffineHom (Ub.map f.left).left))
  · let Eet : PreZeroHypercover.{u} (Ub.obj j.left) :=
      ⟨E.I₀, fun k ↦ (Met k).obj j, fun k ↦ (met k).app j⟩
    exact isZero_cechCohomology_map_etaleToProetale adj I Eet p hp

include adj in
/-- **Čech acyclicity along étale families.** Let `U` be an object of `X_proétale` which is the
limit of a cofiltered system of affine objects `U_b` of `X_étale`.  For a finite family of affine
schemes étale over `U`, the Čech complex of `ε⁻¹ℐ` is acyclic in positive degrees.

The family is the base change of a family of affine schemes étale over a stage `U_{b₀}`, and this
is `AlgebraicGeometry.ProEtale.isZero_cechCohomology_of_isPullback`. -/
theorem isZero_cechCohomology_of_etale {U : X.ProEt} {A : Type u} [SmallCategory A]
    [IsCofiltered A] (Ub : A ⥤ X.Etale) [∀ a, IsAffine (Ub.obj a).left]
    (πU : (Functor.const A).obj U ⟶ Ub ⋙ X.etaleToProetale)
    (hUlim : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone (Cone.mk U πU)))
    (E : PreZeroHypercover.{u} U) [Finite E.I₀] [∀ k, IsAffine (E.X k).left]
    [∀ k, Etale (E.f k).left] (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology E (L.obj I).obj p) := by
  let q := Scheme.ProEt.forget X ⋙ Over.forget X
  let D : A ⥤ Scheme.{u} := Ub ⋙ X.etaleToProetale ⋙ q
  have : ∀ a, IsAffine (D.obj a) := fun a ↦ inferInstanceAs (IsAffine (Ub.obj a).left)
  have : ∀ {a b : A} (g : a ⟶ b), IsAffineHom (D.map g) := fun _ ↦ inferInstance
  have : ∀ {a b : A} (g : a ⟶ b), IsAffineHom (Ub.map g).left := fun g ↦
    inferInstanceAs (IsAffineHom (D.map g))
  let e (k : E.I₀) : (E.X k).left ⟶ (q.mapCone (Cone.mk U πU)).pt := (E.f k).left
  have : ∀ k, Etale (e k) := fun k ↦ inferInstanceAs (Etale (E.f k).left)
  obtain ⟨b₀, hb₀⟩ := exists_stage_forall_etale_isPullback_of_isLimit D (q.mapCone (Cone.mk U πU))
    hUlim (fun k ↦ (E.X k).left) e
  choose W w g hW hw hpb using hb₀
  have : ∀ k, IsAffine (W k) := hW
  let w' (k : E.I₀) : W k ⟶ (Ub.obj b₀).left := w k
  have : ∀ k, Etale (w' k) := hw
  exact isZero_cechCohomology_of_isPullback adj I Ub πU hUlim E b₀ W w' g hpb p hp

include adj in
/-- **Čech acyclicity along ind-étale families.** Let `U` be an object of `X_proétale` which is
the limit of a cofiltered system of affine objects of `X_étale`, with affine underlying scheme.
For a finite family `{U_k → U}` of affine schemes ind-étale over `U`, the Čech complex of
`ε⁻¹ℐ` is acyclic in positive degrees.

Each `U_k` is a limit of affine schemes étale over `U`; the Čech complex along `{U_k → U}` is the
colimit of the Čech complexes along the families of those étale stages
(`AlgebraicGeometry.ProEtale.exists_cofilteredSystem_of_indEtale`, Stacks 099S), and these are
acyclic by `AlgebraicGeometry.ProEtale.isZero_cechCohomology_of_etale`. -/
theorem isZero_cechCohomology_of_indEtale {U : X.ProEt} [IsAffine U.left] {A : Type u}
    [SmallCategory A] [IsCofiltered A] (Ub : A ⥤ X.Etale) [∀ a, IsAffine (Ub.obj a).left]
    (πU : (Functor.const A).obj U ⟶ Ub ⋙ X.etaleToProetale)
    (hUlim : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone (Cone.mk U πU)))
    (E : PreZeroHypercover.{u} U) [Finite E.I₀] [∀ k, IsAffine (E.X k).left]
    (hE : ∀ k, MorphismProperty.ind.{u} CommRingCat.etale (E.f k).left.appTop) (p : ℕ)
    (hp : 0 < p) :
    IsZero (cechCohomology E (L.obj I).obj p) := by
  obtain ⟨Λ, _, _, M, m, πM, hπ, ⟨hB⟩, hM, hMa, hMe⟩ := exists_cofilteredSystem_of_indEtale E hE
  let B : Λ ⥤ X.ProEt := (Functor.const Λ).obj U
  have : ∀ j, (B.obj j).left.IsSeparated := fun _ ↦ inferInstanceAs U.left.IsSeparated
  have hS (n : ℕ) (t : Fin (n + 1) → E.I₀) (j : Λ) :
      IsAffine ((stageFibreProduct E B M m n t).obj j).left :=
    isAffine_left_prod (stageFamily E B M m j) (fun k ↦ hMa k j) n t
  refine isZero_cechCohomology_of_isLimit adj I E _ M m _ πM hπ hB (fun k ↦ (hM k).some)
    (fun n t j ↦ have := hS n t j; inferInstance) (fun n t j ↦ have := hS n t j; inferInstance)
    (fun n t i j f ↦ have := hS n t i; have := hS n t j; isAffineHom_of_isAffine _) p fun j ↦ ?_
  have : ∀ k, IsAffine ((stageFamily E _ M m j).X k).left := fun k ↦ hMa k j
  have : ∀ k, Etale ((stageFamily E _ M m j).f k).left := fun k ↦ hMe k j
  exact isZero_cechCohomology_of_etale adj I Ub πU hUlim (stageFamily E _ M m j) p hp

include adj in
/-- **Higher cohomology of `ε⁻¹ℐ` over affine ind-étale objects.** Let `X` be a scheme, let `ℐ`
be an injective abelian sheaf on `X_étale` and let `V` be an affine object of `X_proétale` which is
ind-étale over an affine object of `X_étale`.  Then the cohomology `H^p(V, ε⁻¹ℐ)` of `ε⁻¹ℐ` over
`V`, the `Ext` group out of the free abelian sheaf on `V`, vanishes for `p > 0`.

This is the Čech criterion of Stacks 03F9 for the objects of this kind and their finite coverings
by affine objects ind-étale over them: these coverings are cofinal
(`AlgebraicGeometry.ProEtale.exists_indEtale_covering_le`), their members and iterated fibre
products are again of this kind, and the Čech complexes of `ε⁻¹ℐ` along them are acyclic in
positive degrees (`AlgebraicGeometry.ProEtale.isZero_cechCohomology_of_indEtale`). -/
theorem subsingleton_ext_proetaleInverseImage_of_injective
    [HasExt.{w} (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v})]
    {V : X.ProEt} (hV : IsAffineIndEtaleOverEtale X V) (p : ℕ) (hp : 0 < p) :
    Subsingleton (Abelian.Ext ((presheafToSheaf (Scheme.ProEt.topology X)
      AddCommGrpCat.{max (u + 1) v}).obj (uliftYoneda.{max (u + 1) v}.obj V ⋙
        AddCommGrpCat.free)) (L.obj I) p) := by
  refine subsingleton_ext_of_cechCohomology_isZero.{w, v, u, u, u + 1} (Scheme.ProEt.topology X)
    (setOf (IsAffineIndEtaleOverEtale X))
    (fun U ↦ {E | Finite E.1.I₀ ∧ IsAffineIndEtaleOverEtale X U ∧ ∀ k, IsAffine (E.1.X k).left ∧
      MorphismProperty.ind.{u} CommRingCat.etale (E.1.f k).left.appTop})
    (fun _ _ _ _ ↦ inferInstance) ?_ ?_ (L.obj I) ?_ V hV p hp
  · rintro U ⟨E, hEJ⟩ ⟨hfin, hU, hE⟩
    have : ∀ k, IsAffine (E.X k).left := fun k ↦ (hE k).1
    exact ⟨hU, fun k ↦ hU.of_hom (E.f k) (hE k).2, fun n t ↦ hU.prod E (fun k ↦ (hE k).2) n t⟩
  · intro U hU R hR
    have : IsAffine U.left := hU.1
    obtain ⟨E, hfin, hEJ, hle, hE⟩ := exists_indEtale_covering_le R hR
    exact ⟨⟨E, hEJ⟩, ⟨hfin, hU, hE⟩, hle⟩
  · rintro U ⟨E, hEJ⟩ ⟨hfin, hU, hE⟩ q hq
    obtain ⟨A, _, _, Ub, πU, hUa, ⟨hUlim⟩⟩ := hU.exists_isLimit
    have : IsAffine U.left := hU.1
    have : ∀ k, IsAffine (E.X k).left := fun k ↦ (hE k).1
    exact isZero_cechCohomology_of_indEtale adj I Ub πU hUlim E (fun k ↦ (hE k).2) q hq

include adj in
/-- **Stacks 099U.** Let `X` be an affine scheme and let `ℐ` be an injective abelian sheaf on
`X_étale`.  Then `H^p(X_proétale, ε⁻¹ℐ) = 0` for `p > 0`, where `ε⁻¹` is an arbitrary left adjoint
of the restriction `ε_*` of pro-étale sheaves to the small étale site.

Pro-étale cohomology is `CategoryTheory.Sheaf.H`, `Ext` out of the constant sheaf `ℤ`.  The
constant sheaf `ℤ` is the free abelian sheaf on the final object `X` of `X_proétale`, which is an
affine object ind-étale over the affine étale `X`-scheme `X`, so this is
`AlgebraicGeometry.ProEtale.subsingleton_ext_proetaleInverseImage_of_injective` at `X`. -/
theorem subsingleton_sheafH_proetaleInverseImage_of_injective [IsAffine X]
    [HasExt.{w} (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v})] (p : ℕ)
    (hp : 0 < p) : Subsingleton (Sheaf.H (L.obj I) p) := by
  let : MorphismProperty.ContainsIdentities (@WeaklyEtale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ ↦ inferInstance⟩
  let T : X.ProEt := X.etaleToProetale.obj (Scheme.Etale.mk (𝟙 X))
  have : IsAffine (Scheme.Etale.mk (𝟙 X)).left := ‹IsAffine X›
  have hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal (@WeaklyEtale) X
  have hsub := subsingleton_ext_proetaleInverseImage_of_injective.{w} adj I
    (isAffineIndEtaleOverEtale_etaleToProetale_obj (Scheme.Etale.mk (𝟙 X))) p hp
  exact (((Abelian.extFunctor p).mapIso
    (freeSheafIsoConstantSheaf.{max (u + 1) v} (Scheme.ProEt.topology X) hT).op).app
      (L.obj I)).addCommGroupIsoToAddEquiv.subsingleton_congr.mpr hsub

end Etale

end AlgebraicGeometry.ProEtale
