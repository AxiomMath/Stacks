module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineLocal
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineLocalUnconditional
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.CoveringSheafCondition
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AssociatedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Comparison
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.RestrictionExactness
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.Defs
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.TopologyComparison
public import StacksFrontier.AlgebraicGeometry.Duality.AdequateSheafOfModules
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Coverings

/-!
# Parasitic modules on a chosen big site

[Stacks, Tag 06ZM] lists five equivalent conditions on an adequate `𝒪`-module `𝓕` on a big
`τ`-site over `S`: (1) `v𝓕 = 0`, (2) `𝓕` is parasitic, (3) `𝓕` is parasitic for the
`τ`-topology, (4) `𝓕(U) = 0` for every open `U ⊆ S`, and (5) `𝓕(Uᵢ) = 0` for the members of
some affine open covering of `S`. This module proves the equivalence. It then describes the
quotient of `Adeq(𝒪)` by the modules killed by `v`: that subcategory is a Serre subcategory and
`v` induces `Adeq(𝒪)/𝒞 ≌ QCoh(𝒪_S)`, which is [Stacks, Tag 06ZN], and the derived statement
`D(Adeq(𝒪))/D_𝒞(Adeq(𝒪)) = D(QCoh(𝒪_S))` of [Stacks, Tag 06ZQ].

## Main definitions

* `Stacks.Adequate.isTauCovering` — a covering family of the site whose image in the schemes
  over `S` is a `τ`-covering family.
* `Stacks.Adequate.BigSite.parasiticAdequate` — the subcategory `𝒞 ⊂ Adeq(𝒪)` of parasitic
  adequate modules.
* `Stacks.Adequate.BigSite.adequateQuotientEquivalence` — the equivalence
  `v̄ : Adeq(𝒪)/𝒞 ≌ QCoh(𝒪_S)` of [Stacks, Tag 06ZN], induced by `v`
  (`Stacks.Adequate.BigSite.quotientFunctorCompAdequateQuotientEquivalenceIso`).

## Main results

* `Stacks.Adequate.tfae_isZero_restrictModule_of_isAdequate` — **[Stacks, Tag 06ZM]**: the five
  conditions are equivalent for an adequate `𝒪`-module on a chosen big `τ`-site over `S`, for
  each of the five topologies.
* `Stacks.Adequate.tfae_isParasitic_of_isAdequate` — conditions (2)–(5) of
  [Stacks, Tag 06ZM], the part not mentioning `v`.
* `Stacks.Adequate.isParasiticFor_of_isParasitic`,
  `Stacks.Adequate.open_vanishing_of_isParasiticFor` and
  `Stacks.Adequate.exists_affine_cover_of_open_vanishing` — the implications
  (2) ⇒ (3) ⇒ (4) ⇒ (5), for an arbitrary sheaf of modules.
* `Stacks.Adequate.isParasitic_of_isAffine_cover` — the implication (5) ⇒ (2), for an adequate
  sheaf of modules.
* `Stacks.Adequate.subsingleton_obj_of_flat_of_isAffine` — an adequate module vanishing on an
  affine object of the site vanishes on every affine object mapping flatly to it.
* `Stacks.Adequate.isZero_restrictModule_of_isParasiticFor` and
  `Stacks.Adequate.open_vanishing_of_isZero_restrictModule` — (3) ⇒ (1) and (1) ⇒ (4).
* `Stacks.Adequate.tauCovering_component_isFlat` — a member of a `τ`-covering family of an
  object isomorphic to the base is flat over the base, for each of the five topologies.
* `Stacks.Adequate.isZero_iff_forall_subsingleton` — a sheaf of modules on a site is a zero
  object exactly when all of its sections vanish.
* `Stacks.Adequate.BigSite.parasiticAdequate_eq_kernel` — `𝒞` is the kernel of `v`
  ([Stacks, Tag 06ZM] (1) ⇔ (2)).
* `Stacks.Adequate.BigSite.isSerreClass_parasiticAdequate` — **[Stacks, Tag 06ZN]**, `𝒞` is a
  Serre subcategory.
* `Stacks.Adequate.BigSite.isLocalization_restrictModuleQCoh` — **[Stacks, Tag 06ZN]**, `v`
  induces `Adeq(𝒪)/𝒞 ≌ QCoh(𝒪_S)`: it is a localization functor for the isomorphisms modulo
  `𝒞`.
* `Stacks.Adequate.BigSite.isLocalization_mapDerivedCategory_restrictModuleQCoh` —
  [Stacks, Tag 06ZQ], the unbounded version; the bounded versions are in
  `StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.ParasiticDerivedQuotient`.

## Implementation notes

The implications (2) ⇒ (3) ⇒ (4) ⇒ (5) and (3) ⇒ (1) ⇒ (4) hold for an arbitrary sheaf of
modules on the site. Adequacy enters only in (5) ⇒ (2), which is the source's argument: an
object `V` of the site flat over `S` is covered by affine opens `Vⱼ` each mapping into some
member `Uᵢ` of the covering, the map `Vⱼ → Uᵢ` is flat because `Uᵢ → S` is an open immersion,
and the flat base-change formula `𝓕(Vⱼ) = 𝓕(Uᵢ) ⊗_{𝒪(Uᵢ)} 𝒪(Vⱼ)` of [Stacks, Tags 06VI and
06UW] (`Stacks.Adequate.bijective_affineSectionBaseChangeMap_base`) gives `𝓕(Vⱼ) = 0`; the
covering `{Vⱼ → V}` is a Zariski covering, hence a `τ`-covering, so `𝓕(V) = 0` because `𝓕` is
a sheaf. Writing `Vⱼ` as the spectrum of an algebra over `𝒪(Uᵢ)` uses
`AlgebraicGeometry.essImage_algSpec`.

Condition (1) is `v𝓕 = 0` for the restriction functor `v` of [Stacks, Tag 06VN], which on every
chosen big `τ`-site is `Stacks.Adequate.BigSite.zariskiRestrictModule`, and (1) ⇔ (4) is the
identification of the sections of `v𝓕` over an open `U ⊆ S` with the sections of `𝓕` over `U`
as an object of the site, which holds by definition.

The Serre subcategory `𝒞` of [Stacks, Tag 06ZN] is the parasitic adequate modules, and it is
the kernel of `v` by [Stacks, Tag 06ZM] (1) ⇔ (2), which is the source's argument: the kernel of
an exact functor is a Serre subcategory ([Stacks, Tag 02MQ]). The exactness of `v` is proved in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/RestrictionExactness.lean`. The quotient
`Adeq(𝒪)/𝒞` is Mathlib's Serre quotient, the localization at `𝒞.isoModSerre`, which is abelian
by [Stacks, Tag 02MS]. That `v` is a localization functor for this class is
`CategoryTheory.Adjunction.isLocalization'` for the adjunction `u ⊣ v` of [Stacks, Tag 06VN]
with `u` fully faithful (the unit `𝓕 → vu𝓕` is an isomorphism), together with Mathlib's
`CategoryTheory.Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms` for the exact functor
`v`: this is the source's essential surjectivity and full faithfulness of `v̄`, both coming from
`u` being a right inverse to `v`. The abelian structure on `Adeq(𝒪)` is
`Stacks.Adequate.abelian_adequate` ([Stacks, Tag 06VQ] (1)), a local instance from the quotient
section on; statements about `𝒞.isoModSerre` must be read with it installed. [Stacks, Tag 06ZQ]
is then [Stacks, Tag 06XM], namely
`CategoryTheory.ObjectProperty.SerreClassLocalization`'s
`isLocalization_mapDerivedCategory_of_leftAdjoint`, applied to `v`.

(2) ⇒ (3) is `Stacks.Adequate.tauCovering_component_isFlat`: a `τ`-covering family of an object
whose structure morphism is an isomorphism consists of morphisms that are flat over the base,
since a `τ`-covering family is an fppf covering family for each of the five topologies and the
structure morphism of each member factors through the isomorphism.

(3) ⇒ (4) tests condition (3) against the two-member covering family `{𝟙 T, U → T}` of the base
read as an object of the site, which is a `τ`-covering family because the identity is jointly
surjective on its own and both members are open immersions.

(4) ⇒ (5) is the covering of `S` by all of its affine opens.

## References

* [Stacks Project, Tag 06ZM](https://stacks.math.columbia.edu/tag/06ZM)
* [Stacks Project, Tag 06ZL](https://stacks.math.columbia.edu/tag/06ZL)
* [Stacks Project, Tag 06ZN](https://stacks.math.columbia.edu/tag/06ZN)
* [Stacks Project, Tag 06ZQ](https://stacks.math.columbia.edu/tag/06ZQ)
* [Stacks Project, Tag 06XM](https://stacks.math.columbia.edu/tag/06XM)
* [Stacks Project, Tag 02MQ](https://stacks.math.columbia.edu/tag/02MQ)
* [Stacks Project, Tag 02MS](https://stacks.math.columbia.edu/tag/02MS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u w u₁ v₁ w₁ w₂

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}}

/-- A covering family of a chosen big site over `S` whose image in the schemes over `S` is a
`τ`-covering family. -/
public abbrev isTauCovering (B : BigSite τ S) (E : Covering.{u + 1, u, w} B.category) : Prop :=
  (E.2.map (B.toOver ⋙ Over.forget S)).presieve₀ ∈
    Scheme.precoverage (coveringMorphismProperty τ) ((B.toOver.obj E.1).left)

/-- A member of a `τ`-covering family of an object of the site whose structure morphism is an
isomorphism is flat over the base: a `τ`-covering family is an fppf covering family, so the
member is flat over the covered object, and the structure morphism of the covered object is an
isomorphism. -/
public theorem tauCovering_component_isFlat (B : BigSite τ S)
    (E : Covering.{u + 1, u, w} B.category) (hE : IsIso ((B.toOver.obj E.1).hom))
    (hcover : isTauCovering B E) (i : E.2.I₀) :
    Flat ((B.toOver.obj (E.2.X i)).hom) := by
  have hdata := (Scheme.ofArrows_mem_precoverage_iff (coveringMorphismProperty τ)).1 hcover
  have hflat : Flat ((B.toOver.map (E.2.f i)).left) := by
    have hFppf : Presieve.ofArrows (E.2.map (B.toOver ⋙ Over.forget S)).X
        (E.2.map (B.toOver ⋙ Over.forget S)).f ∈
        Scheme.fppfPrecoverage ((B.toOver.obj E.1).left) := by
      cases τ with
      | fppf => exact (Scheme.ofArrows_mem_precoverage_iff _).2 hdata
      | syntomic =>
          exact Scheme.syntomicPrecoverage_le_fppfPrecoverage _
            ((Scheme.ofArrows_mem_precoverage_iff _).2 hdata)
      | smooth =>
          exact Scheme.smoothPrecoverage_le_fppfPrecoverage _
            ((Scheme.ofArrows_mem_precoverage_iff _).2 hdata)
      | etale =>
          exact Scheme.etalePrecoverage_le_fppfPrecoverage _
            ((Scheme.ofArrows_mem_precoverage_iff _).2 hdata)
      | zariski =>
          exact Scheme.zariskiPrecoverage_le_fppfPrecoverage _
            ((Scheme.ofArrows_mem_precoverage_iff _).2 hdata)
    exact ((Scheme.ofArrows_mem_precoverage_iff
      (@Flat.{u} ⊓ @LocallyOfFinitePresentation.{u})).1 hFppf).2 i |>.1
  have hfac : (B.toOver.map (E.2.f i)).left ≫ (B.toOver.obj E.1).hom
      = (B.toOver.obj (E.2.X i)).hom := (B.toOver.map (E.2.f i)).w
  have hcomp : Flat ((B.toOver.map (E.2.f i)).left ≫ (B.toOver.obj E.1).hom) := inferInstance
  rw [← hfac]
  exact hcomp

/-- **[Stacks, Tag 06ZM] (2) ⇒ (3).** A parasitic sheaf of modules on a chosen big site over
`S` is parasitic for the `τ`-topology. -/
public theorem isParasiticFor_of_isParasitic (B : BigSite τ S)
    (F : SheafOfModules.{u} B.structureSheaf)
    (hF : IsParasitic S B.toOver F.val) :
    IsParasiticFor.{u, w} S B.toOver (isTauCovering.{u, w} B) F.val :=
  fun _ hE hcover i => hF _ (tauCovering_component_isFlat B _ hE hcover i)

/-- **[Stacks, Tag 06ZM] (3) ⇒ (4).** A sheaf of modules parasitic for the `τ`-topology has no
sections over an object of the site whose structure morphism is an open immersion, so in
particular none over an open of `S`. -/
public theorem open_vanishing_of_isParasiticFor (B : BigSite τ S)
    (F : SheafOfModules.{u} B.structureSheaf)
    (hP : IsParasiticFor.{u, w} S B.toOver (isTauCovering.{u, w} B) F.val) :
    ∀ U : B.category, IsOpenImmersion ((B.toOver.obj U).hom) →
      Subsingleton (F.val.obj (op U)) := by
  intro U hU
  let T : B.category := Over.mk (𝟙 (⟨S, B.base_mem⟩ : SchemeBelow B.cutoff))
  let W : PUnit.{w + 1} ⊕ PUnit.{w + 1} → B.category := fun i =>
    match i with
    | Sum.inl _ => T
    | Sum.inr _ => U
  let g : U ⟶ T := Over.homMk U.hom (by simp [T])
  let E : Covering.{u + 1, u, w} B.category := ⟨T, {
    I₀ := PUnit.{w + 1} ⊕ PUnit.{w + 1}
    X := W
    f := fun i =>
      match i with
      | Sum.inl _ => 𝟙 T
      | Sum.inr _ => g }⟩
  have hE : IsIso ((B.toOver.obj E.1).hom) := by
    change IsIso (𝟙 S)
    infer_instance
  have hcover : isTauCovering.{u, w} B E := by
    change (E.2.map (B.toOver ⋙ Over.forget S)).presieve₀ ∈
      Scheme.precoverage (coveringMorphismProperty τ) S
    refine (Scheme.ofArrows_mem_precoverage_iff (coveringMorphismProperty τ)).2 ⟨?_, ?_⟩
    · intro x
      refine ⟨Sum.inl PUnit.unit, ⟨x, ?_⟩⟩
      change ((B.toOver.map (𝟙 T)).left) x = x
      rfl
    · intro i
      cases i with
      | inl _ =>
          change coveringMorphismProperty τ (𝟙 S)
          exact coveringMorphismProperty_of_isOpenImmersion τ (𝟙 S)
      | inr _ =>
          change coveringMorphismProperty τ ((B.toOver.map g).left)
          rw [show (B.toOver.map g).left = (B.toOver.obj U).hom from rfl]
          exact @coveringMorphismProperty_of_isOpenImmersion τ _ _
            ((B.toOver.obj U).hom) hU
  simpa [E, W] using hP E hE hcover (Sum.inr PUnit.unit)

/-- A sheaf of modules on a chosen big site over `S` with no sections over any open of `S` has no
sections over the members of an affine open covering of `S`, namely the covering of `S` by all
of its affine opens. This is the implication (4) ⇒ (5) of [Stacks, Tag 06ZM], for an arbitrary
sheaf of modules. -/
public theorem exists_affine_cover_of_open_vanishing (B : BigSite τ S)
    (F : SheafOfModules.{u} B.structureSheaf)
    (hopen : ∀ U : S.Opens, Subsingleton (F.val.obj (op (B.opensToBig.obj U)))) :
    ∃ (I : Type u) (U : I → S.Opens), (∀ i, IsAffineOpen (U i)) ∧ (⨆ i, U i) = ⊤ ∧
      ∀ i, Subsingleton (F.val.obj (op (B.opensToBig.obj (U i)))) :=
  ⟨S.affineOpens, (↑), fun V => V.2, iSup_affineOpens_eq_top S, fun V => hopen V⟩

/-- The open immersions of the members of an open covering of `S`, read as objects of a chosen
big site over `S`, are jointly surjective. -/
public theorem iUnion_range_opensToBig_eq_univ (B : BigSite τ S) {I : Type*} (U : I → S.Opens)
    (hU : (⨆ i, U i) = ⊤) :
    (⋃ i, Set.range ((B.toOver.obj (B.opensToBig.obj (U i))).hom)) = Set.univ := by
  refine Set.eq_univ_iff_forall.mpr fun x => ?_
  have hx : x ∈ (⨆ i, U i) := hU ▸ trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  rw [show Set.range ((B.toOver.obj (B.opensToBig.obj (U i))).hom) = Set.range (U i).ι from
    rfl, Scheme.Opens.range_ι]
  exact hi

/-! ### The converse (5) ⇒ (2), for an adequate module -/

/-- An adequate sheaf of modules with no sections over an affine object `U` of the site has no
sections over any affine object `V` of the site mapping flatly to `U`.

Writing `U = Spec A`, the object `V` is the spectrum of a flat `A`-algebra `C` of the site, and
by [Stacks, Tag 06VI] and [Stacks, Tag 06UW] the canonical map `C ⊗_A 𝓕(U) → 𝓕(V)` is
bijective (`Stacks.Adequate.bijective_affineSectionBaseChangeMap_base`); its source vanishes. -/
public theorem subsingleton_obj_of_flat_of_isAffine (B : BigSite τ S)
    (F : SheafOfModules.{u} B.structureSheaf) (hF : IsAdequate B F)
    {U V : B.category} [IsAffine U.left.obj] [IsAffine V.left.obj] (g : V ⟶ U)
    [Flat g.left.hom] (hU : Subsingleton (F.val.obj (op U))) :
    Subsingleton (F.val.obj (op V)) := by
  let A : CommRingCat.{u} := Γ(U.left.obj, ⊤)
  let eU : U.left.obj ≅ Spec A := U.left.obj.isoSpec
  let f : Spec A ⟶ S := eU.inv ≫ U.hom.hom
  have hA : schemeSizeBelow B.cutoff (Spec A) :=
    (Scheme.size_congr eU.symm).trans_lt U.left.property
  let e₀ : (affineSpecOver B A f).obj (op (baseAlgebraInSite B A hA)) ≅ U :=
    Over.isoMk (ObjectProperty.isoMk _ eU.symm) (by
      apply ObjectProperty.hom_ext
      simp [affineSpecOver, f, baseAlgebraInSite]
      rfl)
  have transfer : ∀ {X Y : B.category}, (X ≅ Y) → Subsingleton (F.val.obj (op X)) →
      Subsingleton (F.val.obj (op Y)) := fun e h =>
    @Equiv.subsingleton _ _
      ((F.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat).mapIso e.op).toEquiv h
  have h₀ : Subsingleton
      ((affineSectionFunctor B F A f).obj (op (op (baseAlgebraInSite B A hA)))) :=
    transfer e₀.symm hU
  let V' : Over (Spec A) := Over.mk (g.left.hom ≫ eU.hom)
  have hV' : IsAffine V'.left := inferInstanceAs (IsAffine V.left.obj)
  obtain ⟨R₀, ⟨e⟩⟩ := (essImage_algSpec (G := V')).mpr hV'
  have hsize : schemeSizeBelow B.cutoff (Spec (CommRingCat.of (R₀.unop : Type u))) :=
    (Scheme.size_congr ((Over.forget (Spec A)).mapIso e)).trans_lt V.left.property
  let C : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff) := ⟨R₀.unop, hsize⟩
  have hw : e.hom.left ≫ g.left.hom ≫ eU.hom =
      Spec.map (CommRingCat.ofHom (algebraMap A R₀.unop)) := by
    simpa [V'] using Over.w e.hom
  have hC : Module.Flat A R₀.unop := by
    have hflat : Flat (Spec.map (CommRingCat.ofHom (algebraMap A R₀.unop))) := by
      have h₁ : Flat e.hom.left := by
        have : IsIso e.hom.left := (Over.forget (Spec A)).map_isIso e.hom
        exact inferInstance
      have h₂ : Flat eU.hom := inferInstance
      rw [← hw]
      exact MorphismProperty.comp_mem @Flat _ _ h₁
        (MorphismProperty.comp_mem @Flat _ _ (inferInstanceAs (Flat g.left.hom)) h₂)
    exact RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp hflat)
  let eV : (affineSpecOver B A f).obj (op C) ≅ V :=
    Over.isoMk (ObjectProperty.isoMk _ ((Over.forget (Spec A)).mapIso e)) (by
      apply ObjectProperty.hom_ext
      have gw : g.left.hom ≫ U.hom.hom = V.hom.hom := congrArg (fun p => p.hom) (Over.w g)
      have hw' : e.hom.left ≫ g.left.hom =
          (Spec.map (CommRingCat.ofHom (algebraMap A R₀.unop)) : _ ⟶ Spec A) ≫ eU.inv :=
        (Iso.eq_comp_inv eU).2 ((Category.assoc _ _ _).trans hw)
      change e.hom.left ≫ V.hom.hom =
        Spec.map (CommRingCat.ofHom (algebraMap A R₀.unop)) ≫ eU.inv ≫ U.hom.hom
      rw [← gw, ← Category.assoc, hw']
      exact Category.assoc _ _ _)
  exact transfer eV
    (bijective_affineSectionBaseChangeMap_base.{u, u} B F hF A f hA C hC).2.subsingleton

/-- **The implication (5) ⇒ (2) of [Stacks, Tag 06ZM].** An adequate sheaf of modules on a
chosen big site over `S` which has no sections over the members `Uᵢ` of a jointly surjective
family of open immersions from affine schemes is parasitic.

An object `X` of the site flat over `S` is covered by the affine opens `V ⊆ X` mapping into
one of the members `Uᵢ`; each `V → Uᵢ` is flat, because `V → S` is and `Uᵢ → S` is an open
immersion, so `𝓕(V) = 0` by `Stacks.Adequate.subsingleton_obj_of_flat_of_isAffine`, and
`𝓕(X) = 0` because `𝓕` is a sheaf for the Zariski coverings of the site. -/
public theorem isParasitic_of_isAffine_cover (B : BigSite τ S)
    (F : SheafOfModules.{u} B.structureSheaf) (hF : IsAdequate B F) {I : Type*}
    (U : I → B.category)
    (hU : ∀ i, IsOpenImmersion ((B.toOver.obj (U i)).hom) ∧
      IsAffine ((B.toOver.obj (U i)).left) ∧ Subsingleton (F.val.obj (op (U i))))
    (hcov : (⋃ i, Set.range ((B.toOver.obj (U i)).hom)) = Set.univ) :
    IsParasitic S B.toOver F.val := by
  intro X hX
  let Y : Scheme.{u} := X.left.obj
  let K := Σ i : I, {V : Y.affineOpens //
    ((V : Y.Opens) : Set Y) ⊆ X.hom.hom ⁻¹' Set.range (U i).hom.hom}
  let W (k : K) : B.category :=
    Over.mk (ObjectProperty.homMk
      (X := (⟨(k.2.1 : Y.Opens).toScheme,
        Scheme.size_lt_of_isOpenImmersion (k.2.1 : Y.Opens).ι X.left.property⟩ :
          SchemeBelow B.cutoff))
      (Y := (⟨S, B.base_mem⟩ : SchemeBelow B.cutoff)) ((k.2.1 : Y.Opens).ι ≫ X.hom.hom))
  let ι (k : K) : W k ⟶ X :=
    Over.homMk (ObjectProperty.homMk (k.2.1 : Y.Opens).ι) (ObjectProperty.hom_ext _ rfl)
  have hrange (k : K) : Set.range ((k.2.1 : Y.Opens).ι ≫ X.hom.hom) ⊆
      Set.range (U k.1).hom.hom := by
    rintro _ ⟨y, rfl⟩
    have hy : (k.2.1 : Y.Opens).ι y ∈ ((k.2.1 : Y.Opens) : Set Y) := by
      rw [← Scheme.Opens.range_ι]
      exact ⟨y, rfl⟩
    exact k.2.2 hy
  have hW (k : K) : Subsingleton (F.val.obj (op (W k))) := by
    have : IsOpenImmersion (U k.1).hom.hom := (hU k.1).1
    have : IsAffine (U k.1).left.obj := (hU k.1).2.1
    have : IsAffine (W k).left.obj := k.2.1.2
    let l := IsOpenImmersion.lift (U k.1).hom.hom ((k.2.1 : Y.Opens).ι ≫ X.hom.hom) (hrange k)
    have hl : l ≫ (U k.1).hom.hom = (k.2.1 : Y.Opens).ι ≫ X.hom.hom :=
      IsOpenImmersion.lift_fac _ _ _
    let g : W k ⟶ U k.1 :=
      Over.homMk (ObjectProperty.homMk (X := (W k).left) (Y := (U k.1).left) l)
        (ObjectProperty.hom_ext _ hl)
    have : Flat g.left.hom := by
      have hpost : MorphismProperty.HasOfPostcompProperty @Flat.{u} @IsOpenImmersion.{u} :=
        @hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict @Flat.{u}
          (MorphismProperty.IsStableUnderBaseChange.respectsIso (P := @Flat.{u}))
          fun f _ (_ : Flat f) => inferInstance
      refine hpost.of_postcomp l (U k.1).hom.hom (hU k.1).1 ?_
      rw [hl]
      exact MorphismProperty.comp_mem @Flat _ _ inferInstance (show Flat X.hom.hom from hX)
    exact subsingleton_obj_of_flat_of_isAffine B F hF g (hU k.1).2.2
  have hS : Sieve.generate (Presieve.ofArrows W ι) ∈ B.topology X := by
    refine sieve_generate_mem_topology_of_coveringMorphismProperty B W ι
      (fun k => @coveringMorphismProperty_of_isOpenImmersion τ _ _ (k.2.1 : Y.Opens).ι
        inferInstance) fun x => ?_
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov.symm ▸ Set.mem_univ (X.hom.hom x))
    have : IsOpenImmersion (U i).hom.hom := (hU i).1
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVsub⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (a := x)
        (u := ((X.hom.hom ⁻¹ᵁ (U i).hom.hom.opensRange : Y.Opens) : Set Y)) hi
        (X.hom.hom ⁻¹ᵁ (U i).hom.hom.opensRange).isOpen
    refine ⟨⟨i, ⟨V, hV⟩, hVsub⟩, ?_⟩
    rw [← Scheme.Opens.range_ι] at hxV
    exact hxV
  refine ⟨fun s t => ?_⟩
  have hzero (s : F.val.obj (op X)) : s = 0 :=
    Stacks.SheafOfModules.eq_zero_of_locally_eq_zero (R := B.structureSheaf) s hS
      (by
        rintro Z _ ⟨Z', a, _, ⟨k⟩, rfl⟩
        rw [op_comp, PresheafOfModules.map_comp_apply, (hW k).elim (F.val.map (ι k).op s) 0]
        exact map_zero _)
  rw [hzero s, hzero t]

/-! ### Vanishing of a sheaf of modules -/

/-- A sheaf of modules on a site is a zero object exactly when all of its sections vanish. -/
public theorem isZero_iff_forall_subsingleton {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} (M : SheafOfModules.{u} R) :
    IsZero M ↔ ∀ U : Cᵒᵖ, Subsingleton (M.val.obj U) := by
  refine ⟨fun h U => ?_, fun h => ?_⟩
  · rw [← ModuleCat.isZero_iff_subsingleton]
    exact Functor.map_isZero
      (SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj U) h
  · rw [IsZero.iff_id_eq_zero]
    ext U y
    exact (h U).elim y 0

/-! ### Restriction to the small Zariski site -/

variable {S : Scheme.{u}}

/-- The sections of `v𝓕 = 𝓕|_{S_Zar}` over an open `U ⊆ S` are the sections of `𝓕` over `U`
read as an object of the chosen big site over `S`. -/
public theorem subsingleton_restrictModule_val_obj (B : BigSite τ S)
    (F : SheafOfModules.{u} B.structureSheaf) (U : (S.Opens)ᵒᵖ)
    (h : Subsingleton (F.val.obj (op (B.opensToBig.obj U.unop)))) :
    Subsingleton ((B.zariskiRestrictModule.obj F).val.obj U) := h

/-- **[Stacks, Tag 06ZM] (3) ⇒ (1).** A sheaf of modules on a chosen big `τ`-site over `S`
which is parasitic for the `τ`-topology has `v𝓕 = 0`. -/
public theorem isZero_restrictModule_of_isParasiticFor (B : BigSite τ S)
    (F : SheafOfModules.{u} B.structureSheaf)
    (hP : IsParasiticFor.{u, w} S B.toOver (isTauCovering.{u, w} B) F.val) :
    IsZero (B.zariskiRestrictModule.obj F) :=
  (isZero_iff_forall_subsingleton _).2 fun U => subsingleton_restrictModule_val_obj B F U
    (open_vanishing_of_isParasiticFor B F hP _
      (inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι U.unop))))

/-- **[Stacks, Tag 06ZM] (1) ⇒ (4).** A sheaf of modules on a chosen big `τ`-site over `S`
with `v𝓕 = 0` has no sections over any open of `S`. -/
public theorem open_vanishing_of_isZero_restrictModule (B : BigSite τ S)
    (F : SheafOfModules.{u} B.structureSheaf)
    (h : IsZero (B.zariskiRestrictModule.obj F)) (U : S.Opens) :
    Subsingleton (F.val.obj (op (B.opensToBig.obj U))) :=
  (isZero_iff_forall_subsingleton _).1 h (op U)

/-! ### The equivalence -/

/-- **[Stacks, Tag 06ZM], conditions (2)–(5).** For an adequate `𝒪`-module `𝓕` on a chosen
big `τ`-site over `S`, the following are equivalent: (2) `𝓕` is parasitic, (3) `𝓕` is parasitic
for the `τ`-topology, (4) `𝓕(U) = 0` for every open `U ⊆ S`, and (5) there is an affine open
covering `S = ⋃ Uᵢ` with `𝓕(Uᵢ) = 0` for all `i`.

This carries no tag: the five conditions together, (1) `v𝓕 = 0` included, are
`Stacks.Adequate.tfae_isZero_restrictModule_of_isAdequate`, which carries [Stacks, Tag 06ZM]. -/
public theorem tfae_isParasitic_of_isAdequate (B : BigSite τ S)
    (F : SheafOfModules.{u} B.structureSheaf) (hF : IsAdequate B F) :
    List.TFAE
      [IsParasitic S B.toOver F.val,
        IsParasiticFor.{u, w} S B.toOver (isTauCovering.{u, w} B) F.val,
        ∀ U : S.Opens, Subsingleton (F.val.obj (op (B.opensToBig.obj U))),
        ∃ (I : Type u) (U : I → S.Opens), (∀ i, IsAffineOpen (U i)) ∧ (⨆ i, U i) = ⊤ ∧
          ∀ i, Subsingleton (F.val.obj (op (B.opensToBig.obj (U i))))] := by
  tfae_have 1 → 2 := isParasiticFor_of_isParasitic B F
  tfae_have 2 → 3 := fun h U =>
    open_vanishing_of_isParasiticFor B F h _ (inferInstanceAs (IsOpenImmersion U.ι))
  tfae_have 3 → 4 := exists_affine_cover_of_open_vanishing B F
  tfae_have 4 → 1 := fun ⟨_, U, hUa, hU, hU0⟩ =>
    isParasitic_of_isAffine_cover B F hF (fun i => B.opensToBig.obj (U i))
      (fun i => ⟨inferInstanceAs (IsOpenImmersion (U i).ι), hUa i, hU0 i⟩)
      (iUnion_range_opensToBig_eq_univ B U hU)
  tfae_finish

/-- **[Stacks, Tag 06ZM].** Let `𝓕` be an adequate `𝒪`-module on a chosen big `τ`-site over
`S`, for `τ` any of the five topologies `Zar`, `étale`, `smooth`, `syntomic`, `fppf`. The
following are equivalent:
1. `v𝓕 = 0`, for the restriction `v𝓕 = 𝓕|_{S_Zar}` of `𝓕` to the small Zariski site of `S`
   (`Stacks.Adequate.BigSite.zariskiRestrictModule`, the functor `v` of [Stacks, Tag 06VN]);
2. `𝓕` is parasitic;
3. `𝓕` is parasitic for the `τ`-topology;
4. `𝓕(U) = 0` for every open `U ⊆ S`;
5. there is an affine open covering `S = ⋃ Uᵢ` such that `𝓕(Uᵢ) = 0` for all `i`.

(2)–(5) are `Stacks.Adequate.tfae_isParasitic_of_isAdequate`; (1) ⇔ (4) is the identification of
the sections of `v𝓕` over `U` with those of `𝓕` over `U` as an object of the site. -/
@[stacks 06ZM]
public theorem tfae_isZero_restrictModule_of_isAdequate (B : BigSite τ S)
    (F : SheafOfModules.{u} B.structureSheaf) (hF : IsAdequate B F) :
    List.TFAE
      [IsZero (B.zariskiRestrictModule.obj F),
        IsParasitic S B.toOver F.val,
        IsParasiticFor.{u, w} S B.toOver (isTauCovering.{u, w} B) F.val,
        ∀ U : S.Opens, Subsingleton (F.val.obj (op (B.opensToBig.obj U))),
        ∃ (I : Type u) (U : I → S.Opens), (∀ i, IsAffineOpen (U i)) ∧ (⨆ i, U i) = ⊤ ∧
          ∀ i, Subsingleton (F.val.obj (op (B.opensToBig.obj (U i))))] := by
  have h := tfae_isParasitic_of_isAdequate.{u, w} B F hF
  tfae_have 1 ↔ 4 := ⟨open_vanishing_of_isZero_restrictModule B F, fun h =>
    (isZero_iff_forall_subsingleton _).2 fun U => subsingleton_restrictModule_val_obj B F U
      (h U.unop)⟩
  tfae_have 2 ↔ 4 := h.out 1 3
  tfae_have 3 ↔ 4 := h.out 2 3
  tfae_have 5 ↔ 4 := h.out 4 3
  tfae_finish

/-! ### The quotient of the adequate modules by the parasitic ones -/

section Quotient

variable (B : BigSite τ S)

/-- The parasitic adequate `𝒪`-modules on a chosen big `τ`-site over `S`: the subcategory
`𝒞 ⊂ Adeq(𝒪)` of [Stacks, Tag 06ZN]. -/
public def BigSite.parasiticAdequate : ObjectProperty (adequate.{u, u} B).FullSubcategory :=
  fun F => IsParasitic S B.toOver F.obj.val

/-- The parasitic adequate modules are the kernel of `v : Adeq(𝒪) ⥤ QCoh(𝒪_S)`: this is
[Stacks, Tag 06ZM] (1) ⇔ (2), read in the full subcategory `QCoh(𝒪_S)`. -/
public theorem BigSite.parasiticAdequate_eq_kernel :
    B.parasiticAdequate = B.restrictModuleQCoh.kernel := by
  ext F
  refine ((tfae_isZero_restrictModule_of_isAdequate.{u, u} B F.obj F.property).out 1 2).symm.trans
    ⟨fun h => IsZero.of_full_of_faithful_of_isZero
      (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι _ h,
    fun h => (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι.map_isZero h⟩

attribute [local instance] abelian_adequate

/-- **[Stacks, Tag 06ZN], the Serre subcategory.** The parasitic adequate `𝒪`-modules form a
Serre subcategory `𝒞` of `Adeq(𝒪)`: it is the kernel of the exact functor
`v : Adeq(𝒪) ⥤ QCoh(𝒪_S)` (`Stacks.Adequate.BigSite.parasiticAdequate_eq_kernel`, which is
[Stacks, Tag 06ZM]), and the kernel of an exact functor is a Serre subcategory
([Stacks, Tag 02MQ]). `v` is exact by
`Stacks.Adequate.BigSite.preservesFiniteLimits_restrictModuleQCoh` and
`Stacks.Adequate.BigSite.preservesFiniteColimits_restrictModuleQCoh`. The abelian structure on
`Adeq(𝒪)` is [Stacks, Tag 06VQ] (1), `Stacks.Adequate.abelian_adequate`. -/
@[stacks 06ZN "the subcategory of parasitic adequate modules is a Serre subcategory"]
public instance BigSite.isSerreClass_parasiticAdequate : B.parasiticAdequate.IsSerreClass := by
  rw [B.parasiticAdequate_eq_kernel]
  infer_instance

/-- The morphisms of `Adeq(𝒪)` which are isomorphisms modulo the parasitic adequate modules are
exactly those which `v : Adeq(𝒪) ⥤ QCoh(𝒪_S)` sends to isomorphisms. -/
public theorem BigSite.isoModSerre_parasiticAdequate_eq_inverseImage :
    B.parasiticAdequate.isoModSerre =
      (MorphismProperty.isomorphisms _).inverseImage B.restrictModuleQCoh := by
  have h : ∀ (P : ObjectProperty (adequate.{u, u} B).FullSubcategory) (hP : P.IsSerreClass),
      P = B.restrictModuleQCoh.kernel → P.isoModSerre =
        (MorphismProperty.isomorphisms _).inverseImage B.restrictModuleQCoh := by
    rintro P hP rfl
    exact Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms B.restrictModuleQCoh
  exact h _ inferInstance B.parasiticAdequate_eq_kernel

/-- **[Stacks, Tag 06ZN], the quotient equivalence.** The functor `v : Adeq(𝒪) ⥤ QCoh(𝒪_S)`
induces an equivalence `Adeq(𝒪)/𝒞 ≌ QCoh(𝒪_S)`, where `𝒞` is the Serre subcategory of
parasitic adequate modules and `Adeq(𝒪)/𝒞` is the Serre quotient, the localization of `Adeq(𝒪)`
at the morphisms which are isomorphisms modulo `𝒞` ([Stacks, Tag 02MS]): `v` is a localization
functor for that class of morphisms.

The proof is the source's. `v` is exact, its kernel is `𝒞`, so the morphisms inverted by `v`
are those which are isomorphisms modulo `𝒞`; and `v` has the fully faithful left adjoint
`u : QCoh(𝒪_S) ⥤ Adeq(𝒪)` of [Stacks, Tag 06VN] (`Stacks.Adequate.BigSite.adeqAdjunction`,
the unit `𝓕 → vu𝓕` being an isomorphism), which makes the induced functor `v̄` essentially
surjective and fully faithful (`CategoryTheory.Adjunction.isLocalization'`). -/
@[stacks 06ZN "the functor `v` induces an equivalence `Adeq(𝒪)/𝒞 = QCoh(𝒪_S)`: `v` is a
localization functor for the isomorphisms modulo the Serre subcategory `𝒞`"]
public instance BigSite.isLocalization_restrictModuleQCoh :
    B.restrictModuleQCoh.IsLocalization B.parasiticAdequate.isoModSerre := by
  have := B.full_associatedModuleAdeq
  have := B.faithful_associatedModuleAdeq
  rw [B.isoModSerre_parasiticAdequate_eq_inverseImage]
  exact B.adeqAdjunction.isLocalization'

/-- **[Stacks, Tag 06ZN], the equivalence `v̄ : Adeq(𝒪)/𝒞 ≌ QCoh(𝒪_S)`** from the Serre quotient
of `Adeq(𝒪)` by the parasitic adequate modules, induced by `v`: its composite with the quotient
functor is `v` (`Stacks.Adequate.BigSite.quotientFunctorCompAdequateQuotientEquivalenceIso`). -/
public noncomputable def BigSite.adequateQuotientEquivalence :
    B.parasiticAdequate.isoModSerre.Localization ≌
      (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory :=
  Localization.equivalenceFromModel B.restrictModuleQCoh _

/-- The equivalence `v̄ : Adeq(𝒪)/𝒞 ≌ QCoh(𝒪_S)` is induced by `v`: the quotient functor
followed by `v̄` is `v`. -/
public noncomputable def BigSite.quotientFunctorCompAdequateQuotientEquivalenceIso :
    B.parasiticAdequate.isoModSerre.Q ⋙ B.adequateQuotientEquivalence.functor ≅
      B.restrictModuleQCoh :=
  Localization.qCompEquivalenceFromModelFunctorIso B.restrictModuleQCoh _

/-- **[Stacks, Tag 06ZQ].** `D(Adeq(𝒪))/D_𝒞(Adeq(𝒪)) = D(QCoh(𝒪_S))`: the functor
`D(v) : D(Adeq(𝒪)) ⥤ D(QCoh(𝒪_S))` is a localization functor for the morphisms whose cone has
all its cohomology objects in the Serre subcategory `𝒞` of parasitic adequate modules. This is
[Stacks, Tag 06XM] applied to `v`, which realises the Serre quotient by `𝒞`
(`Stacks.Adequate.BigSite.isLocalization_restrictModuleQCoh`, [Stacks, Tag 06ZN]) and has the
fully faithful left adjoint `u` of [Stacks, Tag 06VN]. -/
@[stacks 06ZQ "the unbounded derived quotient `D(Adeq(𝒪))/D_𝒞(Adeq(𝒪)) = D(QCoh(𝒪_S))`"]
public theorem BigSite.isLocalization_mapDerivedCategory_restrictModuleQCoh
    [HasDerivedCategory.{w₁} (adequate.{u, u} B).FullSubcategory]
    [HasDerivedCategory.{w₂} (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory] :
    B.restrictModuleQCoh.mapDerivedCategory.IsLocalization
      (ObjectProperty.trW (fun X : DerivedCategory (adequate.{u, u} B).FullSubcategory =>
        ∀ n : ℤ, B.parasiticAdequate
          ((DerivedCategory.homologyFunctor (adequate.{u, u} B).FullSubcategory n).obj X))) := by
  have := B.full_associatedModuleAdeq
  have := B.faithful_associatedModuleAdeq
  exact ObjectProperty.SerreClassLocalization.isLocalization_mapDerivedCategory_of_leftAdjoint
    B.restrictModuleQCoh B.parasiticAdequate B.adeqAdjunction

end Quotient

end Stacks.Adequate

end
