module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EtaleLocalizationStrongSplitting
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.Splittings

/-!
# The arrow containment of Stacks 03FM: the generic half

For a finite part `F` of a groupoid in algebraic spaces (Stacks 04RU), this file supplies the
membership criterion for the universal open `Z_univ` on sections
(`AlgebraicGeometry.Space.FinitePartUniversalOpen.exists_lift_universalOpen_iff`, from the
universal property of Stacks 04PE (2)), the pair `(g ∘ x, Z_x)` of Stacks 04PC which a section
`x` of `U'` names, the predicate `CutsOut`, the pair `targetPairAt` which `t'` names, and the
arrow containment on sections,
`AlgebraicGeometry.Space.FinitePartUniversalOpen.exists_toRestriction_eq`.

See `StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationArrowContainment.lean`
for the overview and implementation notes.
-/
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry.Space

open GroupoidInAlgebraicSpaces

section Generic

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS B}

/-- Pullbacks of presheaves on `BigFppfOver C S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_SectionContainment :
    HasPullbacks ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_SectionContainment
    {X Y Z : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- Transfer of lifts along a base-change square of finite open subspaces: if the open
subspace of `q` is cartesian over the open subspace of `p` along `g`, compatibly with the
second projections, then a section of the ambient fibre product of `q` factors through the
open subspace of `q` exactly when its image in the ambient fibre product of `p` factors
through the open subspace of `p`. -/
theorem exists_lift_of_pairSquares {X Y T T' : AlgebraicSpaces C S hS} (f : X ⟶ Y)
    (p : FiniteOpenSubspace C S hS f T) (q : FiniteOpenSubspace C S hS f T')
    (g : T'.obj ⟶ T.obj)
    (j : q.subspace.toFunctor ⟶ p.subspace.toFunctor)
    (hj : IsPullback (q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom) j g
      (p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom))
    (hsnd : j ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom =
      q.subspace.ι ≫ pullback.snd q.toBase.hom f.hom)
    {A : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (φ : A ⟶ T'.obj) (ψ : A ⟶ X.obj)
    (hc : φ ≫ q.toBase.hom = ψ ≫ f.hom)
    (hc' : (φ ≫ g) ≫ p.toBase.hom = ψ ≫ f.hom) :
    (∃ n : A ⟶ q.subspace.toFunctor, n ≫ q.subspace.ι = pullback.lift φ ψ hc) ↔
      ∃ n' : A ⟶ p.subspace.toFunctor,
        n' ≫ p.subspace.ι = pullback.lift (φ ≫ g) ψ hc' := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n ≫ j, pullback.hom_ext ?_ ?_⟩
    · simp only [Category.assoc, pullback.lift_fst]
      rw [← hj.w]
      simp only [Category.assoc]
      rw [← Category.assoc, hn, ← Category.assoc, pullback.lift_fst]
    · simp only [Category.assoc, pullback.lift_snd]
      rw [hsnd, ← Category.assoc, hn, pullback.lift_snd]
  · rintro ⟨n', hn'⟩
    have hwn : φ ≫ g = n' ≫ p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom := by
      rw [← Category.assoc, hn', pullback.lift_fst]
    refine ⟨hj.lift φ n' hwn, pullback.hom_ext ?_ ?_⟩
    · simp only [Category.assoc, pullback.lift_fst]
      exact hj.lift_fst φ n' hwn
    · simp only [Category.assoc, pullback.lift_snd]
      rw [← hsnd, ← Category.assoc, hj.lift_snd φ n' hwn, ← Category.assoc, hn', pullback.lift_snd]

/-- A morphism of presheaves factors through the image subfunctor of a monomorphism exactly
when it factors through that monomorphism. -/
theorem exists_lift_range_iff {D : Type v} [Category.{u} D] {X Y : Dᵒᵖ ⥤ Type u}
    (j : Y ⟶ X) [Mono j] {A : Dᵒᵖ ⥤ Type u} (k : A ⟶ X) :
    (∃ n : A ⟶ (Subfunctor.range j).toFunctor, n ≫ (Subfunctor.range j).ι = k) ↔
      ∃ l : A ⟶ Y, l ≫ j = k := by
  have h1 : inv (Subfunctor.toRange j) ≫ j = (Subfunctor.range j).ι :=
    (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι j).symm
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n ≫ inv (Subfunctor.toRange j), by rw [Category.assoc, h1, hn]⟩
  · rintro ⟨l, hl⟩
    exact ⟨l ≫ Subfunctor.toRange j, by rw [Category.assoc, Subfunctor.toRange_ι, hl]⟩

/-- A morphism of schemes factors through an open immersion exactly when its set-theoretic
image is contained in the image of that open immersion. -/
theorem exists_scheme_lift_iff_range_subset {X₀ Y₀ Z₀ : Scheme.{u}} (jj : Y₀ ⟶ Z₀)
    (hjj : AlgebraicGeometry.IsOpenImmersion jj) (χ : X₀ ⟶ Z₀) :
    (∃ l : X₀ ⟶ Y₀, l ≫ jj = χ) ↔ Set.range χ.base ⊆ Set.range jj.base := by
  constructor
  · rintro ⟨l, rfl⟩ _ ⟨x, rfl⟩
    exact ⟨l x, (Scheme.Hom.comp_apply l jj x).symm⟩
  · intro h
    exact ⟨AlgebraicGeometry.IsOpenImmersion.lift (H := hjj) jj χ h,
      AlgebraicGeometry.IsOpenImmersion.lift_fac (H := hjj) jj χ h⟩

/-- A morphism of the site factors through the inclusion of an open subscheme of its target
exactly when its underlying morphism of schemes factors through that open immersion. -/
theorem exists_siteOpen_lift_iff (T : BigFppfOver C S hS) {W₀ : Scheme.{u}}
    (jj : W₀ ⟶ (BigFppfOver.toScheme C S hS).obj T)
    (hjj : AlgebraicGeometry.IsOpenImmersion jj)
    (V' : BigFppfOver C S hS) (k₀ : V' ⟶ T) :
    (∃ l : V' ⟶ etaleLocalSiteOpenObject C S hS T jj hjj,
        l ≫ siteOpenMap C S hS T jj hjj = k₀) ↔
      ∃ l₁ : (BigFppfOver.toScheme C S hS).obj V' ⟶ W₀,
        l₁ ≫ jj = (BigFppfOver.toScheme C S hS).map k₀ := by
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨(BigFppfOver.toScheme C S hS).map l,
      (((BigFppfOver.toScheme C S hS).map_comp _ _).trans
        (congrArg (fun z => (BigFppfOver.toScheme C S hS).map l ≫ z)
          (toScheme_map_siteOpenMap C S hS T jj hjj))).symm⟩
  · rintro ⟨l₁, hl₁⟩
    have hw : l₁ ≫ jj ≫ T.hom.hom = V'.hom.hom :=
      (Category.assoc l₁ jj T.hom.hom).symm.trans
        ((congrArg (fun z => z ≫ T.hom.hom) hl₁).trans
          (congrArg (fun z : V'.left ⟶ C.obj hS => z.hom) (Over.w k₀)))
    refine ⟨Over.homMk (ObjectProperty.homMk l₁)
      (by apply ObjectProperty.hom_ext; exact hw), ?_⟩
    refine (BigFppfOver.toScheme C S hS).map_injective ?_
    refine ((BigFppfOver.toScheme C S hS).map_comp _ _).trans ?_
    exact (congrArg (fun z => l₁ ≫ z) (toScheme_map_siteOpenMap C S hS T jj hjj)).trans hl₁

namespace FinitePartUniversalOpen

/-- The pair `(g ∘ x, Z_x)` of Stacks 04PC which the object space of the finite part names at
a section `x` of it over a scheme of the site: the image of that section under the inclusion
of the object space into the finite part presheaf, read through the bijection of Stacks 04PE
between sections of the presheaf and finite open subspaces. -/
def objectsPair (F : FinitePartUniversalOpen G) (V : BigFppfOver C S hS)
    (m : yoneda.obj V ⟶ F.objects.obj) :
    FiniteOpenSubspace C S hS G.source (AlgebraicGeometry.schemeSpace V) :=
  (finiteOpenSubspacePresheaf C S hS G.source).sections V
    (F.objectsInclusion.app (Opposite.op V) (yonedaEquiv m))

/-- **The pair named at a section of the object space is the base change of the universal pair
along that section.**  This is the universal property of Stacks 04PE (2) for the classifying
morphism of `Z_univ`, which is the inclusion of the object space of the finite part. -/
theorem objectsPair_isBaseChange (F : FinitePartUniversalOpen G)
    (V : BigFppfOver C S hS) (m : yoneda.obj V ⟶ F.objects.obj) :
    (F.objectsPair V m).toBase.hom = m ≫ F.universalOpen.toBase.hom ∧
      ∃ j : (F.objectsPair V m).subspace.toFunctor ⟶ F.universalOpen.subspace.toFunctor,
        IsPullback ((F.objectsPair V m).subspace.ι ≫
            pullback.fst (F.objectsPair V m).toBase.hom G.source.hom) j m
          (F.universalOpen.subspace.ι ≫
            pullback.fst F.universalOpen.toBase.hom G.source.hom) ∧
        j ≫ F.universalOpen.subspace.ι ≫
            pullback.snd F.universalOpen.toBase.hom G.source.hom =
          (F.objectsPair V m).subspace.ι ≫
            pullback.snd (F.objectsPair V m).toBase.hom G.source.hom := by
  have spec := (finiteOpenSubspaceEquiv C S hS G.source F.objects).2 F.objectsInclusion V m
  rwa [F.objectsInclusion_spec] at spec

/-- The base of the pair named at a section of the object space. -/
theorem objectsPair_toBase_hom (F : FinitePartUniversalOpen G)
    (V : BigFppfOver C S hS) (m : yoneda.obj V ⟶ F.objects.obj) :
    (F.objectsPair V m).toBase.hom = m ≫ F.universalOpen.toBase.hom :=
  (F.objectsPair_isBaseChange V m).1

/-- **Membership in `Z_univ`, stated on sections.**  A section of the ambient fibre product
`U' ×_{g, U, s} R` whose `U'`-component is a section `x` of the object space of the finite part
factors through `Z_univ` exactly when the pair of the identity and its `R`-component factors
through the open subspace `Z_x` which `x` names.

This is the description of membership in `Z_univ` needed by the third step of the proof of
Stacks 03FM: `Z_univ` is characterized by its universal property rather than by a membership
criterion, and this turns the one into the other. -/
theorem exists_lift_universalOpen_iff (F : FinitePartUniversalOpen G)
    (V : BigFppfOver C S hS) (m : yoneda.obj V ⟶ F.objects.obj)
    {A : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (φ : A ⟶ yoneda.obj V) (ψ : A ⟶ G.arrows.obj)
    (hc : φ ≫ (F.objectsPair V m).toBase.hom = ψ ≫ G.source.hom)
    (hc' : (φ ≫ m) ≫ F.universalOpen.toBase.hom = ψ ≫ G.source.hom) :
    (∃ n : A ⟶ (F.objectsPair V m).subspace.toFunctor,
        n ≫ (F.objectsPair V m).subspace.ι = pullback.lift φ ψ hc) ↔
      ∃ n' : A ⟶ F.universalOpen.subspace.toFunctor,
        n' ≫ F.universalOpen.subspace.ι = pullback.lift (φ ≫ m) ψ hc' := by
  obtain ⟨j, hj, hsnd⟩ := (F.objectsPair_isBaseChange V m).2
  exact exists_lift_of_pairSquares G.source F.universalOpen (F.objectsPair V m) m j hj hsnd
    φ ψ hc hc'

/-! ### Membership in a subfunctor, read on morphisms out of representables -/

/-- A morphism out of a representable presheaf factors through a subfunctor exactly when the
section it names lies in that subfunctor. -/
theorem exists_lift_iff_mem {D : Type v} [Category.{u} D] {X : Dᵒᵖ ⥤ Type u}
    (Z : Subfunctor X) (V : D) (k : yoneda.obj V ⟶ X) :
    (∃ n : yoneda.obj V ⟶ Z.toFunctor, n ≫ Z.ι = k) ↔
      yonedaEquiv k ∈ Z.obj (Opposite.op V) := by
  constructor
  · rintro ⟨n, hn⟩
    exact mem_of_lift Z V (yonedaEquiv k) n ((Equiv.symm_apply_apply yonedaEquiv k).symm ▸ hn)
  · intro hk
    obtain ⟨n, hn⟩ := exists_lift_of_mem Z V (yonedaEquiv k) hk
    exact ⟨n, (Equiv.symm_apply_apply yonedaEquiv k) ▸ hn⟩

/-- Two subfunctors whose preimages along two morphisms out of a representable presheaf agree
have the same sections named by those two morphisms. -/
theorem mem_iff_mem_of_preimage_eq {D : Type v} [Category.{u} D] {X₁ X₂ : Dᵒᵖ ⥤ Type u}
    (Z₁ : Subfunctor X₁) (Z₂ : Subfunctor X₂) (V : D)
    (κ₁ : yoneda.obj V ⟶ X₁) (κ₂ : yoneda.obj V ⟶ X₂)
    (h : Z₁.preimage κ₁ = Z₂.preimage κ₂) :
    yonedaEquiv κ₁ ∈ Z₁.obj (Opposite.op V) ↔ yonedaEquiv κ₂ ∈ Z₂.obj (Opposite.op V) := by
  have h' : (Z₁.preimage κ₁).obj (Opposite.op V) = (Z₂.preimage κ₂).obj (Opposite.op V) :=
    congrFun (congrArg Subfunctor.obj h) (Opposite.op V)
  simpa only [Subfunctor.preimage_obj, Set.mem_preimage, yonedaEquiv_apply] using
    Set.ext_iff.1 h' (𝟙 V)

/-- A section of a fibre product is the one determined by its two projections. -/
theorem eq_pullback_lift_fst_snd {D : Type v} [Category.{w} D] [HasPullbacks D]
    {W A A' A'' : D} {f : A ⟶ A''} {g : A' ⟶ A''} (k : W ⟶ pullback f g)
    (hc : (k ≫ pullback.fst f g) ≫ f = (k ≫ pullback.snd f g) ≫ g) :
    k = pullback.lift (k ≫ pullback.fst f g) (k ≫ pullback.snd f g) hc :=
  pullback.hom_ext (pullback.lift_fst _ _ _).symm (pullback.lift_snd _ _ _).symm

/-- A subfunctor is the preimage of another one along a morphism as soon as, at every scheme of
the site, the morphisms out of the represented presheaf factoring through the first are exactly
those whose composition with the morphism factors through the second. -/
theorem subfunctor_eq_preimage_of_exists_lift_iff
    {X₁ X₂ : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (Z₁ : Subfunctor X₁) (Z₂ : Subfunctor X₂) (κ : X₁ ⟶ X₂)
    (h : ∀ (V : BigFppfOver C S hS) (k : yoneda.obj V ⟶ X₁),
      (∃ n : yoneda.obj V ⟶ Z₁.toFunctor, n ≫ Z₁.ι = k) ↔
        ∃ n' : yoneda.obj V ⟶ Z₂.toFunctor, n' ≫ Z₂.ι = k ≫ κ) :
    Z₁ = Z₂.preimage κ := by
  refine Subfunctor.ext ?_
  funext V
  ext x
  rw [Subfunctor.preimage_obj, Set.mem_preimage]
  have hx : yonedaEquiv (yonedaEquiv.symm x : yoneda.obj V.unop ⟶ X₁) = x :=
    Equiv.apply_symm_apply _ _
  have hκ : yonedaEquiv ((yonedaEquiv.symm x : yoneda.obj V.unop ⟶ X₁) ≫ κ) =
      κ.app V x := by
    rw [yonedaEquiv_comp, hx]
  have e₁ : (∃ n : yoneda.obj V.unop ⟶ Z₁.toFunctor,
      n ≫ Z₁.ι = (yonedaEquiv.symm x : yoneda.obj V.unop ⟶ X₁)) ↔ x ∈ Z₁.obj V := by
    rw [exists_lift_iff_mem Z₁ V.unop _, hx]
  have e₂ : (∃ n : yoneda.obj V.unop ⟶ Z₂.toFunctor,
      n ≫ Z₂.ι = (yonedaEquiv.symm x : yoneda.obj V.unop ⟶ X₁) ≫ κ) ↔
      κ.app V x ∈ Z₂.obj V := by
    rw [exists_lift_iff_mem Z₂ V.unop _, hκ]
  exact e₁.symm.trans ((h V.unop _).trans e₂)

/-- Two pairs of Stacks 04PC over the same algebraic space with the same base and with open
subspaces identified by a morphism of the ambient fibre product over the identity are equal.
Restated from the private declaration `pair_eq_of_subspace_eq` of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/GroupoidAssembly.lean`, with
its proof transcribed. -/
theorem pair_eq_of_subspace_eq' {X Y U : AlgebraicSpaces C S hS} (f : X ⟶ Y)
    (q r : FiniteOpenSubspace C S hS f U) (hb : q.toBase = r.toBase)
    (κ : pullback q.toBase.hom f.hom ⟶ pullback r.toBase.hom f.hom)
    (hκ₁ : κ ≫ pullback.fst r.toBase.hom f.hom = pullback.fst q.toBase.hom f.hom)
    (hκ₂ : κ ≫ pullback.snd r.toBase.hom f.hom = pullback.snd q.toBase.hom f.hom)
    (hz : q.subspace = r.subspace.preimage κ) : q = r := by
  obtain ⟨aq, Zq, oq, fq⟩ := q
  obtain ⟨ar, Zr, orr, fr⟩ := r
  obtain rfl : aq = ar := hb
  have h₁ : κ ≫ pullback.fst aq.hom f.hom = pullback.fst aq.hom f.hom := hκ₁
  have h₂ : κ ≫ pullback.snd aq.hom f.hom = pullback.snd aq.hom f.hom := hκ₂
  have hid : κ = 𝟙 (pullback aq.hom f.hom) := by
    apply pullback.hom_ext
    · rw [h₁, Category.id_comp]
    · rw [h₂, Category.id_comp]
  have hz' : Zq = Zr.preimage κ := hz
  rw [hid, Subfunctor.preimage_id] at hz'
  subst hz'
  rfl

/-- Two pairs of Stacks 04PC over the same algebraic space with the same base are equal as soon
as the same morphisms out of representable presheaves factor through their open subspaces. -/
theorem pair_eq_of_exists_lift_iff {X Y U : AlgebraicSpaces C S hS} (f : X ⟶ Y)
    (q r : FiniteOpenSubspace C S hS f U) (hb : q.toBase = r.toBase)
    (hcond : pullback.fst q.toBase.hom f.hom ≫ r.toBase.hom =
      pullback.snd q.toBase.hom f.hom ≫ f.hom)
    (hz : ∀ (V : BigFppfOver C S hS) (k : yoneda.obj V ⟶ pullback q.toBase.hom f.hom),
      (∃ n : yoneda.obj V ⟶ q.subspace.toFunctor, n ≫ q.subspace.ι = k) ↔
        ∃ n' : yoneda.obj V ⟶ r.subspace.toFunctor,
          n' ≫ r.subspace.ι = k ≫ pullback.lift (pullback.fst q.toBase.hom f.hom)
            (pullback.snd q.toBase.hom f.hom) hcond) :
    q = r :=
  pair_eq_of_subspace_eq' f q r hb _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    (subfunctor_eq_preimage_of_exists_lift_iff q.subspace r.subspace _ hz)

/-! ### The predicate cutting out the open subspace which a point names -/

/-- **A predicate on arrows cuts out the open subspace which a section of the object space of
the finite part names** when membership in `Z_univ` over that section, tested on morphisms out
of representable presheaves, is equivalent to it.

For the point `u' = (u, Z_u)` of Situation 04RL the predicate is that the target of the arrow
be `u`; the content of the choice of `Z_u` is that this predicate cuts out `Z_u`. -/
def CutsOut (F : FinitePartUniversalOpen G)
    (P : ∀ V' : BigFppfOver C S hS, (yoneda.obj V' ⟶ G.arrows.obj) → Prop)
    {Y₀ : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (m : Y₀ ⟶ F.objects.obj) : Prop :=
  ∀ (V' : BigFppfOver C S hS) (μ : yoneda.obj V' ⟶ F.objects.obj)
    (ψ : yoneda.obj V' ⟶ G.arrows.obj) (φ : yoneda.obj V' ⟶ Y₀), μ = φ ≫ m →
    ∀ hc : μ ≫ F.universalOpen.toBase.hom = ψ ≫ G.source.hom,
      ((∃ n : yoneda.obj V' ⟶ F.universalOpen.subspace.toFunctor,
          n ≫ F.universalOpen.subspace.ι = pullback.lift μ ψ hc) ↔ P V' ψ)

/-- **An arrow of `R` satisfying the cutting predicate lifts to `Z_univ`**, with a prescribed
section of the object space as its source and the given arrow as its underlying arrow.  This is
the section of `Z_univ` which the third step of the proof of Stacks 03FM exhibits. -/
theorem exists_arrows_of_cutsOut (F : FinitePartUniversalOpen G)
    {P : ∀ V' : BigFppfOver C S hS, (yoneda.obj V' ⟶ G.arrows.obj) → Prop}
    {Y₀ : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} {m : Y₀ ⟶ F.objects.obj}
    (hm : F.CutsOut P m) (V' : BigFppfOver C S hS)
    (μ : yoneda.obj V' ⟶ F.objects.obj) (ψ : yoneda.obj V' ⟶ G.arrows.obj)
    (φ : yoneda.obj V' ⟶ Y₀) (hμ : μ = φ ≫ m)
    (hs : ψ ≫ G.source.hom = μ ≫ F.universalOpen.toBase.hom) (hP : P V' ψ) :
    ∃ a : yoneda.obj V' ⟶ F.arrows.obj,
      a ≫ F.source.hom = μ ∧ a ≫ F.arrowMap.hom = ψ := by
  obtain ⟨n, hn⟩ := (hm V' μ ψ φ hμ hs.symm).2 hP
  exact ⟨n, by
      rw [← pullback.lift_fst μ ψ hs.symm, ← hn, Category.assoc]
      first
        | (unfold FinitePartUniversalOpen.source; rfl),
    by
      rw [← pullback.lift_snd μ ψ hs.symm, ← hn, Category.assoc]
      first
        | (unfold FinitePartUniversalOpen.arrowMap; rfl)⟩

/-! ### The target of a lift -/

/-- The pair of Stacks 04PC which the target morphism of the finite part names at a section of
`Z_univ` over a scheme of the site: on points it is the twist `(t ∘ z, c(Z, i ∘ z))` of the
pair at the source of that section. -/
def targetPairAt (F : FinitePartUniversalOpen G) (V : BigFppfOver C S hS)
    (a : yoneda.obj V ⟶ F.arrows.obj) :
    FiniteOpenSubspace C S hS G.source (AlgebraicGeometry.schemeSpace V) :=
  (finiteOpenSubspacePresheaf C S hS G.source).sections V
    (F.targetClassify.app (Opposite.op V) (yonedaEquiv a))

/-- The pair which the target morphism names at a section of `Z_univ` is the base change of
the twisted pair along that section, by the universal property of Stacks 04PE (2) applied to
the classifying morphism of the twisted pair. -/
theorem targetPairAt_isBaseChange (F : FinitePartUniversalOpen G)
    (V : BigFppfOver C S hS) (a : yoneda.obj V ⟶ F.arrows.obj) :
    (F.targetPairAt V a).toBase.hom = a ≫ F.targetPair.toBase.hom ∧
      ∃ j : (F.targetPairAt V a).subspace.toFunctor ⟶ F.targetPair.subspace.toFunctor,
        IsPullback ((F.targetPairAt V a).subspace.ι ≫
            pullback.fst (F.targetPairAt V a).toBase.hom G.source.hom) j a
          (F.targetPair.subspace.ι ≫
            pullback.fst F.targetPair.toBase.hom G.source.hom) ∧
        j ≫ F.targetPair.subspace.ι ≫
            pullback.snd F.targetPair.toBase.hom G.source.hom =
          (F.targetPairAt V a).subspace.ι ≫
            pullback.snd (F.targetPairAt V a).toBase.hom G.source.hom := by
  have spec := (finiteOpenSubspaceEquiv C S hS G.source F.arrows).2 F.targetClassify V a
  rwa [show (finiteOpenSubspaceEquiv C S hS G.source F.arrows).1 F.targetClassify =
    F.targetPair from Equiv.apply_symm_apply _ _] at spec

/-- **The target of a lift to `Z_univ` is the prescribed target section.**  Let `P` be a
predicate on arrows depending only on their target, cutting out the open subspaces which two
sections `x₁`, `x₂` of the object space of the finite part name, and let `a` be a section of
`Z_univ` whose source is `x₁` and whose arrow has target the image of `x₂`.  Then the target
of `a` is `x₂`.

On points: the pair at the target of `a` is the twist `c(Z_{x₁}, i ∘ z)` of the pair at its
source by its arrow, and since membership in `Z_{x₁}` and in `Z_{x₂}` are the same condition
on the target of the arrow, while composing with `z` does not change that target, the twist is
`Z_{x₂}`.

This is the step of the third part of the proof of Stacks 03FM which says that the
`Spec k`-valued point of `Z_univ` exhibited there has image `u'` under `t'` as well as under
`s'`. -/
theorem target_eq_of_cutsOut (F : FinitePartUniversalOpen G)
    (P : ∀ V' : BigFppfOver C S hS, (yoneda.obj V' ⟶ G.arrows.obj) → Prop)
    (hinv : ∀ (V' : BigFppfOver C S hS) (ψ₁ ψ₂ : yoneda.obj V' ⟶ G.arrows.obj),
      ψ₁ ≫ G.target.hom = ψ₂ ≫ G.target.hom → (P V' ψ₁ ↔ P V' ψ₂))
    (V : BigFppfOver C S hS) (m₁ m₂ : yoneda.obj V ⟶ F.objects.obj)
    (hm₁ : F.CutsOut P m₁) (hm₂ : F.CutsOut P m₂) (a : yoneda.obj V ⟶ F.arrows.obj)
    (hsrc : a ≫ F.source.hom = m₁)
    (htgt : (a ≫ F.arrowMap.hom) ≫ G.target.hom = m₂ ≫ F.universalOpen.toBase.hom) :
    a ≫ F.target.hom = m₂ := by
  have hbase : (F.targetPairAt V a).toBase.hom = (F.objectsPair V m₂).toBase.hom := by
    rw [(F.targetPairAt_isBaseChange V a).1, F.targetPair_toBase_hom, ← Category.assoc, htgt,
      (F.objectsPair_isBaseChange V m₂).1]
  have hb : (F.targetPairAt V a).toBase = (F.objectsPair V m₂).toBase :=
    ObjectProperty.hom_ext _ hbase
  have hcond : pullback.fst (F.targetPairAt V a).toBase.hom G.source.hom ≫
      (F.objectsPair V m₂).toBase.hom =
      pullback.snd (F.targetPairAt V a).toBase.hom G.source.hom ≫ G.source.hom :=
    by rw [← hbase]; exact pullback.condition
  have key : ∀ (V' : BigFppfOver C S hS) (φ₀ : yoneda.obj V' ⟶ yoneda.obj V)
      (ψ₀ : yoneda.obj V' ⟶ G.arrows.obj)
      (hc₀ : φ₀ ≫ (F.targetPairAt V a).toBase.hom = ψ₀ ≫ G.source.hom)
      (hcR : φ₀ ≫ (F.objectsPair V m₂).toBase.hom = ψ₀ ≫ G.source.hom),
      (∃ n : yoneda.obj V' ⟶ (F.targetPairAt V a).subspace.toFunctor,
          n ≫ (F.targetPairAt V a).subspace.ι = pullback.lift φ₀ ψ₀ hc₀) ↔
        ∃ n' : yoneda.obj V' ⟶ (F.objectsPair V m₂).subspace.toFunctor,
          n' ≫ (F.objectsPair V m₂).subspace.ι = pullback.lift φ₀ ψ₀ hcR := by
    intro V' φ₀ ψ₀ hc₀ hcR
    have hcA : (φ₀ ≫ a) ≫ F.targetPair.toBase.hom = ψ₀ ≫ G.source.hom := by
      rw [Category.assoc, ← (F.targetPairAt_isBaseChange V a).1]; exact hc₀
    have hcψ : (φ₀ ≫ m₂) ≫ F.universalOpen.toBase.hom = ψ₀ ≫ G.source.hom := by
      rw [Category.assoc, ← (F.objectsPair_isBaseChange V m₂).1]; exact hcR
    obtain ⟨j, hj, hjsnd⟩ := (F.targetPairAt_isBaseChange V a).2
    have stepA := exists_lift_of_pairSquares G.source F.targetPair (F.targetPairAt V a) a j hj
      hjsnd φ₀ ψ₀ hc₀ hcA
    have hcU := F.targetPair_ambient_cond (φ₀ ≫ a) ψ₀ hcA
    have hUU := F.untwist_base_condition (φ₀ ≫ a) ψ₀ hcU
    have hs' : (φ₀ ≫ a) ≫ F.source.hom = φ₀ ≫ m₁ := by rw [Category.assoc, hsrc]
    have hUU' : (φ₀ ≫ m₁) ≫ F.universalOpen.toBase.hom =
        composeMor G ψ₀ ((φ₀ ≫ a) ≫ F.arrowMap.hom) hcU ≫ G.source.hom :=
      (congrArg (fun z => z ≫ F.universalOpen.toBase.hom) hs'.symm).trans hUU
    have hlift : pullback.lift ((φ₀ ≫ a) ≫ F.source.hom)
          (composeMor G ψ₀ ((φ₀ ≫ a) ≫ F.arrowMap.hom) hcU) hUU =
        pullback.lift (φ₀ ≫ m₁)
          (composeMor G ψ₀ ((φ₀ ≫ a) ≫ F.arrowMap.hom) hcU) hUU' :=
      pullback_lift_congr _ _ _ _ hUU hUU' hs' rfl
    have stepBC : (∃ n' : yoneda.obj V' ⟶ F.targetPair.subspace.toFunctor,
          n' ≫ F.targetPair.subspace.ι = pullback.lift (φ₀ ≫ a) ψ₀ hcA) ↔
        ∃ n'' : yoneda.obj V' ⟶ F.universalOpen.subspace.toFunctor,
          n'' ≫ F.universalOpen.subspace.ι = pullback.lift (φ₀ ≫ m₁)
            (composeMor G ψ₀ ((φ₀ ≫ a) ≫ F.arrowMap.hom) hcU) hUU' := by
      rw [← hlift]
      exact (exists_lift_iff_mem _ V' _).trans
        ((mem_iff_mem_of_preimage_eq F.targetPair.subspace F.universalOpen.subspace V' _ _
          (F.targetPair_preimage_untwist (φ₀ ≫ a) ψ₀ hcA hcU hUU)).trans
          (exists_lift_iff_mem _ V' _).symm)
    exact stepA.trans (stepBC.trans
      ((hm₁ V' (φ₀ ≫ m₁) (composeMor G ψ₀ ((φ₀ ≫ a) ≫ F.arrowMap.hom) hcU) φ₀ rfl
          hUU').trans
        ((hinv V' (composeMor G ψ₀ ((φ₀ ≫ a) ≫ F.arrowMap.hom) hcU) ψ₀
            (composeMor_comp_target G _ _ hcU)).trans
          ((hm₂ V' (φ₀ ≫ m₂) ψ₀ φ₀ rfl hcψ).symm.trans
            (F.exists_lift_universalOpen_iff V m₂ φ₀ ψ₀ hcR hcψ).symm))))
  have hpair : F.targetPairAt V a = F.objectsPair V m₂ := by
    refine pair_eq_of_exists_lift_iff G.source _ _ hb hcond ?_
    intro V' k
    have hc₀ : (k ≫ pullback.fst (F.targetPairAt V a).toBase.hom G.source.hom) ≫
        (F.targetPairAt V a).toBase.hom =
        (k ≫ pullback.snd (F.targetPairAt V a).toBase.hom G.source.hom) ≫ G.source.hom := by
      rw [Category.assoc, pullback.condition, Category.assoc]
    have hcR : (k ≫ pullback.fst (F.targetPairAt V a).toBase.hom G.source.hom) ≫
        (F.objectsPair V m₂).toBase.hom =
        (k ≫ pullback.snd (F.targetPairAt V a).toBase.hom G.source.hom) ≫ G.source.hom := by
      rw [← hbase]; exact hc₀
    have hk : k = pullback.lift
        (k ≫ pullback.fst (F.targetPairAt V a).toBase.hom G.source.hom)
        (k ≫ pullback.snd (F.targetPairAt V a).toBase.hom G.source.hom) hc₀ :=
      eq_pullback_lift_fst_snd k hc₀
    have hkκ : k ≫ pullback.lift
          (pullback.fst (F.targetPairAt V a).toBase.hom G.source.hom)
          (pullback.snd (F.targetPairAt V a).toBase.hom G.source.hom) hcond =
        pullback.lift (k ≫ pullback.fst (F.targetPairAt V a).toBase.hom G.source.hom)
          (k ≫ pullback.snd (F.targetPairAt V a).toBase.hom G.source.hom) hcR :=
      pullback.hom_ext (by erw [Category.assoc, pullback.lift_fst, pullback.lift_fst])
        (by erw [Category.assoc, pullback.lift_snd, pullback.lift_snd])
    refine Iff.trans (iff_of_eq (congrArg
      (fun z => ∃ n : yoneda.obj V' ⟶ (F.targetPairAt V a).subspace.toFunctor,
        n ≫ (F.targetPairAt V a).subspace.ι = z) hk))
      (Iff.trans (key V' _ _ hc₀ hcR) (iff_of_eq (congrArg
        (fun z => ∃ n' : yoneda.obj V' ⟶ (F.objectsPair V m₂).subspace.toFunctor,
          n' ≫ (F.objectsPair V m₂).subspace.ι = z) hkκ.symm)))
  refine F.objects_hom_ext _ _ ?_
  rw [Category.assoc, F.target_comp_objectsInclusion]
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_comp]
  exact Equiv.injective ((finiteOpenSubspacePresheaf C S hS G.source).sections V) hpair

/-! ### The arrow containment, on sections -/

/-- **The arrow containment of Stacks 03FM, stated on sections.**  Let `P` be a predicate on
arrows depending only on their target and cutting out the open subspaces which two sections
`x₁`, `x₂` of the object space of the finite part name.  Then every section of the arrow space
of the restriction `R|_{U'}` whose source lift is `x₁`, whose target lift is `x₂`, and whose
underlying arrow satisfies `P`, comes from a section of `Z_univ` along
`(f, t', s') : Z_univ ⟶ R'`.

This is the third step of the proof of Stacks 03FM: the triple
`(s ∘ z, Z_u ×_{Spec κ(u), s ∘ z} Spec k, z)` of that proof is the section `a` produced
here. -/
theorem exists_toRestriction_eq (F : FinitePartUniversalOpen G)
    (P : ∀ V' : BigFppfOver C S hS, (yoneda.obj V' ⟶ G.arrows.obj) → Prop)
    (hinv : ∀ (V' : BigFppfOver C S hS) (ψ₁ ψ₂ : yoneda.obj V' ⟶ G.arrows.obj),
      ψ₁ ≫ G.target.hom = ψ₂ ≫ G.target.hom → (P V' ψ₁ ↔ P V' ψ₂))
    (V : BigFppfOver C S hS) (m₁ m₂ : yoneda.obj V ⟶ F.objects.obj)
    (hm₁ : F.CutsOut P m₁) (hm₂ : F.CutsOut P m₂)
    (w : yoneda.obj V ⟶
      (GroupoidInAlgebraicSpaces.restrictionArrows G F.objectProjection).obj)
    (hs : w ≫ (GroupoidInAlgebraicSpaces.restrictionSource G F.objectProjection).hom = m₁)
    (ht : w ≫ (GroupoidInAlgebraicSpaces.restrictionTarget G F.objectProjection).hom = m₂)
    (hP : P V (w ≫
      (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows G F.objectProjection).hom)) :
    ∃ b : yoneda.obj V ⟶ F.arrows.obj, b ≫ F.toRestriction.hom = w := by
  have hg : F.objectProjection.hom = F.universalOpen.toBase.hom :=
    F.universalOpen_toBase_hom.symm
  have hrs : (GroupoidInAlgebraicSpaces.restrictionSource G F.objectProjection).hom ≫
      F.objectProjection.hom =
      (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows G F.objectProjection).hom ≫
        G.source.hom :=
    congrArg
      (fun z : GroupoidInAlgebraicSpaces.restrictionArrows G F.objectProjection ⟶
        G.objects => z.hom)
      (GroupoidInAlgebraicSpaces.restriction_condition G F.objectProjection)
  have hrt : (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows G F.objectProjection).hom ≫
      G.target.hom =
      (GroupoidInAlgebraicSpaces.restrictionTarget G F.objectProjection).hom ≫
        F.objectProjection.hom :=
    congrArg
      (fun z : GroupoidInAlgebraicSpaces.restrictionArrows G F.objectProjection ⟶
        G.objects => z.hom)
      (GroupoidInAlgebraicSpaces.restriction_condition' G F.objectProjection)
  have hψs : (w ≫ (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows G
        F.objectProjection).hom) ≫ G.source.hom = m₁ ≫ F.universalOpen.toBase.hom := by
    rw [Category.assoc, ← hrs, ← Category.assoc, hs, hg]
  have hψt : (w ≫ (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows G
        F.objectProjection).hom) ≫ G.target.hom = m₂ ≫ F.universalOpen.toBase.hom := by
    rw [Category.assoc, hrt, ← Category.assoc, ht, hg]
  obtain ⟨a, hasrc, haarr⟩ := F.exists_arrows_of_cutsOut hm₁ V m₁
    (w ≫ (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows G F.objectProjection).hom)
    (𝟙 (yoneda.obj V)) (Category.id_comp m₁).symm hψs hP
  have hatgt : a ≫ F.target.hom = m₂ :=
    F.target_eq_of_cutsOut P hinv V m₁ m₂ hm₁ hm₂ a hasrc
      ((congrArg (fun z => z ≫ G.target.hom) haarr).trans hψt)
  have key : ∀ {Y : AlgebraicSpaces C S hS}
      (X : GroupoidInAlgebraicSpaces.restrictionArrows G F.objectProjection ⟶ Y)
      (Z : F.arrows ⟶ Y), F.toRestriction ≫ X = Z → a ≫ Z.hom = w ≫ X.hom →
      X.hom.app (Opposite.op V) (yonedaEquiv (a ≫ F.toRestriction.hom)) =
        X.hom.app (Opposite.op V) (yonedaEquiv w) := by
    intro Y X Z hZ e
    rw [← yonedaEquiv_comp, ← yonedaEquiv_comp, Category.assoc, ← e]
    exact congrArg (fun k : F.arrows ⟶ Y => yonedaEquiv (a ≫ k.hom)) hZ
  refine ⟨a, yonedaEquiv.injective ?_⟩
  refine restrictionArrows_ext F.objectProjection (Opposite.op V) _ _ ?_ ?_ ?_
  · exact key _ _ F.toRestriction_comp_restrictionSource (hasrc.trans hs.symm)
  · exact key _ _ F.toRestriction_comp_arrowsToArrows haarr
  · exact key _ _ F.toRestriction_comp_restrictionTarget (hatgt.trans ht.symm)

end FinitePartUniversalOpen

end Generic

end AlgebraicGeometry.Space

end
