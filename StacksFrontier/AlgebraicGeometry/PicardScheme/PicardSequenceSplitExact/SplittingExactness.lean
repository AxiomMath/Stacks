module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceSplitExact.DescentGluing

/-!
# The splitting of the Picard sequence and exactness in the middle

For a morphism `f : X ⟶ S` of a big fppf site with a section `σ`: the induced section of a base
change, the splitting of `Pic(T) ⟶ Pic(X_T)` by `σ_T^*`, the vanishing of the composite
`Pic(T) ⟶ Pic(X_T) ⟶ Pic_{X/S}(T)`, separatedness of the kernel of `σ_T^*`, and exactness of
the sequence at `Pic(X_T)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open CategoryTheory.Pseudofunctor CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v w z u' v'

namespace Stacks.PicardFunctor

variable (B : BigFppfSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : B.obj hX ⟶ B.obj hS) (σ : S ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 S)

/-! ### The induced section of a base change -/

/-- The induced section of the base change to `T`, followed by the first projection, is the
composite of the structure morphism of `T` with `σ`. -/
@[simp]
theorem baseChangeSection_comp_fst (T : BigFppfOver B S hS) :
    baseChangeSection B hX hS f σ hσ T ≫
        pullback.fst (B.inclusion.map f) (B.inclusion.map T.hom) =
      B.inclusion.map T.hom ≫ σ :=
  pullback.lift_fst _ _ _

/-- The induced sections are compatible with the transition maps of the base changes. -/
theorem baseChangeSection_comp_baseChangeMap {T U : BigFppfOver B S hS} (g : T ⟶ U) :
    baseChangeSection B hX hS f σ hσ T ≫ baseChangeMap B hX hS f g =
      B.inclusion.map g.left ≫ baseChangeSection B hX hS f σ hσ U := by
  have hg : B.inclusion.map g.left ≫ B.inclusion.map U.hom = B.inclusion.map T.hom := by
    rw [← Functor.map_comp, Over.w g]
  have hfst : baseChangeMap B hX hS f g ≫
      pullback.fst (B.inclusion.map f) (B.inclusion.map U.hom) =
        pullback.fst (B.inclusion.map f) (B.inclusion.map T.hom) := by
    simp only [baseChangeMap, pullback.map, pullback.lift_fst, Category.comp_id]
  have hsnd : baseChangeMap B hX hS f g ≫
      pullback.snd (B.inclusion.map f) (B.inclusion.map U.hom) =
        pullback.snd (B.inclusion.map f) (B.inclusion.map T.hom) ≫ B.inclusion.map g.left :=
    pullback.lift_snd _ _ _
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, hfst, baseChangeSection_comp_fst, Category.assoc,
      baseChangeSection_comp_fst, ← Category.assoc, hg]
  · rw [Category.assoc, hsnd, ← Category.assoc,
      baseChangeSection_comp_snd B hX hS f σ hσ T,
      Category.id_comp, Category.assoc,
      baseChangeSection_comp_snd B hX hS f σ hσ U]
    exact (Category.comp_id _).symm

/-! ### The splitting of the Picard sequence -/

/-- **Stacks Project, Tag 0B9N.** Pullback of Picard classes along the induced section
`σ_T : T ⟶ X_T` is a left inverse of pullback along the projection `X_T ⟶ T`: the sequence
`0 ⟶ Pic(T) ⟶ Pic(X_T) ⟶ Pic_{X/S}(T) ⟶ 0` is split by `σ_T^*`. -/
@[stacks 0B9N "the splitting"]
theorem schemePullbackClass_baseChangeSection_baseChangeProj (T : BigFppfOver B S hS) :
    Function.LeftInverse
      (Stacks.Picard.schemePullbackClass (baseChangeSection B hX hS f σ hσ T))
      (Stacks.Picard.schemePullbackClass (baseChangeProj B hX hS f T)) := fun x => by
  rw [Stacks.Picard.schemePullbackClass_comp,
    baseChangeSection_comp_snd B hX hS f σ hσ T,
    Stacks.Picard.schemePullbackClass_id]

include σ hσ in
/-- **Stacks Project, Tag 0B9N.** Pullback of Picard classes along the projection `X_T ⟶ T` is
injective, the induced section providing a left inverse; this is exactness at `Pic(T)` of
`0 ⟶ Pic(T) ⟶ Pic(X_T) ⟶ Pic_{X/S}(T) ⟶ 0`. -/
@[stacks 0B9N "injectivity"]
theorem injective_schemePullbackClass_baseChangeProj_of_section (T : BigFppfOver B S hS) :
    Function.Injective (Stacks.Picard.schemePullbackClass (baseChangeProj B hX hS f T)) :=
  (schemePullbackClass_baseChangeSection_baseChangeProj B hX hS f σ hσ T).injective

/-- Pullback of Picard classes along the projection commutes with restriction along a morphism
of test schemes. -/
theorem schemePullbackClass_baseChangeProj_natural {T U : BigFppfOver B S hS} (g : T ⟶ U)
    (x : Stacks.Picard.ofScheme ((BigFppfOver.toScheme B S hS).obj U)) :
    Stacks.Picard.schemePullbackClass (baseChangeMap B hX hS f g)
        (Stacks.Picard.schemePullbackClass (baseChangeProj B hX hS f U) x) =
      Stacks.Picard.schemePullbackClass (baseChangeProj B hX hS f T)
        (Stacks.Picard.schemePullbackClass ((BigFppfOver.toScheme B S hS).map g) x) := by
  rw [Stacks.Picard.schemePullbackClass_comp, Stacks.Picard.schemePullbackClass_comp]
  exact congrArg (fun k => Stacks.Picard.schemePullbackClass k x) (pullback.lift_snd _ _ _)

/-- Pullback of Picard classes along the induced section commutes with restriction along a
morphism of test schemes. -/
theorem schemePullbackClass_baseChangeSection_natural {T U : BigFppfOver B S hS} (g : T ⟶ U)
    (x : Stacks.Picard.ofScheme (baseChange B hX hS f U)) :
    Stacks.Picard.schemePullbackClass (baseChangeSection B hX hS f σ hσ T)
        (Stacks.Picard.schemePullbackClass (baseChangeMap B hX hS f g) x) =
      Stacks.Picard.schemePullbackClass ((BigFppfOver.toScheme B S hS).map g)
        (Stacks.Picard.schemePullbackClass (baseChangeSection B hX hS f σ hσ U) x) := by
  rw [Stacks.Picard.schemePullbackClass_comp, Stacks.Picard.schemePullbackClass_comp]
  exact congrArg (fun k => Stacks.Picard.schemePullbackClass k x)
    (baseChangeSection_comp_baseChangeMap B hX hS f σ hσ g)

/-! ### The image of `Pic(T)` lies in the kernel of the map to the Picard functor -/

/-- Two sections of an fppf sheaf on the `S`-schemes of the site that agree on the members of a
covering family of `T` agree at `T`. -/
private theorem eq_of_bigFppfOver_cover
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (T : BigFppfOver B S hS) (E : PreZeroHypercover T.left)
    (hE : B.IsCovering ⟨T.left, E⟩) {x y : F.obj (Opposite.op T)}
    (h : ∀ i, F.map (Opposite.op (Over.homMk (U := Over.mk (E.f i ≫ T.hom)) (V := T)
          (E.f i))) x =
      F.map (Opposite.op (Over.homMk (U := Over.mk (E.f i ≫ T.hom)) (V := T) (E.f i))) y) :
    x = y := by
  have hg : Sieve.ofArrows (fun i : E.I₀ => (Over.mk (E.f i ≫ T.hom) : BigFppfOver B S hS))
      (fun i => Over.homMk (E.f i)) ∈ BigFppfOver.topology B S hS T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact Precoverage.generate_mem_toGrothendieck ⟨E, rfl, hE⟩
  have heq : (TypeCat.ofHom (fun _ : PUnit.{u + 2} => x)) =
      TypeCat.ofHom (fun _ : PUnit.{u + 2} => y) := by
    apply hF.hom_ext_ofArrows
      (X := fun i : E.I₀ => (Over.mk (E.f i ≫ T.hom) : BigFppfOver B S hS))
      (fun i => Over.homMk (E.f i)) hg
    intro i
    ext z
    exact h i
  exact ConcreteCategory.congr_hom heq PUnit.unit

/-- **The composite `Pic(T) ⟶ Pic(X_T) ⟶ Pic_{X/S}(T)` is zero.** An invertible module on `T`
is trivial on a Zariski covering of `T`, which is tautologically equivalent to a covering family
of the site, and the Picard functor is an fppf sheaf; so a Picard class pulled back from `T`
dies in the Picard functor. -/
theorem toPicardFunctorHom_schemePullbackClass_baseChangeProj (T : BigFppfOver B S hS)
    (N : Stacks.Picard.ofScheme ((BigFppfOver.toScheme B S hS).obj T)) :
    toPicardFunctorHom B hX hS f T
      (Stacks.Picard.schemePullbackClass (baseChangeProj B hX hS f T) N) = 0 := by
  obtain ⟨𝒰, h𝒰⟩ := Stacks.Picard.exists_openCover_schemePullbackClass_eq_zero N
  obtain ⟨W, hW, hequiv⟩ :=
    AlgebraicGeometry.exists_isCovering_tautologicallyEquivalent_openCover B T.left 𝒰
  obtain ⟨β, hβ⟩ := hequiv.2
  have hzero : ∀ i : W.I₀,
      Stacks.Picard.schemePullbackClass ((PreZeroHypercover.map B.inclusion W).f i) N = 0 := by
    intro i
    obtain ⟨e, he⟩ := hβ i
    rw [← he, ← Stacks.Picard.schemePullbackClass_comp, h𝒰 (β i)]
    exact map_zero (Stacks.Picard.schemePullbackClassHom e.hom)
  have key : toPicardFunctorHom B hX hS f T
      (Stacks.Picard.schemePullbackClass (baseChangeProj B hX hS f T) N) =
      toPicardFunctorHom B hX hS f T 0 := by
    apply eq_of_bigFppfOver_cover B hS (isSheaf_picardFunctor B hX hS f) T W hW
    intro i
    have hstep : picardMap B hX hS f
        (Over.homMk (U := Over.mk (W.f i ≫ T.hom)) (V := T) (W.f i))
          (Stacks.Picard.schemePullbackClass (baseChangeProj B hX hS f T) N) =
        picardMap B hX hS f
          (Over.homMk (U := Over.mk (W.f i ≫ T.hom)) (V := T) (W.f i))
          (0 : picardAt B hX hS f T) := by
      refine (schemePullbackClass_baseChangeProj_natural B hX hS f _ N).trans ?_
      refine Eq.trans ?_ (map_zero (Stacks.Picard.schemePullbackClassHom
        (baseChangeMap B hX hS f
          (Over.homMk (U := Over.mk (W.f i ≫ T.hom)) (V := T) (W.f i))))).symm
      rw [show Stacks.Picard.schemePullbackClass ((BigFppfOver.toScheme B S hS).map
          (Over.homMk (U := Over.mk (W.f i ≫ T.hom)) (V := T) (W.f i))) N = 0 from hzero i]
      exact map_zero (Stacks.Picard.schemePullbackClassHom (baseChangeProj B hX hS f _))
    rw [toPicardFunctorHom_apply, toPicardFunctorHom_apply,
      ← toPicardFunctor_app_naturality, ← toPicardFunctor_app_naturality, hstep]
  rw [key]
  exact map_zero _

/-- The base change of a composite named by an equation. -/
private theorem baseChangeMap_comp_eq {T U W : BigFppfOver B S hS} (g : U ⟶ T) (b : W ⟶ U)
    (k : W ⟶ T) (hk : b ≫ g = k) :
    baseChangeMap B hX hS f b ≫ baseChangeMap B hX hS f g = baseChangeMap B hX hS f k := by
  rw [← baseChangeMap_comp, hk]

/-- The transition map of two test schemes followed by the induced section of the base and a
further transition map, with the composite named by an equation. -/
private theorem inclusion_comp_sectionComp {T U W : BigFppfOver B S hS} (g : U ⟶ T)
    (b : W ⟶ U) (k : W ⟶ T) (hk : b ≫ g = k) :
    B.inclusion.map b.left ≫ (baseChangeSection B hX hS f σ hσ U ≫
        baseChangeMap B hX hS f g) =
      baseChangeSection B hX hS f σ hσ W ≫ baseChangeMap B hX hS f k := by
  rw [← Category.assoc, ← baseChangeSection_comp_baseChangeMap B hX hS f σ hσ b,
    Category.assoc, baseChangeMap_comp_eq B hX hS f g b k hk]

open Pseudofunctor.LocallyDiscreteOpToCat in
/-- The restriction along a morphism of test schemes of a homomorphism between the pullbacks of
two modules on `X_T` along the induced section of `T`. -/
private noncomputable def sectionRestrict {T : BigFppfOver B S hS}
    {L' M' : (baseChange B hX hS f T).Modules}
    (β : (modulePullbackPseudofunctor.map
          (baseChangeSection B hX hS f σ hσ T).op.toLoc).toFunctor.obj L' ⟶
      (modulePullbackPseudofunctor.map
          (baseChangeSection B hX hS f σ hσ T).op.toLoc).toFunctor.obj M')
    {U : BigFppfOver B S hS} (g : U ⟶ T) :
    (modulePullbackPseudofunctor.map (baseChangeSection B hX hS f σ hσ U ≫
        baseChangeMap B hX hS f g).op.toLoc).toFunctor.obj L' ⟶
      (modulePullbackPseudofunctor.map (baseChangeSection B hX hS f σ hσ U ≫
        baseChangeMap B hX hS f g).op.toLoc).toFunctor.obj M' :=
  pullHom β (B.inclusion.map g.left) _ _
    (baseChangeSection_comp_baseChangeMap B hX hS f σ hσ g).symm
    (baseChangeSection_comp_baseChangeMap B hX hS f σ hσ g).symm

open Pseudofunctor.LocallyDiscreteOpToCat in
/-- Restricting the two directions of an isomorphism along the section of a test scheme gives
mutually inverse homomorphisms. -/
private theorem sectionRestrict_hom_comp_inv {T : BigFppfOver B S hS}
    {L' M' : (baseChange B hX hS f T).Modules}
    (β : (modulePullbackPseudofunctor.map
          (baseChangeSection B hX hS f σ hσ T).op.toLoc).toFunctor.obj L' ≅
      (modulePullbackPseudofunctor.map
          (baseChangeSection B hX hS f σ hσ T).op.toLoc).toFunctor.obj M')
    {U : BigFppfOver B S hS} (g : U ⟶ T) :
    sectionRestrict B hX hS f σ hσ β.hom g ≫ sectionRestrict B hX hS f σ hσ β.inv g = 𝟙 _ :=
  Stacks.Picard.pullHom_hom_comp_pullHom_inv β (B.inclusion.map g.left) _ _ _ _

open Pseudofunctor.LocallyDiscreteOpToCat in
private theorem sectionRestrict_inv_comp_hom {T : BigFppfOver B S hS}
    {L' M' : (baseChange B hX hS f T).Modules}
    (β : (modulePullbackPseudofunctor.map
          (baseChangeSection B hX hS f σ hσ T).op.toLoc).toFunctor.obj L' ≅
      (modulePullbackPseudofunctor.map
          (baseChangeSection B hX hS f σ hσ T).op.toLoc).toFunctor.obj M')
    {U : BigFppfOver B S hS} (g : U ⟶ T) :
    sectionRestrict B hX hS f σ hσ β.inv g ≫ sectionRestrict B hX hS f σ hσ β.hom g = 𝟙 _ :=
  Stacks.Picard.pullHom_inv_comp_pullHom_hom β (B.inclusion.map g.left) _ _ _ _

open Pseudofunctor.LocallyDiscreteOpToCat in
/-- **The normalised trivialisation on a member of a covering family.** A trivialisation of an
invertible module on `X_T` along the induced section of `T` singles out, among the isomorphisms
of its restriction to `X_U` with the restriction of the structure sheaf, the one restricting
along the induced section of `U` to the restriction of that trivialisation. -/
private theorem exists_pullHom_eq_sectionRestrict
    (hOiso : ∀ U : BigFppfOver B S hS,
      IsIso (baseChangeProj B hX hS f U).toLRSHom.toHom.c)
    {T : BigFppfOver B S hS} (L' M' : (baseChange B hX hS f T).Modules)
    (hL' : Stacks.SheafOfModules.IsInvertible (baseChange B hX hS f T).presheaf
      (baseChange B hX hS f T).ringCatSheaf.2 L')
    (hM' : Stacks.SheafOfModules.IsInvertible (baseChange B hX hS f T).presheaf
      (baseChange B hX hS f T).ringCatSheaf.2 M')
    (β : (modulePullbackPseudofunctor.map
          (baseChangeSection B hX hS f σ hσ T).op.toLoc).toFunctor.obj L' ≅
      (modulePullbackPseudofunctor.map
          (baseChangeSection B hX hS f σ hσ T).op.toLoc).toFunctor.obj M')
    {U : BigFppfOver B S hS} (g : U ⟶ T)
    (e : (modulePullbackPseudofunctor.map (baseChangeMap B hX hS f g).op.toLoc).toFunctor.obj
        L' ≅
      (modulePullbackPseudofunctor.map (baseChangeMap B hX hS f g).op.toLoc).toFunctor.obj M') :
    ∃ ψ : (modulePullbackPseudofunctor.map
          (baseChangeMap B hX hS f g).op.toLoc).toFunctor.obj L' ≅
        (modulePullbackPseudofunctor.map
          (baseChangeMap B hX hS f g).op.toLoc).toFunctor.obj M',
      pullHom ψ.hom (baseChangeSection B hX hS f σ hσ U) _ _ rfl rfl =
        sectionRestrict B hX hS f σ hσ β.hom g := by
  have hsec : baseChangeSection B hX hS f σ hσ U ≫ baseChangeProj B hX hS f U = 𝟙 _ :=
    baseChangeSection_comp_snd B hX hS f σ hσ U
  obtain ⟨a, ha⟩ := (Stacks.Picard.bijective_pullHom_section' (baseChangeMap B hX hS f g)
    (baseChangeMap B hX hS f g) (baseChangeProj B hX hS f U)
    (baseChangeSection B hX hS f σ hσ U) hsec (hOiso U) L' M' hL' hM' e _ _ rfl
    rfl).surjective (sectionRestrict B hX hS f σ hσ β.hom g)
  obtain ⟨b, hb⟩ := (Stacks.Picard.bijective_pullHom_section' (baseChangeMap B hX hS f g)
    (baseChangeMap B hX hS f g) (baseChangeProj B hX hS f U)
    (baseChangeSection B hX hS f σ hσ U) hsec (hOiso U) M' L' hM' hL' e.symm _ _ rfl
    rfl).surjective (sectionRestrict B hX hS f σ hσ β.inv g)
  have ha' : pullHom a (baseChangeSection B hX hS f σ hσ U)
      (baseChangeSection B hX hS f σ hσ U ≫ baseChangeMap B hX hS f g)
      (baseChangeSection B hX hS f σ hσ U ≫ baseChangeMap B hX hS f g) rfl rfl =
      sectionRestrict B hX hS f σ hσ β.hom g := ha
  have hb' : pullHom b (baseChangeSection B hX hS f σ hσ U)
      (baseChangeSection B hX hS f σ hσ U ≫ baseChangeMap B hX hS f g)
      (baseChangeSection B hX hS f σ hσ U ≫ baseChangeMap B hX hS f g) rfl rfl =
      sectionRestrict B hX hS f σ hσ β.inv g := hb
  have hLL := Stacks.Picard.bijective_pullHom_section' (baseChangeMap B hX hS f g)
    (baseChangeMap B hX hS f g) (baseChangeProj B hX hS f U)
    (baseChangeSection B hX hS f σ hσ U) hsec (hOiso U) L' L' hL' hL' (Iso.refl _) _ _ rfl rfl
  have hMM := Stacks.Picard.bijective_pullHom_section' (baseChangeMap B hX hS f g)
    (baseChangeMap B hX hS f g) (baseChangeProj B hX hS f U)
    (baseChangeSection B hX hS f σ hσ U) hsec (hOiso U) M' M' hM' hM' (Iso.refl _) _ _ rfl rfl
  refine ⟨⟨a, b, hLL.injective ?_, hMM.injective ?_⟩, ha'⟩
  · show pullHom (a ≫ b) _ _ _ rfl rfl = pullHom (𝟙 _) _ _ _ rfl rfl
    rw [Stacks.Picard.pullHom_comp' a b (baseChangeSection B hX hS f σ hσ U) _ _ _ rfl rfl rfl,
      ha', hb', sectionRestrict_hom_comp_inv]
    exact (Stacks.Picard.pullHom_id' (F := modulePullbackPseudofunctor) L'
      (baseChangeMap B hX hS f g)
      (baseChangeSection B hX hS f σ hσ U) _ rfl).symm
  · show pullHom (b ≫ a) _ _ _ rfl rfl = pullHom (𝟙 _) _ _ _ rfl rfl
    rw [Stacks.Picard.pullHom_comp' b a (baseChangeSection B hX hS f σ hσ U) _ _ _ rfl rfl rfl,
      ha', hb', sectionRestrict_inv_comp_hom]
    exact (Stacks.Picard.pullHom_id' (F := modulePullbackPseudofunctor) M'
      (baseChangeMap B hX hS f g)
      (baseChangeSection B hX hS f σ hσ U) _ rfl).symm

open Pseudofunctor.LocallyDiscreteOpToCat in
/-- Restricting a restriction along the section is the restriction along the composite. -/
private theorem pullHom_sectionRestrict {T : BigFppfOver B S hS}
    {L' M' : (baseChange B hX hS f T).Modules}
    (β : (modulePullbackPseudofunctor.map
          (baseChangeSection B hX hS f σ hσ T).op.toLoc).toFunctor.obj L' ⟶
      (modulePullbackPseudofunctor.map
          (baseChangeSection B hX hS f σ hσ T).op.toLoc).toFunctor.obj M')
    {U W : BigFppfOver B S hS} (g : U ⟶ T) (b : W ⟶ U) :
    pullHom (sectionRestrict B hX hS f σ hσ β g) (B.inclusion.map b.left) _ _
        (inclusion_comp_sectionComp B hX hS f σ hσ g b _ rfl)
        (inclusion_comp_sectionComp B hX hS f σ hσ g b _ rfl) =
      sectionRestrict B hX hS f σ hσ β (b ≫ g) := by
  have hg : B.inclusion.map b.left ≫ B.inclusion.map g.left =
      B.inclusion.map (b ≫ g).left := by
    rw [Over.comp_left, Functor.map_comp]
  exact Stacks.Picard.pullHom_pullHom_of_eq β (B.inclusion.map g.left) _ _ _ _
    (B.inclusion.map b.left) (B.inclusion.map (b ≫ g).left) hg _ _ _ _ _ _

open Pseudofunctor.LocallyDiscreteOpToCat in
/-- Restricting a restriction along the section, with the composite named by an equation. -/
private theorem pullHom_sectionRestrict' {T : BigFppfOver B S hS}
    {L' M' : (baseChange B hX hS f T).Modules}
    (β : (modulePullbackPseudofunctor.map
          (baseChangeSection B hX hS f σ hσ T).op.toLoc).toFunctor.obj L' ⟶
      (modulePullbackPseudofunctor.map
          (baseChangeSection B hX hS f σ hσ T).op.toLoc).toFunctor.obj M')
    {U W : BigFppfOver B S hS} (g : U ⟶ T) (b : W ⟶ U) (k : W ⟶ T) (hk : b ≫ g = k) :
    pullHom (sectionRestrict B hX hS f σ hσ β g) (B.inclusion.map b.left) _ _
        (inclusion_comp_sectionComp B hX hS f σ hσ g b k hk)
        (inclusion_comp_sectionComp B hX hS f σ hσ g b k hk) =
      sectionRestrict B hX hS f σ hσ β k := by
  subst hk
  exact pullHom_sectionRestrict B hX hS f σ hσ β g b

open Pseudofunctor.LocallyDiscreteOpToCat in
/-- The restriction along the section of `W` of a normalised homomorphism, further restricted
along a morphism `W ⟶ U`, is the restriction of the trivialisation downstairs along the
composite `W ⟶ T`. This is what makes the normalised homomorphisms agree on overlaps. -/
private theorem pullHom_section_pullHom_baseChangeMap {T : BigFppfOver B S hS}
    {L' M' : (baseChange B hX hS f T).Modules}
    (β : (modulePullbackPseudofunctor.map
          (baseChangeSection B hX hS f σ hσ T).op.toLoc).toFunctor.obj L' ⟶
      (modulePullbackPseudofunctor.map
          (baseChangeSection B hX hS f σ hσ T).op.toLoc).toFunctor.obj M')
    {U W : BigFppfOver B S hS} (g : U ⟶ T) (b : W ⟶ U) (k : W ⟶ T) (hk : b ≫ g = k)
    (φ : (modulePullbackPseudofunctor.map
          (baseChangeMap B hX hS f g).op.toLoc).toFunctor.obj L' ⟶
      (modulePullbackPseudofunctor.map
          (baseChangeMap B hX hS f g).op.toLoc).toFunctor.obj M')
    (h : pullHom φ (baseChangeSection B hX hS f σ hσ U) _ _ rfl rfl =
      sectionRestrict B hX hS f σ hσ β g) :
    pullHom (pullHom φ (baseChangeMap B hX hS f b) (baseChangeMap B hX hS f k)
          (baseChangeMap B hX hS f k) (baseChangeMap_comp_eq B hX hS f g b k hk)
          (baseChangeMap_comp_eq B hX hS f g b k hk))
        (baseChangeSection B hX hS f σ hσ W) _ _ rfl rfl =
      sectionRestrict B hX hS f σ hσ β k := by
  have hsw : baseChangeSection B hX hS f σ hσ W ≫ baseChangeMap B hX hS f b =
      B.inclusion.map b.left ≫ baseChangeSection B hX hS f σ hσ U :=
    baseChangeSection_comp_baseChangeMap B hX hS f σ hσ b
  have p2 : B.inclusion.map b.left ≫ (baseChangeSection B hX hS f σ hσ U ≫
      baseChangeMap B hX hS f g) =
      baseChangeSection B hX hS f σ hσ W ≫ baseChangeMap B hX hS f k :=
    inclusion_comp_sectionComp B hX hS f σ hσ g b k hk
  have p1 : (B.inclusion.map b.left ≫ baseChangeSection B hX hS f σ hσ U) ≫
      baseChangeMap B hX hS f g =
      baseChangeSection B hX hS f σ hσ W ≫ baseChangeMap B hX hS f k := by
    rw [Category.assoc]; exact p2
  calc pullHom (pullHom φ (baseChangeMap B hX hS f b) (baseChangeMap B hX hS f k)
          (baseChangeMap B hX hS f k) (baseChangeMap_comp_eq B hX hS f g b k hk)
          (baseChangeMap_comp_eq B hX hS f g b k hk))
        (baseChangeSection B hX hS f σ hσ W) _ _ rfl rfl
      = pullHom φ (B.inclusion.map b.left ≫ baseChangeSection B hX hS f σ hσ U) _ _ p1 p1 :=
        Stacks.Picard.pullHom_pullHom_of_eq φ (baseChangeMap B hX hS f b) _ _
          (baseChangeMap_comp_eq B hX hS f g b k hk)
          (baseChangeMap_comp_eq B hX hS f g b k hk)
          (baseChangeSection B hX hS f σ hσ W) _ hsw _ _ rfl rfl p1 p1
    _ = pullHom (pullHom φ (baseChangeSection B hX hS f σ hσ U) _ _ rfl rfl)
          (B.inclusion.map b.left) _ _ p2 p2 :=
        (Stacks.Picard.pullHom_pullHom_of_eq φ (baseChangeSection B hX hS f σ hσ U) _ _ rfl rfl
          (B.inclusion.map b.left) _ rfl _ _ p2 p2 p1 p1).symm
    _ = pullHom (sectionRestrict B hX hS f σ hσ β g) (B.inclusion.map b.left) _ _ p2 p2 := by
        rw [h]
    _ = sectionRestrict B hX hS f σ hσ β k :=
        pullHom_sectionRestrict' B hX hS f σ hσ β g b k hk

open Pseudofunctor.LocallyDiscreteOpToCat in
/-- **Normalised trivialisations agree after any further pullback.** A family of homomorphisms
between the pullbacks of two invertible modules on `X_T` along the base changes of a family of
test schemes, each restricting along the induced section to the restriction of one homomorphism
downstairs, agrees after pullback along any pair of morphisms into two members with the same
composite to `X_T`. The comparison is made on the base change of a fibre product of the two
members, where the induced section is available. -/
private theorem pullHom_eq_of_pullHom_section_eq
    (hOiso : ∀ U : BigFppfOver B S hS,
      IsIso (baseChangeProj B hX hS f U).toLRSHom.toHom.c)
    {T : BigFppfOver B S hS} (L' M' : (baseChange B hX hS f T).Modules)
    (hL' : Stacks.SheafOfModules.IsInvertible (baseChange B hX hS f T).presheaf
      (baseChange B hX hS f T).ringCatSheaf.2 L')
    (hM' : Stacks.SheafOfModules.IsInvertible (baseChange B hX hS f T).presheaf
      (baseChange B hX hS f T).ringCatSheaf.2 M')
    (β : (modulePullbackPseudofunctor.map
          (baseChangeSection B hX hS f σ hσ T).op.toLoc).toFunctor.obj L' ⟶
      (modulePullbackPseudofunctor.map
          (baseChangeSection B hX hS f σ hσ T).op.toLoc).toFunctor.obj M')
    {ι : Type*} {U : ι → BigFppfOver B S hS} (g : ∀ i, U i ⟶ T)
    (ψ : ∀ i, (modulePullbackPseudofunctor.map
          (baseChangeMap B hX hS f (g i)).op.toLoc).toFunctor.obj L' ⟶
      (modulePullbackPseudofunctor.map
          (baseChangeMap B hX hS f (g i)).op.toLoc).toFunctor.obj M')
    (hψ : ∀ i, pullHom (ψ i) (baseChangeSection B hX hS f σ hσ (U i)) _ _ rfl rfl =
      sectionRestrict B hX hS f σ hσ β (g i))
    (etriv : ∀ (V : BigFppfOver B S hS) (i : ι) (b : V ⟶ U i) (k : V ⟶ T), b ≫ g i = k →
      Nonempty ((modulePullbackPseudofunctor.map
            (baseChangeMap B hX hS f k).op.toLoc).toFunctor.obj L' ≅
        (modulePullbackPseudofunctor.map
            (baseChangeMap B hX hS f k).op.toLoc).toFunctor.obj M'))
    ⦃Y : Scheme.{u}⦄ (q : Y ⟶ baseChange B hX hS f T) ⦃i₁ i₂ : ι⦄
    (a₁ : Y ⟶ baseChange B hX hS f (U i₁)) (a₂ : Y ⟶ baseChange B hX hS f (U i₂))
    (ha₁ : a₁ ≫ baseChangeMap B hX hS f (g i₁) = q)
    (ha₂ : a₂ ≫ baseChangeMap B hX hS f (g i₂) = q) :
    pullHom (ψ i₁) a₁ q q ha₁ ha₁ = pullHom (ψ i₂) a₂ q q ha₂ ha₂ := by
  obtain ⟨W, b₁, b₂, hb, hpb⟩ := exists_isPullback_bigFppfOver B hS (g i₁) (g i₂)
  obtain ⟨eW⟩ := etriv W i₁ b₁ (b₁ ≫ g i₁) rfl
  have hpbbc := baseChangeMap_isPullback B hX hS f b₁ b₂ (g i₁) (g i₂) hpb hb
  have hsecW : baseChangeSection B hX hS f σ hσ W ≫ baseChangeProj B hX hS f W = 𝟙 _ :=
    baseChangeSection_comp_snd B hX hS f σ hσ W
  have hkey : pullHom (ψ i₁) (baseChangeMap B hX hS f b₁)
        (baseChangeMap B hX hS f (b₁ ≫ g i₁)) (baseChangeMap B hX hS f (b₁ ≫ g i₁))
        (baseChangeMap_comp_eq B hX hS f (g i₁) b₁ _ rfl)
        (baseChangeMap_comp_eq B hX hS f (g i₁) b₁ _ rfl) =
      pullHom (ψ i₂) (baseChangeMap B hX hS f b₂)
        (baseChangeMap B hX hS f (b₁ ≫ g i₁)) (baseChangeMap B hX hS f (b₁ ≫ g i₁))
        (baseChangeMap_comp_eq B hX hS f (g i₂) b₂ _ hb.symm)
        (baseChangeMap_comp_eq B hX hS f (g i₂) b₂ _ hb.symm) := by
    refine (Stacks.Picard.bijective_pullHom_section'
      (baseChangeMap B hX hS f (b₁ ≫ g i₁)) (baseChangeMap B hX hS f (b₁ ≫ g i₁))
      (baseChangeProj B hX hS f W) (baseChangeSection B hX hS f σ hσ W) hsecW (hOiso W)
      L' M' hL' hM' eW _ _ rfl rfl).injective ?_
    show pullHom _ (baseChangeSection B hX hS f σ hσ W) _ _ rfl rfl =
      pullHom _ (baseChangeSection B hX hS f σ hσ W) _ _ rfl rfl
    rw [pullHom_section_pullHom_baseChangeMap B hX hS f σ hσ β (g i₁) b₁ _ rfl (ψ i₁) (hψ i₁),
      pullHom_section_pullHom_baseChangeMap B hX hS f σ hσ β (g i₂) b₂ _ hb.symm (ψ i₂)
        (hψ i₂)]
  have hl₁ : hpbbc.lift a₁ a₂ (by rw [ha₁, ha₂]) ≫ baseChangeMap B hX hS f b₁ = a₁ :=
    hpbbc.lift_fst _ _ _
  have hl₂ : hpbbc.lift a₁ a₂ (by rw [ha₁, ha₂]) ≫ baseChangeMap B hX hS f b₂ = a₂ :=
    hpbbc.lift_snd _ _ _
  have hq : hpbbc.lift a₁ a₂ (by rw [ha₁, ha₂]) ≫
      baseChangeMap B hX hS f (b₁ ≫ g i₁) = q := by
    rw [← baseChangeMap_comp_eq B hX hS f (g i₁) b₁ _ rfl, ← Category.assoc, hl₁, ha₁]
  rw [← Stacks.Picard.pullHom_pullHom_of_eq (ψ i₁) (baseChangeMap B hX hS f b₁) _ _
      (baseChangeMap_comp_eq B hX hS f (g i₁) b₁ _ rfl)
      (baseChangeMap_comp_eq B hX hS f (g i₁) b₁ _ rfl)
      (hpbbc.lift a₁ a₂ (by rw [ha₁, ha₂])) a₁ hl₁ q q hq hq ha₁ ha₁,
    ← Stacks.Picard.pullHom_pullHom_of_eq (ψ i₂) (baseChangeMap B hX hS f b₂) _ _
      (baseChangeMap_comp_eq B hX hS f (g i₂) b₂ _ hb.symm)
      (baseChangeMap_comp_eq B hX hS f (g i₂) b₂ _ hb.symm)
      (hpbbc.lift a₁ a₂ (by rw [ha₁, ha₂])) a₂ hl₂ q q hq hq ha₂ ha₂,
    hkey]

private theorem isPullback_baseChangeMap_proj {U T : BigFppfOver B S hS} (a : U ⟶ T) :
    IsPullback (baseChangeMap B hX hS f a)
      (pullback.snd (B.inclusion.map f) (B.inclusion.map U.hom))
      (pullback.snd (B.inclusion.map f) (B.inclusion.map T.hom))
      (B.inclusion.map a.left) :=
  baseChangeMap_isPullback_proj B hX hS f a

/-- The base change along `X ⟶ S` of a covering family of a test scheme `T` is an fpqc covering
family of `X_T`: each `X_{U_i} ⟶ X_T` is the base change of `U_i ⟶ T` along the projection
`X_T ⟶ T`, and an fppf covering family is in particular an fpqc one. -/
theorem baseChange_presieve_mem_fpqcPrecoverage (T : BigFppfOver B S hS)
    (E : PreZeroHypercover.{u + 1} T) (hE : BigFppfOver.IsCovering B S hS ⟨T, E⟩) :
    Presieve.ofArrows (fun i : E.I₀ => baseChange B hX hS f (E.X i))
        (fun i : E.I₀ => baseChangeMap B hX hS f (E.f i)) ∈
      Scheme.fpqcPrecoverage.{u} (baseChange B hX hS f T) := by
  have hfppf : Presieve.ofArrows
      (fun i : E.I₀ => B.inclusion.obj (E.X i).left)
      (fun i : E.I₀ => B.inclusion.map (E.f i).left) ∈
      Scheme.fppfPrecoverage (B.inclusion.obj T.left) := by
    simpa only [IsFppfCovering, Precoverage.mem_comap_iff, Presieve.map_ofArrows,
      PreZeroHypercover.map, Over.forget_obj, Over.forget_map] using hE.1
  apply Scheme.fppfPrecoverage_le_fpqcPrecoverage
  exact Precoverage.mem_coverings_of_isPullback
    (fun i : E.I₀ => B.inclusion.map (E.f i).left) hfppf
    (pullback.snd (B.inclusion.map f) (B.inclusion.map T.hom))
    (fun i : E.I₀ => baseChangeMap B hX hS f (E.f i))
    (fun i : E.I₀ => pullback.snd (B.inclusion.map f) (B.inclusion.map (E.X i).hom))
    (fun i => isPullback_baseChangeMap_proj B hX hS f (E.f i))

/-! ### Separatedness of the kernel of the section pullback -/

/-- **The kernel of `σ_T^*` is separated for the topology of the site.** A Picard class of `X_T`
that dies on the restriction along the induced section of `T` and dies on the base change of
every member of a covering family of `T` is zero.

The trivialisations on the members of the family are normalised by prescribing their restriction
along the induced sections, which makes them agree on overlaps — the overlap of two members is
again a base change, so it carries an induced section — and the normalised trivialisations
therefore glue to a trivialisation of the class on `X_T` itself. -/
theorem eq_zero_of_schemePullbackClass_baseChangeSection_eq_zero
    (hOiso : ∀ U : BigFppfOver B S hS,
      IsIso (baseChangeProj B hX hS f U).toLRSHom.toHom.c)
    (T : BigFppfOver B S hS) (E : PreZeroHypercover.{u + 1} T)
    (hE : BigFppfOver.IsCovering B S hS ⟨T, E⟩) (c : picardAt B hX hS f T)
    (hc : Stacks.Picard.schemePullbackClass (baseChangeSection B hX hS f σ hσ T) c = 0)
    (hloc : ∀ i, picardMap B hX hS f (E.f i) c = 0) :
    c = 0 := by
  classical
  have hLinv : Stacks.SheafOfModules.IsInvertible (baseChange B hX hS f T).presheaf
      (baseChange B hX hS f T).ringCatSheaf.2
      (Stacks.Picard.picardRepresentative (baseChange B hX hS f T).toRingedSpace c).obj :=
    (Stacks.Picard.picardRepresentative (baseChange B hX hS f T).toRingedSpace c).property
  have hOinv : Stacks.SheafOfModules.IsInvertible (baseChange B hX hS f T).presheaf
      (baseChange B hX hS f T).ringCatSheaf.2
      (SheafOfModules.unit (baseChange B hX hS f T).ringCatSheaf) :=
    Stacks.SheafOfModules.isInvertible_unit _ _
  obtain ⟨β⟩ := Stacks.Picard.nonempty_pullHomIso_of_schemePullbackClass_eq_zero
    (baseChangeSection B hX hS f σ hσ T) c hc
  have etriv : ∀ (V : BigFppfOver B S hS) (i : E.I₀) (b : V ⟶ E.X i) (k : V ⟶ T),
      b ≫ E.f i = k →
      Nonempty ((modulePullbackPseudofunctor.map
            (baseChangeMap B hX hS f k).op.toLoc).toFunctor.obj
          (Stacks.Picard.picardRepresentative
            (baseChange B hX hS f T).toRingedSpace c).obj ≅
        (modulePullbackPseudofunctor.map
            (baseChangeMap B hX hS f k).op.toLoc).toFunctor.obj
          (SheafOfModules.unit (baseChange B hX hS f T).ringCatSheaf)) := by
    intro V i b k hk
    refine Stacks.Picard.nonempty_pullHomIso_of_schemePullbackClass_eq_zero
      (baseChangeMap B hX hS f k) c ?_
    rw [← baseChangeMap_comp_eq B hX hS f (E.f i) b k hk,
      ← Stacks.Picard.schemePullbackClass_comp,
      show Stacks.Picard.schemePullbackClass (baseChangeMap B hX hS f (E.f i)) c = 0 from hloc i]
    exact map_zero (Stacks.Picard.schemePullbackClassHom (baseChangeMap B hX hS f b))
  have hnorm : ∀ i : E.I₀, ∃ ψ : (modulePullbackPseudofunctor.map
          (baseChangeMap B hX hS f (E.f i)).op.toLoc).toFunctor.obj
            (Stacks.Picard.picardRepresentative
              (baseChange B hX hS f T).toRingedSpace c).obj ≅
        (modulePullbackPseudofunctor.map
          (baseChangeMap B hX hS f (E.f i)).op.toLoc).toFunctor.obj
            (SheafOfModules.unit (baseChange B hX hS f T).ringCatSheaf),
      pullHom ψ.hom (baseChangeSection B hX hS f σ hσ (E.X i)) _ _ rfl rfl =
        sectionRestrict B hX hS f σ hσ β.hom (E.f i) := by
    intro i
    exact exists_pullHom_eq_sectionRestrict B hX hS f σ hσ hOiso _ _ hLinv hOinv β (E.f i)
      (etriv (E.X i) i (𝟙 _) (E.f i) (Category.id_comp _)).some
  choose ψ hψ using hnorm
  have hfpqc := baseChange_presieve_mem_fpqcPrecoverage B hX hS f T E hE
  have hLqc := Stacks.Picard.isQuasicoherent_of_isInvertible _ hLinv
  have hOqc := Stacks.Picard.isQuasicoherent_of_isInvertible _ hOinv
  rw [Stacks.Picard.eq_zero_iff_nonempty_iso_unit]
  exact Stacks.Picard.nonempty_iso_of_pullHom_hom_eq
    (fun i => baseChangeMap B hX hS f (E.f i))
    (Stacks.Picard.bijective_toDescentData_map_of_fpqc _ hfpqc _ _ hLqc hOqc)
    (Stacks.Picard.bijective_toDescentData_map_of_fpqc _ hfpqc _ _ hOqc hLqc)
    (Stacks.Picard.bijective_toDescentData_map_of_fpqc _ hfpqc _ _ hLqc hLqc)
    (Stacks.Picard.bijective_toDescentData_map_of_fpqc _ hfpqc _ _ hOqc hOqc)
    ψ
    (pullHom_eq_of_pullHom_section_eq B hX hS f σ hσ hOiso _ _ hLinv hOinv β.hom
      (fun i => E.f i) (fun i => (ψ i).hom) hψ etriv)

/-! ### Exactness in the middle -/

/-- Membership of the equalizer sieve of two Picard classes of `X_T` says that they have the
same pullback to the base change of the test scheme. -/
private theorem picardMap_eq_of_equalizerSieve {T V : BigFppfOver B S hS}
    {x y : picardAt B hX hS f T} {k : V ⟶ T}
    (h : Presheaf.equalizerSieve (F := picardPresheaf B hX hS f) (X := Opposite.op T) x y k) :
    picardMap B hX hS f k x = picardMap B hX hS f k y := h

/-- A Picard class of `X_T` whose class in the Picard functor vanishes is trivial on the base
change of some covering family of `T`. -/
theorem exists_isCovering_picardMap_eq_zero (T : BigFppfOver B S hS)
    (c : picardAt B hX hS f T) (hc : toPicardFunctorHom B hX hS f T c = 0) :
    ∃ E : PreZeroHypercover.{u + 1} T, BigFppfOver.IsCovering B S hS ⟨T, E⟩ ∧
      ∀ i, picardMap B hX hS f (E.f i) c = 0 := by
  have hli : Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS)
      (toSheafify (BigFppfOver.topology B S hS) (picardPresheaf B hX hS f)) := inferInstance
  have happ : (toPicardFunctor B hX hS f).app (Opposite.op T) c =
      (toPicardFunctor B hX hS f).app (Opposite.op T) (0 : picardAt B hX hS f T) := by
    rw [← toPicardFunctorHom_apply, ← toPicardFunctorHom_apply, hc, map_zero]
  have hmem := hli.equalizerSieve_mem c (0 : picardAt B hX hS f T) happ
  obtain ⟨E, hE, hle⟩ := BigFppfOver.exists_isCovering_sieve₀_le B S hS hmem
  refine ⟨E, hE, fun i => ?_⟩
  refine (picardMap_eq_of_equalizerSieve B hX hS f (hle _ (E.sieve₀_f i))).trans ?_
  exact map_zero (picardMapHom B hX hS f (E.f i))

include σ hσ in
/-- **Stacks Project, Tag 0B9N.** The image of pullback from `Pic(T)` is exactly the kernel of
the map to the Picard functor: a Picard class of `X_T` dies in `Pic_{X/S}(T)` if and only if it
is pulled back along the projection `X_T ⟶ T`. This is exactness in the middle of
`0 ⟶ Pic(T) ⟶ Pic(X_T) ⟶ Pic_{X/S}(T) ⟶ 0`. -/
@[stacks 0B9N "exactness in the middle"]
theorem exact_schemePullbackClass_baseChangeProj_toPicardFunctorHom
    (hOiso : ∀ U : BigFppfOver B S hS,
      IsIso (baseChangeProj B hX hS f U).toLRSHom.toHom.c)
    (T : BigFppfOver B S hS) :
    Function.Exact (Stacks.Picard.schemePullbackClass (baseChangeProj B hX hS f T))
      (toPicardFunctorHom B hX hS f T) := by
  intro c
  refine ⟨fun hc => ?_, ?_⟩
  · refine ⟨Stacks.Picard.schemePullbackClassHom (baseChangeSection B hX hS f σ hσ T) c, ?_⟩
    have hsplit := schemePullbackClass_baseChangeSection_baseChangeProj B hX hS f σ hσ T
      (Stacks.Picard.schemePullbackClassHom (baseChangeSection B hX hS f σ hσ T) c)
    have hsec : Stacks.Picard.schemePullbackClassHom (baseChangeSection B hX hS f σ hσ T)
        (c - Stacks.Picard.schemePullbackClassHom (baseChangeProj B hX hS f T)
          (Stacks.Picard.schemePullbackClassHom
            (baseChangeSection B hX hS f σ hσ T) c)) = 0 := by
      rw [map_sub]
      rw [show Stacks.Picard.schemePullbackClassHom (baseChangeSection B hX hS f σ hσ T)
          (Stacks.Picard.schemePullbackClassHom (baseChangeProj B hX hS f T)
            (Stacks.Picard.schemePullbackClassHom
              (baseChangeSection B hX hS f σ hσ T) c)) = _ from hsplit, sub_self]
    have hzero : toPicardFunctorHom B hX hS f T
        (c - Stacks.Picard.schemePullbackClassHom (baseChangeProj B hX hS f T)
          (Stacks.Picard.schemePullbackClassHom
            (baseChangeSection B hX hS f σ hσ T) c)) = 0 := by
      rw [map_sub, hc,
        show toPicardFunctorHom B hX hS f T
            (Stacks.Picard.schemePullbackClassHom (baseChangeProj B hX hS f T)
              (Stacks.Picard.schemePullbackClassHom
                (baseChangeSection B hX hS f σ hσ T) c)) = 0 from
          toPicardFunctorHom_schemePullbackClass_baseChangeProj B hX hS f T _,
        sub_zero]
    obtain ⟨E, hE, hloc⟩ := exists_isCovering_picardMap_eq_zero B hX hS f T _ hzero
    have := eq_zero_of_schemePullbackClass_baseChangeSection_eq_zero B hX hS f σ hσ hOiso T E hE
      _ hsec hloc
    rw [sub_eq_zero] at this
    exact this.symm
  · rintro ⟨N, rfl⟩
    exact toPicardFunctorHom_schemePullbackClass_baseChangeProj B hX hS f T N

end Stacks.PicardFunctor

end
