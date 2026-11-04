module

public import StacksFrontier.AlgebraicGeometry.AmpleLimit.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalCocycle
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.DescendUnconditional
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MorphismDescentGlue
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.PullbackSectionCalculus
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.MulIsomorphism
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs
public import StacksCore.Tactic.StacksAttribute

/-!
# Tag 09MT, unconditionally: ampleness descends through a cofiltered limit

`StacksFrontier/AlgebraicGeometry/AmpleLimit/Basic.lean` proves [Stacks Project, Tag 09MT] from
one named hypothesis, `Stacks.AlgebraicGeometry.AmpleLimit.NonvanishingLocusDescent`, the
consequence of [Stacks Project, Tag 01Z0] that the source's proof consumes.  That file's
implementation notes propose discharging it by trivialising `M^{⊗ n}` on an affine open cover and
glueing.  This file discharges it a different and much shorter way, from
[Stacks Project, Tag 01ZR] (2): a global section of a module **is** a morphism out of the
structure sheaf, so fullness of base change on morphisms between finitely presented modules is
surjectivity of base change on global sections, and the tensor powers of an invertible module are
finitely presented.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.exists_canonical_section_eq_of_isLimit`: the
  surjectivity half of [Stacks Project, Tag 01Z0] for a module of finite presentation on a stage,
  pinned through `Stacks.AlgebraicGeometry.ModuleLimits.canHom`.  The `@[stacks 01Z0]` attribute
  is withheld — see the declaration's docstring.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_nonvanishingLocus_eq_preimage_of_isLimit`: the
  same read on nonvanishing loci.
* `...ModuleLimits.exists_canonical_section_eq_of_canonical_section_eq_of_isLimit`:
  the **injectivity** half of [Stacks Project, Tag 01Z0] for a module of finite presentation on a
  stage, pinned the same way.  The `@[stacks 01Z0]` attribute is withheld for the same reason —
  see the declaration's docstring.  It is [Stacks Project, Tag 01ZR] (3) read through the
  identification of a global section with a morphism out of the structure sheaf, which is
  `Stacks.AlgebraicGeometry.ModuleLimits.sectionsMap_canHom_modulePullbackSection_eq_iff`.
* `Stacks.AlgebraicGeometry.ModuleLimits.sectionsMap_canHom_modulePullbackSection_comp`: the
  composition law for canonical images of sections, which is the cocone clause of the colimit
  assertion the two halves assemble into.
* `Stacks.AlgebraicGeometry.AmpleLimit.nonvanishingLocusDescent_of_isLimit`:
  `NonvanishingLocusDescent` is a theorem.
* `Stacks.AlgebraicGeometry.AmpleLimit.exists_isAmple_pullback_map_of_isLimit_of_qcqs`:
  **[Stacks Project, Tag 09MT]**, with no hypothesis beyond Situation 086P.

## Implementation notes

Tag 01ZR (2) is `Stacks.AlgebraicGeometry.ModuleLimits.exists_map_of_pullback_of_isLimit`
(`StacksFrontier/AlgebraicGeometry/ModuleLimits/LocalDescentRefine.lean`), and it is applied with the structure sheaf of the
stage as the source module: that is finitely presented by
`...ModuleLimits.isFinitePresentation_unit`, and `M^{⊗ n}` is finitely presented because it is
invertible (`Stacks.SheafOfModules.Invertible.tensorPower_isInvertible` followed by
`AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isInvertible`).

Two comparisons are needed and are proved here.  `unitHomEquiv_pullbackUnitIso_inv_comp` says
that the morphism `𝒪_Y ≅ f^*𝒪_X ⟶ f^*N` attached to a global section of `N` names the pullback
of that section, which is the one place `Stacks.SheafOfModules.modulePullbackSection` — the
spelling [Stacks Project, Tag 0H78] and `AmpleLimit/Basic.lean` use — has to be matched against
the categorical pullback; the two units of adjunction involved are definitionally equal, and the
`1`-level input is
`Stacks.AlgebraicGeometry.PicardBaseChange.pullbackUnitIso_hom_pullbackUnitSections`.
`pullbackUnitIso_inv_canHom` is the compatibility of `𝒪 ≅ f^*𝒪` with the canonical identification
of an iterated pullback with the pullback along the composite; both sides are morphisms out of the
structure sheaf, so it reduces to a computation on the unit section, where
`...ModuleLimits.canHom_app_top_pullbackSection` is exactly the needed step.  Neither comparison
touches the tensor product, which is why no coherence of
`AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso` with composition of pullbacks is
required.

**`SectionsDescent` itself is *not* discharged here, and the reason is sharp.**  That hypothesis
asserts an equality of *sections*, pinned through
`Stacks.AlgebraicGeometry.AmpleLimit.transportSection`, which composes the pullback of a section
with `AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso` at the *lower* stage, whereas the
route above produces the section through `pullbackTensorPowerIso` at the *upper* stage.  Equating
the two needs the compatibility of `pullbackTensorPowerIso` with composition of pullbacks, whose
successor step is the compatibility of [Stacks Project, Tag 01CD] with composition — a coherence
of the monoidal comparison that this development does not have, and which no statement about
nonvanishing loci needs, because a nonvanishing locus is unchanged by any isomorphism of modules.
So the weaker `NonvanishingLocusDescent` is discharged, Tag 09MT closes, and `SectionsDescent`
remains open.

## References

* [Stacks Project, Tag 09MT](https://stacks.math.columbia.edu/tag/09MT)
* [Stacks Project, Tag 01Z0](https://stacks.math.columbia.edu/tag/01Z0)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.SheafOfModules
open Stacks.SheafOfModules.Invertible (tensorPower tensorPower_isInvertible)
open Stacks.AlgebraicGeometry.SectionsBaseChange (pullbackUnitSections le_preimage_top
  pullbackSectionsHom_top pullbackSectionsHom_apply pullbackUnitSections_naturality_module)
open AlgebraicGeometry.Scheme.Modules (pullbackSection pullbackTensorPowerIso pullbackUnitIso)

universe v u

namespace Stacks.AlgebraicGeometry.ModuleLimits

-- `Scheme.unitModule X` is the structure sheaf of `X` read as a module over itself; the statements
-- below spell it `SheafOfModules.unit X.ringCatSheaf`, and `rw` matches syntactically.
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.unitModule

/-! ### Two generic reassociations -/

private theorem map_comp_assoc_aux {C E : Type*} [Category C] [Category E] (F : C ⥤ E)
    {X Y Z : C} {W T : E} (a : W ⟶ F.obj X) (b : X ⟶ Y) (cc : Y ⟶ Z) (d : F.obj Z ⟶ T) :
    (a ≫ F.map (b ≫ cc)) ≫ d = (a ≫ F.map b) ≫ F.map cc ≫ d := by
  rw [F.map_comp]; simp only [Category.assoc]

private theorem triangle_aux {C : Type*} [Category C] {A B B' P Q : C}
    {nu : A ⟶ B} {m : B ⟶ B'} {cg : B' ⟶ P} {cf : B ⟶ Q} {phi : Q ⟶ P} {uu : A ⟶ Q}
    (h1 : m ≫ cg = cf ≫ phi) (h2 : nu ≫ cf = uu) : nu ≫ m ≫ cg = uu ≫ phi := by
  rw [h1, ← Category.assoc, h2]

/-! ### Global sections of a module on a scheme are determined over the whole space -/

/-- Two global sections of a module on a scheme that agree over `⊤` are equal: every other value
is the restriction of the value over `⊤`. -/
theorem sections_ext_top {X : Scheme.{u}} {N : X.Modules} (a b : N.sections)
    (h : a.eval (op ⊤) = b.eval (op ⊤)) : a = b := by
  refine PresheafOfModules.sections_ext _ _ fun U => ?_
  have ha := a.property (homOfLE (le_top (a := U.unop))).op
  have hb := b.property (homOfLE (le_top (a := U.unop))).op
  exact ha.symm.trans ((congrArg (fun z => (ConcreteCategory.hom
    ((N.val.presheaf ⋙ forget Ab).map (homOfLE (le_top (a := U.unop))).op)) z) h).trans hb)

/-- An isomorphism of modules and its inverse cancel on sections over a fixed open. -/
theorem iso_inv_app_hom_app {Y : Scheme.{u}} {A B : Y.Modules} (e : A ≅ B)
    (V : Y.Opens) (x : Γ(A, V)) :
    Scheme.Modules.Hom.app e.inv V (Scheme.Modules.Hom.app e.hom V x) = x :=
  congrArg (fun k : A ⟶ A => Scheme.Modules.Hom.app k V x) e.hom_inv_id

/-! ### The pulled-back unit section -/

/-- **`pullbackUnitIso` carries the unit section of `𝒪_X` to the unit section of `𝒪_Y`**, read
backwards: the inverse of `pullbackUnitIso f` sends `1` to the pullback of `1`.  This is
`Stacks.AlgebraicGeometry.PicardBaseChange.pullbackUnitIso_hom_pullbackUnitSections` at `r = 1`,
where the ring map sends `1` to `1`. -/
theorem pullbackUnitIso_inv_app_top_one {X Y : Scheme.{u}} (f : Y ⟶ X) :
    Scheme.Modules.Hom.app (pullbackUnitIso f).inv ⊤ (1 : Γ(Y, ⊤))
      = pullbackUnitSections f (SheafOfModules.unit X.ringCatSheaf) ⊤ (1 : Γ(X, ⊤)) := by
  have h := Stacks.AlgebraicGeometry.PicardBaseChange.pullbackUnitIso_hom_pullbackUnitSections
    f (1 : Γ(X, ⊤))
  rw [map_one] at h
  have h2 := congrArg
    (fun z => Scheme.Modules.Hom.app (pullbackUnitIso f).inv (⊤ : Y.Opens) z) h
  exact h2.symm.trans (iso_inv_app_hom_app (pullbackUnitIso f) ⊤ _)

/-- Over the whole space the pullback of a section is the unit of `f^* ⊣ f_*` on sections. -/
theorem pullbackSection_top_eq {X Y : Scheme.{u}} (p : Y ⟶ X) (F : X.Modules) (a : Γ(F, ⊤)) :
    (pullbackSection p F ⊤ ⊤ (le_preimage_top p ⊤) a :
        Γ((Scheme.Modules.pullback p).obj F, ⊤))
      = pullbackUnitSections p F ⊤ a :=
  (pullbackSectionsHom_apply p F ⊤ ⊤ (le_preimage_top p ⊤) a).symm.trans
    (pullbackSectionsHom_top p F a)

/-- **A global section of `f^*N` coming from a morphism out of the structure sheaf is the pullback
of the corresponding global section of `N`.**  Through `SheafOfModules.unitHomEquiv`, a global
section of `N` is a morphism `𝒪_X ⟶ N`; applying `f^*` to it and precomposing with
`𝒪_Y ≅ f^*𝒪_X` gives a global section of `f^*N`, and it is the image of the original one under
the unit of `f^* ⊣ f_*`, i.e. `Stacks.SheafOfModules.modulePullbackSection`. -/
theorem unitHomEquiv_pullbackUnitIso_inv_comp {X Y : Scheme.{u}} (f : Y ⟶ X) (N : X.Modules)
    (ψ : SheafOfModules.unit X.ringCatSheaf ⟶ N) :
    SheafOfModules.unitHomEquiv _
        ((pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map ψ)
      = Stacks.SheafOfModules.modulePullbackSection f.toLRSHom N
          (SheafOfModules.unitHomEquiv N ψ) := by
  refine sections_ext_top _ _ ?_
  have hnat := pullbackUnitSections_naturality_module f ψ ⊤ (1 : Γ(X, ⊤))
  have h1 := pullbackUnitIso_inv_app_top_one f
  have e2 := Stacks.SheafOfModules.modulePullbackSection_eval_top f.toLRSHom N
    (SheafOfModules.unitHomEquiv N ψ)
  refine Eq.trans ?_ e2.symm
  refine Eq.trans ?_ hnat
  exact congrArg
    (fun z => Scheme.Modules.Hom.app ((Scheme.Modules.pullback f).map ψ) (f ⁻¹ᵁ ⊤) z) h1

/-- **The comparison `𝒪 ≅ f^*𝒪` is compatible with the canonical identification of an iterated
pullback with the pullback along the composite.**  Both sides are morphisms
`𝒪_W ⟶ pi^*𝒪_X`, so it is enough to compare the global sections they name, and there both sides
are the pullback of `1` along `pi` — on the left by
`Stacks.AlgebraicGeometry.ModuleLimits.canHom_app_top_pullbackSection`. -/
theorem pullbackUnitIso_inv_canHom {W Z X : Scheme.{u}} (q : W ⟶ Z) (g : Z ⟶ X) (pi : W ⟶ X)
    (hpi : q ≫ g = pi) :
    ((pullbackUnitIso q).inv ≫ (Scheme.Modules.pullback q).map (pullbackUnitIso g).inv) ≫
        canHom q g pi hpi (SheafOfModules.unit X.ringCatSheaf)
      = (pullbackUnitIso pi).inv := by
  apply (SheafOfModules.unitHomEquiv _).injective
  refine sections_ext_top _ _ ?_
  have hc := canHom_app_top_pullbackSection q g pi hpi
    (SheafOfModules.unit X.ringCatSheaf) (1 : Γ(X, ⊤))
  rw [pullbackSection_top_eq g (SheafOfModules.unit X.ringCatSheaf) (1 : Γ(X, ⊤)),
    pullbackSection_top_eq q ((Scheme.Modules.pullback g).obj
        (SheafOfModules.unit X.ringCatSheaf))
      (pullbackUnitSections g (SheafOfModules.unit X.ringCatSheaf) ⊤ (1 : Γ(X, ⊤))),
    pullbackSection_top_eq pi (SheafOfModules.unit X.ringCatSheaf) (1 : Γ(X, ⊤))] at hc
  have hn := pullbackUnitSections_naturality_module q (pullbackUnitIso g).inv ⊤ (1 : Γ(Z, ⊤))
  simp only [AlgebraicGeometry.Scheme.unitModule] at hn
  show Scheme.Modules.Hom.app (canHom q g pi hpi (SheafOfModules.unit X.ringCatSheaf)) ⊤
      (Scheme.Modules.Hom.app ((Scheme.Modules.pullback q).map (pullbackUnitIso g).inv)
        (q ⁻¹ᵁ ⊤) (Scheme.Modules.Hom.app (pullbackUnitIso q).inv ⊤ (1 : Γ(W, ⊤)))) = _
  rw [pullbackUnitIso_inv_app_top_one q, hn, pullbackUnitIso_inv_app_top_one g]
  exact hc.trans (pullbackUnitIso_inv_app_top_one pi).symm

/-- The canonical image of the pullback of the section named by `ψ : 𝒪_Z ⟶ g⁺G` is named by
`𝒪_W ≅ q⁺𝒪_Z ⟶ q⁺g⁺G ⟶ pi⁺G`. -/
private theorem sectionsMap_canHom_unitHomEquiv {W Z X : Scheme.{u}} (q : W ⟶ Z) (g : Z ⟶ X)
    (pi : W ⟶ X) (hpi : q ≫ g = pi) (G : X.Modules)
    (ψ : SheafOfModules.unit Z.ringCatSheaf ⟶ (Scheme.Modules.pullback g).obj G) :
    SheafOfModules.sectionsMap (canHom q g pi hpi G)
          (Stacks.SheafOfModules.modulePullbackSection q.toLRSHom _
            (SheafOfModules.unitHomEquiv _ ψ))
      = SheafOfModules.unitHomEquiv _
          (((pullbackUnitIso q).inv ≫ (Scheme.Modules.pullback q).map ψ) ≫
            canHom q g pi hpi G) := by
  exact (congrArg (SheafOfModules.sectionsMap (canHom q g pi hpi G))
    (unitHomEquiv_pullbackUnitIso_inv_comp q _ ψ).symm).trans rfl

/-! ### Tag 01Z0 for a module of finite presentation at a stage -/

/-- **[Stacks Project, Tag 01Z0], surjectivity half, for a module of finite presentation at a
stage, and canonically pinned.**  Let `c` be a limit cone on a cofiltered diagram of
quasi-compact quasi-separated schemes with affine transition morphisms and let `G` be a module of
finite presentation on the stage `D.obj i`.  Then every global section of the pullback of `G` to
`c.pt` is the pullback of a global section of the pullback of `G` to some stage over `i`, through
`Stacks.AlgebraicGeometry.ModuleLimits.canHom`.

This is [Stacks Project, Tag 01ZR] (2) — `exists_map_of_pullback_of_isLimit` — applied with the
structure sheaf as the source: a global section of a module is a morphism out of the structure
sheaf, so fullness of base change on morphisms of finitely presented modules *is* surjectivity of
base change on global sections.  The two comparisons this needs are
`unitHomEquiv_pullbackUnitIso_inv_comp` and `pullbackUnitIso_inv_canHom`.

The `@[stacks 01Z0]` attribute is **withheld**: the tag asserts that `Γ(c.pt, f₀^*ℱ₀)` is the
filtered colimit of the `Γ(Sᵢ, f_{i0}^*ℱ₀)` for an arbitrary *quasi-coherent* `ℱ₀`, whereas this
states only the surjectivity half and only for `ℱ₀` of finite presentation. -/
theorem exists_canonical_section_eq_of_isLimit {I : Type u} [Category.{v} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (G : (D.obj i).Modules) (hG : G.IsFinitePresentation)
    (s : ((Scheme.Modules.pullback (c.π.app i)).obj G).sections) :
    ∃ (k : I) (e : k ⟶ i) (t : ((Scheme.Modules.pullback (D.map e)).obj G).sections),
      SheafOfModules.sectionsMap (canHom (c.π.app k) (D.map e) (c.π.app i) (c.w e) G)
          (Stacks.SheafOfModules.modulePullbackSection (c.π.app k).toLRSHom _ t) = s := by
  have : G.IsFinitePresentation := hG
  have : (SheafOfModules.unit (D.obj i).ringCatSheaf).IsFinitePresentation :=
    isFinitePresentation_unit _
  obtain ⟨k, e, Φ, hΦ⟩ := exists_map_of_pullback_of_isLimit D c hc i
    (SheafOfModules.unit (D.obj i).ringCatSheaf) G
    ((pullbackUnitIso (c.π.app i)).hom ≫ (SheafOfModules.unitHomEquiv _).symm s)
  refine ⟨k, e, SheafOfModules.unitHomEquiv _ ((pullbackUnitIso (D.map e)).inv ≫ Φ), ?_⟩
  have h1 : (Scheme.Modules.pullback (c.π.app k)).map Φ ≫
        canHom (c.π.app k) (D.map e) (c.π.app i) (c.w e) G
      = canHom (c.π.app k) (D.map e) (c.π.app i) (c.w e)
          (SheafOfModules.unit (D.obj i).ringCatSheaf) ≫
        ((pullbackUnitIso (c.π.app i)).hom ≫ (SheafOfModules.unitHomEquiv _).symm s) := by
    simpa [canHom] using hΦ
  have key : ((pullbackUnitIso (c.π.app k)).inv ≫ (Scheme.Modules.pullback (c.π.app k)).map
        ((pullbackUnitIso (D.map e)).inv ≫ Φ)) ≫
        canHom (c.π.app k) (D.map e) (c.π.app i) (c.w e) G
      = (SheafOfModules.unitHomEquiv _).symm s :=
    (map_comp_assoc_aux (Scheme.Modules.pullback (c.π.app k)) _ _ _ _).trans
      ((triangle_aux h1
        (pullbackUnitIso_inv_canHom (c.π.app k) (D.map e) (c.π.app i) (c.w e))).trans
        (Iso.inv_hom_id_assoc _ _))
  exact (sectionsMap_canHom_unitHomEquiv _ _ _ _ G _).trans
    ((congrArg (SheafOfModules.unitHomEquiv _) key).trans (Equiv.apply_symm_apply _ s))

/-- **The nonvanishing locus of a global section at the limit is the preimage of a nonvanishing
locus at a stage**, for a module at the limit isomorphic to the pullback of a finitely presented
module at a stage.  Nonvanishing loci are unchanged by an isomorphism of modules
(`Stacks.SheafOfModules.nonvanishingLocus_sectionsMap`) and are preimages under pullback of a
section ([Stacks Project, Tag 0H78]), so this is exactly
`exists_canonical_section_eq_of_isLimit` read on loci. -/
theorem exists_nonvanishingLocus_eq_preimage_of_isLimit {I : Type u} [Category.{v} I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (G : (D.obj i).Modules) (hG : G.IsFinitePresentation)
    (A : c.pt.Modules) (eA : A ≅ (Scheme.Modules.pullback (c.π.app i)).obj G)
    (s : A.sections) :
    ∃ (k : I) (e : k ⟶ i) (t : ((Scheme.Modules.pullback (D.map e)).obj G).sections),
      nonvanishingLocus (X := c.pt.toRingedSpace) A s
        = (c.π.app k).base ⁻¹' nonvanishingLocus (X := (D.obj k).toRingedSpace)
            ((Scheme.Modules.pullback (D.map e)).obj G) t := by
  obtain ⟨k, e, t, ht⟩ := exists_canonical_section_eq_of_isLimit D c hc i G hG
    (SheafOfModules.sectionsMap eA.hom s)
  refine ⟨k, e, t, ?_⟩
  have hiso := isIso_canHom (c.π.app k) (D.map e) (c.π.app i) (c.w e) G
  have e1 := (nonvanishingLocus_sectionsMap c.pt.toRingedSpace eA s).symm
  have e2 := (congrArg (Stacks.SheafOfModules.nonvanishingLocus
      ((Scheme.Modules.pullback (c.π.app i)).obj G)) ht.symm).trans
    (nonvanishingLocus_sectionsMap c.pt.toRingedSpace
      (@asIso _ _ _ _ (canHom (c.π.app k) (D.map e) (c.π.app i) (c.w e) G) hiso)
      (Stacks.SheafOfModules.modulePullbackSection (c.π.app k).toLRSHom _ t))
  have e3 := (Stacks.SheafOfModules.preimage_nonvanishingLocus (c.π.app k).toLRSHom
    ((Scheme.Modules.pullback (D.map e)).obj G) t).symm
  exact e1.trans (e2.trans e3)

/-! ### The canonical image of a section, read as a morphism out of the structure sheaf -/

/-- **The canonical image of a section of `g⁺G` in `pi⁺G`, named by a morphism out of the
structure sheaf.**  For `q ≫ g = pi` the section obtained from `x` by pulling back along `q` and
applying `Stacks.AlgebraicGeometry.ModuleLimits.canHom` is the one that the composite
`𝒪_W ≅ q⁺𝒪_Z ⟶ q⁺g⁺G ⟶ pi⁺G` names.  This is `unitHomEquiv_pullbackUnitIso_inv_comp` followed
by `SheafOfModules.unitHomEquiv_comp_apply`. -/
theorem sectionsMap_canHom_modulePullbackSection_eq {W Z X : Scheme.{u}} (q : W ⟶ Z)
    (g : Z ⟶ X) (pi : W ⟶ X) (hpi : q ≫ g = pi) (G : X.Modules)
    (x : ((Scheme.Modules.pullback g).obj G).sections) :
    SheafOfModules.sectionsMap (canHom q g pi hpi G)
          (Stacks.SheafOfModules.modulePullbackSection q.toLRSHom _ x)
      = SheafOfModules.unitHomEquiv _
          (((pullbackUnitIso q).inv ≫ (Scheme.Modules.pullback q).map
            ((SheafOfModules.unitHomEquiv _).symm x)) ≫ canHom q g pi hpi G) := by
  refine Eq.trans ?_ (sectionsMap_canHom_unitHomEquiv q g pi hpi G
    ((SheafOfModules.unitHomEquiv ((Scheme.Modules.pullback g).obj G)).symm x))
  exact congrArg (fun z => SheafOfModules.sectionsMap (canHom q g pi hpi G)
    (Stacks.SheafOfModules.modulePullbackSection q.toLRSHom _ z))
    (Equiv.apply_symm_apply _ x).symm

/-- **Two sections of `g⁺G` have the same canonical image in `pi⁺G` exactly when the morphisms
out of the structure sheaf that they name have the same pullback along `q`.**  Both the canonical
identification and the comparison `𝒪_W ≅ q⁺𝒪_Z` are isomorphisms, so they cancel. -/
theorem sectionsMap_canHom_modulePullbackSection_eq_iff {W Z X : Scheme.{u}} (q : W ⟶ Z)
    (g : Z ⟶ X) (pi : W ⟶ X) (hpi : q ≫ g = pi) (G : X.Modules)
    (x y : ((Scheme.Modules.pullback g).obj G).sections) :
    SheafOfModules.sectionsMap (canHom q g pi hpi G)
            (Stacks.SheafOfModules.modulePullbackSection q.toLRSHom _ x)
          = SheafOfModules.sectionsMap (canHom q g pi hpi G)
            (Stacks.SheafOfModules.modulePullbackSection q.toLRSHom _ y)
      ↔ (Scheme.Modules.pullback q).map ((SheafOfModules.unitHomEquiv _).symm x)
          = (Scheme.Modules.pullback q).map ((SheafOfModules.unitHomEquiv _).symm y) := by
  rw [sectionsMap_canHom_modulePullbackSection_eq q g pi hpi G x,
    sectionsMap_canHom_modulePullbackSection_eq q g pi hpi G y]
  constructor
  · intro hh
    exact (cancel_epi (pullbackUnitIso q).inv).mp
      ((cancel_mono (canHom q g pi hpi G)).mp
        ((SheafOfModules.unitHomEquiv ((Scheme.Modules.pullback pi).obj G)).injective hh))
  · intro hh
    exact congrArg (fun z => SheafOfModules.unitHomEquiv
      ((Scheme.Modules.pullback pi).obj G) z) (by rw [hh])

/-- The morphism-level form of the composition law for canonical images of sections: the two ways
of carrying a morphism `𝒪_Z ⟶ s⁺G` to a morphism `𝒪_L ⟶ ptz⁺G` along `L ⟶ W ⟶ Z` agree.  This is
the cocycle `canHom_comp_canHom`, the naturality `canHom_naturality` and the compatibility
`pullbackUnitIso_inv_canHom` of `𝒪 ≅ f⁺𝒪` with the canonical identification. -/
private theorem pullbackUnitIso_inv_map_canHom_comp {L W Z X : Scheme.{u}} (p : L ⟶ W)
    (t : W ⟶ Z) (s : Z ⟶ X) (pt : L ⟶ Z) (h1 : p ≫ t = pt) (ts : W ⟶ X) (h3 : t ≫ s = ts)
    (ptz : L ⟶ X) (h2 : pt ≫ s = ptz) (h4 : p ≫ ts = ptz) (G : X.Modules)
    (ψ : SheafOfModules.unit Z.ringCatSheaf ⟶ (Scheme.Modules.pullback s).obj G) :
    ((pullbackUnitIso p).inv ≫ (Scheme.Modules.pullback p).map
          (((pullbackUnitIso t).inv ≫ (Scheme.Modules.pullback t).map ψ) ≫ canHom t s ts h3 G))
        ≫ canHom p ts ptz h4 G
      = ((pullbackUnitIso pt).inv ≫ (Scheme.Modules.pullback pt).map ψ)
          ≫ canHom pt s ptz h2 G := by
  have hnat := canHom_naturality p t pt h1 ψ
  have hunit := pullbackUnitIso_inv_canHom p t pt h1
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← canHom_comp_canHom p t s pt h1 ts h3 ptz h2 h4 G, reassoc_of% hnat,
    reassoc_of% hunit]

/-- **The canonical images of a section compose.**  For a chain `L ⟶ W ⟶ Z ⟶ X` the canonical
image in `ptz⁺G` of the canonical image in `ts⁺G` of a section of `s⁺G` is its canonical image
along the composite `pt`.  Every composite of morphisms of schemes is supplied as a hypothesis,
so a diagram whose transition morphism is `D.map (e₁ ≫ e₂)` can be fed to this lemma. -/
theorem sectionsMap_canHom_modulePullbackSection_comp {L W Z X : Scheme.{u}} (p : L ⟶ W)
    (t : W ⟶ Z) (s : Z ⟶ X) (pt : L ⟶ Z) (h1 : p ≫ t = pt) (ts : W ⟶ X) (h3 : t ≫ s = ts)
    (ptz : L ⟶ X) (h2 : pt ≫ s = ptz) (h4 : p ≫ ts = ptz) (G : X.Modules)
    (x : ((Scheme.Modules.pullback s).obj G).sections) :
    SheafOfModules.sectionsMap (canHom p ts ptz h4 G)
          (Stacks.SheafOfModules.modulePullbackSection p.toLRSHom _
            (SheafOfModules.sectionsMap (canHom t s ts h3 G)
              (Stacks.SheafOfModules.modulePullbackSection t.toLRSHom _ x)))
      = SheafOfModules.sectionsMap (canHom pt s ptz h2 G)
          (Stacks.SheafOfModules.modulePullbackSection pt.toLRSHom _ x) := by
  have hψ : (SheafOfModules.unitHomEquiv ((Scheme.Modules.pullback ts).obj G)).symm
        (SheafOfModules.sectionsMap (canHom t s ts h3 G)
          (Stacks.SheafOfModules.modulePullbackSection t.toLRSHom _ x))
      = ((pullbackUnitIso t).inv ≫ (Scheme.Modules.pullback t).map
          ((SheafOfModules.unitHomEquiv ((Scheme.Modules.pullback s).obj G)).symm x))
        ≫ canHom t s ts h3 G :=
    (congrArg (fun z => (SheafOfModules.unitHomEquiv
        ((Scheme.Modules.pullback ts).obj G)).symm z)
      (sectionsMap_canHom_modulePullbackSection_eq t s ts h3 G x)).trans
      (Equiv.symm_apply_apply _ _)
  refine Eq.trans (sectionsMap_canHom_modulePullbackSection_eq p ts ptz h4 G _) ?_
  refine Eq.trans ?_ (sectionsMap_canHom_modulePullbackSection_eq pt s ptz h2 G x).symm
  refine congrArg
    (fun z => SheafOfModules.unitHomEquiv ((Scheme.Modules.pullback ptz).obj G) z) ?_
  refine Eq.trans ?_ (pullbackUnitIso_inv_map_canHom_comp p t s pt h1 ts h3 ptz h2 h4 G
    ((SheafOfModules.unitHomEquiv ((Scheme.Modules.pullback s).obj G)).symm x))
  exact congrArg (fun z => ((pullbackUnitIso p).inv ≫ (Scheme.Modules.pullback p).map z)
    ≫ canHom p ts ptz h4 G) hψ

/-! ### Tag 01Z0 for a module of finite presentation at a stage: the injectivity half -/

/-- **[Stacks Project, Tag 01Z0], injectivity half, for a module of finite presentation at a
stage, and canonically pinned.**  Let `c` be a limit cone on a cofiltered diagram of
quasi-compact schemes with affine transition morphisms, let `G` be a module of finite presentation
on the stage `D.obj i`, and let `x` and `y` be global sections of the pullback of `G` to a stage
`D.obj k` over `i` whose canonical images in the pullback of `G` to `c.pt` agree.  Then already
their canonical images at some stage over `k` agree.

This is [Stacks Project, Tag 01ZR] (3) — `exists_pullback_map_eq_of_isLimit'` — applied with the
structure sheaf of `D.obj k` as the source: a global section of a module is a morphism out of the
structure sheaf, and under that identification the canonical image of a section is the pullback
of the corresponding morphism followed by two isomorphisms, by
`sectionsMap_canHom_modulePullbackSection_eq_iff`.  So faithfulness of base change on morphisms
of finitely presented modules *is* the injectivity half of the colimit assertion on global
sections.

The conclusion is universally quantified over the morphism `f : l ⟶ i` representing the composite
and over the equation identifying it, so that a caller whose diagram names that composite
differently from `g ≫ e` need not transport along an equality of morphisms of schemes.

The `@[stacks 01Z0]` attribute is **withheld**, exactly as it is on the surjectivity half
`exists_canonical_section_eq_of_isLimit`: the tag asserts that `Γ(c.pt, f₀⁺ℱ₀)` is the filtered
colimit of the `Γ(Sᵢ, f_{i0}⁺ℱ₀)` for an arbitrary *quasi-coherent* `ℱ₀`, whereas this is one of
the two halves and only for `ℱ₀` of finite presentation.  The two halves are assembled into the
colimit assertion, still only for a module of finite presentation, by
`AlgebraicGeometry.isStagesColimit_stagePullbackSection_of_isFinitePresentation` in
`StacksFrontier/AlgebraicGeometry/ModuleLimits/SectionsColimitFinitePresentation.lean`, which is the
declaration carrying `@[stacks 01Z0 ...]` keyed to that restriction. -/
theorem exists_canonical_section_eq_of_canonical_section_eq_of_isLimit {I : Type u}
    [Category.{v} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D) (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj i)] (i : I) (G : (D.obj i).Modules)
    (hG : G.IsFinitePresentation) (k : I) (e : k ⟶ i)
    (x y : ((Scheme.Modules.pullback (D.map e)).obj G).sections)
    (h : SheafOfModules.sectionsMap (canHom (c.π.app k) (D.map e) (c.π.app i) (c.w e) G)
            (Stacks.SheafOfModules.modulePullbackSection (c.π.app k).toLRSHom _ x)
          = SheafOfModules.sectionsMap (canHom (c.π.app k) (D.map e) (c.π.app i) (c.w e) G)
            (Stacks.SheafOfModules.modulePullbackSection (c.π.app k).toLRSHom _ y)) :
    ∃ (l : I) (g : l ⟶ k), ∀ (f : l ⟶ i) (w : D.map g ≫ D.map e = D.map f),
      SheafOfModules.sectionsMap (canHom (D.map g) (D.map e) (D.map f) w G)
            (Stacks.SheafOfModules.modulePullbackSection (D.map g).toLRSHom _ x)
          = SheafOfModules.sectionsMap (canHom (D.map g) (D.map e) (D.map f) w G)
            (Stacks.SheafOfModules.modulePullbackSection (D.map g).toLRSHom _ y) := by
  have hGfp : G.IsFinitePresentation := hG
  have hpbfp : ((Scheme.Modules.pullback (D.map e)).obj G).IsFinitePresentation :=
    isFinitePresentation_pullback (D.map e) G
  have hunitfp : (SheafOfModules.unit (D.obj k).ringCatSheaf).IsFinitePresentation :=
    isFinitePresentation_unit _
  obtain ⟨l, g, hg⟩ := exists_pullback_map_eq_of_isLimit' D c hc k
    (SheafOfModules.unit (D.obj k).ringCatSheaf)
    ((Scheme.Modules.pullback (D.map e)).obj G)
    ((SheafOfModules.unitHomEquiv _).symm x) ((SheafOfModules.unitHomEquiv _).symm y)
    ((sectionsMap_canHom_modulePullbackSection_eq_iff (c.π.app k) (D.map e) (c.π.app i)
      (c.w e) G x y).mp h)
  exact ⟨l, g, fun f w => (sectionsMap_canHom_modulePullbackSection_eq_iff (D.map g)
    (D.map e) (D.map f) w G x y).mpr hg⟩

end Stacks.AlgebraicGeometry.ModuleLimits

namespace Stacks.AlgebraicGeometry.AmpleLimit

open scoped Stacks.AlgebraicGeometry.AmpleLimit

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
variable [IsCofiltered I] [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

include c in
/-- **The hypothesis `NonvanishingLocusDescent` is a theorem.**  Each tensor power of an
invertible module on a stage is invertible, hence of finite presentation (clause 2 of
[Stacks Project, Tag 0B8M] followed by [Stacks Project, Tag 05P2]), and its pullback to the limit
is the corresponding tensor power of the pullback
(`AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso`).  So
`Stacks.AlgebraicGeometry.ModuleLimits.exists_nonvanishingLocus_eq_preimage_of_isLimit` applies,
and that is [Stacks Project, Tag 01ZR] (2). -/
theorem nonvanishingLocusDescent_of_isLimit (hc : IsLimit c) (j : I) (M : (D.obj j).Modules)
    [_root_.AlgebraicGeometry.SheafOfModules.IsInvertible (D.obj j).toRingedSpace.presheaf
      (structureSheafRing (D.obj j).toRingedSpace).property M] :
    NonvanishingLocusDescent D c j M := by
  intro n s
  have hGinv := tensorPower_isInvertible (D.obj j).toRingedSpace.presheaf
    (structureSheafRing (D.obj j).toRingedSpace).property M (n : ℤ)
  have hG : (tensorPower (D.obj j).toRingedSpace.presheaf
      (structureSheafRing (D.obj j).toRingedSpace).property M (n : ℤ)).IsFinitePresentation :=
    @_root_.AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isInvertible
      (D.obj j) _ hGinv
  obtain ⟨k, e, t, hloc⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_nonvanishingLocus_eq_preimage_of_isLimit
      D c hc j _ hG _ (pullbackTensorPowerIso (c.π.app j) M n).symm s
  refine ⟨k, e, SheafOfModules.sectionsMap (pullbackTensorPowerIso (D.map e) M n).hom t, ?_⟩
  exact TopologicalSpace.Opens.ext (hloc.trans (congrArg
    (fun S => (c.π.app k).base ⁻¹' S)
    (nonvanishingLocus_sectionsMap (D.obj k).toRingedSpace
      (pullbackTensorPowerIso (D.map e) M n) t).symm))

include c in
/-- **[Stacks Project, Tag 09MT].**  Let `c` be a limit cone on a cofiltered diagram `D` of
quasi-compact quasi-separated schemes with affine transition morphisms and let `M` be an
invertible module on the stage `D.obj j`.  If the pullback of `M` to `c.pt` is ample, then the
pullback of `M` to some stage over `j` is ample.

This is `exists_isAmple_pullback_map_of_isLimit` with its hypothesis `hdesc` discharged by
`nonvanishingLocusDescent_of_isLimit`, which derives it from [Stacks Project, Tag 01ZR] (2). -/
@[stacks 09MT]
theorem exists_isAmple_pullback_map_of_isLimit_of_qcqs (hc : IsLimit c) (j : I)
    (M : (D.obj j).Modules)
    [_root_.AlgebraicGeometry.SheafOfModules.IsInvertible (D.obj j).toRingedSpace.presheaf
      (structureSheafRing (D.obj j).toRingedSpace).property M]
    (hample : Scheme.Modules.IsAmple c.pt ((Scheme.Modules.pullback (c.π.app j)).obj M)) :
    ∃ (j' : I) (g : j' ⟶ j),
      Scheme.Modules.IsAmple (D.obj j') ((Scheme.Modules.pullback (D.map g)).obj M) :=
  exists_isAmple_pullback_map_of_isLimit D c hc j M
    (nonvanishingLocusDescent_of_isLimit D c hc j M) hample

end Stacks.AlgebraicGeometry.AmpleLimit

end
