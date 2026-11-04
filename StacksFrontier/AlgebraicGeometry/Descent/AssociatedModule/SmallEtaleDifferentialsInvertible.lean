module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedDerivation
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.UnitQuasicoherent

/-!
# The key compatibility of Stacks 04CS, and `(Ω_{X/Y})^a` as a retract

Let `f : X ⟶ Y` be a morphism of schemes with `X` in a big étale site `B`.
`AlgebraicGeometry.SmallEtale.differentialsComparison` is the comparison map
`c'' : (Ω_{X/Y})^a ⟶ 𝓕` of Stacks 04CS attached to a derivation `D` of `𝒪_{X_étale}` which
annihilates the functions pulled back from `Y`, and
`AlgebraicGeometry.SmallEtale.associatedDerivation` is the derivation `d^a` of that source's
proof.  This module proves the compatibility between them which the source's proof asserts and
leaves unverified: the comparison map of `d^a` is the identity.

Combined with the naturality of the comparison map in the coefficient sheaf, that gives the
uniqueness half of the universal property of `d^a` — a morphism out of `(Ω_{X/Y})^a` is
determined by its effect on `d^a` — and hence `c'' ≫ c = 𝟙`, exhibiting `(Ω_{X/Y})^a` as a
retract of `Ω_{X_étale/Y_étale}`.

## Main results

* `AlgebraicGeometry.SmallEtale.homEquiv_associatedModuleIsoSectionsSheaf_hom`: the adjunct of
  the isomorphism of Stacks 070S (2) is `AlgebraicGeometry.SmallEtale.sectionsUnit`.  This is
  the bridge which converts the abstract unit of the associated-module adjunction into a
  concrete map on sections, and is what lets the universal derivation `d_{X/Y}` be compared
  with the objectwise values of `d^a`.
* `AlgebraicGeometry.pullbackSectionHom_universalRelativeDerivation`: the pullback to an open
  subscheme `U` of the universal differential `d_{X/Y} a` is `d_{U/Y}` of the restriction of
  `a`, read through Stacks 04BX.  This is the objectwise core.
* `AlgebraicGeometry.SmallEtale.universalRelativeDerivation_postcomp_sectionsUnit`: the small
  Zariski restriction of `d^a` is `d_{X/Y}` followed by the section-pullback map.
* `AlgebraicGeometry.SmallEtale.differentialsComparison_associatedDerivation`: **the key
  compatibility** — the comparison map of `d^a` is the identity of `(Ω_{X/Y})^a`.
* `AlgebraicGeometry.SmallEtale.differentialsComparison_postcomp_associatedDerivation` and
  `AlgebraicGeometry.SmallEtale.postcomp_associatedDerivation_injective`: the uniqueness half
  of the universal property of `d^a`.

## Implementation notes

The three factors of `associatedModuleIsoSectionsSheaf` are discharged in turn.  The first is
`AlgebraicGeometry.SmallEtale.associatedModuleSheafificationIso`, which is
`CategoryTheory.SheafOfModules.pullbackIso` and hence a
`CategoryTheory.Adjunction.leftAdjointUniq`;
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` therefore replaces the unit of the
associated-module adjunction composed with it by the unit of
`CategoryTheory.SheafOfModules.PullbackConstruction.adjunction`, whose forgetful image is
definitionally the presheaf-level pullback unit followed by the sheafification unit.  The
remaining two factors are handled by `CategoryTheory.Adjunction.unit_comp_map_unit_comp` fed
`AlgebraicGeometry.SmallEtale.unit_comp_map_sectionsComparison`, and the sheafification counit
cancels against its unit by the triangle identity.

Each of those steps is stated as a `have` and used by `Eq.trans` or `rw` rather than being
rewritten into the goal directly: the definitions involved are wrappers around the Mathlib ones,
so the Mathlib lemmas apply up to definitional unfolding but their left-hand sides do not match
the goal syntactically.  For the same reason the isomorphism of Stacks 070S (2) is cancelled
pointwise, by `ConcreteCategory.congr_hom` on its `hom_inv_id`, rather than through
`AlgebraicGeometry.SheafOfModules.postcomp_comp_val`, whose statement is instantiated at a
different base ring sheaf and so does not apply here.

`AlgebraicGeometry.SmallEtale.zariskiRestriction` takes the vanishing hypothesis as an explicit
argument, so a rewrite under it has a proof-dependent motive; `simp only` is used where `rw`
cannot abstract that occurrence.

## What remains of the invertibility clause

The results here give one composite, `c'' ≫ c = 𝟙`.  The other, `c ≫ c'' = 𝟙`, is the existence
half of the universal property of `d^a`, i.e. the statement that a `Y`-derivation of
`𝒪_{X_étale}` with values in a sheaf of `𝒪_{X_étale}`-modules is determined by its restriction
to the small Zariski site of `X`.  That is the one genuinely mathematical step of the source's
proof, and it is precisely the verification Stacks 04CS omits; it is not proved here, and so
neither is the canonical isomorphism `(Ω_{X/Y})^a ≅ Ω_{X_étale/Y_étale}`.  No registration is
made for that clause.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S), part (2).
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU), clause (4), the
  associated-module functor and its right adjoint.
* [Stacks Project, Tag 04BX](https://stacks.math.columbia.edu/tag/04BX), the étale localization
  of relative differentials.
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV), the canonical morphism
  on relative differentials and its characterization.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The universal differential of a section pulls back to the universal differential of its
restriction.**  For an open `U` of `X` and a section `a` of `𝒪_X` over `U`, the pullback to the
open subscheme `U` of the universal differential `d_{X/Y} a` is the value of
`AlgebraicGeometry.etaleAssociatedDerivation` on `a` read as a global function on `U`.

This is the characterizing property of the canonical morphism of Stacks 01UV, taken at the open
`U` itself, where `U.ι ⁻¹ᵁ U` is all of the open subscheme: the comparison of Stacks 04BX carries
the left-hand side to `d_{U/Y}` of the restriction of `a`, and
`AlgebraicGeometry.etaleAssociatedDerivation` is `d_{U/Y}` read back through that comparison. -/
theorem pullbackSectionHom_universalRelativeDerivation
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) (a : Γ(X, U)) :
    pullbackSectionHom U.ι (Scheme.Hom.relativeDifferentials f) U ⊤
        (Scheme.Opens.top_le_ι_preimage le_rfl)
        ((Scheme.Hom.universalRelativeDerivation f).d a) =
      etaleAssociatedDerivation f U.ι ((Scheme.Opens.topIso U).inv.hom a) := by
  have hle : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := Scheme.Opens.top_le_ι_preimage le_rfl
  have hchar := Scheme.Hom.isRelativeDifferentialsMap_etaleRelativeDifferentialsIso
    U.ι f (U.ι ≫ f) rfl U a
  -- the restriction of `a` to the open subscheme `U`, in the two spellings
  have hsec : (Scheme.Hom.relativeDifferentials (U.ι ≫ f)).presheaf.map (homOfLE hle).op
        ((Scheme.Hom.universalRelativeDerivation (U.ι ≫ f)).d
          ((Scheme.Hom.app U.ι U).hom a)) =
      (Scheme.Hom.universalRelativeDerivation (U.ι ≫ f)).d
        ((Scheme.Opens.topIso U).inv.hom a) := by
    refine Eq.trans ((Scheme.Hom.universalRelativeDerivation (U.ι ≫ f)).d_map
      (homOfLE hle).op ((Scheme.Hom.app U.ι U).hom a)).symm ?_
    refine congrArg (Scheme.Hom.universalRelativeDerivation (U.ι ≫ f)).d ?_
    refine Eq.trans (ConcreteCategory.comp_apply _ _ a).symm ?_
    exact congrArg (fun g : Γ(X, U) ⟶ Γ(U.toScheme, ⊤) => ConcreteCategory.hom g a)
      (Scheme.Opens.ι_appLE_top U hle)
  -- the 04BX comparison on global sections of the pulled-back universal differential
  have hA : differentialSectionsComparison f U.ι
      (pullbackSectionHom U.ι (Scheme.Hom.relativeDifferentials f) U ⊤ hle
        ((Scheme.Hom.universalRelativeDerivation f).d a)) =
      (Scheme.Hom.universalRelativeDerivation (U.ι ≫ f)).d
        ((Scheme.Opens.topIso U).inv.hom a) := by
    refine Eq.trans ?_ (Eq.trans (congrArg
      ((Scheme.Hom.relativeDifferentials (U.ι ≫ f)).presheaf.map (homOfLE hle).op) hchar) hsec)
    exact PresheafOfModules.naturality_apply
      (Scheme.Hom.etaleRelativeDifferentialsIso U.ι f (U.ι ≫ f) rfl).hom.val
      (homOfLE hle).op
      (((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app
        (Scheme.Hom.relativeDifferentials f)).app U
          ((Scheme.Hom.universalRelativeDerivation f).d a))
  rw [etaleAssociatedDerivation_apply, ← hA]
  exact ((differentialSectionsComparisonIso f U.ι).hom_inv_id_apply _).symm

end AlgebraicGeometry

namespace AlgebraicGeometry.SmallEtale

section

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : S.Modules) [F.IsQuasicoherent]

/-- **The adjunct of the isomorphism of Stacks 070S (2) is the section-pullback map.**
Transposing `AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsSheaf` across the
adjunction between the associated-module functor of Stacks 03DU (4) and restriction to the small
Zariski site of `S` returns `AlgebraicGeometry.SmallEtale.sectionsUnit`, the map which pulls a
section of `𝓕` over an open `U` of `S` back to the open subscheme `U`.

`AlgebraicGeometry.SmallEtale.sectionsComparison` is defined as the adjunct of `sectionsUnit`,
and the isomorphism of 070S (2) is built from it by sheafification; this says that passing back
across the adjunction recovers `sectionsUnit` on the nose. -/
public theorem homEquiv_associatedModuleIsoSectionsSheaf_hom :
    (((associatedModuleAdjunction B S hS).homEquiv F (associatedSectionsSheaf B S hS F))
        (associatedModuleIsoSectionsSheaf B S hS F).hom).val =
      sectionsUnit B S hS F := by
  have hiso : (associatedModuleIsoSectionsSheaf B S hS F).hom =
      (associatedModuleSheafificationIso B S hS).hom.app F ≫
        ((PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf B S hS).obj)).map
            (sectionsComparison B S hS F) ≫
          (PresheafOfModules.sheafificationAdjunction
              (𝟙 (structureSheaf B S hS).obj)).counit.app
            (associatedSectionsSheaf B S hS F)) := rfl
  have hB : (associatedModuleAdjunction B S hS).unit.app F ≫
        (restrictModule B S hS).map ((associatedModuleSheafificationIso B S hS).hom.app F) =
      (SheafOfModules.PullbackConstruction.adjunction.{u} (structureMap B S hS)).unit.app F :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ F
  have hkey := Adjunction.unit_comp_map_unit_comp
      (PresheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B S hS).hom)
      (PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheaf B S hS).obj))
      ((SheafOfModules.forget S.ringCatSheaf).obj F)
      (sectionsComparison B S hS F)
      (unit_comp_map_sectionsComparison B S hS F)
  have hgoal : ((SheafOfModules.PullbackConstruction.adjunction.{u}
          (structureMap B S hS)).unit.app F ≫
        (restrictModule B S hS).map
          ((PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf B S hS).obj)).map
              (sectionsComparison B S hS F) ≫
            (PresheafOfModules.sheafificationAdjunction
                (𝟙 (structureSheaf B S hS).obj)).counit.app
              (associatedSectionsSheaf B S hS F))).val =
      (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
              (structureMap B S hS).hom).unit.app
            ((SheafOfModules.forget S.ringCatSheaf).obj F) ≫
          (PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).map
            ((PresheafOfModules.sheafificationAdjunction
                (𝟙 (structureSheaf B S hS).obj)).unit.app
              ((PresheafOfModules.pullback.{u} (structureMap B S hS).hom).obj
                ((SheafOfModules.forget S.ringCatSheaf).obj F)))) ≫
        (PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).map
          ((SheafOfModules.forget (structureSheaf B S hS) ⋙
              PresheafOfModules.restrictScalars (𝟙 (structureSheaf B S hS).obj)).map
            ((PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf B S hS).obj)).map
              (sectionsComparison B S hS F)))) ≫
        (PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).map
          ((SheafOfModules.forget (structureSheaf B S hS) ⋙
              PresheafOfModules.restrictScalars (𝟙 (structureSheaf B S hS).obj)).map
            ((PresheafOfModules.sheafificationAdjunction
                (𝟙 (structureSheaf B S hS).obj)).counit.app
              (associatedSectionsSheaf B S hS F))) := rfl
  rw [Adjunction.homEquiv_unit, hiso, Functor.map_comp, ← Category.assoc, hB]
  refine hgoal.trans ?_
  have htri : (PresheafOfModules.sheafificationAdjunction
          (𝟙 (structureSheaf B S hS).obj)).unit.app (sectionsPresheafOfModules B S hS F) ≫
        (SheafOfModules.forget (structureSheaf B S hS) ⋙
            PresheafOfModules.restrictScalars (𝟙 (structureSheaf B S hS).obj)).map
          ((PresheafOfModules.sheafificationAdjunction
              (𝟙 (structureSheaf B S hS).obj)).counit.app
            (associatedSectionsSheaf B S hS F)) =
      𝟙 (sectionsPresheafOfModules B S hS F) :=
    Adjunction.right_triangle_components
      (PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheaf B S hS).obj))
      (associatedSectionsSheaf B S hS F)
  rw [hkey, Category.assoc, ← Functor.map_comp, htri]
  exact Eq.trans (congrArg (sectionsUnit B S hS F ≫ ·)
    ((PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).map_id _))
    (Category.comp_id _)

end

section

variable (B : BigEtaleSite.{u}) {X Y : Scheme.{u}} (hX : B.Contains X) (f : X ⟶ Y)

/-- **The small Zariski restriction of `d^a` is `d_{X/Y}` followed by the section-pullback
map.**  Over an open `W` of `X` the restriction of `d^a` to the small Zariski site is, by
definition, the value of `d^a` over the object `W ↪ X` of the small étale site; that value is
`d_{W/Y}` read through Stacks 04BX, and
`AlgebraicGeometry.pullbackSectionHom_universalRelativeDerivation` says that this is the
pullback to `W` of `d_{X/Y}`.

This is the objectwise half of the key compatibility of Stacks 04CS, assembled over the small
Zariski site; the coefficient sheaf is taken in the sections form of `(Ω_{X/Y})^a`. -/
public theorem universalRelativeDerivation_postcomp_sectionsUnit :
    (f.universalRelativeDerivation).postcomp
        (sectionsUnit B X hX (Scheme.Hom.relativeDifferentials f)) =
      zariskiRestriction B hX f (associatedSectionsDerivation B hX f)
        (associatedSectionsDerivation_pullbackSection_eq_zero B hX f) := by
  ext W a
  exact pullbackSectionHom_universalRelativeDerivation f W.unop a

/-- Postcomposing a derivation with a morphism and then with a left inverse of it does nothing. -/
private theorem postcomp_postcomp_of_comp_eq_id
    {C : Type*} [Category C] {R S : Cᵒᵖ ⥤ CommRingCat.{u}} {φ : S ⟶ R}
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (d : M.Derivation' φ) (a : M ⟶ N) (b : N ⟶ M) (h : ∀ V, (a ≫ b).app V = 𝟙 _) :
    (d.postcomp a).postcomp b = d :=
  PresheafOfModules.Derivation.ext (funext fun V => AddMonoidHom.ext fun x =>
    ConcreteCategory.congr_hom (h V) (d.d x))

/-- **The key compatibility of Stacks 04CS.**  The comparison map `c''` attached to the
derivation `d^a` is the identity of `(Ω_{X/Y})^a`.

Together with
`AlgebraicGeometry.SmallEtale.differentialsComparison_postcomp` this says that for any
derivation `D` obtained from `d^a` by postcomposition, the comparison map of `D` is that
postcomposition: in particular, if `D` is the universal derivation of
`Ω_{X_étale/Y_étale}` and `c` is the map with `d^a = D.postcomp c`, then `c'' ≫ c = 𝟙`, so
`(Ω_{X/Y})^a` is a retract of `Ω_{X_étale/Y_étale}`. -/
public theorem differentialsComparison_associatedDerivation :
    differentialsComparison B hX f (associatedDerivation B hX f)
        (associatedDerivation_pullbackSection_eq_zero B hX f) =
      𝟙 (associatedRelativeDifferentials B hX f) := by
  refine (eq_differentialsComparison B hX f (associatedDerivation B hX f)
    (associatedDerivation_pullbackSection_eq_zero B hX f)
    (𝟙 (associatedRelativeDifferentials B hX f)) ?_).symm
  -- `I` is the isomorphism of Stacks 070S (2); postcomposing a derivation with its restriction
  -- to the small Zariski site is injective, so it is enough to check the identity after doing
  -- so, and there both sides are the Zariski restriction of `d^a` in its sections form.
  have hsections : (associatedDerivation B hX f).postcomp
      (associatedModuleIsoSectionsSheaf B X hX
        (Scheme.Hom.relativeDifferentials f)).hom.val =
      associatedSectionsDerivation B hX f :=
    postcomp_postcomp_of_comp_eq_id _ _ _ fun V => by
      erw [← SheafOfModules.comp_val, Iso.inv_hom_id]
      rfl
  have hcancel : ∀ A C : SheafOfModules.SheafDerivation (inverseImageStructureMap f)
        ((restrictModule B X hX).obj (associatedRelativeDifferentials B hX f)),
      A.postcomp ((restrictModule B X hX).map
          (associatedModuleIsoSectionsSheaf B X hX
            (Scheme.Hom.relativeDifferentials f)).hom).val =
        C.postcomp ((restrictModule B X hX).map
          (associatedModuleIsoSectionsSheaf B X hX
            (Scheme.Hom.relativeDifferentials f)).hom).val → A = C := by
    intro A C h
    have hcollapse : ∀ E : SheafOfModules.SheafDerivation (inverseImageStructureMap f)
          ((restrictModule B X hX).obj (associatedRelativeDifferentials B hX f)),
        (E.postcomp ((restrictModule B X hX).map (associatedModuleIsoSectionsSheaf B X hX
              (Scheme.Hom.relativeDifferentials f)).hom).val).postcomp
            ((restrictModule B X hX).map (associatedModuleIsoSectionsSheaf B X hX
              (Scheme.Hom.relativeDifferentials f)).inv).val = E := fun E =>
      postcomp_postcomp_of_comp_eq_id _ _ _ fun V => by
        erw [← SheafOfModules.comp_val, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
          CategoryTheory.Functor.map_id]
        rfl
    exact Eq.trans (hcollapse A).symm (Eq.trans (congrArg (fun E =>
      PresheafOfModules.Derivation.postcomp E ((restrictModule B X hX).map
        (associatedModuleIsoSectionsSheaf B X hX
          (Scheme.Hom.relativeDifferentials f)).inv).val) h) (hcollapse C))
  refine hcancel _ _ ?_
  have hcomb : ((f.universalRelativeDerivation).postcomp
        (((associatedModuleAdjunction B X hX).homEquiv (Scheme.Hom.relativeDifferentials f)
          (associatedRelativeDifferentials B hX f))
            (𝟙 (associatedRelativeDifferentials B hX f))).val).postcomp
      ((restrictModule B X hX).map (associatedModuleIsoSectionsSheaf B X hX
        (Scheme.Hom.relativeDifferentials f)).hom).val =
      (f.universalRelativeDerivation).postcomp
        ((((associatedModuleAdjunction B X hX).homEquiv (Scheme.Hom.relativeDifferentials f)
            (associatedRelativeDifferentials B hX f))
              (𝟙 (associatedRelativeDifferentials B hX f)) ≫
          (restrictModule B X hX).map (associatedModuleIsoSectionsSheaf B X hX
            (Scheme.Hom.relativeDifferentials f)).hom)).val := rfl
  refine Eq.trans hcomb ?_
  rw [← Adjunction.homEquiv_naturality_right, Category.id_comp,
    homEquiv_associatedModuleIsoSectionsSheaf_hom, zariskiRestriction_postcomp]
  simp only [hsections]
  exact universalRelativeDerivation_postcomp_sectionsUnit B hX f

/-- **The comparison map recovers a morphism from its effect on `d^a`.**  For any morphism
`g : (Ω_{X/Y})^a ⟶ 𝓕`, the comparison map of the derivation `d^a` followed by `g` is `g`
itself.

This is the uniqueness half of the universal property of `d^a`: it says that `g` is determined
by `d^a.postcomp g`.  It is
`AlgebraicGeometry.SmallEtale.differentialsComparison_postcomp` combined with the key
compatibility `AlgebraicGeometry.SmallEtale.differentialsComparison_associatedDerivation`. -/
public theorem differentialsComparison_postcomp_associatedDerivation
    {F : SheafOfModules.{u} (structureSheaf B X hX)}
    (g : associatedRelativeDifferentials B hX f ⟶ F) :
    differentialsComparison B hX f ((associatedDerivation B hX f).postcomp g.val)
        (postcomp_pullbackSection_eq_zero B hX f (associatedDerivation B hX f)
          (associatedDerivation_pullbackSection_eq_zero B hX f) g) = g := by
  rw [differentialsComparison_postcomp B hX f (associatedDerivation B hX f)
    (associatedDerivation_pullbackSection_eq_zero B hX f) g,
    differentialsComparison_associatedDerivation B hX f, Category.id_comp]

/-- **A morphism out of `(Ω_{X/Y})^a` is determined by its effect on `d^a`.**  This is the
uniqueness half of the universal property of the derivation `d^a` of Stacks 04CS: at most one
morphism `(Ω_{X/Y})^a ⟶ 𝓕` carries `d^a` to a given derivation of `𝒪_{X_étale}`.

Both morphisms are recovered from that derivation by the comparison map, by
`AlgebraicGeometry.SmallEtale.differentialsComparison_postcomp_associatedDerivation`. -/
public theorem postcomp_associatedDerivation_injective
    {F : SheafOfModules.{u} (structureSheaf B X hX)}
    (g₁ g₂ : associatedRelativeDifferentials B hX f ⟶ F)
    (h : (associatedDerivation B hX f).postcomp g₁.val =
      (associatedDerivation B hX f).postcomp g₂.val) :
    g₁ = g₂ := by
  refine Eq.trans (differentialsComparison_postcomp_associatedDerivation B hX f g₁).symm
    (Eq.trans ?_ (differentialsComparison_postcomp_associatedDerivation B hX f g₂))
  simp only [h]

end

end AlgebraicGeometry.SmallEtale

end
