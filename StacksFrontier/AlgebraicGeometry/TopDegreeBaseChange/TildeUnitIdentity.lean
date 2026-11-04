module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeSectionsBijection

/-!
# The two readings of the unit of the functions on `W` over the functions on `V` agree

Over a compatible pair of affine opens — `V` of `Y'` and `W` of `Y''` with `W ≤ h⁻¹(V)` —
conclusion (c) of [Stacks, Tag 0EX3] is computed twice. The Eilenberg-Watts presentation of
conclusion (b) produces the ring unit `Γ(V, ⊤) ⟶ Γ(Y'', W)`, turned into a map of modules on
`f'⁻¹(V)` by the tilde functor and the pullback; the geometry produces the canonical map
`𝒪_V ⟶ (h ∣_ V^W)_* 𝒪_W` of [Stacks, Tag 01I7], pulled back along `f' ∣_ V`. This file proves
that the two agree.

That identity is the point at which the two computations of conclusion (c) meet. It is what
makes the value of the Eilenberg-Watts comparison on a pure tensor `1 ⊗ x` equal to the value of
the pullback map on cohomology, which is the form the derived side produces.

## Main results

Both in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `toSpanSingleton_comp_sectionsIsoPushforwardUnitSections`: **the ring unit is the map on global
  sections of the canonical map of structure sheaves.** Both are maps of `Γ(V, ⊤)`-modules out of
  the free rank-one module `Γ(V, ⊤)`, so they are determined by their value at `1`, and there
  both are `1`.
* `pullbackTildeUnitIso_inv_comp_pullbackTildeSectionsIso`: **the two readings agree**, as maps
  `𝒪_{f'⁻¹(V)} ⟶ (f' ∣_ V)^* (affineTilde V Γ((h ∣_ V^W)_* 𝒪_W, ⊤))`. Neither base carries a
  hypothesis; only the two opens are affine.

## Implementation notes

*Three known facts do the work, and no computation is left.* The naturality of the crossing,
`…TopDegreeBaseChange.pullbackTildeIsoPullbackAffineTilde_naturality`, moves the tilde of the
ring unit from one spelling to the other; the ring-level identity below replaces it by the map
on global sections of the canonical map of structure sheaves; and the naturality of the
identification of a quasi-coherent module with the module of its sections,
`…TopDegreeBaseChange.unitToPushforwardUnit_comp_pushforwardUnitIsoAffineTilde_inv`, turns that
into the canonical map itself.

*Why the unitor is written through the sections-counit.*
`…TopDegreeBaseChange.pullbackTildeUnitIso` spells the Eilenberg-Watts unitor through
`Stacks.Coherent.affineTildeObjSectionsIso` rather than through `AlgebraicGeometry.tildeSelf`.
Both are canonical, and the Eilenberg-Watts presentation
`…TopDegreeBaseChange.bijective_fromExtendScalarsComp` accepts either, because it takes the
identification of its module as an arbitrary isomorphism; the first is the one the geometric side
produces, so with it the identity below needs no coherence between the two spellings of the
structure sheaf.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-- **The reassociation the identity below needs, on variables of an abstract category.** A
five-fold composite whose middle three factors are known, and whose remaining two factors then
combine, collapses. It is stated at variables because at the concrete spelling the goal is not
type-correct at `implicit` transparency, so neither `rw [Category.assoc]` nor
`simp only [Category.assoc]` fires on it; at variables the reassociation is free and the unifier
meets the concrete spelling only once, at the application. -/
theorem comp_assoc_cancel_middle {C : Type*} [Category C] {A₁ A₂ A₃ A₄ A₅ A₆ : C}
    (q : A₁ ⟶ A₂) (r : A₂ ⟶ A₃) (s : A₃ ⟶ A₄) (t : A₄ ⟶ A₅) (u : A₅ ⟶ A₆)
    {v : A₂ ⟶ A₅} (hv : r ≫ s ≫ t = v) {w : A₁ ⟶ A₆} (hw : q ≫ v ≫ u = w) :
    (q ≫ r) ≫ s ≫ t ≫ u = w := by
  rw [← hw, ← hv]
  simp only [Category.assoc]

variable {Y'' : Scheme.{u}} (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
  (h : Y'' ⟶ S.Y') {V : S.Y'.Opens} {W : Y''.Opens} (hWV : W ≤ h ⁻¹ᵁ V)

/-- **The unit of the ring of `W` over the functions on `V` is the canonical map of structure
sheaves, on global sections.** The `Γ(V, ⊤)`-linear map `r ↦ r • 1` into the functions on `W`,
read through `…TopDegreeBaseChange.sectionsIsoPushforwardUnitSections`, is the map on global
sections of the canonical `𝒪_V ⟶ (h ∣_ V^W)_* 𝒪_W` of [Stacks, Tag 01I7].

Both sides are `Γ(V, ⊤)`-linear maps out of `Γ(V, ⊤)`, so they are determined by their value at
`1`, and there both are `1`: the first because `1 • 1 = 1` and the ring isomorphism
`Γ(Y'', W) ≅ Γ(W, ⊤)` preserves it, the second because a morphism of schemes carries `1` to
`1`. -/
theorem toSpanSingleton_comp_sectionsIsoPushforwardUnitSections :
    ModuleCat.ofHom (LinearMap.toSpanSingleton Γ((V : Scheme), ⊤)
          ((ModuleCat.restrictScalars
            ((h.appLE V W hWV).hom.comp (Scheme.Opens.topIso V).hom.hom)).obj
              (ModuleCat.of Γ(Y'', W) Γ(Y'', W))) (1 : Γ(Y'', W))) ≫
        (sectionsIsoPushforwardUnitSections S h hWV).hom =
      (_root_.SheafOfModules.evaluation (V : Scheme).ringCatSheaf (op ⊤)).map
        (Scheme.Modules.unitToPushforwardUnit (h.resLE V W hWV)) := by
  refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
  refine Eq.trans (congrArg (ModuleCat.Hom.hom
    (sectionsIsoPushforwardUnitSections S h hWV).hom) (one_smul Γ((V : Scheme), ⊤) _)) ?_
  rw [sectionsIsoPushforwardUnitSections,
    ModuleCat.ExtendScalars.restrictScalarsSelfIso_hom_apply]
  have hgoal : (((Scheme.Opens.topIso W).symm.commRingCatIsoToRingEquiv (1 : Γ(Y'', W))) :
      Γ((W : Scheme), ⊤)) = (h.resLE V W hWV).appTop.hom (1 : Γ((V : Scheme), ⊤)) :=
    (map_one _).trans (map_one _).symm
  exact hgoal

variable [IsAffine (V : Scheme)] [IsAffine (W : Scheme)]

/-- **The two readings of a map out of the functions on `V`, pulled back to `f'⁻¹(V)`, agree —
as soon as the map is the canonical one on global sections.** On the left is the Eilenberg-Watts
reading: the unitor of conclusion (b) over `V`, inverted, followed by the pullback of the tilde
of `ψ` and by the comparison of the two tilde functors. On the right is the geometric reading:
the pullback of the canonical map `𝒪_V ⟶ (h ∣_ V^W)_* 𝒪_W` of [Stacks, Tag 01I7], read through
the identification of `(h ∣_ V^W)_* 𝒪_W` with the module associated to its global sections.

The map is a **variable** rather than the ring unit written out, with the one property of it that
is used as the hypothesis `hψ`. That is not a generalization for its own sake: writing the ring
unit out inside the proof makes the elaborator rebuild the restriction of scalars at a second
spelling of the functions on `V`, where the module instance is not found, and the statement is
large enough that re-elaborating it exhausts the budget.

Three facts do the work: the naturality of the crossing, the hypothesis `hψ`, and the
naturality of the identification of a quasi-coherent module with the module of its sections. -/
theorem pullbackTildeUnitIso_inv_comp_pullbackTildeSectionsIso
    (ψ : ModuleCat.of Γ((V : Scheme), ⊤) Γ((V : Scheme), ⊤) ⟶
      (ModuleCat.restrictScalars
        ((h.appLE V W hWV).hom.comp (Scheme.Opens.topIso V).hom.hom)).obj
          (ModuleCat.of Γ(Y'', W) Γ(Y'', W)))
    (hψ : ψ ≫ (sectionsIsoPushforwardUnitSections S h hWV).hom =
      (_root_.SheafOfModules.evaluation (V : Scheme).ringCatSheaf (op ⊤)).map
        (Scheme.Modules.unitToPushforwardUnit (h.resLE V W hWV))) :
    (pullbackTildeUnitIso S.f' V).inv ≫
        (Scheme.Modules.pullback ((S.f' ∣_ V) ≫ (V : Scheme).isoSpec.hom)).map
          ((AlgebraicGeometry.tilde.functor (CommRingCat.of Γ((V : Scheme), ⊤))).map ψ) ≫
        (pullbackTildeSectionsIso S h hWV).hom =
      (Scheme.Modules.pullbackUnitIso (S.f' ∣_ V)).inv ≫
        (Scheme.Modules.pullback (S.f' ∣_ V)).map
          (Scheme.Modules.unitToPushforwardUnit (h.resLE V W hWV) ≫
            (pushforwardUnitIsoAffineTilde (h.resLE V W hWV)).inv) := by
  have hcross := pullbackTildeIsoPullbackAffineTilde_naturality S.f' V ψ
  have hinner := Eq.trans
    (congrArg (fun z => (Stacks.Coherent.affineTildeObjSectionsIso (V : Scheme)
        (Scheme.unitModule (V : Scheme)) inferInstance).inv ≫ z)
      (Eq.trans ((Stacks.Coherent.affineTilde (V : Scheme)).map_comp ψ
          (sectionsIsoPushforwardUnitSections S h hWV).hom).symm
        (congrArg (Stacks.Coherent.affineTilde (V : Scheme)).map hψ)))
    (unitToPushforwardUnit_comp_pushforwardUnitIsoAffineTilde_inv (h.resLE V W hWV)).symm
  have hfinal := Eq.trans
    (congrArg (fun z => (Scheme.Modules.pullback (S.f' ∣_ V)).map
        (Stacks.Coherent.affineTildeObjSectionsIso (V : Scheme)
          (Scheme.unitModule (V : Scheme)) inferInstance).inv ≫ z)
      ((Scheme.Modules.pullback (S.f' ∣_ V)).map_comp
        ((Stacks.Coherent.affineTilde (V : Scheme)).map ψ)
        ((Stacks.Coherent.affineTilde (V : Scheme)).map
          (sectionsIsoPushforwardUnitSections S h hWV).hom)).symm)
    (Eq.trans ((Scheme.Modules.pullback (S.f' ∣_ V)).map_comp _ _).symm
      (congrArg (Scheme.Modules.pullback (S.f' ∣_ V)).map hinner))
  have e1 : (pullbackTildeUnitIso S.f' V).inv =
      (Scheme.Modules.pullbackUnitIso (S.f' ∣_ V)).inv ≫
        (Scheme.Modules.pullback (S.f' ∣_ V)).map
          (Stacks.Coherent.affineTildeObjSectionsIso (V : Scheme)
            (Scheme.unitModule (V : Scheme)) inferInstance).inv ≫
        (pullbackTildeIsoPullbackAffineTilde S.f' V
          (ModuleCat.of Γ((V : Scheme), ⊤) Γ((V : Scheme), ⊤))).inv := rfl
  have e2 : (pullbackTildeSectionsIso S h hWV).hom =
      (pullbackTildeIsoPullbackAffineTilde S.f' V
          ((ModuleCat.restrictScalars
            ((h.appLE V W hWV).hom.comp (Scheme.Opens.topIso V).hom.hom)).obj
              (ModuleCat.of Γ(Y'', W) Γ(Y'', W)))).hom ≫
        (Scheme.Modules.pullback (S.f' ∣_ V)).map
          ((Stacks.Coherent.affineTilde (V : Scheme)).map
            (sectionsIsoPushforwardUnitSections S h hWV).hom) := rfl
  rw [e1, e2]
  exact congrArg (fun z => (Scheme.Modules.pullbackUnitIso (S.f' ∣_ V)).inv ≫ z)
    (comp_assoc_cancel_middle _ _ _ _ _ hcross hfinal)

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
