module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineTildePushforwardUnit

/-!
# The comparison of a quasi-coherent module with its sections is natural

`Stacks.Coherent.affineTildeObjSectionsIso` identifies a quasi-coherent module `N` on an affine
scheme `Z` with the module associated to its global sections. The proof of conclusion (c) of
[Stacks, Tag 0EX3] uses that identification twice over one affine open — once at the structure
sheaf and once at the direct image `q_* 𝒪_P` of the structure sheaf along an affine morphism —
and what joins the two uses is that the identification is **natural**: a morphism of
quasi-coherent modules is carried to the associated map of the modules of sections.

This file proves that naturality and draws the one consequence conclusion (c) consumes: the
canonical map `𝒪_Z ⟶ q_* 𝒪_P` of [Stacks, Tag 01I7], read through the two identifications, is
the module map associated to the ring map it induces on global sections.

## Main results

All in the namespace `Stacks.Coherent` or `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `Stacks.Coherent.evaluation_map_affineTildeObjSectionsIso_hom`: **the global sections of the
  identification are the inverse of the unit** of `Stacks.Coherent.affineTildeAdjunction`. This
  is what makes the identification computable: it is pinned by its value under a faithful
  functor.
* `Stacks.Coherent.affineTildeObjSectionsIso_hom_naturality`: **the identification is natural in
  the quasi-coherent module.**
* `…TopDegreeBaseChange.unitToPushforwardUnit_comp_pushforwardUnitIsoAffineTilde_inv`: **the
  canonical map `𝒪_Z ⟶ q_* 𝒪_P` is the associated map of its global sections**, for an affine
  morphism `q : P ⟶ Z` into an affine scheme. Neither `P` nor the morphism carries a hypothesis
  beyond affineness, and `Z` is an arbitrary affine scheme — in particular an affine *open* of an
  arbitrary scheme.

## Implementation notes

*Why the proofs go through global sections and not through the adjunction.* The identification
is defined as the preimage, under the fully faithful functor
`Stacks.Coherent.affineQuasicoherentSectionsFullyFaithful`, of the inverse of the unit
isomorphism `Stacks.Coherent.affineTildeSectionsIso`. So its defining property is the value of
its image under that functor, and every statement about it is proved by
`Stacks.Coherent.affineQuasicoherentHom_ext`: two morphisms of quasi-coherent modules on an
affine scheme agreeing on global sections are equal. Identifying it with the counit of
`Stacks.Coherent.affineTildeAdjunction` first would cost a triangle identity and buy nothing,
since the counit would then be computed the same way.

*The quasi-coherence of the associated module is an instance and that of `N` is an argument.*
`Stacks.Coherent.affineTilde_quasicoherent` is a theorem rather than an instance, so the
`IsQuasicoherent` hypothesis of `affineQuasicoherentHom_ext` at the source is supplied by `have`;
at the target it is the argument `hN`, which is how `affineTildeObjSectionsIso` itself takes it.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Coherent

variable (Z : Scheme.{u}) [IsAffine Z]

/-- **The global sections of the identification of a quasi-coherent module with the module
associated to its sections are the inverse of the unit** of
`Stacks.Coherent.affineTildeAdjunction`. -/
theorem evaluation_map_affineTildeObjSectionsIso_hom (N : Z.Modules) (hN : N.IsQuasicoherent) :
    (SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).map
        (affineTildeObjSectionsIso Z N hN).hom =
      (affineTildeSectionsIso Z
        ((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).obj N)).inv :=
  (affineQuasicoherentSectionsFullyFaithful Z).map_preimage
    (X := ⟨(affineTilde Z).obj ((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).obj N),
      affineTilde_quasicoherent Z _⟩)
    (Y := ⟨N, hN⟩)
    (affineTildeSectionsIso Z ((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).obj N)).symm.hom

/-- **A quasi-coherent module on an affine scheme is the module of its global sections,
naturally.** For a morphism `u : N₁ ⟶ N₂` of quasi-coherent modules on an affine scheme, the
associated map of the modules of global sections is `u` read through the two identifications
`Stacks.Coherent.affineTildeObjSectionsIso`.

Both sides are morphisms of quasi-coherent modules, so they are equal as soon as their global
sections agree; there the statement is the naturality of the unit of
`Stacks.Coherent.affineTildeAdjunction`, rearranged past the two inverses. -/
theorem affineTildeObjSectionsIso_hom_naturality {N₁ N₂ : Z.Modules}
    (h₁ : N₁.IsQuasicoherent) (h₂ : N₂.IsQuasicoherent) (u : N₁ ⟶ N₂) :
    (affineTilde Z).map ((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).map u) ≫
        (affineTildeObjSectionsIso Z N₂ h₂).hom =
      (affineTildeObjSectionsIso Z N₁ h₁).hom ≫ u := by
  have e₁ : ((affineTilde Z).obj
      ((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).obj N₁)).IsQuasicoherent :=
    affineTilde_quasicoherent Z _
  have := h₂
  have hnat : (SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).map u ≫
      (affineTildeSectionsIso Z
        ((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).obj N₂)).hom =
    (affineTildeSectionsIso Z
        ((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).obj N₁)).hom ≫
      (SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).map
        ((affineTilde Z).map ((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).map u)) :=
    (affineTildeAdjunction Z).unit.naturality
      ((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).map u)
  have core : (SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).map
        ((affineTilde Z).map ((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).map u)) ≫
      (affineTildeSectionsIso Z
        ((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).obj N₂)).inv =
    (affineTildeSectionsIso Z
        ((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).obj N₁)).inv ≫
      (SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).map u :=
    (Iso.comp_inv_eq _).2
      (Eq.trans (Iso.inv_hom_id_assoc (affineTildeSectionsIso Z _) _).symm
        (Eq.trans (congrArg (fun k => (affineTildeSectionsIso Z _).inv ≫ k) hnat.symm)
          (Category.assoc _ _ _).symm))
  refine affineQuasicoherentHom_ext (X := Z)
    (Eq.trans ((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).map_comp _ _)
      (Eq.trans ?_ ((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).map_comp _ _).symm))
  exact Eq.trans
    (congrArg (fun k => (SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).map
        ((affineTilde Z).map ((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).map u)) ≫ k)
      (evaluation_map_affineTildeObjSectionsIso_hom Z N₂ h₂))
    (Eq.trans core
      (congrArg (fun k => k ≫ (SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).map u)
        (evaluation_map_affineTildeObjSectionsIso_hom Z N₁ h₁)).symm)

end Stacks.Coherent

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-- **The canonical map `𝒪_Z ⟶ q_* 𝒪_P` is the module map associated to the ring map it induces
on global sections.** For an affine morphism `q : P ⟶ Z` into an affine scheme `Z`, the two
identifications of `Stacks.Coherent.affineTildeObjSectionsIso` — at the structure sheaf of `Z`
and at `q_* 𝒪_P`, the latter being
`…TopDegreeBaseChange.pushforwardUnitIsoAffineTilde` — carry the associated map of
`Γ(q_* 𝒪_P, ⊤)` over `Γ(Z, ⊤)` to the canonical map of [Stacks, Tag 01I7].

This is the geometric content conclusion (c) of [Stacks, Tag 0EX3] needs over a compatible pair
of affine opens: the tilde of the ring map `Γ(Y', V) ⟶ Γ(Y'', W)` **is** the canonical
`𝒪_V ⟶ (h ∣_ V^W)_* 𝒪_W`. -/
theorem unitToPushforwardUnit_comp_pushforwardUnitIsoAffineTilde_inv {P Z : Scheme.{u}}
    [IsAffine Z] (q : P ⟶ Z) [IsAffineHom q] :
    Scheme.Modules.unitToPushforwardUnit q ≫ (pushforwardUnitIsoAffineTilde q).inv =
      (Stacks.Coherent.affineTildeObjSectionsIso Z (Scheme.unitModule Z)
          inferInstance).inv ≫
        (Stacks.Coherent.affineTilde Z).map
          ((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).map
            (Scheme.Modules.unitToPushforwardUnit q)) := by
  rw [pushforwardUnitIsoAffineTilde, Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
  exact (Stacks.Coherent.affineTildeObjSectionsIso_hom_naturality Z inferInstance
    (Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom q _ inferInstance)
    (Scheme.Modules.unitToPushforwardUnit q)).symm

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
