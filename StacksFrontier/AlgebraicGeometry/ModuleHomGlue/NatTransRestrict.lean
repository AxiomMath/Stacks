module

public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.NatTrans
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Restrict

/-!
# Glueing natural isomorphisms given as isomorphisms of the restricted functors

`StacksFrontier/AlgebraicGeometry/ModuleHomGlue/NatTrans.lean` glues a family of
`Stacks.AlgebraicGeometry.ModuleNatTransGlue.LocalNatTrans`, natural transformations recorded on
the *sections* over the opens below a member of a cover.  A construction, however, produces its
local comparisons as isomorphisms of the *restricted functors*,
`G ⋙ (- |_U) ≅ H ⋙ (- |_U)`.  This file converts between the two and states the glueing in that
shape, with the compatibility hypothesis weakened to the affine opens.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleNatTransGlue.LocalNatTrans.ofRestrict`: the local natural
  transformation on sections cut out of a natural transformation of the restricted functors.

## Main results

* `Stacks.AlgebraicGeometry.ModuleNatTransGlue.LocalNatTrans.app_eq_of_affine`: **two local
  natural transformations which agree on the sections over every affine open contained in both of
  their domains agree on the sections over every open contained in both.**  This is the sheaf
  axiom for the target: the affine opens form a basis, so an open is covered by the affine opens
  it contains, and a section is determined by its restrictions to them.
* `Stacks.AlgebraicGeometry.ModuleNatTransGlue.exists_natIso_of_restrictIso`: **a family of
  isomorphisms of the restricted functors over the members of an open cover, agreeing on the
  sections over the affine opens contained in two members, comes from a natural isomorphism
  `G ≅ H`.**

## Implementation notes

The agreement hypothesis is stated on *affine* opens rather than on all opens because that is
what the consumer can prove: in the Gabriel–Rosenberg reconstruction (Tag 0GPJ) the two local
comparisons over a common open are compared by a rigidity statement which needs the open to be
affine.  Weakening the hypothesis to the affine opens here is exactly the sheaf-theoretic step
that bridges the two.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

universe u v w

namespace Stacks.AlgebraicGeometry.ModuleHomGlue

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {M N P : Y.Modules}

/-- `localApp` is compatible with composition: both sides are the action of the composite on the
sections over the image open, the two identifications being `Iso.refl`. -/
public theorem localApp_comp (ψ : M.restrict f ⟶ N.restrict f) (χ : N.restrict f ⟶ P.restrict f)
    {W : X.Opens} {V : Y.Opens} (hWV : f ''ᵁ W = V) :
    localApp f (ψ ≫ χ) hWV = localApp f ψ hWV ≫ localApp f χ hWV := by
  subst hWV
  exact Scheme.Modules.Hom.comp_app (U := W) ψ χ

/-- `localApp` of the identity is the identity. -/
public theorem localApp_id {W : X.Opens} {V : Y.Opens} (hWV : f ''ᵁ W = V) :
    localApp f (𝟙 (M.restrict f)) hWV = 𝟙 _ := by
  subst hWV
  exact Scheme.Modules.Hom.id_app (U := W) (M.restrict f)

/-- `localApp` of an isomorphism is an isomorphism. -/
public instance isIso_localApp (ψ : M.restrict f ⟶ N.restrict f) [IsIso ψ] {W : X.Opens}
    {V : Y.Opens} (hWV : f ''ᵁ W = V) : IsIso (localApp f ψ hWV) :=
  ⟨localApp f (inv ψ) hWV, by
    rw [← localApp_comp, IsIso.hom_inv_id, localApp_id], by
    rw [← localApp_comp, IsIso.inv_hom_id, localApp_id]⟩

end Stacks.AlgebraicGeometry.ModuleHomGlue

namespace Stacks.AlgebraicGeometry.ModuleNatTransGlue

variable {Y : Scheme.{u}} {C : Type v} [Category.{w} C]

/-- The inclusion of an open subscheme has the open itself as its image. -/
public theorem image_top_ι (U : Y.Opens) : U.ι ''ᵁ (⊤ : U.toScheme.Opens) = U := by simp

/-- The affine opens contained in an open cover that open: they form a basis of the topology of a
scheme, so every point of `V` has an affine open neighbourhood inside `V`. -/
public theorem le_iSup_affineOpens_le (V : Y.Opens) :
    V ≤ ⨆ W : {W : Y.affineOpens // (W : Y.Opens) ≤ V}, (W.1 : Y.Opens) := by
  intro x hx
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W, hW⟩, hWV⟩, hxW⟩

namespace LocalNatTrans

variable {G H : C ⥤ Y.Modules}

/-- **A natural transformation of the restricted functors, read on sections.**  For an open `U`
of `Y` a natural transformation `G ⋙ (- |_U) ⟶ H ⋙ (- |_U)` gives a
`Stacks.AlgebraicGeometry.ModuleNatTransGlue.LocalNatTrans`: the map on the sections over an open
`V ≤ U` is `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp`, the action of the component at the
preimage of `V`, read on the sections over `V` itself.

Linearity and compatibility with restriction are `localApp_smul` and `localApp_map`; naturality
in the object of `C` is the naturality of the given transformation, read through
`Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_restrictFunctor_map`. -/
public def ofRestrict (U : Y.Opens)
    (ψ : G ⋙ Scheme.Modules.restrictFunctor U.ι ⟶ H ⋙ Scheme.Modules.restrictFunctor U.ι) :
    LocalNatTrans G H U where
  app A V hV := ModuleHomGlue.localApp U.ι (ψ.app A)
    (ModuleHomGlue.image_preimage_eq_self U.ι (hV.trans (image_top_ι U).ge))
  app_smul _ _ _ r s := ModuleHomGlue.localApp_smul _ _ _ r s
  app_map _ _ _ _ hWV s := ModuleHomGlue.localApp_map _ _ _ _ hWV s
  app_naturality {A B} φ V hV s := by
    have hnat := ψ.naturality φ
    have h2 := congrArg (fun χ => ModuleHomGlue.localApp U.ι χ
      (ModuleHomGlue.image_preimage_eq_self U.ι (hV.trans (image_top_ι U).ge))) hnat
    simp only [ModuleHomGlue.localApp_comp, Functor.comp_map,
      ModuleHomGlue.localApp_restrictFunctor_map] at h2
    exact congr($h2 s)

/-- The map of `ofRestrict U ψ` on the sections over `V ≤ U` is
`Stacks.AlgebraicGeometry.ModuleHomGlue.localApp` of the component `ψ.app A`. -/
@[simp]
public theorem ofRestrict_app (U : Y.Opens)
    (ψ : G ⋙ Scheme.Modules.restrictFunctor U.ι ⟶ H ⋙ Scheme.Modules.restrictFunctor U.ι)
    (A : C) (V : Y.Opens) (hV : V ≤ U) :
    (ofRestrict U ψ).app A V hV = ModuleHomGlue.localApp U.ι (ψ.app A)
      (ModuleHomGlue.image_preimage_eq_self U.ι (hV.trans (image_top_ι U).ge)) :=
  rfl

/-- **Two local natural transformations which agree on the affine opens agree everywhere.**  If
`t₁` over `U₁` and `t₂` over `U₂` have the same map on the sections over every affine open
contained in both `U₁` and `U₂`, then they have the same map on the sections over every open
contained in both.

An open `V` is covered by the affine opens it contains
(`Stacks.AlgebraicGeometry.ModuleNatTransGlue.le_iSup_affineOpens_le`), and both maps commute
with the restriction to such an affine open; so the two images of a section of `G.obj A` over `V`
have the same restrictions and are equal by the sheaf axiom for `H.obj A`. -/
public theorem app_eq_of_affine {U₁ U₂ : Y.Opens} (t₁ : LocalNatTrans G H U₁)
    (t₂ : LocalNatTrans G H U₂) (A : C)
    (h : ∀ (W : Y.affineOpens) (h₁ : (W : Y.Opens) ≤ U₁) (h₂ : (W : Y.Opens) ≤ U₂),
      t₁.app A W h₁ = t₂.app A W h₂)
    (V : Y.Opens) (hV₁ : V ≤ U₁) (hV₂ : V ≤ U₂) :
    t₁.app A V hV₁ = t₂.app A V hV₂ := by
  ext s
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf (H.obj A).isSheaf
    (ι := {W : Y.affineOpens // (W : Y.Opens) ≤ V}) (fun W => (W.1 : Y.Opens))
    (fun W => W.2) (le_iSup_affineOpens_le V) fun W => ?_
  exact (t₁.app_map A V W hV₁ W.2 s).symm.trans
    ((congr($(h W.1 (W.2.trans hV₁) (W.2.trans hV₂)) _)).trans (t₂.app_map A V W hV₂ W.2 s))

end LocalNatTrans

/-- **A compatible family of isomorphisms of the restricted functors glues to a natural
isomorphism.**  Let `G H : C ⥤ Y.Modules`, let `U` be an open cover of `Y` and suppose given for
each `i` an isomorphism `Θ i : G ⋙ (- |_{U i}) ≅ H ⋙ (- |_{U i})`.  If any two of them induce the
same map on the sections over every affine open contained in both of their domains, then
`G ≅ H`.

The agreement is extended from the affine opens to all opens by
`Stacks.AlgebraicGeometry.ModuleNatTransGlue.LocalNatTrans.app_eq_of_affine`, which makes the
family a `Stacks.AlgebraicGeometry.ModuleNatTransGlue.CompatibleFamily`; the glueing is
`Stacks.AlgebraicGeometry.ModuleNatTransGlue.CompatibleFamily.glueIso`, and each glued component
is invertible because `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp` of an isomorphism is an
isomorphism. -/
public theorem exists_natIso_of_restrictIso {G H : C ⥤ Y.Modules} {ι : Type u} {U : ι → Y.Opens}
    (hU : IsOpenCover U)
    (Θ : ∀ i, G ⋙ Scheme.Modules.restrictFunctor (U i).ι ≅
      H ⋙ Scheme.Modules.restrictFunctor (U i).ι)
    (hagree : ∀ (A : C) (i j : ι) (W : Y.affineOpens) (h₁ : (W : Y.Opens) ≤ U i)
      (h₂ : (W : Y.Opens) ≤ U j),
      (LocalNatTrans.ofRestrict (U i) (Θ i).hom).app A W h₁ =
        (LocalNatTrans.ofRestrict (U j) (Θ j).hom).app A W h₂) :
    Nonempty (G ≅ H) := by
  refine ⟨CompatibleFamily.glueIso
    { trans := fun i => LocalNatTrans.ofRestrict (U i) (Θ i).hom
      agree := fun A i j V hVi hVj =>
        LocalNatTrans.app_eq_of_affine _ _ A (hagree A i j) V hVi hVj } hU fun A i V hV => ?_⟩
  rw [LocalNatTrans.ofRestrict_app]
  infer_instance

end Stacks.AlgebraicGeometry.ModuleNatTransGlue

end
