module

public import StacksFrontier.AlgebraicGeometry.Cohomology.CoherentExtension.IdealPowerSections
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CanonicalSectionsInjective

/-!
# The canonical map from ideal-power duals to morphisms on an open complement

Let `X` be a scheme, let `I` be a quasi-coherent sheaf of ideals on `X` given by its
affine-local ideal data, and let `G` and `F` be `𝒪_X`-modules. Writing `U` for the open
complement of the support of `I`, a morphism `φ : I ^ n • G ⟶ F` has a canonical restriction to
a morphism `G|_U ⟶ F|_U`: over `U` the subsheaf `I ^ n • G` has *all* the sections of `G`, so
the inclusion `I ^ n • G ⟶ G` becomes an isomorphism after restriction to `U`, and one
precomposes `φ|_U` with its inverse. These morphisms are compatible with the inclusions
`I ^ (n + 1) • G ⊆ I ^ n • G`, so they assemble into a map

`colim_n Hom(I ^ n • G, F) ⟶ Hom_{𝒪_U}(G|_U, F|_U)`.

This file constructs that map and pins it down by the property that it restricts a
representative. It is the map whose bijectivity is the morphism clause of
[Stacks, Tag 01YB]; bijectivity is not proved here. The sections clause of that tag is the
corresponding statement for `G = 𝒪_X`, whose map is
`Stacks.LocalCohomology.canonicalMapToSections` and whose bijectivity is
`Stacks.LocalCohomology.canonicalMapToSections_bijective_of_isQuasicoherent`.

## Main definitions

* `Stacks.LocalCohomology.restrictSubmoduleIso`: a subsheaf of `G` which has all the sections of
  `G` over every open contained in `V` becomes, after restriction to `V`, isomorphic to `G`.
* `Stacks.LocalCohomology.idealPowerSystemRestrictIso`: the special case `(I ^ n • G)|_U ≅ G|_U`
  for `U = X ∖ V(I)`, phrased at the objects of the ideal-power system.
* `Stacks.LocalCohomology.canonicalMapToHoms`: the canonical map
  `colim_n Hom(I ^ n • G, F) → Hom_{𝒪_U}(G|_U, F|_U)`, bundled with the restriction property
  that characterises it.

## Main results

* `Stacks.LocalCohomology.isIso_restrict_submodule_ι`: the inclusion of such a subsheaf is an
  isomorphism after restriction. It is injective on sections because it is an inclusion, and
  surjective because the subsheaf has every section of `G` on the opens that occur.
* `Stacks.LocalCohomology.restrict_idealPowerSystem_map_comp`: the identifications
  `(I ^ n • G)|_U ≅ G|_U` are compatible with the transition maps of the ideal-power system.

## Implementation notes

No finiteness, coherence or Noetherian hypothesis is used: the map exists for arbitrary
`𝒪_X`-modules `G` and `F` and an arbitrary quasi-coherent sheaf of ideals. All of those
hypotheses belong to the *bijectivity* statement, not to the map.

`canonicalMapToHoms` is bundled as a subtype, for the same reason as
`Stacks.LocalCohomology.canonicalMapToSections`: the accompanying property — that
precomposing the value at the class of `φ` with the restricted inclusion
`(I ^ n • G)|_U ⟶ G|_U` returns `φ|_U` — pins the map down independently of its construction,
so consumers should use only the property.

The sections of `Scheme.Modules.restrict M V.ι` over an open `W` of `V` are by definition the
sections of `M` over `V.ι ''ᵁ W`, which is contained in `V` by
`AlgebraicGeometry.Scheme.Opens.ι_image_le`; that is what makes the two section-wise
verifications behind `isIso_restrict_submodule_ι` immediate, with no gluing.

`Stacks.SheafOfModules.isIso_of_bijective_app` is the same criterion for a general site, but it
is stated for a site `C : Type u` with `Category.{u} C`, which the site `X.Opens` of a scheme —
a preorder, so `Category.{0}` — does not satisfy; the two-line argument is therefore repeated
here at the `X.Modules` spelling rather than imported. DEDUP OWED: a single statement covering
both would be a general fact about `SheafOfModules` and belongs in neither file.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower

universe u

namespace Stacks.LocalCohomology

noncomputable section

variable {X : Scheme.{u}}

/-! ### Restricting a subsheaf which is everything on an open -/

/-- **The inclusion of a subsheaf becomes an isomorphism on an open where the subsheaf is
everything.** If a subsheaf `P` of `G` has all the sections of `G` over every open contained in
`V`, then the restriction of the inclusion `P ⟶ G` to `V` is an isomorphism.

The sections of a restriction over an open `W` of `V` are the sections over `V.ι ''ᵁ W`, which
is contained in `V`; so the inclusion is injective there because it is the inclusion of a
submodule, and surjective there because that submodule is everything. A morphism of sheaves of
modules bijective on all sections is an isomorphism, `X.Modules` being balanced. -/
public theorem isIso_restrict_submodule_ι {G : X.Modules} (P : G.Submodule) (V : X.Opens)
    (hP : ∀ W : X.Opens, W ≤ V → P.toSubmodule.obj (op W) = ⊤) :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map P.ι) := by
  have hinj : ∀ ⦃W : (V.toScheme.Opens)ᵒᵖ⦄,
      Function.Injective (((Scheme.Modules.restrictFunctor V.ι).map P.ι).val.app W) :=
    fun _ _ _ h => Subtype.ext h
  have hsurj : ∀ ⦃W : (V.toScheme.Opens)ᵒᵖ⦄,
      Function.Surjective (((Scheme.Modules.restrictFunctor V.ι).map P.ι).val.app W) :=
    fun W y => ⟨⟨y, Submodule.eq_top_iff'.1
      (hP (V.ι ''ᵁ W.unop) (V.ι_image_le W.unop)) y⟩, rfl⟩
  have _ : Mono ((Scheme.Modules.restrictFunctor V.ι).map P.ι) :=
    (SheafOfModules.forget V.toScheme.ringCatSheaf).mono_of_mono_map
      (PresheafOfModules.mono_of_injective hinj)
  have _ : Epi ((Scheme.Modules.restrictFunctor V.ι).map P.ι) :=
    (SheafOfModules.forget V.toScheme.ringCatSheaf).epi_of_epi_map
      (PresheafOfModules.epi_of_surjective hsurj)
  exact isIso_of_mono_of_epi _

/-- **A subsheaf becomes the whole sheaf after restriction to an open where it is everything.**
The isomorphism of `Stacks.LocalCohomology.isIso_restrict_submodule_ι`, packaged. -/
public noncomputable def restrictSubmoduleIso {G : X.Modules} (P : G.Submodule) (V : X.Opens)
    (hP : ∀ W : X.Opens, W ≤ V → P.toSubmodule.obj (op W) = ⊤) :
    P.toModules.restrict V.ι ≅ G.restrict V.ι :=
  let := isIso_restrict_submodule_ι P V hP
  asIso ((Scheme.Modules.restrictFunctor V.ι).map P.ι)

/-- The forward direction of `restrictSubmoduleIso` is the restricted inclusion. -/
public lemma restrictSubmoduleIso_hom {G : X.Modules} (P : G.Submodule) (V : X.Opens)
    (hP : ∀ W : X.Opens, W ≤ V → P.toSubmodule.obj (op W) = ⊤) :
    (restrictSubmoduleIso P V hP).hom = (Scheme.Modules.restrictFunctor V.ι).map P.ι :=
  rfl

/-! ### The ideal-power subsheaves away from `V(I)` -/

/-- Over any open contained in the complement of `V(I)` the subsheaf `I ^ n • G` has all the
sections of `G`: such an open is disjoint from the support of `I`. -/
public lemma idealPowerMultiple_obj_eq_top_of_le_idealComplement (I : X.IdealSheafData) (n : ℕ)
    (G : X.Modules) (W : X.Opens) (hW : W ≤ idealComplement I) :
    (idealPowerMultiple I n G).toSubmodule.obj (op W) = ⊤ :=
  idealPowerMultiple_obj_eq_top_of_disjoint_support' I n G W fun _ hx => hW hx

/-- **`(I ^ n • G)|_U ≅ G|_U` away from `V(I)`.** On the open complement `U = X ∖ V(I)` the
inclusion of the ideal-power subsheaf `I ^ n • G` into `G` is an isomorphism after restriction
to `U`.

The source is spelled as the object of `Stacks.LocalCohomology.idealPowerSystem` at `n`, which
is the same sheaf of modules, so that this composes with the transition maps of that system
without transport. -/
public noncomputable def idealPowerSystemRestrictIso (I : X.IdealSheafData) (G : X.Modules)
    (n : ℕ) :
    ((idealPowerSystem I G).obj (op n)).restrict (idealComplement I).ι ≅
      G.restrict (idealComplement I).ι :=
  restrictSubmoduleIso (idealPowerMultiple I n G) (idealComplement I)
    (idealPowerMultiple_obj_eq_top_of_le_idealComplement I n G)

/-- The forward direction of `idealPowerSystemRestrictIso` is the restricted inclusion. -/
public lemma idealPowerSystemRestrictIso_hom (I : X.IdealSheafData) (G : X.Modules) (n : ℕ) :
    (idealPowerSystemRestrictIso I G n).hom =
      (Scheme.Modules.restrictFunctor (idealComplement I).ι).map
        (idealPowerMultiple I n G).ι :=
  rfl

/-- The identifications `(I ^ n • G)|_U ≅ G|_U` are compatible with the transition maps of the
ideal-power system: the restricted transition map `I ^ m • G ⟶ I ^ n • G` followed by the
identification at `n` is the identification at `m`.

This is the restriction functor applied to
`Stacks.LocalCohomology.idealPowerSystem_map_comp_ι`. -/
public lemma restrict_idealPowerSystem_map_comp (I : X.IdealSheafData) (G : X.Modules)
    {n m : ℕ} (h : n ≤ m) :
    (Scheme.Modules.restrictFunctor (idealComplement I).ι).map
        ((idealPowerSystem I G).map (homOfLE h).op) ≫
      (idealPowerSystemRestrictIso I G n).hom =
        (idealPowerSystemRestrictIso I G m).hom :=
  ((Scheme.Modules.restrictFunctor (idealComplement I).ι).map_comp
      ((idealPowerSystem I G).map (homOfLE h).op) (idealPowerMultiple I n G).ι).symm.trans
    (congrArg (Scheme.Modules.restrictFunctor (idealComplement I).ι).map
      (idealPowerSystem_map_comp_ι I G n m h))

/-- The inverse identifications absorb the restricted transition maps of the ideal-power
system. This is what makes the legs below a cocone. -/
public lemma restrict_idealPowerSystem_map_comp_inv (I : X.IdealSheafData) (G : X.Modules)
    {n m : ℕ} (h : n ≤ m) :
    (idealPowerSystemRestrictIso I G m).inv ≫
        (Scheme.Modules.restrictFunctor (idealComplement I).ι).map
          ((idealPowerSystem I G).map (homOfLE h).op) =
      (idealPowerSystemRestrictIso I G n).inv := by
  rw [Iso.inv_comp_eq, Iso.eq_comp_inv]
  exact restrict_idealPowerSystem_map_comp I G h

/-! ### Restricting a single homomorphism out of an ideal power -/

/-- **The restriction to `U = X ∖ V(I)` of a morphism `φ : I ^ n • G ⟶ F`, read as a morphism
`G|_U ⟶ F|_U`.** This is `φ|_U` precomposed with the inverse of
`idealPowerSystemRestrictIso`. -/
public noncomputable def restrictIdealPowerHom (I : X.IdealSheafData) {G F : X.Modules} (n : ℕ)
    (φ : (idealPowerSystem I G).obj (op n) ⟶ F) :
    G.restrict (idealComplement I).ι ⟶ F.restrict (idealComplement I).ι :=
  (idealPowerSystemRestrictIso I G n).inv ≫
    (Scheme.Modules.restrictFunctor (idealComplement I).ι).map φ

/-- **The characterising property of `restrictIdealPowerHom`**: precomposing it with the
restricted inclusion `(I ^ n • G)|_U ⟶ G|_U` returns `φ|_U`. -/
public lemma restrict_ι_comp_restrictIdealPowerHom (I : X.IdealSheafData) {G F : X.Modules}
    (n : ℕ) (φ : (idealPowerSystem I G).obj (op n) ⟶ F) :
    (Scheme.Modules.restrictFunctor (idealComplement I).ι).map
        (idealPowerMultiple I n G).ι ≫ restrictIdealPowerHom I n φ =
      (Scheme.Modules.restrictFunctor (idealComplement I).ι).map φ := by
  dsimp only [restrictIdealPowerHom]
  rw [← idealPowerSystemRestrictIso_hom I G n]
  exact (idealPowerSystemRestrictIso I G n).hom_inv_id_assoc _

/-- `restrictIdealPowerHom` is constant along the direct system `n ↦ Hom(I ^ n • G, F)`: a
morphism and its precomposition with an inclusion of ideal powers have the same restriction
to `U`. This is what makes the legs of `canonicalMapToHoms` a cocone. -/
public lemma restrictIdealPowerHom_idealPowerHom_map (I : X.IdealSheafData) (G F : X.Modules)
    {n m : ℕ} (h : n ≤ m) (φ : (idealPowerSystem I G).obj (op n) ⟶ F) :
    restrictIdealPowerHom I m ((idealPowerHom I G F).map (homOfLE h) φ) =
      restrictIdealPowerHom I n φ := by
  rw [idealPowerHom_map_apply I G F h φ]
  dsimp only [restrictIdealPowerHom]
  rw [(Scheme.Modules.restrictFunctor (idealComplement I).ι).map_comp, ← Category.assoc,
    restrict_idealPowerSystem_map_comp_inv I G h]

/-! ### The canonical map to morphisms on the open complement -/

/-- The canonical map `colim_n Hom(I ^ n • G, F) → Hom_{𝒪_U}(G|_U, F|_U)` for
`U = X ∖ V(I)`, bundled with the property that characterises it: the value at the class of
`φ : I ^ n • G ⟶ F`, precomposed with the restricted inclusion `(I ^ n • G)|_U ⟶ G|_U`, is
`φ|_U`.

The map itself is the colimit descent of the cocone whose components are
`restrictIdealPowerHom`; that these form a cocone is
`restrictIdealPowerHom_idealPowerHom_map`, and the characterising property is
`restrict_ι_comp_restrictIdealPowerHom`. Nothing downstream should use the construction, only
the property. -/
public noncomputable def canonicalMapToHoms (I : X.IdealSheafData) (G F : X.Modules) :
    { f : colimit (idealPowerHom I G F) →
        (G.restrict (idealComplement I).ι ⟶ F.restrict (idealComplement I).ι) //
      ∀ (n : ℕ) (φ : (idealPowerSystem I G).obj (op n) ⟶ F),
        (Scheme.Modules.restrictFunctor (idealComplement I).ι).map
            (idealPowerMultiple I n G).ι ≫
          f ((colimit.ι (idealPowerHom I G F) n) φ) =
            (Scheme.Modules.restrictFunctor (idealComplement I).ι).map φ } := by
  classical
  let c : Cocone (idealPowerHom I G F) :=
    { pt := G.restrict (idealComplement I).ι ⟶ F.restrict (idealComplement I).ι
      ι := NatTrans.ofSequence (fun n => TypeCat.ofHom (restrictIdealPowerHom I n))
        (fun n => by
          ext φ
          exact restrictIdealPowerHom_idealPowerHom_map I G F (Nat.le_succ n) φ) }
  refine ⟨(colimit.desc (idealPowerHom I G F) c).hom.toFun, fun n φ => ?_⟩
  have hval : (colimit.desc (idealPowerHom I G F) c).hom.toFun
      ((colimit.ι (idealPowerHom I G F) n) φ) = restrictIdealPowerHom I n φ :=
    congrFun (congrArg (fun g : (idealPowerHom I G F).obj n ⟶ c.pt => g.hom.toFun)
      (colimit.ι_desc c n)) φ
  rw [hval]
  exact restrict_ι_comp_restrictIdealPowerHom I n φ

end

end Stacks.LocalCohomology

end
