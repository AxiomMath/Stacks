module

public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Restrict
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.RestrictOpen

/-!
# Glueing a morphism, and an isomorphism, of inverse systems of modules over an open cover

Let `X` be a scheme and let `S` and `T` be inverse systems of sheaves of `𝒪_X`-modules indexed by
`ℕᵒᵖ`. A morphism `S ⟶ T` of such systems is a family of morphisms of `𝒪_X`-modules, one at each
level, commuting with the transition maps. This file glues such a morphism — and, when the local
data are invertible, such an **isomorphism** — out of morphisms of the termwise restrictions of
`S` and `T` to the members of an open cover of `X`.

The glueing is **levelwise**: nothing is assumed about the shape of the systems, and the
compatibility of the glued morphism with the transition maps of `S` and `T` is not an extra
hypothesis. It is a consequence of the glueing itself: a naturality square for the glued morphism
is an equation between two morphisms of `𝒪_X`-modules whose restrictions to each member of the
cover agree — they agree because the local morphisms are themselves natural — and morphisms of
sheaves of modules are determined by their restrictions to a cover.

The same locality statement, applied one level at a time, upgrades a family of local
*isomorphisms* to a global one: the glued morphism is invertible at each level because
invertibility of a morphism of sheaves of modules is local on the base, and a morphism of inverse
systems invertible at every level is invertible.

The last statement transports this to the category `Coh(X, ℐ)` of coherent `ℐ`-adic systems. That
is a full subcategory of `ℕᵒᵖ ⥤ X.Modules`, so a morphism of coherent adic systems carries no data
beyond the underlying morphism of systems, and the glueing applies verbatim.

## Main definitions

* `Stacks.underlyingObjIso` — the isomorphism of the underlying objects carried by an isomorphism
  in a full subcategory.
* `Stacks.Coherent.localAppOpen` — the action on the sections over an open `V` of `X` of a
  morphism of the restrictions of two `𝒪_X`-modules to an open `U ⊇ V`. This is the shape in which
  the local data of a glueing are compared on the overlaps: both sides of the comparison are maps
  `Γ(M, V) ⟶ Γ(N, V)` for one and the same open `V` of `X`, so no transport along an isomorphism
  of opens appears anywhere.

## Main results

* `Stacks.Coherent.hom_ext_of_restrictCover` — **morphisms of sheaves of modules are determined by
  their restrictions to a cover by open subschemes.**
* `Stacks.Coherent.existsUnique_systemHom_of_restrictCover` — **a morphism of inverse systems
  glues, levelwise, over a cover by open subschemes.** A family of morphisms of the termwise
  restrictions of `S` and `T`, agreeing wherever two members of the cover see the same open of
  `X`, comes from exactly one morphism `S ⟶ T`.
* `Stacks.Coherent.existsUnique_systemHom_of_openCover` — the same for a cover by opens of `X`,
  with the overlap comparison written with `Stacks.Coherent.localAppOpen`.
* `Stacks.Coherent.existsUnique_systemIso_of_openCover` — **an isomorphism of inverse systems
  glues, levelwise, over an open cover**: if each local morphism is invertible, so is the glued
  one.
* `Stacks.Coherent.existsUnique_coherentSystemIso_of_openCover` — **an isomorphism of coherent
  `ℐ`-adic systems glues, levelwise, over an open cover.**
* `Stacks.Coherent.modulesSections_eq_of_locally_eq` — two sections of a sheaf of modules on a
  scheme agreeing near every point of their common domain are equal.
* `Stacks.Coherent.localAppOpen_map_of_le` — the action on the sections over an open is
  compatible with restriction to a smaller open.
* `Stacks.Coherent.localAppOpen_eq_of_locally_eq` and
  `Stacks.Coherent.localAppOpen_eq_of_affineOpens` — **two local actions on the sections over an
  open agree as soon as they agree near every point of it, in particular as soon as they agree
  over every affine open contained in both members of the cover.** This is the locality statement
  that the overlap hypotheses of the two glueings below are quantified over every open for.
* `Stacks.Coherent.existsUnique_hom_of_affineComparison` and
  `Stacks.Coherent.existsUnique_coherentSystemIso_of_affineComparison` — the two glueings with
  their overlap hypotheses weakened to the affine opens.
* `Stacks.Coherent.sectionMap_eq_of_locally_eq`,
  `Stacks.Coherent.sectionMap_eq_of_affineOpens` and
  `Stacks.Coherent.existsUnique_hom_of_cover_affineApp` — the same locality statement and the
  same weakening for an *arbitrary* restriction-compatible family of maps on sections, not only
  for the action of a morphism of restrictions. The local data of a glueing are usually a
  composite of such an action with an identification of charts, which is not itself of that
  shape.
* `Stacks.Coherent.exists_restrictHom_of_app` — **a family of maps on the sections over the opens
  inside `U`, linear and compatible with restriction, is the action on sections of exactly one
  morphism `M|_U ⟶ N|_U`.** This is the converse of `Stacks.Coherent.localAppOpen`.
* `Stacks.Coherent.localAppOpen_eq_of_localApp_eq` — **two local actions on the sections over an
  open agree as soon as they agree at some presentation of that open as an image.** This is the
  bridge from a sheaf-level equation over that open to the overlap hypotheses of the two
  glueings.

## Implementation notes

The index type of the cover lands in the same universe as the scheme. That is inherited from
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover`, which is where the
sheaf condition is used; the invertibility half,
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`, has no such restriction.

The overlap hypothesis of the version stated for a cover by open subschemes quantifies over
*every* open of `X` presented as the image of an open of two of the covering schemes, inherited
from the same source. For a cover by opens of `X` that collapses: every open `V ≤ U i` is the
image of `U i ⁻¹ᵁ V`, and
`Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_congr` says the comparison does not depend on
which preimage is chosen, so the hypothesis is equivalent to the single equation between the two
`Stacks.Coherent.localAppOpen` maps over `V` — the shape that
`Stacks.Modules.exists_coherent_glued_of_basisComparison` produces its chart identifications in,
and the shape `Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_cover_app` consumes.

Invertibility is *not* glued by glueing an inverse as well. Doing so would need the overlap
hypothesis for the inverses too, and would then owe the two identities; instead the glued morphism
is shown invertible at each level by locality of invertibility, which needs only the local data
already given.

## Use

These glueings are the passage from the affine case of Tag 0889 part (2) to the global statement
`Stacks.Algebraization.exists_unique_algebraization_dual_of_isNoetherian`.

## References

* [Stacks Project, Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)
* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ModuleHomGlue

universe u

namespace Stacks

/-- The isomorphism of the underlying objects carried by an isomorphism in a full subcategory. -/
public def underlyingObjIso {C : Type*} [Category C] {P : ObjectProperty C}
    {A B : P.FullSubcategory} (e : A ≅ B) : A.obj ≅ B.obj where
  hom := e.hom.hom
  inv := e.inv.hom
  hom_inv_id := ObjectProperty.isoHom_inv_id_hom e
  inv_hom_id := ObjectProperty.isoInv_hom_id_hom e

end Stacks

namespace Stacks.Coherent

/-! ### Locality of morphisms of sheaves of modules -/

/-- **Morphisms of sheaves of modules are determined by their restrictions to a cover by open
subschemes.** This is the separation half of the glueing
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover`, and it is deduced
from its uniqueness clause: the restrictions of `u` are a compatible family of local data, by
`Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_restrictFunctor_map_eq`, so both `u` and `v`
are *the* morphism that family glues to. -/
public theorem hom_ext_of_restrictCover {Y : Scheme.{u}} {ι : Type u} {Z : ι → Scheme.{u}}
    (g : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (g i)]
    (hg : ⨆ i, g i ''ᵁ (⊤ : (Z i).Opens) = ⊤) {M N : Y.Modules} (u v : M ⟶ N)
    (h : ∀ i, (Scheme.Modules.restrictFunctor (g i)).map u =
      (Scheme.Modules.restrictFunctor (g i)).map v) : u = v := by
  obtain ⟨φ, -, huniq⟩ := existsUnique_hom_of_restrict_cover g hg
    (fun i => (Scheme.Modules.restrictFunctor (g i)).map u)
    (fun i j _ _ _ h₁ h₂ => localApp_restrictFunctor_map_eq (g i) (g j) u h₁ h₂)
  exact (huniq u fun _ => rfl).trans (huniq v fun i => (h i).symm).symm

/-- **The action on the sections over an open of `X` of a morphism of the restrictions to a larger
open.** For `V ≤ U` the open `V` is the image of `U.ι ⁻¹ᵁ V` under the inclusion of `U`, so
`Stacks.AlgebraicGeometry.ModuleHomGlue.localApp` applies at that presentation. Writing the map on
`Γ(M, V)` rather than on the sections of the restriction is what lets two such maps coming from
two different members of a cover be compared by an equation: both are maps between the same two
modules of sections. -/
public def localAppOpen {X : Scheme.{u}} (U : X.Opens) {M N : X.Modules}
    (ψ : M.restrict U.ι ⟶ N.restrict U.ι) {V : X.Opens} (hV : V ≤ U) : Γ(M, V) ⟶ Γ(N, V) :=
  localApp U.ι ψ (image_preimage_eq_self U.ι (hV.trans U.ι_image_top.ge))

/-- The restriction of a morphism `φ : M ⟶ N` to an open `U` acts on the sections over an open
`V ≤ U` as `φ` itself. This is what makes the overlap hypothesis of the glueing checkable, and the
conclusion usable. -/
public theorem localAppOpen_restrictFunctor_map {X : Scheme.{u}} (U : X.Opens)
    {M N : X.Modules} (φ : M ⟶ N) {V : X.Opens} (hV : V ≤ U) :
    localAppOpen U ((Scheme.Modules.restrictFunctor U.ι).map φ) hV = φ.app V :=
  localApp_restrictFunctor_map U.ι φ _

/-- `Stacks.Coherent.localAppOpen` is `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp` at any
presentation of `V` as an image, since by
`Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_congr` the latter does not depend on the
presentation. -/
public theorem localApp_eq_localAppOpen {X : Scheme.{u}} (U : X.Opens) {M N : X.Modules}
    (ψ : M.restrict U.ι ⟶ N.restrict U.ι) {W : U.toScheme.Opens} {V : X.Opens}
    (hWV : U.ι ''ᵁ W = V) (hV : V ≤ U) :
    localApp U.ι ψ hWV = localAppOpen U ψ hV :=
  localApp_congr U.ι ψ hWV _

/-! ### Glueing a morphism of inverse systems -/

/-- **A morphism of inverse systems of sheaves of modules glues, levelwise, over a cover by open
subschemes.** Let `g i : Z i ⟶ X` be open immersions whose images cover `X`, and let `S` and `T`
be inverse systems of `𝒪_X`-modules indexed by `ℕᵒᵖ`. A family of morphisms
`S|_{Z i} ⟶ T|_{Z i}` of the termwise restrictions, agreeing wherever two members of the cover
see the same open of `X`, comes from exactly one morphism `S ⟶ T`.

Each level is glued separately, by
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover`. Commutation of the
resulting family with the transition maps is then automatic: both composites in a naturality
square restrict, along each `g i`, to the two sides of a naturality square for the local morphism
`ψ i`, so they agree by `Stacks.Coherent.hom_ext_of_restrictCover`. Nothing about the indexing
category `ℕᵒᵖ` is used, so no induction on the level appears.

Unconditional: `X` is an arbitrary scheme, the covering morphisms are arbitrary open immersions,
and `S` and `T` are arbitrary inverse systems of sheaves of modules. -/
public theorem existsUnique_systemHom_of_restrictCover {X : Scheme.{u}} {ι : Type u}
    {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ X) [∀ i, IsOpenImmersion (g i)]
    (hg : ⨆ i, g i ''ᵁ (⊤ : (Z i).Opens) = ⊤) {S T : ℕᵒᵖ ⥤ X.Modules}
    (ψ : ∀ i, S ⋙ Scheme.Modules.restrictFunctor (g i) ⟶
      T ⋙ Scheme.Modules.restrictFunctor (g i))
    (hψ : ∀ (i j : ι) (n : ℕᵒᵖ) (W₁ : (Z i).Opens) (W₂ : (Z j).Opens) (V : X.Opens)
      (h₁ : g i ''ᵁ W₁ = V) (h₂ : g j ''ᵁ W₂ = V),
      localApp (g i) ((ψ i).app n) h₁ = localApp (g j) ((ψ j).app n) h₂) :
    ∃! φ : S ⟶ T, ∀ i, Functor.whiskerRight φ (Scheme.Modules.restrictFunctor (g i)) = ψ i := by
  choose φ hφ huniq using fun n : ℕᵒᵖ => existsUnique_hom_of_restrict_cover g hg
    (fun i => (ψ i).app n) (fun i j W₁ W₂ V h₁ h₂ => hψ i j n W₁ W₂ V h₁ h₂)
  refine ⟨{ app := φ
            naturality := fun n m h =>
              hom_ext_of_restrictCover g hg _ _ fun i => ?_ },
    fun i => NatTrans.ext (funext fun n => hφ n i),
    fun φ' hφ' => NatTrans.ext (funext fun n => huniq n _ fun i =>
      congrArg (fun z => NatTrans.app z n) (hφ' i))⟩
  rw [Functor.map_comp, Functor.map_comp, hφ n i, hφ m i]
  exact (ψ i).naturality h

/-- **A morphism of inverse systems of sheaves of modules glues, levelwise, over a cover of `X` by
opens.** The overlap comparison is a single equation over each open `V` contained in two members
of the cover, between the two actions of the local morphisms on `Γ(S_n, V)`.

This is `Stacks.Coherent.existsUnique_systemHom_of_restrictCover` for the cover by the inclusions
of the `U j`; the overlap hypotheses match because
`Stacks.Coherent.localApp_eq_localAppOpen` identifies the comparison at an arbitrary presentation
of `V` as an image with the one over `V` itself. -/
public theorem existsUnique_systemHom_of_openCover {X : Scheme.{u}} {J : Type u}
    (U : J → X.Opens) (hU : IsOpenCover U) {S T : ℕᵒᵖ ⥤ X.Modules}
    (ψ : ∀ j, S ⋙ Scheme.Modules.restrictFunctor (U j).ι ⟶
      T ⋙ Scheme.Modules.restrictFunctor (U j).ι)
    (hψ : ∀ (i j : J) (n : ℕᵒᵖ) (V : X.Opens) (hVi : V ≤ U i) (hVj : V ≤ U j),
      localAppOpen (U i) ((ψ i).app n) hVi = localAppOpen (U j) ((ψ j).app n) hVj) :
    ∃! φ : S ⟶ T, ∀ j, Functor.whiskerRight φ (Scheme.Modules.restrictFunctor (U j).ι) = ψ j := by
  have hg : ⨆ j, (U j).ι ''ᵁ (⊤ : (U j).toScheme.Opens) = ⊤ := by
    simp only [Scheme.Opens.ι_image_top]
    exact hU
  refine existsUnique_systemHom_of_restrictCover (fun j => (U j).ι) hg ψ
    fun i j n W₁ W₂ V h₁ h₂ => ?_
  have hVi : V ≤ U i := h₁.symm.le.trans ((U i).ι_image_le W₁)
  have hVj : V ≤ U j := h₂.symm.le.trans ((U j).ι_image_le W₂)
  exact (localApp_eq_localAppOpen (U i) ((ψ i).app n) h₁ hVi).trans
    ((hψ i j n V hVi hVj).trans
      (localApp_eq_localAppOpen (U j) ((ψ j).app n) h₂ hVj).symm)

/-! ### Glueing an isomorphism of inverse systems -/

/-- **An isomorphism of inverse systems of sheaves of modules glues, levelwise, over an open
cover.** A family of isomorphisms of the termwise restrictions of `S` and `T` to the members of an
open cover of `X`, whose actions on the sections agree over every open contained in two members,
comes from exactly one isomorphism `S ≅ T`.

The underlying morphism is glued by
`Stacks.Coherent.existsUnique_systemHom_of_openCover`. It is invertible at each level because its
restriction to each member of the cover is, being the corresponding component of a local
isomorphism, and invertibility of a morphism of sheaves of modules is local on the base
(`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`); a morphism of inverse
systems invertible at every level is invertible. So only the overlap agreement of the local
isomorphisms themselves is needed — none for their inverses. -/
public theorem existsUnique_systemIso_of_openCover {X : Scheme.{u}} {J : Type u}
    (U : J → X.Opens) (hU : IsOpenCover U) {S T : ℕᵒᵖ ⥤ X.Modules}
    (ε : ∀ j, S ⋙ Scheme.Modules.restrictFunctor (U j).ι ≅
      T ⋙ Scheme.Modules.restrictFunctor (U j).ι)
    (hε : ∀ (i j : J) (n : ℕᵒᵖ) (V : X.Opens) (hVi : V ≤ U i) (hVj : V ≤ U j),
      localAppOpen (U i) ((ε i).hom.app n) hVi = localAppOpen (U j) ((ε j).hom.app n) hVj) :
    ∃! e : S ≅ T, ∀ j,
      Functor.isoWhiskerRight e (Scheme.Modules.restrictFunctor (U j).ι) = ε j := by
  obtain ⟨φ, hφ, huniq⟩ :=
    existsUnique_systemHom_of_openCover U hU (fun j => (ε j).hom) hε
  have happ : ∀ (j : J) (n : ℕᵒᵖ),
      (Scheme.Modules.restrictFunctor (U j).ι).map (φ.app n) = (ε j).hom.app n :=
    fun j n => congrArg (fun z => NatTrans.app z n) (hφ j)
  have hiso : IsIso φ := by
    rw [NatTrans.isIso_iff_isIso_app]
    refine fun n => Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict
      (φ.app n) U hU fun j => ?_
    rw [happ j n]
    exact NatIso.isIso_app_of_isIso (ε j).hom n
  refine ⟨asIso φ, fun j => Iso.ext (hφ j), fun e he => Iso.ext (huniq e.hom fun j => ?_)⟩
  exact congrArg Iso.hom (he j)

/-- **An isomorphism of coherent `ℐ`-adic systems glues, levelwise, over an open cover.** Let `X`
be a locally Noetherian scheme, `ℐ` a quasi-coherent sheaf of ideals on `X` and `S`, `T` coherent
`ℐ`-adic systems. A family of isomorphisms `S|_{U j} ≅ T|_{U j}` in `Coh(U j, ℐ|_{U j})`, indexed
by an open cover of `X` and agreeing on the sections over every open contained in two members,
comes from exactly one isomorphism `S ≅ T` in `Coh(X, ℐ)` restricting to each of them.

`Coh(X, ℐ)` is a full subcategory of `ℕᵒᵖ ⥤ X.Modules`, so a morphism of coherent adic systems is
a morphism of the underlying systems and nothing more, and the restriction functor of coherent
adic systems acts as termwise restriction. So this is
`Stacks.Coherent.existsUnique_systemIso_of_openCover` read through
`CategoryTheory.ObjectProperty.isoMk`; the defining properties of a coherent adic system play no
part in the glueing, only in the statement. -/
public theorem existsUnique_coherentSystemIso_of_openCover {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData) {J : Type u} (U : J → X.Opens)
    (hU : IsOpenCover U) {S T : CoherentAdicSystems I}
    (ε : ∀ j, (restrictFunctor I (U j).ι).obj S ≅ (restrictFunctor I (U j).ι).obj T)
    (hε : ∀ (i j : J) (n : ℕᵒᵖ) (V : X.Opens) (hVi : V ≤ U i) (hVj : V ≤ U j),
      localAppOpen (U i) ((ε i).hom.hom.app n) hVi =
        localAppOpen (U j) ((ε j).hom.hom.app n) hVj) :
    ∃! d : S ≅ T, ∀ j, (restrictFunctor I (U j).ι).map d.hom = (ε j).hom := by
  obtain ⟨e, he, huniq⟩ := existsUnique_systemIso_of_openCover (S := S.obj) (T := T.obj) U hU
    (fun j => underlyingObjIso (ε j)) hε
  refine ⟨ObjectProperty.isoMk (IsCoherentAdicSystem I) e,
    fun j => ObjectProperty.hom_ext _ (congrArg Iso.hom (he j)),
    fun d hd => Iso.ext (ObjectProperty.hom_ext _ (congrArg Iso.hom
      (huniq (underlyingObjIso d) fun j => Iso.ext ?_)))⟩
  exact (ObjectProperty.ι (IsCoherentAdicSystem (I.comap (U j).ι))).congr_map (hd j)

/-! ### Locality: agreement on a basis of opens is agreement on all opens -/

/-- **Two sections of a sheaf of modules on a scheme which agree near every point of their common
domain are equal.** This is the separation half of the sheaf axiom,
`TopCat.Sheaf.eq_of_locally_eq'`, read for `AlgebraicGeometry.Scheme.Modules`, whose sections over
an open *are* the sections of its underlying `Ab`-valued presheaf. -/
public theorem modulesSections_eq_of_locally_eq {X : Scheme.{u}} (N : X.Modules) (V : X.Opens)
    (s t : Γ(N, V))
    (h : ∀ x ∈ V, ∃ (V' : X.Opens) (hle : V' ≤ V), x ∈ V' ∧
      (Scheme.Modules.presheaf N).map (homOfLE hle).op s =
        (Scheme.Modules.presheaf N).map (homOfLE hle).op t) : s = t := by
  choose! V' hle hx heq using h
  exact TopCat.Sheaf.eq_of_locally_eq' (⟨Scheme.Modules.presheaf N, N.isSheaf⟩ : TopCat.Sheaf _ _)
    (fun x : {x : X.carrier // x ∈ V} => V' x.1) V (fun x => homOfLE (hle x.1 x.2))
    (fun x hx' => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx'⟩, hx x hx'⟩) s t
    fun x => heq x.1 x.2

/-- **The action on the sections over an open is compatible with restriction to a smaller open.**
This is `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_map` read through
`Stacks.Coherent.localApp_eq_localAppOpen` at both presentations. -/
public theorem localAppOpen_map_of_le {X : Scheme.{u}} (U : X.Opens) {M N : X.Modules}
    (ψ : M.restrict U.ι ⟶ N.restrict U.ι) {V V' : X.Opens} (hVU : V ≤ U) (hV' : V' ≤ V)
    (s : Γ(M, V)) :
    localAppOpen U ψ (hV'.trans hVU) ((Scheme.Modules.presheaf M).map (homOfLE hV').op s) =
      (Scheme.Modules.presheaf N).map (homOfLE hV').op (localAppOpen U ψ hVU s) := by
  exact localApp_map U.ι ψ _ _ hV' s

/-- **The two local actions on the sections over an open agree as soon as they agree near every
point of it.** The two sides are maps between the same two modules of sections, so they agree as
soon as they agree on every section; and two sections of `N` agreeing near every point are equal,
by `Stacks.Coherent.modulesSections_eq_of_locally_eq`. Pushing a section down to a smaller open
is `Stacks.Coherent.localAppOpen_map_of_le` on both sides.

This is what turns an overlap comparison checked on a *basis* of opens into one holding over
every open, which is the form the overlap hypotheses of
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_cover_app` and of
`Stacks.Coherent.existsUnique_coherentSystemIso_of_openCover` are stated in. -/
public theorem localAppOpen_eq_of_locally_eq {X : Scheme.{u}} {U U' : X.Opens}
    {M N : X.Modules} (ψ : M.restrict U.ι ⟶ N.restrict U.ι)
    (ψ' : M.restrict U'.ι ⟶ N.restrict U'.ι) {V : X.Opens} (hVU : V ≤ U) (hVU' : V ≤ U')
    (h : ∀ x ∈ V, ∃ (V' : X.Opens) (hle : V' ≤ V), x ∈ V' ∧
      localAppOpen U ψ (hle.trans hVU) = localAppOpen U' ψ' (hle.trans hVU')) :
    localAppOpen U ψ hVU = localAppOpen U' ψ' hVU' := by
  ext s
  refine modulesSections_eq_of_locally_eq N V _ _ fun x hx => ?_
  obtain ⟨V', hle, hxV', hVeq⟩ := h x hx
  refine ⟨V', hle, hxV', ?_⟩
  rw [← localAppOpen_map_of_le U ψ hVU hle s, ← localAppOpen_map_of_le U' ψ' hVU' hle s, hVeq]

/-- **Agreement over the affine opens is agreement over every open.** The affine opens form a
basis (`AlgebraicGeometry.Scheme.isBasis_affineOpens`), so this is
`Stacks.Coherent.localAppOpen_eq_of_locally_eq` with the neighbourhoods taken affine. -/
public theorem localAppOpen_eq_of_affineOpens {X : Scheme.{u}} {U U' : X.Opens}
    {M N : X.Modules} (ψ : M.restrict U.ι ⟶ N.restrict U.ι)
    (ψ' : M.restrict U'.ι ⟶ N.restrict U'.ι)
    (h : ∀ (k : X.affineOpens) (hkU : k.1 ≤ U) (hkU' : k.1 ≤ U'),
      localAppOpen U ψ hkU = localAppOpen U' ψ' hkU')
    {V : X.Opens} (hVU : V ≤ U) (hVU' : V ≤ U') :
    localAppOpen U ψ hVU = localAppOpen U' ψ' hVU' := by
  refine localAppOpen_eq_of_locally_eq ψ ψ' hVU hVU' fun x hx => ?_
  obtain ⟨t, ⟨k, hk, rfl⟩, hxk, hkV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
  exact ⟨k, hkV, hxk, h ⟨k, hk⟩ (hkV.trans hVU) (hkV.trans hVU')⟩

/-- **An isomorphism of coherent `ℐ`-adic systems glues over an open cover from agreement on the
affine opens alone.** This is
`Stacks.Coherent.existsUnique_coherentSystemIso_of_openCover` with its overlap hypothesis weakened
from every open contained in two members of the cover to every *affine* open contained in two of
them, by `Stacks.Coherent.localAppOpen_eq_of_affineOpens`. -/
public theorem existsUnique_coherentSystemIso_of_affineComparison {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData) {J : Type u} (U : J → X.Opens)
    (hU : IsOpenCover U) {S T : CoherentAdicSystems I}
    (ε : ∀ j, (restrictFunctor I (U j).ι).obj S ≅ (restrictFunctor I (U j).ι).obj T)
    (hε : ∀ (i j : J) (n : ℕᵒᵖ) (k : X.affineOpens) (hki : k.1 ≤ U i) (hkj : k.1 ≤ U j),
      localAppOpen (U i) ((ε i).hom.hom.app n) hki =
        localAppOpen (U j) ((ε j).hom.hom.app n) hkj) :
    ∃! d : S ≅ T, ∀ j, (restrictFunctor I (U j).ι).map d.hom = (ε j).hom :=
  existsUnique_coherentSystemIso_of_openCover I U hU ε
    fun i j n _ hVi hVj => localAppOpen_eq_of_affineOpens _ _ (fun k => hε i j n k) hVi hVj

/-- **A morphism of sheaves of modules glues over an open cover from agreement on the affine opens
alone.** This is `Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_cover_app` with its
overlap hypothesis weakened to the affine opens: the local data are the actions on sections of
morphisms of the restrictions, so
`Stacks.Coherent.localAppOpen_eq_of_affineOpens` upgrades agreement there to agreement
everywhere. -/
public theorem existsUnique_hom_of_affineComparison {X : Scheme.{u}} {M N : X.Modules}
    {ι : Type u} {U : ι → X.Opens} (hU : ⨆ i, U i = ⊤)
    (ψ : ∀ i, M.restrict (U i).ι ⟶ N.restrict (U i).ι)
    (hψ : ∀ (i j : ι) (k : X.affineOpens) (hki : k.1 ≤ U i) (hkj : k.1 ≤ U j),
      localAppOpen (U i) (ψ i) hki = localAppOpen (U j) (ψ j) hkj) :
    ∃! φ : M ⟶ N, ∀ (i : ι) (V : X.Opens) (hV : V ≤ U i),
      Scheme.Modules.Hom.app φ V = localAppOpen (U i) (ψ i) hV :=
  existsUnique_hom_of_cover_app hU (fun i _ hV => localAppOpen (U i) (ψ i) hV)
    (fun i _ _ r s => localApp_smul (U i).ι (ψ i) _ r s)
    (fun i _ _ hV hWV s => localAppOpen_map_of_le (U i) (ψ i) hV hWV s)
    fun i j _ hVi hVj => localAppOpen_eq_of_affineOpens _ _ (fun k => hψ i j k) hVi hVj

/-! ### Locality for an arbitrary family of maps on sections -/

/-- **Two families of maps on sections, each compatible with restriction, agree over an open as
soon as they agree near every point of it.** This is
`Stacks.Coherent.localAppOpen_eq_of_locally_eq` for an arbitrary restriction-compatible family
rather than for the action of a morphism of restrictions: that action is one such family, but the
local data of a glueing are often a composite of one with an identification of charts, and such a
composite is not itself of that shape.

The two sides are maps between the same two modules of sections, so they agree as soon as they
agree on every section, and two sections of `N` agreeing near every point are equal by
`Stacks.Coherent.modulesSections_eq_of_locally_eq`. -/
public theorem sectionMap_eq_of_locally_eq {X : Scheme.{u}} {M N : X.Modules} {U U' : X.Opens}
    (g : ∀ V : X.Opens, V ≤ U → (Γ(M, V) ⟶ Γ(N, V)))
    (g' : ∀ V : X.Opens, V ≤ U' → (Γ(M, V) ⟶ Γ(N, V)))
    (hg : ∀ (V W : X.Opens) (hV : V ≤ U) (hWV : W ≤ V) (s : Γ(M, V)),
      g W (hWV.trans hV) ((Scheme.Modules.presheaf M).map (homOfLE hWV).op s) =
        (Scheme.Modules.presheaf N).map (homOfLE hWV).op (g V hV s))
    (hg' : ∀ (V W : X.Opens) (hV : V ≤ U') (hWV : W ≤ V) (s : Γ(M, V)),
      g' W (hWV.trans hV) ((Scheme.Modules.presheaf M).map (homOfLE hWV).op s) =
        (Scheme.Modules.presheaf N).map (homOfLE hWV).op (g' V hV s))
    {V : X.Opens} (hVU : V ≤ U) (hVU' : V ≤ U')
    (h : ∀ x ∈ V, ∃ (V' : X.Opens) (hle : V' ≤ V), x ∈ V' ∧
      g V' (hle.trans hVU) = g' V' (hle.trans hVU')) :
    g V hVU = g' V hVU' := by
  ext s
  refine modulesSections_eq_of_locally_eq N V _ _ fun x hx => ?_
  obtain ⟨V', hle, hxV', hVeq⟩ := h x hx
  refine ⟨V', hle, hxV', ?_⟩
  rw [← hg V V' hVU hle s, ← hg' V V' hVU' hle s, hVeq]

/-- **Agreement over the affine opens is agreement over every open**, for an arbitrary
restriction-compatible family of maps on sections. The affine opens form a basis
(`AlgebraicGeometry.Scheme.isBasis_affineOpens`), so this is
`Stacks.Coherent.sectionMap_eq_of_locally_eq` with the neighbourhoods taken affine. -/
public theorem sectionMap_eq_of_affineOpens {X : Scheme.{u}} {M N : X.Modules} {U U' : X.Opens}
    (g : ∀ V : X.Opens, V ≤ U → (Γ(M, V) ⟶ Γ(N, V)))
    (g' : ∀ V : X.Opens, V ≤ U' → (Γ(M, V) ⟶ Γ(N, V)))
    (hg : ∀ (V W : X.Opens) (hV : V ≤ U) (hWV : W ≤ V) (s : Γ(M, V)),
      g W (hWV.trans hV) ((Scheme.Modules.presheaf M).map (homOfLE hWV).op s) =
        (Scheme.Modules.presheaf N).map (homOfLE hWV).op (g V hV s))
    (hg' : ∀ (V W : X.Opens) (hV : V ≤ U') (hWV : W ≤ V) (s : Γ(M, V)),
      g' W (hWV.trans hV) ((Scheme.Modules.presheaf M).map (homOfLE hWV).op s) =
        (Scheme.Modules.presheaf N).map (homOfLE hWV).op (g' V hV s))
    (h : ∀ (k : X.affineOpens) (hkU : k.1 ≤ U) (hkU' : k.1 ≤ U'), g k.1 hkU = g' k.1 hkU')
    {V : X.Opens} (hVU : V ≤ U) (hVU' : V ≤ U') :
    g V hVU = g' V hVU' := by
  refine sectionMap_eq_of_locally_eq g g' hg hg' hVU hVU' fun x hx => ?_
  obtain ⟨t, ⟨k, hk, rfl⟩, hxk, hkV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
  exact ⟨k, hkV, hxk, h ⟨k, hk⟩ (hkV.trans hVU) (hkV.trans hVU')⟩

/-- **The glueing of morphisms of sheaves of modules on sections, with the overlap hypothesis
weakened to the affine opens.** This is
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_cover_app` with its agreement
hypothesis required only over the affine opens contained in two members of the cover;
`Stacks.Coherent.sectionMap_eq_of_affineOpens` upgrades that to agreement over every open, using
the restriction-compatibility that the glueing already asks for. -/
public theorem existsUnique_hom_of_cover_affineApp {X : Scheme.{u}} {M N : X.Modules}
    {ι : Type u} {U : ι → X.Opens} (hU : ⨆ i, U i = ⊤)
    (g : ∀ (i : ι) (V : X.Opens), V ≤ U i → (Γ(M, V) ⟶ Γ(N, V)))
    (hsmul : ∀ (i : ι) (V : X.Opens) (hV : V ≤ U i) (r : Γ(X, V)) (s : Γ(M, V)),
      g i V hV (r • s) = r • g i V hV s)
    (hres : ∀ (i : ι) (V W : X.Opens) (hV : V ≤ U i) (hWV : W ≤ V) (s : Γ(M, V)),
      g i W (hWV.trans hV) ((Scheme.Modules.presheaf M).map (homOfLE hWV).op s) =
        (Scheme.Modules.presheaf N).map (homOfLE hWV).op (g i V hV s))
    (hg : ∀ (i j : ι) (k : X.affineOpens) (hki : k.1 ≤ U i) (hkj : k.1 ≤ U j),
      g i k.1 hki = g j k.1 hkj) :
    ∃! φ : M ⟶ N, ∀ (i : ι) (V : X.Opens) (hV : V ≤ U i),
      Scheme.Modules.Hom.app φ V = g i V hV :=
  existsUnique_hom_of_cover_app hU g hsmul hres
    fun i j _ hVi hVj =>
      sectionMap_eq_of_affineOpens (g i) (g j) (hres i) (hres j) (fun k => hg i j k) hVi hVj

/-! ### A morphism of the restrictions to an open from its action on sections -/

/-- The action on the sections over an open of a morphism whose action on sections is `g` is `g`,
at any presentation of that open as an image. The presentation is a hypothesis so that
substituting it reduces `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp` to
`Stacks.AlgebraicGeometry.ModuleHomGlue.appImage`, which is the action itself. -/
private theorem localApp_eq_of_app {X : Scheme.{u}} (U : X.Opens) {M N : X.Modules}
    (ψ : M.restrict U.ι ⟶ N.restrict U.ι)
    (g : ∀ V : X.Opens, V ≤ U → (Γ(M, V) ⟶ Γ(N, V)))
    (hψ : ∀ A : U.toScheme.Opens,
      Scheme.Modules.Hom.app ψ A = g (U.ι ''ᵁ A) (U.ι_image_le A))
    {A : U.toScheme.Opens} {V : X.Opens} (hAV : U.ι ''ᵁ A = V) (hV : V ≤ U) :
    localApp U.ι ψ hAV = g V hV := by
  subst hAV
  exact hψ A

/-- **A family of maps on the sections over the opens inside `U`, linear and compatible with
restriction, is the action on sections of exactly one morphism of the restrictions to `U`.**

This is the converse of `Stacks.Coherent.localAppOpen`, and it is the direction base did not
have: `Stacks.AlgebraicGeometry.ModuleHomGlue.localModuleHomOfApp` already packages such a family
as a `TopCat.Sheaf.LocalModuleHom`, whose only consumer is the glueing over a whole *cover*, so
there was no passage from the family to a morphism `M|_U ⟶ N|_U` on a single open. The docstring
of `localModuleHomOfApp` states that the two are "the same thing"; this is that statement, with
the round-trip identity against `Stacks.Coherent.localAppOpen` as the characterizing property, so
that one can move freely between the two presentations.

It is proved by the glueing itself, applied on the scheme `U` to the one-element cover `{⊤}`:
there the agreement hypothesis is vacuous, and what the glueing returns is a morphism of the
restrictions whose action on the sections over an open of `U` is the given family at the image of
that open. Transporting the linearity across the restriction is
`AlgebraicGeometry.Scheme.Modules.smul_restrictAppIso_hom_apply` — the scalars of a restriction
are those of the ambient scheme read through
`AlgebraicGeometry.Scheme.Hom.appIso`, so linearity over `Γ(X, V)` is linearity over
`Γ(U, ·)` after that transport — and the compatibility with restriction is the given one at the
images, the two morphisms of opens agreeing because the category of opens is thin. -/
public theorem exists_restrictHom_of_app {X : Scheme.{u}} (U : X.Opens) {M N : X.Modules}
    (g : ∀ V : X.Opens, V ≤ U → (Γ(M, V) ⟶ Γ(N, V)))
    (hsmul : ∀ (V : X.Opens) (hV : V ≤ U) (r : Γ(X, V)) (s : Γ(M, V)),
      g V hV (r • s) = r • g V hV s)
    (hres : ∀ (V W : X.Opens) (hV : V ≤ U) (hWV : W ≤ V) (s : Γ(M, V)),
      g W (hWV.trans hV) ((Scheme.Modules.presheaf M).map (homOfLE hWV).op s) =
        (Scheme.Modules.presheaf N).map (homOfLE hWV).op (g V hV s)) :
    ∃! ψ : M.restrict U.ι ⟶ N.restrict U.ι,
      ∀ (V : X.Opens) (hV : V ≤ U), localAppOpen U ψ hV = g V hV := by
  obtain ⟨ψ, hψ, huniq⟩ := Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_cover_app
    (X := U.toScheme) (M := M.restrict U.ι) (N := N.restrict U.ι)
    (ι := PUnit.{u+1}) (U := fun _ => (⊤ : U.toScheme.Opens)) (by simp)
    (fun _ A _ => g (U.ι ''ᵁ A) (U.ι_image_le A))
    (fun _ A _ r s => by
      have h₁ := Scheme.Modules.smul_restrictAppIso_hom_apply U.ι M A r s
      have h₂ := Scheme.Modules.smul_restrictAppIso_hom_apply U.ι N A r
        (g (U.ι ''ᵁ A) (U.ι_image_le A) s)
      refine Eq.trans (congrArg (fun y => (g (U.ι ''ᵁ A) (U.ι_image_le A)) y) h₁) ?_
      exact (hsmul (U.ι ''ᵁ A) (U.ι_image_le A)
        ((Scheme.Hom.appIso U.ι A).inv r) s).trans h₂.symm)
    (fun _ A B _ hBA s => hres (U.ι ''ᵁ A) (U.ι ''ᵁ B) (U.ι_image_le A)
      (Scheme.Hom.image_mono U.ι hBA) s)
    (fun _ _ _ _ _ => rfl)
  refine ⟨ψ, fun V hV => ?_, fun ψ' hψ' => huniq ψ' fun _ A _ => ?_⟩
  · exact localApp_eq_of_app U ψ g (fun A => hψ PUnit.unit A le_top) _ hV
  · have h := hψ' (U.ι ''ᵁ A) (U.ι_image_le A)
    rwa [← localApp_eq_localAppOpen U ψ' rfl (U.ι_image_le A)] at h

/-- **Two local actions on the sections over an open agree as soon as they agree at some
presentation of that open as an image.** If `localApp U.ι ψ hB = localApp U'.ι ψ' hB'` for
presentations `hB : U.ι ''ᵁ B = W` and `hB' : U'.ι ''ᵁ B' = W`, then the actions
`Stacks.Coherent.localAppOpen` of `ψ` and `ψ'` on the sections over `W` agree. This is
`Stacks.Coherent.localApp_eq_localAppOpen` on both sides.

It is the bridge from a *sheaf-level* statement over `W` to the overlap hypotheses of the two
glueings, which are phrased with `Stacks.Coherent.localAppOpen`: an equation between morphisms of
the restrictions to `W` yields, after substituting a presentation of `W` as an image, an equation
between the two `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp` maps, and this turns that into
the required equation over `W` itself. Going through the sheaf level is what avoids reading the
terms of a completion on sections, which cannot be done from the projections: those are
epimorphisms of sheaves of modules (`Stacks.Algebraization.epi_completionProjection`), not
surjections on the sections over a fixed open. -/
public theorem localAppOpen_eq_of_localApp_eq {X : Scheme.{u}} {U U' W : X.Opens}
    (hWU : W ≤ U) (hWU' : W ≤ U') {M N : X.Modules}
    (ψ : M.restrict U.ι ⟶ N.restrict U.ι) (ψ' : M.restrict U'.ι ⟶ N.restrict U'.ι)
    {B : U.toScheme.Opens} {B' : U'.toScheme.Opens} (hB : U.ι ''ᵁ B = W)
    (hB' : U'.ι ''ᵁ B' = W) (h : localApp U.ι ψ hB = localApp U'.ι ψ' hB') :
    localAppOpen U ψ hWU = localAppOpen U' ψ' hWU' :=
  (localApp_eq_localAppOpen U ψ hB hWU).symm.trans
    (h.trans (localApp_eq_localAppOpen U' ψ' hB' hWU'))

end Stacks.Coherent

end
