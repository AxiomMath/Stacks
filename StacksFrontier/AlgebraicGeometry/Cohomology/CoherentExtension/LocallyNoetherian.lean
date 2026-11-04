module

public import Mathlib.Order.Zorn
public import StacksFrontier.AlgebraicGeometry.Cohomology.CoherentExtension.AffineSeparation
public import StacksFrontier.AlgebraicGeometry.Cohomology.CoherentExtension.MorphismExtension
public import StacksFrontier.AlgebraicGeometry.IntegralReduction.Transport
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjects

/-!
# Extending a morphism of coherent modules on a locally Noetherian scheme

Let `X` be a locally Noetherian scheme, `F` and `G` coherent `𝒪_X`-modules and `U ⊆ X` an open
subscheme. A morphism `φ : F|_U ⟶ G|_U` extends to all of `X` after replacing `F` by a coherent
submodule agreeing with it over `U`: there are a coherent `F'`, a monomorphism `F' ⟶ F` which is
invertible over `U`, and a morphism `F' ⟶ G` restricting to `φ`.

The construction extends the *graph* of `φ`. Inside `H = F ⊞ G` the graph of `φ` is a
quasi-coherent subobject of `H|_U`; Stacks 01PE extends it to a quasi-coherent submodule `K₀ ⊆ H`
agreeing with it over `U`, and what remains is to shrink `K₀` until the first projection
`K₀ ⟶ F` is injective on sections over *every* open, not just over `U`. Over `U` it is injective
because `K₀` is the graph there.

That shrinking is a Zorn argument over the opens `V` with `U ≤ V ≤ X` to which the injectivity
has already been extended, and this module is that argument. A single step is
`AlgebraicGeometry.exists_submodule_eq_of_injective_sup_affine`: it extends the injectivity across
one affine open, by replacing the submodule with `ℐ ^ m` of it for `ℐ` the ideal of the closed
complement of `V`. One affine open at a time is all that a scheme which is not quasi-compact
allows, since both the Artin–Rees constant and the exponent annihilating a torsion sheaf are
uniform only over a finite affine cover.

## Main definitions

* `AlgebraicGeometry.SubmoduleExtension` — the data the Zorn argument runs over: an open
  containing `U`, a quasi-coherent submodule agreeing with a given one over `U`, and the
  injectivity of a morphism on its sections over that open.

## Main results

* `AlgebraicGeometry.SubmoduleExtension.bddAbove_of_isChain` — every nonempty chain of such data
  is bounded above.
* `AlgebraicGeometry.exists_submodule_injective_of_isLocallyNoetherian` — the Zorn conclusion:
  the injectivity extends to the whole scheme.
* `AlgebraicGeometry.exists_coherent_submodule_extension_of_isLocallyNoetherian` — **Tag 0FD0**.

## Implementation notes

The submodules the Zorn argument carries are submodules of `H` over the whole of `X`, not over
the open `V` reached so far, and they are compared by their sections over the opens contained in
`V`. Nothing is glued: the ideal `ℐ` is the unit ideal over `V`, so the single step leaves the
sections over `V` untouched by itself, and no open of an open subscheme is ever identified with
an open of `X`.

Two places still need an extension across `V`. The upper bound of a chain is the infimum of the
*comaps along their own opens* of the chain's submodules — the comap is what makes the infimum
still agree with each member over that member's open, since membership in a comap along `V` is
decided over `V` — and that infimum is quasi-coherent only over the union of the chain, so Stacks
01PE is applied once more to replace it by a globally quasi-coherent submodule agreeing with it
there. The agreement is read off from 01PE's compatibility by comparing the images of the
sections (`AlgebraicGeometry.imageSubmodule`).

## References

* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
* [Stacks Project, Tag 0FD0](https://stacks.math.columbia.edu/tag/0FD0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.Tag01YEIntegralReduction (isIso_restrictFunctor_map_of_forall_app
  isIso_app_of_isIso_restrictFunctor_map)

universe u

namespace AlgebraicGeometry

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A submodule of a quasi-coherent module on a locally Noetherian scheme which is quasi-coherent
over an open `V` agrees over `V` with a globally quasi-coherent submodule. -/
private theorem exists_isQuasicoherent_submodule_eq_of_restrict [IsLocallyNoetherian X]
    {H : X.Modules} [H.IsQuasicoherent] (L : H.Submodule) (V : X.Opens)
    (hLqc : ((Scheme.Modules.restrictFunctor V.ι).obj
      (L.toSheafOfModules : X.Modules)).IsQuasicoherent) :
    ∃ K : H.Submodule, K.toSheafOfModules.IsQuasicoherent ∧
      ∀ W : X.Opens, W ≤ V → K.toSubmodule.obj (op W) = L.toSubmodule.obj (op W) := by
  classical
  have hmono : Mono ((Scheme.Modules.restrictFunctor V.ι).map
      (L.ι : (L.toSheafOfModules : X.Modules) ⟶ H)) :=
    mono_of_val_app_injective _ fun _ _ _ hab => Subtype.ext hab
  set ψ : ((Scheme.Modules.restrictFunctor V.ι).obj (L.toSheafOfModules : X.Modules)) ⟶
    (Scheme.Modules.restrictFunctor V.ι).obj H := (Scheme.Modules.restrictFunctor V.ι).map L.ι
  have hGqc : (Subobject.mk ψ : V.toScheme.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).prop_of_iso
      (Subobject.underlyingIso ψ).symm hLqc
  obtain ⟨C, hCqc, e, he⟩ :=
    exists_quasicoherentSubobject_restrict V.ι H (Subobject.mk ψ) hGqc
  have hCqc' : (C : X.Modules).IsQuasicoherent := hCqc
  set β : ((Scheme.Modules.restrictFunctor V.ι).obj (C : X.Modules)) ⟶
      (Scheme.Modules.restrictFunctor V.ι).obj (L.toSheafOfModules : X.Modules) :=
    e.hom ≫ (Subobject.underlyingIso ψ).hom with hβ
  have hβiso : IsIso β := by
    rw [hβ]
    infer_instance
  have hstar : (Scheme.Modules.restrictFunctor V.ι).map C.arrow = β ≫ ψ := by
    rw [hβ, Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk ψ, he]
  have hstar' : ψ = inv β ≫ (Scheme.Modules.restrictFunctor V.ι).map C.arrow := by
    rw [hstar, IsIso.inv_hom_id_assoc]
  have key : ∀ W' : V.toScheme.Opens, (imageSubmodule C.arrow).toSubmodule.obj
      (op (V.ι ''ᵁ W')) = L.toSubmodule.obj (op (V.ι ''ᵁ W')) := by
    intro W'
    rw [imageSubmodule_obj C.arrow inferInstance (V.ι ''ᵁ W'),
      ← range_submodule_ι_app L (V.ι ''ᵁ W')]
    refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
    · obtain ⟨x, rfl⟩ := hy
      exact ⟨β.val.app (op W') x, congrArg (fun m => m.val.app (op W') x) hstar.symm⟩
    · obtain ⟨z, rfl⟩ := hy
      exact ⟨(inv β).val.app (op W') z,
        (congrArg (fun m => m.val.app (op W') z) hstar').symm⟩
  refine ⟨imageSubmodule C.arrow, isQuasicoherent_imageSubmodule C.arrow, fun W hW => ?_⟩
  have hWeq : V.ι ''ᵁ (V.ι ⁻¹ᵁ W) = W :=
    (TopologicalSpace.Opens.functor_map_eq_inf V W).trans (inf_eq_left.mpr hW)
  exact hWeq ▸ key (V.ι ⁻¹ᵁ W)

/-- The data a Zorn argument extending the injectivity of `p` runs over: an open `dom` containing
`U`, together with a quasi-coherent submodule of `H` which agrees with `K₀` over `U` and on whose
sections over the opens contained in `dom` the morphism `p` is injective. -/
structure SubmoduleExtension (H F : X.Modules) (p : H ⟶ F) (U : X.Opens) (K₀ : H.Submodule) where
  /-- the open over which the morphism is already injective on the submodule -/
  dom : X.Opens
  /-- the submodule of `H` -/
  submodule : H.Submodule
  /-- the open reached so far contains `U` -/
  le_dom : U ≤ dom
  /-- the submodule is quasi-coherent -/
  isQuasicoherent : submodule.toSheafOfModules.IsQuasicoherent
  /-- the submodule still agrees with the one it started from over `U` -/
  obj_eq : ∀ W : X.Opens, W ≤ U →
    submodule.toSubmodule.obj (op W) = K₀.toSubmodule.obj (op W)
  /-- the morphism kills no nonzero section of the submodule over an open contained in `dom` -/
  injective : ∀ W : X.Opens, W ≤ dom → ∀ s ∈ submodule.toSubmodule.obj (op W),
    (p.val.app (op W)) s = 0 → s = 0

namespace SubmoduleExtension

variable {H F : X.Modules} {p : H ⟶ F} {U : X.Opens} {K₀ : H.Submodule}

/-- One extension refines another when its open is larger and the two submodules have the same
sections over the opens contained in the smaller one. -/
instance : Preorder (SubmoduleExtension H F p U K₀) where
  le D D' := D.dom ≤ D'.dom ∧ ∀ W : X.Opens, W ≤ D.dom →
    D.submodule.toSubmodule.obj (op W) = D'.submodule.toSubmodule.obj (op W)
  le_refl _ := ⟨le_refl _, fun _ _ => rfl⟩
  le_trans _ _ _ h h' :=
    ⟨h.1.trans h'.1, fun W hW => (h.2 W hW).trans (h'.2 W (hW.trans h.1))⟩

/-- `D ≤ D'` holds exactly when the open of `D` is contained in that of `D'` and the two submodules
have the same sections over every open contained in the open of `D`. -/
theorem le_def {D D' : SubmoduleExtension H F p U K₀} :
    D ≤ D' ↔ D.dom ≤ D'.dom ∧ ∀ W : X.Opens, W ≤ D.dom →
      D.submodule.toSubmodule.obj (op W) = D'.submodule.toSubmodule.obj (op W) :=
  Iff.rfl

/-- The infimum of the comaps along their own opens of the submodules of a chain of extensions
agrees with each member of the chain over that member's open. -/
private theorem iInf_comapOpen_obj_eq {c : Set (SubmoduleExtension H F p U K₀)}
    (hc : IsChain (· ≤ ·) c)
    {D : SubmoduleExtension H F p U K₀} (hD : D ∈ c) {W : X.Opens} (hW : W ≤ D.dom) :
    (⨅ D' : c, ((D' : SubmoduleExtension H F p U K₀).submodule).comapOpen
      (D' : SubmoduleExtension H F p U K₀).dom).toSubmodule.obj (op W) =
      D.submodule.toSubmodule.obj (op W) := by
  refine le_antisymm (fun s hs => ?_) (fun s hs => ?_)
  · exact (SheafOfModules.Submodule.comapOpen_obj_of_le _ hW).le
      ((mem_iInf_submodule_obj _ (op W) s).1 hs ⟨D, hD⟩)
  · refine (mem_iInf_submodule_obj _ (op W) s).2 fun D' => ?_
    refine (SheafOfModules.Submodule.mem_comapOpen_iff _ _ _ s).2 ?_
    have hres := val_map_mem_submodule D.submodule
      (CategoryTheory.homOfLE (inf_le_left : W ⊓ (D' : SubmoduleExtension H F p U K₀).dom ≤ W)).op
      hs
    rcases hc.total hD D'.2 with h | h
    · rwa [← h.2 (W ⊓ (D' : SubmoduleExtension H F p U K₀).dom) (inf_le_left.trans hW)]
    · rwa [h.2 (W ⊓ (D' : SubmoduleExtension H F p U K₀).dom) inf_le_right]

/-- **Every nonempty chain of extensions is bounded above.** The infimum of the comaps along their
own opens of the chain's submodules agrees with each member over that member's open — membership
in a comap along an open is decided over that open, and the chain is totally ordered — so it is
quasi-coherent over the union of the chain, and Stacks 01PE replaces it by a globally
quasi-coherent submodule agreeing with it there. -/
theorem bddAbove_of_isChain [IsLocallyNoetherian X] [H.IsCoherent]
    (c : Set (SubmoduleExtension H F p U K₀)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) :
    BddAbove c := by
  classical
  have hHqc : H.IsQuasicoherent := isQuasicoherent_of_isCoherent H
  obtain ⟨D₀, hD₀⟩ := hne
  set V : X.Opens := ⨆ D : c, (D : SubmoduleExtension H F p U K₀).dom with hV
  set L : H.Submodule := ⨅ D : c,
    ((D : SubmoduleExtension H F p U K₀).submodule).comapOpen
      (D : SubmoduleExtension H F p U K₀).dom
  have hleV : ∀ D : c, (D : SubmoduleExtension H F p U K₀).dom ≤ V := fun D =>
    (le_iSup (fun D : c => (D : SubmoduleExtension H F p U K₀).dom) D).trans hV.ge
  have hLagree : ∀ D : SubmoduleExtension H F p U K₀, D ∈ c → ∀ W : X.Opens, W ≤ D.dom →
      L.toSubmodule.obj (op W) = D.submodule.toSubmodule.obj (op W) :=
    fun _ hD _ hW => iInf_comapOpen_obj_eq hc hD hW
  have hLqc : ((Scheme.Modules.restrictFunctor V.ι).obj
      (L.toSheafOfModules : X.Modules)).IsQuasicoherent := by
    refine isQuasicoherent_restrict_iSup_of_agree L
      (fun D : c => (D : SubmoduleExtension H F p U K₀).dom)
      (fun D : c => ((D : SubmoduleExtension H F p U K₀).submodule).comapOpen
        (D : SubmoduleExtension H F p U K₀).dom) (fun D => iInf_le _ D) ?_ ?_
    · intro D W hW
      rw [SheafOfModules.Submodule.comapOpen_obj_of_le _ hW, ← hLagree _ D.2 W hW]
    · intro D
      have := (D : SubmoduleExtension H F p U K₀).isQuasicoherent
      exact isQuasicoherent_restrict_of_le_of_agree
        (SheafOfModules.Submodule.le_comapOpen _ _)
        (fun W hW => (SheafOfModules.Submodule.comapOpen_obj_of_le _ hW).le)
        (Scheme.Modules.isQuasicoherent_restrictFunctor _ _)
  obtain ⟨K, hKqc, hKagree⟩ := exists_isQuasicoherent_submodule_eq_of_restrict L V hLqc
  refine ⟨⟨V, K, D₀.le_dom.trans (hleV ⟨D₀, hD₀⟩), hKqc,
    fun W hW => ?_, fun W hW s hs hps => ?_⟩, fun D hD => ⟨hleV ⟨D, hD⟩, fun W hW => ?_⟩⟩
  · rw [hKagree W (hW.trans (D₀.le_dom.trans (hleV ⟨D₀, hD₀⟩))),
      hLagree D₀ hD₀ W (hW.trans D₀.le_dom), D₀.obj_eq W hW]
  · refine (_root_.Submodule.mem_bot _).1 ((kernelSubmodule_id_obj H (op W)).le
      (mem_submodule_of_locally_mem _ W s fun x hx => ?_))
    obtain ⟨D, hD⟩ := (TopologicalSpace.Opens.mem_iSup).1 (hW hx)
    refine ⟨W ⊓ (D : SubmoduleExtension H F p U K₀).dom, inf_le_left, ⟨hx, hD⟩,
      (kernelSubmodule_id_obj H _).ge ((_root_.Submodule.mem_bot _).2 ?_)⟩
    refine (D : SubmoduleExtension H F p U K₀).injective _ inf_le_right _ ?_ ?_
    · rw [← hLagree _ D.2 _ inf_le_right,
        ← hKagree _ (inf_le_left.trans hW)]
      exact val_map_mem_submodule K (CategoryTheory.homOfLE inf_le_left).op hs
    · rw [PresheafOfModules.naturality_apply p.val (CategoryTheory.homOfLE inf_le_left).op s, hps]
      exact map_zero _
  · rw [← hLagree D hD W hW, hKagree W (hW.trans (hleV ⟨D, hD⟩))]

end SubmoduleExtension

/-- **The Zorn conclusion.** On a locally Noetherian scheme, a morphism out of a coherent module
which is injective on the sections of a quasi-coherent submodule over the opens contained in `U`
stays so after shrinking the submodule, without changing it over `U`, to one on which it is
injective over *every* open. -/
theorem exists_submodule_injective_of_isLocallyNoetherian [IsLocallyNoetherian X]
    (H F : X.Modules) [H.IsCoherent] [F.IsCoherent] (p : H ⟶ F) (U : X.Opens)
    (K₀ : H.Submodule) (hK₀ : K₀.toSheafOfModules.IsQuasicoherent)
    (hinj : ∀ W : X.Opens, W ≤ U → ∀ s ∈ K₀.toSubmodule.obj (op W),
      (p.val.app (op W)) s = 0 → s = 0) :
    ∃ K : H.Submodule, K.toSheafOfModules.IsQuasicoherent ∧
      (∀ W : X.Opens, W ≤ U → K.toSubmodule.obj (op W) = K₀.toSubmodule.obj (op W)) ∧
      ∀ W : X.Opens, ∀ s ∈ K.toSubmodule.obj (op W), (p.val.app (op W)) s = 0 → s = 0 := by
  classical
  have : Nonempty (SubmoduleExtension H F p U K₀) := ⟨⟨U, K₀, le_rfl, hK₀, fun _ _ => rfl, hinj⟩⟩
  obtain ⟨D, hmax⟩ := zorn_le_nonempty (α := SubmoduleExtension H F p U K₀)
    SubmoduleExtension.bddAbove_of_isChain
  have hdom : D.dom = ⊤ := by
    by_contra hdne
    obtain ⟨x, hx⟩ : ∃ x : X, x ∉ D.dom := by
      by_contra hall
      push Not at hall
      exact hdne (TopologicalSpace.Opens.ext (Set.eq_univ_iff_forall.2 hall))
    obtain ⟨-, ⟨W, hW, rfl⟩, hxW, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    obtain ⟨B, hBqc, -, hBagree, hBinj⟩ :=
      exists_submodule_eq_of_injective_sup_affine H F p D.submodule D.isQuasicoherent D.dom
        D.injective ⟨W, hW⟩
    have hle : D ≤ (⟨D.dom ⊔ W, B, D.le_dom.trans le_sup_left, hBqc,
        fun W₀ hW₀ => (hBagree W₀ (hW₀.trans D.le_dom)).trans (D.obj_eq W₀ hW₀),
        hBinj⟩ : SubmoduleExtension H F p U K₀) :=
      ⟨le_sup_left, fun W₀ hW₀ => (hBagree W₀ hW₀).symm⟩
    exact hx ((le_sup_right.trans (hmax hle).1) hxW)
  exact ⟨D.submodule, D.isQuasicoherent, D.obj_eq, fun W => D.injective W (hdom ▸ le_top)⟩

/-- On a locally Noetherian scheme, the graph of a morphism `φ : F|_U ⟶ G|_U` of coherent modules
extends to a quasi-coherent subobject `C` of `F ⊞ G` whose first projection is bijective on
sections over the opens contained in `U`, and whose second projection over `U` is the first
followed by `φ`. -/
private theorem exists_quasicoherent_subobject_graph [IsLocallyNoetherian X]
    (F G : X.Modules) [F.IsCoherent] [G.IsCoherent] (U : X.Opens)
    (φ : F.restrict U.ι ⟶ G.restrict U.ι) :
    ∃ C : Subobject (F ⊞ G), (C : X.Modules).IsQuasicoherent ∧
      (∀ W : X.Opens, W ≤ U →
        Function.Bijective ((C.arrow ≫ biprod.fst : (C : X.Modules) ⟶ F).app W)) ∧
      (Scheme.Modules.restrictFunctor U.ι).map
          (C.arrow ≫ biprod.fst : (C : X.Modules) ⟶ F) ≫ φ =
        (Scheme.Modules.restrictFunctor U.ι).map
          (C.arrow ≫ biprod.snd : (C : X.Modules) ⟶ G) := by
  classical
  have hFqc : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have hGqc : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
  have hRFcoh : ((Scheme.Modules.restrictFunctor U.ι).obj F).IsCoherent :=
    AlgebraicGeometry.Modules.isCoherent_restrict F U
  have hgqc : ((Subobject.mk (graphHom F G U φ) :
      Subobject ((F ⊞ G).restrict U.ι)) : U.toScheme.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      (Subobject.underlyingIso (graphHom F G U φ)).symm (isQuasicoherent_of_isCoherent _)
  obtain ⟨C, hCqc, e₀, he₀⟩ := exists_quasicoherentSubobject_restrict U.ι (F ⊞ G)
    (Subobject.mk (graphHom F G U φ)) hgqc
  have hfst : (Scheme.Modules.restrictFunctor U.ι).map
      (C.arrow ≫ biprod.fst : (C : X.Modules) ⟶ F) =
      e₀.hom ≫ (Subobject.mk (graphHom F G U φ)).arrow ≫
        (Scheme.Modules.restrictFunctor U.ι).map biprod.fst := by
    rw [Functor.map_comp, ← he₀, Category.assoc]
  have hp : IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (C.arrow ≫ biprod.fst : (C : X.Modules) ⟶ F)) := by
    rw [hfst]
    exact IsIso.comp_isIso' inferInstance (isIso_graphSubobject_arrow_comp_fst F G U φ)
  refine ⟨C, hCqc, fun W hW => (ConcreteCategory.isIso_iff_bijective _).1
    (isIso_app_of_isIso_restrictFunctor_map _ U hp W hW), ?_⟩
  rw [hfst, Functor.map_comp, ← he₀]
  simp only [Category.assoc]
  rw [graphSubobject_arrow_comp_snd]

/-- If the second projection of a subobject `C` of `F ⊞ G` is, over `U`, its first projection
followed by `φ`, then so is that of any submodule of `F ⊞ G` agreeing with the image of `C` over
the opens contained in `U`. -/
private theorem restrictFunctor_map_fst_comp_eq_snd_of_obj_eq {F G : X.Modules} {U : X.Opens}
    {φ : F.restrict U.ι ⟶ G.restrict U.ι} {C : Subobject (F ⊞ G)}
    (hkey : (Scheme.Modules.restrictFunctor U.ι).map
        (C.arrow ≫ biprod.fst : (C : X.Modules) ⟶ F) ≫ φ =
      (Scheme.Modules.restrictFunctor U.ι).map (C.arrow ≫ biprod.snd : (C : X.Modules) ⟶ G))
    {K : (F ⊞ G).Submodule} (hK : ∀ W : X.Opens, W ≤ U →
      K.toSubmodule.obj (op W) = (imageSubmodule C.arrow).toSubmodule.obj (op W)) :
    (Scheme.Modules.restrictFunctor U.ι).map (K.ι ≫ (biprod.fst : F ⊞ G ⟶ F)) ≫ φ =
      (Scheme.Modules.restrictFunctor U.ι).map (K.ι ≫ (biprod.snd : F ⊞ G ⟶ G)) := by
  refine Scheme.Modules.hom_ext _ _ fun W' => ?_
  ext a
  have hmem : a.1 ∈ (imageSubmodule C.arrow).toSubmodule.obj (op (U.ι ''ᵁ W')) := by
    rw [← hK _ (U.ι_image_le W')]
    exact a.2
  rw [imageSubmodule_obj C.arrow inferInstance (U.ι ''ᵁ W')] at hmem
  obtain ⟨x, hx⟩ := hmem
  have hkeyW := congrArg (fun m => m.app W' x) hkey
  change φ.app W' ((C.arrow ≫ (biprod.fst : F ⊞ G ⟶ F)).app (U.ι ''ᵁ W') x) =
    (C.arrow ≫ (biprod.snd : F ⊞ G ⟶ G)).app (U.ι ''ᵁ W') x at hkeyW
  show φ.app W' ((biprod.fst : F ⊞ G ⟶ F).app (U.ι ''ᵁ W') a.1) =
    (biprod.snd : F ⊞ G ⟶ G).app (U.ι ''ᵁ W') a.1
  rw [← hx]
  exact hkeyW

/-- **Stacks Project, Tag 0FD0.** Let `F` and `G` be coherent modules on a locally Noetherian
scheme `X`, and let `φ : F|_U ⟶ G|_U` be a morphism over an open subscheme `U`. Then there is a
coherent submodule `F' ⟶ F` agreeing with `F` over `U` and a morphism `φ' : F' ⟶ G` whose
restriction to `U` is `φ` under that agreement.

The submodule is presented as a monomorphism `i : F' ⟶ F` whose restriction to `U` is an
isomorphism `e`; the two equations say that `e` is that restriction and that `φ` is the
restriction of `φ'` read through `e`. -/
@[stacks 0FD0]
theorem exists_coherent_submodule_extension_of_isLocallyNoetherian [IsLocallyNoetherian X]
    (F G : X.Modules) [F.IsCoherent] [G.IsCoherent] (U : X.Opens)
    (φ : F.restrict U.ι ⟶ G.restrict U.ι) :
    ∃ (F' : X.Modules) (_ : F'.IsCoherent) (i : F' ⟶ F) (_ : Mono i)
      (φ' : F' ⟶ G) (e : F'.restrict U.ι ≅ F.restrict U.ι),
      (Scheme.Modules.restrictFunctor U.ι).map i = e.hom ∧
        e.hom ≫ φ = (Scheme.Modules.restrictFunctor U.ι).map φ' := by
  classical
  have hFqc : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have hGqc : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
  have hFft : F.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  have hGft : G.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  have hHft : (F ⊞ G).IsFiniteType := finiteType_biprod F G
  have hHcoh : (F ⊞ G).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isQuasicoherent_isFiniteType
      (F := F ⊞ G)
  obtain ⟨C, hCqc, hbij, hkey⟩ := exists_quasicoherent_subobject_graph F G U φ
  set K₀ : (F ⊞ G).Submodule := imageSubmodule C.arrow with hK₀
  have hinj : ∀ W : X.Opens, W ≤ U → ∀ s ∈ K₀.toSubmodule.obj (op W),
      ((biprod.fst : F ⊞ G ⟶ F).val.app (op W)) s = 0 → s = 0 := by
    intro W hW s hs hps
    rw [hK₀, imageSubmodule_obj C.arrow inferInstance W] at hs
    obtain ⟨x, rfl⟩ := hs
    obtain rfl : x = 0 := (hbij W hW).1 (hps.trans (map_zero _).symm)
    exact map_zero _
  obtain ⟨K, hKqc, hKagree, hKinj⟩ := exists_submodule_injective_of_isLocallyNoetherian
    (F ⊞ G) F biprod.fst U K₀ (isQuasicoherent_imageSubmodule C.arrow) hinj
  have hKcoh : (K.toSheafOfModules : X.Modules).IsCoherent :=
    Stacks.AlgebraicGeometry.IdealPowerSmul.isCoherent_of_isQuasicoherent_submodule
      (F ⊞ G) K hKqc
  have hKinj' : ∀ W : X.Opens, Function.Injective
      ((K.ι ≫ (biprod.fst : F ⊞ G ⟶ F)).val.app (op W)) := fun W a b hab =>
    Subtype.ext (sub_eq_zero.1 (hKinj W (a.1 - b.1)
      (_root_.Submodule.sub_mem _ a.2 b.2) (by rwa [map_sub, sub_eq_zero])))
  have hKmono : Mono (K.ι ≫ (biprod.fst : F ⊞ G ⟶ F)) :=
    mono_of_val_app_injective _ fun W => hKinj' W.unop
  have hiso : IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (K.ι ≫ (biprod.fst : F ⊞ G ⟶ F))) := by
    refine isIso_restrictFunctor_map_of_forall_app _ U fun W hW => ?_
    refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨hKinj' W, fun y => ?_⟩
    · obtain ⟨x, hxy⟩ := (hbij W hW).2 y
      refine ⟨⟨C.arrow.val.app (op W) x, ?_⟩, hxy⟩
      rw [hKagree W hW, hK₀, imageSubmodule_obj C.arrow inferInstance W]
      exact ⟨x, rfl⟩
  exact ⟨K.toSheafOfModules, hKcoh, K.ι ≫ (biprod.fst : F ⊞ G ⟶ F), hKmono,
    K.ι ≫ (biprod.snd : F ⊞ G ⟶ G),
    asIso ((Scheme.Modules.restrictFunctor U.ι).map (K.ι ≫ (biprod.fst : F ⊞ G ⟶ F))), rfl,
    restrictFunctor_map_fst_comp_eq_snd_of_obj_eq hkey hKagree⟩

end AlgebraicGeometry

end
