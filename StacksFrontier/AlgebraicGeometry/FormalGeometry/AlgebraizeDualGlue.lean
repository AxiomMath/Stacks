module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizeDualOverlap
public import StacksFrontier.AlgebraicGeometry.Modules.GluedCoherentOfBasis

/-!
# Glueing the local algebraizations of a map out of a completion

Let `X` be a locally Noetherian scheme, `ℐ` a quasi-coherent sheaf of ideals on `X`, `G` a
coherent `𝒪_X`-module, `(F_n)` a coherent `ℐ`-adic system and `α : G^∧ ⟶ (F_n)` the datum of
Stacks 0889 part (2). Given a local algebraization of `α` over every affine open of `X`, with the
comparisons of any two of them over an affine open contained in both, we glue them to a single
coherent `𝒪_X`-module `M`, and over each affine open we build the local comparison of the
completion of `M` with `(F_n)`.

## Main results

* `Stacks.Algebraization.localAppOpen_map`: the action on the sections over an open of a
  morphism of restrictions is compatible with restriction.
* `Stacks.Algebraization.exists_affineOpen_mem_and_le`: every point of an open has an affine
  open neighbourhood inside it.
* `Stacks.Algebraization.exists_sectionComparison_restrictionCompatible`: the overlap
  comparisons carried to sections, with their cocycle identity and their restriction
  compatibility.
* `Stacks.Algebraization.exists_glued_of_localAlgebraizations`: the coherent module glued from a
  family of local algebraizations, together with the overlap comparisons and their two defining
  identities.
* `Stacks.Algebraization.localAppOpen_id_eq`: the identity acts on sections as the identity.
* `Stacks.Algebraization.exists_restrictIso_of_appEquiv`: a family of linear equivalences of the
  sections over the opens inside `U`, compatible with restriction, is the action on sections of
  an isomorphism of the restrictions to `U`.
* `Stacks.Algebraization.exists_chartIso_of_appEquiv`: the chart identification of a glued
  coherent module, as an isomorphism of coherent modules, together with its action on sections.
* `Stacks.Algebraization.completionRestrictChartIso`: the local comparison of the completion of
  the glued module with the given system over a chart.
* `Stacks.Algebraization.restrictDownIso`: the canonical comparison of the two routes from `X`
  down to an open `W ≤ U`.
* `Stacks.Algebraization.localAppOpen_eq_restrictDown`: the action on the sections over `W` of
  a morphism of the restrictions to `U ⊇ W` is the action of its restriction along `W ⟶ U`.
* `Stacks.Algebraization.localAppOpen_eq_of_restrictDown_eq`: two morphisms of restrictions to
  two different opens act the same way on the sections over a common smaller open as soon as
  their restrictions to it agree.
* `Stacks.Algebraization.localAppOpen_eq_restrictDown_of_le`: the same as
  `Stacks.Algebraization.localAppOpen_eq_restrictDown`, over a yet smaller open.

## Implementation notes

The glued module is produced by `Stacks.Modules.exists_coherent_glued_of_basisComparison` for
the cover of `X` by all of its affine opens, with the affine opens themselves as the basis of
adapted opens.

The morphisms compared over overlaps are built from the terms of a completion, which are
cokernels, so they are determined only at the sheaf level:
`Stacks.Algebraization.epi_completionProjection` is an epimorphism of sheaves of modules, not a
surjection on the sections over a fixed open. The lemma
`Stacks.Algebraization.localAppOpen_eq_restrictDown` and its variants reduce overlap hypotheses
stated on sections to equations between morphisms of sheaves of modules over the overlap.

## References

* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

open Stacks.AlgebraicGeometry.ModuleHomGlue

/-- The action on the sections over an open of a morphism of restrictions is compatible with
restriction. -/
public theorem localAppOpen_map {X : Scheme.{u}} (U : X.Opens) {M N : X.Modules}
    (ψ : M.restrict U.ι ⟶ N.restrict U.ι) {V : X.Opens} (hVU : V ≤ U) (s : Γ(M, U)) :
    Stacks.Coherent.localAppOpen U ψ hVU ((Scheme.Modules.presheaf M).map (homOfLE hVU).op s) =
      (Scheme.Modules.presheaf N).map (homOfLE hVU).op
        (Stacks.Coherent.localAppOpen U ψ le_rfl s) := by
  rw [← Stacks.Coherent.localApp_eq_localAppOpen U ψ
      (image_preimage_eq_self U.ι (hVU.trans U.ι_image_top.ge)) hVU,
    ← Stacks.Coherent.localApp_eq_localAppOpen U ψ U.ι_image_top le_rfl]
  exact localApp_map U.ι ψ _ _ hVU s

/-- Every point of an open of a scheme has an affine open neighbourhood inside it. -/
public theorem exists_affineOpen_mem_and_le {X : Scheme.{u}} (V : X.Opens) (x : X) (hx : x ∈ V) :
    ∃ k : X.affineOpens, x ∈ k.1 ∧ k.1 ≤ V := by
  obtain ⟨t, ⟨W, hW, rfl⟩, hxt, htV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
  exact ⟨⟨W, hW⟩, hxt, htV⟩

/-- `Stacks.Algebraization.localAppOpenEquiv` acts on sections as the action of the forward
morphism. -/
public theorem localAppOpenEquiv_apply {X : Scheme.{u}} (U : X.Opens) {M N : X.Modules}
    (ψ : M.restrict U.ι ≅ N.restrict U.ι) {V : X.Opens} (hV : V ≤ U) (x : Γ(M, V)) :
    localAppOpenEquiv U ψ hV x = Stacks.Coherent.localAppOpen U ψ.hom hV x := rfl

/-- The overlap comparisons carried to sections, with their cocycle identity and their
restriction compatibility: the comparison over a smaller open agrees with the restriction of the
comparison over a larger one, provided the comparisons of coherent modules do. The comparison
over `W` is the action on sections of `Stacks.Algebraization.overlapRestrictIso` of `d`. -/
public theorem exists_sectionComparison_restrictionCompatible {X : Scheme.{u}}
    [IsLocallyNoetherian X] {ι : Type*} (U : ι → X.Opens)
    (F : ∀ i : ι, AlgebraicGeometry.SheafOfModules.CoherentModules (U i).toScheme.ringCatSheaf)
    (good : X.Opens → ι → Prop) (hgood : ∀ (W : X.Opens) (i : ι), good W i → W ≤ U i)
    (d : ∀ (W : X.Opens) (i j : ι) (hi : good W i) (hj : good W j),
      restrictCoherentModules (X.homOfLE (hgood W i hi)) (F i) ≅
        restrictCoherentModules (X.homOfLE (hgood W j hj)) (F j))
    (hcoc : ∀ (W : X.Opens) (i j m : ι) (hi : good W i) (hj : good W j) (hm : good W m),
      d W i j hi hj ≪≫ d W j m hj hm = d W i m hi hm)
    (hdres : ∀ (W W' : X.Opens) (i j : ι) (hi : good W i) (hj : good W j) (hi' : good W' i)
      (hj' : good W' j) (h : W' ≤ W),
      Stacks.Coherent.localAppOpen W'
          (overlapRestrictIso (hgood W' i hi') (hgood W' j hj') (d W' i j hi' hj')).hom le_rfl =
        Stacks.Coherent.localAppOpen W
          (overlapRestrictIso (hgood W i hi) (hgood W j hj) (d W i j hi hj)).hom h) :
    ∃ e : ∀ (W : X.Opens) (i j : ι), good W i → good W j →
        Γ(coherentModulesPushforward (U i).ι (F i), W) ≃ₗ[Γ(X, W)]
          Γ(coherentModulesPushforward (U j).ι (F j), W),
      (∀ (W : X.Opens) (i j m : ι) (hi : good W i) (hj : good W j) (hm : good W m)
          (s : Γ(coherentModulesPushforward (U i).ι (F i), W)),
        e W j m hj hm (e W i j hi hj s) = e W i m hi hm s) ∧
      (∀ (W W' : X.Opens) (i j : ι) (hi : good W i) (hj : good W j) (hi' : good W' i)
        (hj' : good W' j) (h : W' ≤ W)
        (s : Γ(coherentModulesPushforward (U i).ι (F i), W)),
        e W' i j hi' hj'
            ((Scheme.Modules.presheaf (coherentModulesPushforward (U i).ι (F i))).map
              (homOfLE h).op s) =
          (Scheme.Modules.presheaf (coherentModulesPushforward (U j).ι (F j))).map
            (homOfLE h).op (e W i j hi hj s)) ∧
      ∀ (W : X.Opens) (i j : ι) (hi : good W i) (hj : good W j)
        (s : Γ(coherentModulesPushforward (U i).ι (F i), W)),
        e W i j hi hj s = Stacks.Coherent.localAppOpen W
          (overlapRestrictIso (hgood W i hi) (hgood W j hj) (d W i j hi hj)).hom le_rfl s := by
  refine ⟨fun W i j hi hj =>
    localAppOpenEquiv W (overlapRestrictIso (hgood W i hi) (hgood W j hj) (d W i j hi hj))
      le_rfl, fun W i j m hi hj hm s => ?_, fun W W' i j hi hj hi' hj' h s => ?_,
    fun W i j hi hj s => localAppOpenEquiv_apply W _ le_rfl s⟩
  · have hstep := localAppOpen_comp_apply W
      (overlapRestrictIso (hgood W i hi) (hgood W j hj) (d W i j hi hj)).hom
      (overlapRestrictIso (hgood W j hj) (hgood W m hm) (d W j m hj hm)).hom (le_refl W) s
    rw [overlapRestrictIso_comp, hcoc W i j m hi hj hm] at hstep
    exact hstep
  · rw [localAppOpenEquiv_apply, localAppOpenEquiv_apply, hdres W W' i j hi hj hi' hj' h]
    exact localAppOpen_map W _ h s

/-- The coherent module glued from a family of local algebraizations. Let `α : G^∧ ⟶ (F_n)`
be the datum of Stacks 0889 (2) and suppose given, over every affine open `U` of `X`, a local
algebraization `b U : G|_U ⟶ F U` with `β U : (F U)^∧ ≅ (F_n)|_U` whose kernel and cokernel are
annihilated by a power of `ℐ|_U`. Then there is a single coherent `𝒪_X`-module `M` whose
sections over any open of any chart are identified with those of the direct image of that
chart's module, compatibly with restriction and intertwined by the overlap comparisons. The
overlap comparisons `d` and their two defining identities are returned as well. -/
public theorem exists_glued_of_localAlgebraizations {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : ((completionFunctor X I).obj G).obj ⟶ Fsys.obj)
    (F : ∀ i : X.affineOpens,
      AlgebraicGeometry.SheafOfModules.CoherentModules i.1.toScheme.ringCatSheaf)
    (b : ∀ i : X.affineOpens, restrictCoherentModules i.1.ι G ⟶ F i)
    (β : ∀ i : X.affineOpens,
      ((completionFunctor i.1.toScheme (I.comap i.1.ι)).obj (F i)).obj ≅
        ((Stacks.Coherent.restrictFunctor I i.1.ι).obj Fsys).obj)
    (hβ : ∀ i : X.affineOpens, restrictedSystemMapDual i.1.ι I G Fsys α =
      ((completionFunctor i.1.toScheme (I.comap i.1.ι)).map (b i)).hom ≫ (β i).hom)
    (hK : ∀ i : X.affineOpens, IsPowerAnnihilated (I.comap i.1.ι)
      (kernel (C := i.1.toScheme.Modules) (b i).hom))
    (hC : ∀ i : X.affineOpens, IsPowerAnnihilated (I.comap i.1.ι)
      (cokernel (C := i.1.toScheme.Modules) (b i).hom)) :
    ∃ (M : X.Modules)
      (d : ∀ (k i j : X.affineOpens) (hki : k.1 ≤ i.1) (hkj : k.1 ≤ j.1),
        restrictCoherentModules (X.homOfLE hki) (F i) ≅
          restrictCoherentModules (X.homOfLE hkj) (F j))
      (c : ∀ (i : X.affineOpens) (V : X.Opens), V ≤ i.1 →
        (Γ(M, V) ≃ₗ[Γ(X, V)] Γ(coherentModulesPushforward i.1.ι (F i), V))),
      (M.IsQuasicoherent ∧ _root_.SheafOfModules.IsCoherent M) ∧
      (∀ (k i j : X.affineOpens) (hki : k.1 ≤ i.1) (hkj : k.1 ≤ j.1),
          restrictedAlgebraizationMapOfLE hki (b i) ≫ (d k i j hki hkj).hom =
            restrictedAlgebraizationMapOfLE hkj (b j)) ∧
      (∀ (k i j : X.affineOpens) (hki : k.1 ≤ i.1) (hkj : k.1 ≤ j.1),
          ((completionFunctor k.1.toScheme (I.comap k.1.ι)).map (d k i j hki hkj).hom).hom ≫
              (restrictedAlgebraizationIsoOfLE I Fsys hkj (β j)).hom =
            (restrictedAlgebraizationIsoOfLE I Fsys hki (β i)).hom) ∧
      (∀ (i : X.affineOpens) (V V' : X.Opens) (hV : V ≤ i.1) (h : V' ≤ V) (s : Γ(M, V)),
          c i V' (h.trans hV) ((Scheme.Modules.presheaf M).map (homOfLE h).op s) =
            (Scheme.Modules.presheaf (coherentModulesPushforward i.1.ι (F i))).map (homOfLE h).op
              (c i V hV s)) ∧
      ∀ (k i j : X.affineOpens) (hki : k.1 ≤ i.1) (hkj : k.1 ≤ j.1) (s : Γ(M, k.1)),
          c j k.1 hkj s = Stacks.Coherent.localAppOpen k.1
            (overlapRestrictIso hki hkj (d k i j hki hkj)).hom le_rfl (c i k.1 hki s) := by
  obtain ⟨d, hd₁, hd₂, hdcoc⟩ :=
    exists_overlapComparison_of_localAlgebraizations I G Fsys α F b β hβ hK hC
  set good : X.Opens → X.affineOpens → Prop := fun V i => IsAffineOpen V ∧ V ≤ i.1 with hgoodDef
  have hgood : ∀ (V : X.Opens) (i : X.affineOpens), good V i → V ≤ i.1 := fun _ _ h => h.2
  obtain ⟨e, hcoc, hres, hform⟩ := exists_sectionComparison_restrictionCompatible
    (fun i : X.affineOpens => i.1) F good hgood
    (fun V i j hi hj => d ⟨V, hi.1⟩ i j hi.2 hj.2)
    (fun V i j m hi hj hm => hdcoc ⟨V, hi.1⟩ i j m hi.2 hj.2 hm.2)
    (fun V V' i j hi hj hi' hj' h =>
      localAppOpen_overlapRestrictIso_restrict I G Fsys α ⟨V', hi'.1⟩ hi.2 hj.2 h (b i) (b j)
        (β i) (β j) (hβ i) (hβ j) (hK i) (hC i) (hK j) (hC j) _
        (hd₁ ⟨V, hi.1⟩ i j hi.2 hj.2) (hd₂ ⟨V, hi.1⟩ i j hi.2 hj.2) _
        (hd₁ ⟨V', hi'.1⟩ i j hi'.2 hj'.2) (hd₂ ⟨V', hi'.1⟩ i j hi'.2 hj'.2))
  obtain ⟨M, c, hq', hcoh, hcres, hchart⟩ :=
    Stacks.Modules.exists_coherent_glued_of_basisComparison
      (fun i : X.affineOpens => i.1) (iSup_affineOpens_eq_top X)
      (fun i => coherentModulesPushforward i.1.ι (F i))
      (fun i => isQuasicoherent_restrict_coherentModulesPushforward i.1.ι (F i))
      (fun i => isFiniteType_restrict_coherentModulesPushforward i.1.ι (F i))
      (fun k : X.affineOpens => k.1) (fun k i => good k.1 i) (fun k i h => h.2)
      (fun i j V hV x hx => by
        obtain ⟨k, hxk, hkV⟩ := exists_affineOpen_mem_and_le V x hx
        exact ⟨k, ⟨k.2, (hkV.trans hV).trans inf_le_left⟩,
          ⟨k.2, (hkV.trans hV).trans inf_le_right⟩, hxk, hkV⟩)
      (fun i j m V hV x hx => by
        obtain ⟨k, hxk, hkV⟩ := exists_affineOpen_mem_and_le V x hx
        exact ⟨k, ⟨k.2, (hkV.trans hV).trans (inf_le_left.trans inf_le_left)⟩,
          ⟨k.2, (hkV.trans hV).trans (inf_le_left.trans inf_le_right)⟩,
          ⟨k.2, (hkV.trans hV).trans inf_le_right⟩, hxk, hkV⟩)
      (fun k i j hki hkj => e k.1 i j hki hkj)
      (fun k l i j hki hkj hli hlj h s => hres k.1 l.1 i j hki hkj hli hlj h s)
      (fun k i j m hi hj hm s => hcoc k.1 i j m hi hj hm s)
  refine ⟨M, d, fun i V hV => c i V hV, ⟨hq', hcoh⟩, hd₁, hd₂,
    fun i V V' hV h s => hcres i V V' hV h s, fun k i j hki hkj s => ?_⟩
  exact (hchart k i j ⟨k.2, hki⟩ ⟨k.2, hkj⟩ s).trans (hform k.1 i j ⟨k.2, hki⟩ ⟨k.2, hkj⟩ _)

/-! ### An isomorphism of the restrictions from a family of linear equivalences -/

/-- The identity acts on the sections over an open as the identity. -/
public theorem localAppOpen_id_eq {X : Scheme.{u}} (U : X.Opens) {M : X.Modules} {V : X.Opens}
    (hV : V ≤ U) :
    Stacks.Coherent.localAppOpen U (𝟙 (M.restrict U.ι)) hV = 𝟙 Γ(M, V) := by
  rw [← CategoryTheory.Functor.map_id (Scheme.Modules.restrictFunctor U.ι) M,
    Stacks.Coherent.localAppOpen_restrictFunctor_map]
  rfl

/-- A family of linear equivalences of the sections over the opens inside `U`, compatible with
restriction, is the action on sections of an isomorphism of the restrictions to `U`. -/
public theorem exists_restrictIso_of_appEquiv {X : Scheme.{u}} (U : X.Opens) {M N : X.Modules}
    (c : ∀ V : X.Opens, V ≤ U → (Γ(M, V) ≃ₗ[Γ(X, V)] Γ(N, V)))
    (hres : ∀ (V W : X.Opens) (hV : V ≤ U) (hWV : W ≤ V) (s : Γ(M, V)),
      c W (hWV.trans hV) ((Scheme.Modules.presheaf M).map (homOfLE hWV).op s) =
        (Scheme.Modules.presheaf N).map (homOfLE hWV).op (c V hV s)) :
    ∃ e : M.restrict U.ι ≅ N.restrict U.ι,
      ∀ (V : X.Opens) (hV : V ≤ U) (s : Γ(M, V)),
        Stacks.Coherent.localAppOpen U e.hom hV s = c V hV s := by
  -- the forward and backward families as morphisms of abelian groups
  set g : ∀ V : X.Opens, V ≤ U → (Γ(M, V) ⟶ Γ(N, V)) := fun V hV =>
    AddCommGrpCat.ofHom (c V hV).toLinearMap.toAddMonoidHom with hgdef
  set g' : ∀ V : X.Opens, V ≤ U → (Γ(N, V) ⟶ Γ(M, V)) := fun V hV =>
    AddCommGrpCat.ofHom (c V hV).symm.toLinearMap.toAddMonoidHom with hg'def
  have hgapp : ∀ (V : X.Opens) (hV : V ≤ U) (s : Γ(M, V)), g V hV s = c V hV s := fun _ _ _ => rfl
  have hg'app : ∀ (V : X.Opens) (hV : V ≤ U) (t : Γ(N, V)),
      g' V hV t = (c V hV).symm t := fun _ _ _ => rfl
  have hres' : ∀ (V W : X.Opens) (hV : V ≤ U) (hWV : W ≤ V) (t : Γ(N, V)),
      g' W (hWV.trans hV) ((Scheme.Modules.presheaf N).map (homOfLE hWV).op t) =
        (Scheme.Modules.presheaf M).map (homOfLE hWV).op (g' V hV t) := by
    intro V W hV hWV t
    rw [hg'app, hg'app]
    refine (c W (hWV.trans hV)).injective ?_
    rw [LinearEquiv.apply_symm_apply, hres V W hV hWV ((c V hV).symm t),
      LinearEquiv.apply_symm_apply]
  have hsmul : ∀ (V : X.Opens) (hV : V ≤ U) (r : Γ(X, V)) (s : Γ(M, V)),
      g V hV (r • s) = r • g V hV s := fun V hV r s => (c V hV).map_smul r s
  have hsmul' : ∀ (V : X.Opens) (hV : V ≤ U) (r : Γ(X, V)) (t : Γ(N, V)),
      g' V hV (r • t) = r • g' V hV t := fun V hV r t => (c V hV).symm.map_smul r t
  obtain ⟨ψ, hψ, -⟩ := Stacks.Coherent.exists_restrictHom_of_app U g hsmul hres
  obtain ⟨φ, hφ, -⟩ := Stacks.Coherent.exists_restrictHom_of_app U g' hsmul' hres'
  obtain ⟨_idM, -, huniqM⟩ := Stacks.Coherent.exists_restrictHom_of_app U
    (fun V (_ : V ≤ U) => 𝟙 Γ(M, V)) (fun _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
  obtain ⟨_idN, -, huniqN⟩ := Stacks.Coherent.exists_restrictHom_of_app U
    (fun V (_ : V ≤ U) => 𝟙 Γ(N, V)) (fun _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
  refine ⟨⟨ψ, φ, ?_, ?_⟩, fun V hV s => by rw [hψ V hV]; exact hgapp V hV s⟩
  · refine (huniqM (ψ ≫ φ) fun V hV => ?_).trans
      (huniqM (𝟙 _) fun V hV => localAppOpen_id_eq U hV).symm
    rw [localAppOpen_comp, hψ V hV, hφ V hV]
    ext s
    exact (c V hV).symm_apply_apply s
  · refine (huniqN (φ ≫ ψ) fun V hV => ?_).trans
      (huniqN (𝟙 _) fun V hV => localAppOpen_id_eq U hV).symm
    rw [localAppOpen_comp, hφ V hV, hψ V hV]
    ext t
    exact (c V hV).apply_symm_apply t

/-! ### The local comparison of the completion of the glued module with the given system -/

/-- Cancelling an isomorphism against its inverse at the end of a composite. -/
private theorem comp_hom_inv_cancel {C : Type*} [Category C] {A B D : C} (a : A ⟶ B) (k : B ≅ D) :
    (a ≫ k.hom) ≫ k.inv = a := by
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The chart identification of a glued coherent module, as an isomorphism of coherent modules.
A family of linear equivalences between the sections of `M` and of the direct image of `Fi` over
the opens inside `U`, compatible with restriction, comes from an isomorphism
`M|_U ≅ Fi` of coherent modules, whose action on sections, read through
`AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso`, is that family. -/
public theorem exists_chartIso_of_appEquiv {X : Scheme.{u}} [IsLocallyNoetherian X]
    (U : X.Opens) {M : X.Modules} (hM : _root_.SheafOfModules.IsCoherent M)
    (Fi : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf)
    (c : ∀ V : X.Opens, V ≤ U →
      (Γ(M, V) ≃ₗ[Γ(X, V)] Γ(coherentModulesPushforward U.ι Fi, V)))
    (hres : ∀ (V W : X.Opens) (hV : V ≤ U) (hWV : W ≤ V) (s : Γ(M, V)),
      c W (hWV.trans hV) ((Scheme.Modules.presheaf M).map (homOfLE hWV).op s) =
        (Scheme.Modules.presheaf (coherentModulesPushforward U.ι Fi)).map (homOfLE hWV).op
          (c V hV s)) :
    ∃ e : restrictCoherentModules U.ι ⟨M, hM⟩ ≅ Fi,
      ∀ (V : X.Opens) (hV : V ≤ U) (s : Γ(M, V)),
        Stacks.Coherent.localAppOpen U ((underlyingObjIso e).hom ≫
          ((Scheme.Modules.restrictFunctorAdjCounitIso U.ι).app Fi.obj).inv) hV s = c V hV s := by
  obtain ⟨e, he⟩ := exists_restrictIso_of_appEquiv U c hres
  refine ⟨ObjectProperty.isoMk _
    (e ≪≫ (Scheme.Modules.restrictFunctorAdjCounitIso U.ι).app Fi.obj), fun V hV s => ?_⟩
  exact (congrArg (fun ψ => Stacks.Coherent.localAppOpen U ψ hV s)
    (comp_hom_inv_cancel e.hom ((Scheme.Modules.restrictFunctorAdjCounitIso U.ι).app Fi.obj))).trans
    (he V hV s)

/-- The local comparison of the completion of a glued coherent module with the given system.
Over a chart `U`, the completion of the glued module restricted to `U` is the completion of its
restriction, by the comparison of Stacks 0880
(`Stacks.Algebraization.completionRestrictOpenIso`); that restriction is the chart's module
through `chart`; and the completion of the chart's module is the restricted system, by `βi`. -/
public def completionRestrictChartIso {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (U : X.Opens)
    (Fg : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (Fi : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf)
    (chart : restrictCoherentModules U.ι Fg ≅ Fi)
    (βi : ((completionFunctor U.toScheme (I.comap U.ι)).obj Fi).obj ≅
      ((Stacks.Coherent.restrictFunctor I U.ι).obj Fsys).obj) :
    (Stacks.Coherent.restrictFunctor I U.ι).obj ((completionFunctor X I).obj Fg) ≅
      (Stacks.Coherent.restrictFunctor I U.ι).obj Fsys :=
  ObjectProperty.isoMk _ (completionRestrictOpenIso U.ι I Fg ≪≫
    underlyingObjIso ((completionFunctor U.toScheme (I.comap U.ι)).mapIso chart) ≪≫ βi)

/-! ### Restricting the action on sections to a smaller open -/

/-- The action on sections of a threefold composite. Stated at this shape because
`AlgebraicGeometry.Scheme.Modules.Hom.comp_app` does not always match; see the implementation
notes of `StacksFrontier/AlgebraicGeometry/FormalGeometry/AlgebraizeDualOverlap.lean`. -/
private theorem app_comp₃ {X : Scheme.{u}} {M N P Q : X.Modules} (a : M ⟶ N) (b : N ⟶ P)
    (c : P ⟶ Q) (A : X.Opens) :
    Scheme.Modules.Hom.app (a ≫ b ≫ c) A =
      Scheme.Modules.Hom.app a A ≫ Scheme.Modules.Hom.app b A ≫
        Scheme.Modules.Hom.app c A := rfl

/-- The action on the sections over an open presented as an image, sandwiched between two
restriction maps whose source and target coincide: the sandwich contributes nothing, because the
category of opens is thin. -/
private theorem localApp_sandwich_eq {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : Y.Modules} (ψ : M.restrict f ⟶ N.restrict f) {B : X.Opens} {V : Y.Opens}
    (hB : f ''ᵁ B = V) (j₁ : f ''ᵁ B ⟶ V) (j₂ : V ⟶ f ''ᵁ B) :
    localApp f ψ hB =
      (Scheme.Modules.presheaf M).map j₁.op ≫ Scheme.Modules.Hom.app ψ B ≫
        (Scheme.Modules.presheaf N).map j₂.op := by
  subst hB
  rw [Subsingleton.elim j₁ (𝟙 _), Subsingleton.elim j₂ (𝟙 _)]
  simp
  rfl

/-- The canonical comparison of the two routes from `X` down to an open `W ≤ U`: restricting
to `W` directly, or restricting to `U` and then along `W ⟶ U`. -/
public def restrictDownIso {X : Scheme.{u}} {U W : X.Opens} (hWU : W ≤ U) (M : X.Modules) :
    M.restrict W.ι ≅ (M.restrict U.ι).restrict (X.homOfLE hWU) :=
  (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hWU)).symm.app M ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE hWU) U.ι).app M

/-- `Stacks.Algebraization.restrictDownIso` acts on the sections over an open as a restriction
map of the presheaf: both of its factors do, and the category of opens is thin, so the morphism of
opens is an argument. -/
public theorem restrictDownIso_hom_app {X : Scheme.{u}} {U W : X.Opens} (hWU : W ≤ U)
    (M : X.Modules) (A : W.toScheme.Opens)
    (i : U.ι ''ᵁ (X.homOfLE hWU ''ᵁ A) ⟶ W.ι ''ᵁ A) :
    Scheme.Modules.Hom.app (restrictDownIso hWU M).hom A =
      (Scheme.Modules.presheaf M).map i.op := by
  simp only [restrictDownIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.restrictFunctorCongr_inv_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app]
  exact presheafMap_comp₂_eq M _ _ _

/-- The inverse of `Stacks.Algebraization.restrictDownIso` on sections. -/
public theorem restrictDownIso_inv_app {X : Scheme.{u}} {U W : X.Opens} (hWU : W ≤ U)
    (M : X.Modules) (A : W.toScheme.Opens)
    (i : W.ι ''ᵁ A ⟶ U.ι ''ᵁ (X.homOfLE hWU ''ᵁ A)) :
    Scheme.Modules.Hom.app (restrictDownIso hWU M).inv A =
      (Scheme.Modules.presheaf M).map i.op := by
  simp only [restrictDownIso, Iso.trans_inv, Iso.symm_inv, Iso.app_inv,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.restrictFunctorCongr_hom_app_app,
    Scheme.Modules.restrictFunctorComp_inv_app_app]
  exact presheafMap_comp₂_eq M _ _ _

/-- The restriction of a morphism along `W ⟶ U`, conjugated by
`Stacks.Algebraization.restrictDownIso`, acts on the sections over an open as the morphism itself
does, sandwiched between two restriction maps. -/
public theorem localApp_restrictDownIso {X : Scheme.{u}} {U W : X.Opens} (hWU : W ≤ U)
    {M N : X.Modules} (ψ : M.restrict U.ι ⟶ N.restrict U.ι)
    {A : W.toScheme.Opens} {V : X.Opens} (hA : W.ι ''ᵁ A = V)
    (i₁ : U.ι ''ᵁ (X.homOfLE hWU ''ᵁ A) ⟶ V)
    (i₂ : V ⟶ U.ι ''ᵁ (X.homOfLE hWU ''ᵁ A)) :
    localApp W.ι ((restrictDownIso hWU M).hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map ψ ≫
          (restrictDownIso hWU N).inv) hA =
      (Scheme.Modules.presheaf M).map i₁.op ≫
        Scheme.Modules.Hom.app ψ (X.homOfLE hWU ''ᵁ A) ≫
          (Scheme.Modules.presheaf N).map i₂.op := by
  subst hA
  show Scheme.Modules.Hom.app ((restrictDownIso hWU M).hom ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map ψ ≫
        (restrictDownIso hWU N).inv) A = _
  rw [app_comp₃, restrictDownIso_hom_app hWU M A i₁, restrictDownIso_inv_app hWU N A i₂,
    restrictFunctor_map_app]
  rfl

/-- The action over `V ≤ W ≤ U` of a morphism of the restrictions to `U` is the action over `V` of
its restriction along `W ⟶ U`. -/
private theorem localAppOpen_eq_restrictDown_aux {X : Scheme.{u}} {U W V : X.Opens}
    (hWU : W ≤ U) (hVW : V ≤ W) {M N : X.Modules} (ψ : M.restrict U.ι ⟶ N.restrict U.ι) :
    Stacks.Coherent.localAppOpen U ψ (hVW.trans hWU) =
      Stacks.Coherent.localAppOpen W ((restrictDownIso hWU M).hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map ψ ≫
          (restrictDownIso hWU N).inv) hVW := by
  have hA : W.ι ''ᵁ (X.homOfLE hVW ''ᵁ (⊤ : V.toScheme.Opens)) = V :=
    (image_comp_eq_of_eq (X.homOfLE hVW) W.ι V.ι (X.homOfLE_ι hVW) ⊤).trans V.ι_image_top
  have hB : U.ι ''ᵁ (X.homOfLE hWU ''ᵁ (X.homOfLE hVW ''ᵁ (⊤ : V.toScheme.Opens))) = V :=
    (image_comp_eq_of_eq (X.homOfLE hWU) U.ι W.ι (X.homOfLE_ι hWU)
      (X.homOfLE hVW ''ᵁ ⊤)).trans hA
  refine Stacks.Coherent.localAppOpen_eq_of_localApp_eq (hVW.trans hWU) hVW ψ _ hB hA ?_
  exact (localApp_sandwich_eq U.ι ψ hB (eqToHom hB) (eqToHom hB.symm)).trans
    (localApp_restrictDownIso hWU ψ hA (eqToHom hB) (eqToHom hB.symm)).symm

/-- The action on the sections over `W` of a morphism of the restrictions to `U ⊇ W` is the
action of its restriction along `W ⟶ U`. -/
public theorem localAppOpen_eq_restrictDown {X : Scheme.{u}} {U W : X.Opens} (hWU : W ≤ U)
    {M N : X.Modules} (ψ : M.restrict U.ι ⟶ N.restrict U.ι) :
    Stacks.Coherent.localAppOpen U ψ hWU =
      Stacks.Coherent.localAppOpen W ((restrictDownIso hWU M).hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map ψ ≫
          (restrictDownIso hWU N).inv) le_rfl :=
  localAppOpen_eq_restrictDown_aux hWU le_rfl ψ

/-- Two morphisms of restrictions to two different opens have the same action on the sections
over a common smaller open as soon as their restrictions to that open agree. -/
public theorem localAppOpen_eq_of_restrictDown_eq {X : Scheme.{u}} {U U' W : X.Opens}
    (hWU : W ≤ U) (hWU' : W ≤ U') {M N : X.Modules}
    (ψ : M.restrict U.ι ⟶ N.restrict U.ι) (ψ' : M.restrict U'.ι ⟶ N.restrict U'.ι)
    (h : (restrictDownIso hWU M).hom ≫
          (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map ψ ≫
            (restrictDownIso hWU N).inv =
        (restrictDownIso hWU' M).hom ≫
          (Scheme.Modules.restrictFunctor (X.homOfLE hWU')).map ψ' ≫
            (restrictDownIso hWU' N).inv) :
    Stacks.Coherent.localAppOpen U ψ hWU = Stacks.Coherent.localAppOpen U' ψ' hWU' :=
  (localAppOpen_eq_restrictDown hWU ψ).trans
    ((congrArg (fun φ => Stacks.Coherent.localAppOpen W φ le_rfl) h).trans
      (localAppOpen_eq_restrictDown hWU' ψ').symm)

/-- `Stacks.Algebraization.localAppOpen_eq_restrictDown` over a yet smaller open: for
`V ≤ W ≤ U`, the action on the sections over `V` of a morphism of the restrictions to `U` is the
action over `V` of its restriction along `W ⟶ U`. -/
public theorem localAppOpen_eq_restrictDown_of_le {X : Scheme.{u}} {U W V : X.Opens}
    (hWU : W ≤ U) (hVW : V ≤ W) {M N : X.Modules} (ψ : M.restrict U.ι ⟶ N.restrict U.ι) :
    Stacks.Coherent.localAppOpen U ψ (hVW.trans hWU) =
      Stacks.Coherent.localAppOpen W ((restrictDownIso hWU M).hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map ψ ≫
          (restrictDownIso hWU N).inv) hVW :=
  localAppOpen_eq_restrictDown_aux hWU hVW ψ

end Stacks.Algebraization

end
