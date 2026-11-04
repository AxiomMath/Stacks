module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjModuleRestriction
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackAnyUniverse
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseIso
public import StacksFrontier.Topology.Sheaves.Basis.ModuleFMap
public import StacksFrontier.Topology.Sheaves.Basis.ModuleRestriction

/-!
# Associated sheaves under the Veronese isomorphism

Let `S` be a graded ring, `d ≥ 1`, and `T` a graded `S`-module. The sheaf `T̃` on `Proj S`
associated to `T` is the pullback, along the canonical isomorphism
`Stacks.Veronese.veroneseProjIso : Proj S ≅ Proj S⁽ᵈ⁾`, of the sheaf associated to the Veronese
part `T⁽ᵈ⁾` over the Veronese subring `S⁽ᵈ⁾`.

## Main definitions

* `Stacks.Veronese.veroneseAssociatedSheafIso`: the canonical isomorphism of sheaves of
  modules `T̃ ≅ i^* (T⁽ᵈ⁾~)`, for a module whose carrier lies in any universe.
* `Stacks.Veronese.associatedModuleSheafVeroneseIso`: the same isomorphism for a module whose
  carrier lies in the ring's universe, in the `AlgebraicGeometry.Scheme.Modules` spelling.
* `Stacks.Veronese.veroneseSectionsAddEquiv` and `Stacks.Veronese.veroneseSectionsMap`: the
  comparison of sections over a standard open, and the same map with its source and target
  written as sections of sheaves on the two schemes.
* `Stacks.Veronese.veroneseSectionIso`: that comparison as an isomorphism onto the sections of the
  pushforward.
* `Stacks.Veronese.associatedSchemeModules`: the sheaf associated to a graded module, presented as
  a sheaf of modules on the scheme `Proj 𝒜`.
* `Stacks.Veronese.positiveBasicOpenSet` and `Stacks.Veronese.veronesePowerBasicOpenSet`: the
  standard opens of positive-degree homogeneous elements, and those of their `d`-th powers.
* `Stacks.Veronese.pushforwardSectionsIso`: an additive, semilinear comparison of sections over
  `U` and over `f⁻¹U` presented as an isomorphism onto the sections of a pushforward.

## Main results

* `Stacks.Veronese.veroneseAssociatedSheafIso_standardOpen` and
  `Stacks.Veronese.associatedModuleSheafVeroneseIso_standardOpen`: the value of the
  isomorphism on every positive-degree standard open.
* `Stacks.Veronese.exists_veroneseIso` and `Stacks.Veronese.exists_veronesePushforwardIso`: the
  pullback and pushforward forms of the isomorphism, with the same chartwise characterization.
* `Stacks.Veronese.veroneseSections_smul`, `Stacks.Veronese.veroneseSectionsAddEquiv_smul` and
  `Stacks.Veronese.veroneseSectionsAddEquiv_restrict`: the semilinearity of the section comparison
  over the structure sheaf, over the degree-zero localizations, and its compatibility with
  restriction.
* `Stacks.Veronese.veroneseSectionIso_hom_apply` and
  `Stacks.Veronese.veroneseSectionIso_naturality`: the same two facts for the chartwise
  isomorphism.
* `Stacks.Veronese.positiveBasicOpenSet_isBasis` and
  `Stacks.Veronese.veronesePowerBasicOpenSet_isBasis`: both families are bases of opens.
* `Stacks.Veronese.exists_moduleSheafIso_of_sectionIso_onBasis`: a compatible family of section
  isomorphisms on a basis of opens comes from an isomorphism of sheaves of modules.
* `Stacks.Veronese.exists_pullbackIso_of_pushforwardIso`: along an isomorphism of schemes, an
  isomorphism onto a pushforward is the same thing as one from a pullback.
* `Stacks.Veronese.pushforwardSectionsIso_apply`,
  `Stacks.Veronese.pushforwardSectionsIso_naturality` and
  `Stacks.Veronese.moduleSheafHom_app_cast`: the computation rules for the section comparison and
  for transporting a section along an equality of opens.

## Universes

For `S : Type u` and a module carrier `T : Type v` the sheaf
`ProjectiveSpectrum.Proj.associatedModuleSheaf` has its sections in `Type (max u v)`, so the
isomorphism is one of objects of `SheafOfModules.{max u v} (Proj 𝒮).ringCatSheaf`, with the
pullback `SheafOfModules.pullback.{max u v}`. At `v = u` this pullback is
`AlgebraicGeometry.Scheme.Modules.pullback`, and `associatedModuleSheafVeroneseIso` states the
isomorphism in that form.

## References

* [Stacks Project, Tag 0B5J](https://stacks.math.columbia.edu/tag/0B5J)
-/

@[expose] public section

namespace Stacks.Veronese

open AlgebraicGeometry CategoryTheory DirectSum TopologicalSpace Opposite

attribute [local instance_reducible] TopCat.Sheaf
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] ProjectiveSpectrum.isPrime

universe u v w

variable {S : Type u} {M : Type v} {σ : Type w}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  (𝒨 : ℤ → AddSubgroup M)
  [Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨]

/-- Transporting an isomorphism `eA` of sections over `A` along `h : A = B` gives `eB`, provided
`eA` and `eB` commute with the restriction from `A` to `B`. -/
theorem moduleSheafIso_transport {X : TopCat.{u}} (𝒪 : TopCat.Sheaf RingCat X)
    (F G : SheafOfModules.{max u v} 𝒪) {A B : Opens X} (h : A = B)
    (eA : F.val.obj (op A) ≅ G.val.obj (op A))
    (eB : F.val.obj (op B) ≅ G.val.obj (op B))
    (hn : ∀ s, eB.hom (F.val.map (homOfLE h.ge).op s) =
      G.val.map (homOfLE h.ge).op (eA.hom s)) : h ▸ eA = eB := by
  cases h
  apply Iso.ext
  ext s
  simpa using (hn s).symm

/-- Compatibility of isomorphisms of sections with restriction is preserved by transporting them
along equalities of opens. -/
theorem moduleSheafIso_transport_naturality {X : TopCat.{u}}
    (𝒪 : TopCat.Sheaf RingCat X) (F G : SheafOfModules.{max u v} 𝒪)
    {A B A' B' : Opens X} (hA : A = A') (hB : B = B')
    (eA : F.val.obj (op A) ≅ G.val.obj (op A))
    (eB : F.val.obj (op B) ≅ G.val.obj (op B)) (h : B ≤ A)
    (hn : ∀ s, eB.hom (F.val.map (homOfLE h).op s) =
      G.val.map (homOfLE h).op (eA.hom s)) (h' : B' ≤ A') :
    ∀ s, (hB ▸ eB).hom (F.val.map (homOfLE h').op s) =
      G.val.map (homOfLE h').op ((hA ▸ eA).hom s) := by
  cases hA
  cases hB
  exact hn

/-- Isomorphisms between the sections of two sheaves of modules over the members of a basis of
opens, compatible with restriction, come from an isomorphism of sheaves of modules. -/
theorem exists_moduleSheafIso_of_sectionIso_onBasis
    {X : TopCat.{u}} {𝒪 : TopCat.Sheaf RingCat X}
    (F G : SheafOfModules.{max u v} 𝒪) {ι : Type*} (U : ι → Opens X)
    (hU : Opens.IsBasis (Set.range U))
    (e : ∀ a, F.val.obj (op (U a)) ≅ G.val.obj (op (U a)))
    (hn : ∀ a b (h : U b ≤ U a) (s : F.val.obj (op (U a))),
      (e b).hom (F.val.map (homOfLE h).op s) =
        G.val.map (homOfLE h).op ((e a).hom s)) :
    ∃ E : F ≅ G, ∀ a, E.hom.val.app (op (U a)) = (e a).hom := by
  classical
  let B := Stacks.BasisRestriction.BasisCat (Set.range U)
  let r := Stacks.BasisRestriction.restrictModuleSheaf hU 𝒪
  let : r.IsEquivalence := Stacks.BasisRestriction.isEquivalence_restrictModuleSheaf hU 𝒪
  let a (V : B) : ι := V.property.choose
  have ha (V : B) : U (a V) = V.obj := V.property.choose_spec
  let eb (V : B) : F.val.obj (op V.obj) ≅ G.val.obj (op V.obj) :=
    (ha V) ▸ e (a V)
  have eb_spec (V : B) (i : ι) (hi : U i = V.obj) : eb V = hi ▸ e i := by
    apply moduleSheafIso_transport 𝒪 F G rfl (eb V) (hi ▸ e i)
    exact moduleSheafIso_transport_naturality 𝒪 F G (ha V) hi (e (a V)) (e i)
      ((ha V).trans hi.symm).ge (hn (a V) i _) le_rfl
  let er : r.obj F ≅ r.obj G :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun V ↦ eb V.unop) (by
      intro V W h
      ext s
      exact moduleSheafIso_transport_naturality 𝒪 F G (ha V.unop) (ha W.unop)
        (e (a V.unop)) (e (a W.unop))
        (by rw [ha, ha]; exact h.unop.hom.le)
        (hn (a V.unop) (a W.unop) _) h.unop.hom.le s))
  refine ⟨r.preimageIso er, ?_⟩
  intro i
  have h := congrArg (fun φ ↦ φ.val.app (op (⟨U i, ⟨i, rfl⟩⟩ : B)))
    (r.map_preimage er.hom)
  change (r.preimageIso er).hom.val.app (op (U i)) =
    (eb ⟨U i, ⟨i, rfl⟩⟩).hom at h
  rwa [eb_spec _ i rfl] at h

/-- An additive equivalence `e` from the sections of `G` over `U` to the sections of `F` over
`V = f⁻¹ᵁ U`, semilinear along `f.appLE U V`, as an isomorphism of modules onto the sections of the
pushforward of `F` over `U`. -/
noncomputable def pushforwardSectionsIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) (F : SheafOfModules.{max u v} X.ringCatSheaf)
    (G : SheafOfModules.{max u v} Y.ringCatSheaf)
    (U : Y.Opens) (V : X.Opens) (h : f ⁻¹ᵁ U = V)
    (e : G.val.obj (op U) ≃+ F.val.obj (op V))
    (hs : ∀ (r : Y.ringCatSheaf.obj.obj (op U)) (s : G.val.obj (op U)),
      e (r • s) = @SMul.smul _ _ (F.val.obj (op V)).isModule.toDistribMulAction.toSMul
        ((f.appLE U V (by rw [h])).hom r) (e s)) :
    G.val.obj (op U) ≅
      ((SheafOfModules.pushforward.{max u v} f.toRingCatSheafHom).obj F).val.obj (op U) := by
  subst V
  let l : G.val.obj (op U) →ₗ[Y.ringCatSheaf.obj.obj (op U)]
      ((SheafOfModules.pushforward.{max u v} f.toRingCatSheafHom).obj F).val.obj (op U) :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := by
        intro r s
        simpa only [Scheme.Hom.appLE_eq_app, RingHom.id_apply] using! hs r s }
  exact (LinearEquiv.ofBijective l e.bijective).toModuleIso

/-- After transport along `f⁻¹ᵁ U = V`, `pushforwardSectionsIso f F G U V h e hs` is `e`. -/
theorem pushforwardSectionsIso_apply {X Y : Scheme.{u}}
    (f : X ⟶ Y) (F : SheafOfModules.{max u v} X.ringCatSheaf)
    (G : SheafOfModules.{max u v} Y.ringCatSheaf)
    (U : Y.Opens) (V : X.Opens) (h : f ⁻¹ᵁ U = V)
    (e : G.val.obj (op U) ≃+ F.val.obj (op V))
    (hs : ∀ (r : Y.ringCatSheaf.obj.obj (op U)) (s : G.val.obj (op U)),
      e (r • s) = @SMul.smul _ _ (F.val.obj (op V)).isModule.toDistribMulAction.toSMul
        ((f.appLE U V (by rw [h])).hom r) (e s))
    (s : G.val.obj (op U)) :
    h ▸ (pushforwardSectionsIso f F G U V h e hs).hom s = e s := by
  subst V
  rfl

/-- Along an isomorphism of schemes `f`, an isomorphism `G ≅ f_* F` comes from an isomorphism
`F ≅ f^* G` through the unit of the pullback–pushforward adjunction. -/
theorem exists_pullbackIso_of_pushforwardIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] (F : SheafOfModules.{max u v} X.ringCatSheaf)
    (G : SheafOfModules.{max u v} Y.ringCatSheaf)
    (e : G ≅ (SheafOfModules.pushforward.{max u v} f.toRingCatSheafHom).obj F) :
    ∃ E : F ≅ (SheafOfModules.pullback.{max u v} f.toRingCatSheafHom).obj G,
      (SheafOfModules.pullbackPushforwardAdjunction.{max u v} f.toRingCatSheafHom).unit.app G ≫
        (SheafOfModules.pushforward.{max u v} f.toRingCatSheafHom).map E.inv = e.hom := by
  let adj := SheafOfModules.pullbackPushforwardAdjunction.{max u v} f.toRingCatSheafHom
  let k : (SheafOfModules.pullback.{max u v} f.toRingCatSheafHom).obj G ≅ F :=
    (SheafOfModules.pullback.{max u v} f.toRingCatSheafHom).mapIso e ≪≫
      asIso (adj.counit.app F)
  refine ⟨k.symm, ?_⟩
  show adj.homEquiv G F (adj.homEquiv G F |>.symm e.hom) = e.hom
  exact (adj.homEquiv G F).apply_symm_apply e.hom

/-- `pushforwardSectionsIso` commutes with restriction when the underlying equivalences do. -/
theorem pushforwardSectionsIso_naturality {X Y : Scheme.{u}}
    (f : X ⟶ Y) (F : SheafOfModules.{max u v} X.ringCatSheaf)
    (G : SheafOfModules.{max u v} Y.ringCatSheaf)
    (U U' : Y.Opens) (V V' : X.Opens)
    (h : f ⁻¹ᵁ U = V) (h' : f ⁻¹ᵁ U' = V')
    (e : G.val.obj (op U) ≃+ F.val.obj (op V))
    (e' : G.val.obj (op U') ≃+ F.val.obj (op V'))
    (hs : ∀ (r : Y.ringCatSheaf.obj.obj (op U)) (s : G.val.obj (op U)),
      e (r • s) = @SMul.smul _ _ (F.val.obj (op V)).isModule.toDistribMulAction.toSMul
        ((f.appLE U V (by rw [h])).hom r) (e s))
    (hs' : ∀ (r : Y.ringCatSheaf.obj.obj (op U')) (s : G.val.obj (op U')),
      e' (r • s) = @SMul.smul _ _ (F.val.obj (op V')).isModule.toDistribMulAction.toSMul
        ((f.appLE U' V' (by rw [h'])).hom r) (e' s))
    (hU : U' ≤ U) (hV : V' ≤ V)
    (hn : ∀ s, e' (G.val.map (homOfLE hU).op s) =
      F.val.map (homOfLE hV).op (e s)) (s : G.val.obj (op U)) :
    (pushforwardSectionsIso f F G U' V' h' e' hs').hom
      (G.val.map (homOfLE hU).op s) =
    ((SheafOfModules.pushforward.{max u v} f.toRingCatSheafHom).obj F).val.map (homOfLE hU).op
      ((pushforwardSectionsIso f F G U V h e hs).hom s) := by
  subst V
  subst V'
  exact hn s

/-- The standard opens `D₊(f)` of the projective spectrum for homogeneous `f` of positive
degree. -/
def positiveBasicOpenSet : Set (Opens (ProjectiveSpectrum.top 𝒮)) :=
  {U | ∃ f e, 0 < e ∧ f ∈ 𝒮 e ∧ U = ProjectiveSpectrum.basicOpen 𝒮 f}

/-- The comparison of the sections of the sheaf associated to the Veronese module over `D₊(f ᵈ)`
with the sections of the sheaf associated to the module over `D₊(f)`: the degree-zero Veronese
localization comparison `veroneseModuleAwayEquiv`, read through the identifications of sections
over a standard open with degree-zero localizations. -/
noncomputable def veroneseSectionsAddEquiv
    (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)]
    [DirectSum.Decomposition (veroneseModuleGrading 𝒮 𝒨 d)] (hd : 0 < d)
    (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) :
    (ProjectiveSpectrum.Proj.associatedModuleSheaf
      (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d)).val.obj
        (.op (ProjectiveSpectrum.basicOpen (veroneseGrading 𝒮 d)
          (veronesePower 𝒮 d f hf))) ≃+
      (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj
        (.op (ProjectiveSpectrum.basicOpen 𝒮 f) : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ) := by
  let vf := veronesePower 𝒮 d f hf
  let E₁ := ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv
    (veroneseGrading 𝒮 d)
    (veroneseModuleGrading 𝒮 𝒨 d)
    (show vf ∈ veroneseGrading 𝒮 d e by
      change f ^ d ∈ 𝒮 (e * d)
      simpa [mul_comm] using SetLike.pow_mem_graded d hf) he
  let E₂ := veroneseModuleAwayEquiv 𝒮 d 𝒨 f hf hd
  let E₃ := ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf he
  exact (E₁.toAddEquiv.trans E₂).trans E₃.symm.toAddEquiv

/-- `veroneseSectionsAddEquiv` is semilinear along `veroneseAwayEquiv` over the degree-zero
localizations. -/
theorem veroneseSectionsAddEquiv_smul
    (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)]
    [DirectSum.Decomposition (veroneseModuleGrading 𝒮 𝒨 d)] (hd : 0 < d)
    (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) :
    letI : SMul
        (HomogeneousLocalization.Away
          (veroneseGrading 𝒮 d)
          (veronesePower 𝒮 d f hf))
        ((ProjectiveSpectrum.Proj.associatedModuleSheaf
          (veroneseGrading 𝒮 d)
          (veroneseModuleGrading 𝒮 𝒨 d)).val.obj
            (.op (ProjectiveSpectrum.basicOpen (veroneseGrading 𝒮 d)
              (veronesePower 𝒮 d f hf)))) :=
      (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenModule
        (veroneseGrading 𝒮 d)
        (veroneseModuleGrading 𝒮 𝒨 d)
        (veronesePower 𝒮 d f hf)).toDistribMulAction.toSMul
    letI : SMul (HomogeneousLocalization.Away 𝒮 f)
        ((ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj
          (.op (ProjectiveSpectrum.basicOpen 𝒮 f))) :=
      (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenModule 𝒮
        𝒨 f).toDistribMulAction.toSMul
    ∀ (r : HomogeneousLocalization.Away
      (veroneseGrading 𝒮 d)
      (veronesePower 𝒮 d f hf))
      (z : (ProjectiveSpectrum.Proj.associatedModuleSheaf
        (veroneseGrading 𝒮 d)
        (veroneseModuleGrading 𝒮 𝒨 d)).val.obj
          (.op (ProjectiveSpectrum.basicOpen (veroneseGrading 𝒮 d)
            (veronesePower 𝒮 d f hf)))),
      veroneseSectionsAddEquiv 𝒮 𝒨 d hd f he hf (r • z) =
        veroneseAwayEquiv 𝒮 d f hf hd r •
          veroneseSectionsAddEquiv 𝒮 𝒨 d hd f he hf z := by
  let : SMul
      (HomogeneousLocalization.Away
        (veroneseGrading 𝒮 d)
        (veronesePower 𝒮 d f hf))
      ((ProjectiveSpectrum.Proj.associatedModuleSheaf
        (veroneseGrading 𝒮 d)
        (veroneseModuleGrading 𝒮 𝒨 d)).val.obj
          (.op (ProjectiveSpectrum.basicOpen (veroneseGrading 𝒮 d)
            (veronesePower 𝒮 d f hf)))) :=
    (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenModule
      (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d)
      (veronesePower 𝒮 d f hf)).toDistribMulAction.toSMul
  let : SMul (HomogeneousLocalization.Away 𝒮 f)
      ((ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj
        (.op (ProjectiveSpectrum.basicOpen 𝒮 f))) :=
    (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenModule 𝒮
      𝒨 f).toDistribMulAction.toSMul
  let vf := veronesePower 𝒮 d f hf
  let E₁ := ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv
    (veroneseGrading 𝒮 d)
    (veroneseModuleGrading 𝒮 𝒨 d)
    (veronesePower_mem 𝒮 d f hf) he
  let E₂ := veroneseModuleAwayEquiv 𝒮 d 𝒨 f hf hd
  let E₃ := ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf he
  intro r z
  exact (congrArg (fun x ↦ E₃.symm (E₂ x)) (E₁.map_smul r z)).trans
    ((congrArg E₃.symm (veroneseModuleAwayEquiv_smul 𝒮 d 𝒨 f hf hd r (E₁ z))).trans
      (E₃.symm.map_smul _ _))

/-- `veroneseSectionsAddEquiv` is semilinear over the structure sheaf, along the map on sections
of the Veronese isomorphism. -/
theorem veroneseSections_smul (d : ℕ)
    [DirectSum.Decomposition (veroneseModuleGrading 𝒮 𝒨 d)] (hd : 0 < d)
    (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    let U := Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf)
    let V := Proj.basicOpen 𝒮 f
    let F := ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨
    let G := ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d)
    ∀ (r : (AlgebraicGeometry.Proj (veroneseGrading 𝒮 d)).ringCatSheaf.obj.obj (op U))
      (s : G.val.obj (op U)),
    veroneseSectionsAddEquiv 𝒮 𝒨 d hd f he hf
      (@SMul.smul _ _ (G.val.obj (op U)).isModule.toDistribMulAction.toSMul r s) =
      @SMul.smul _ _ (F.val.obj (op V)).isModule.toDistribMulAction.toSMul
        (((veroneseProjIso 𝒮 d hd).hom.appLE U V
          (by rw [veroneseProjIso_basicOpen 𝒮 d hd f he hf])).hom r)
        (veroneseSectionsAddEquiv 𝒮 𝒨 d hd f he hf s) := by
  let : GradedRing (veroneseGrading 𝒮 d) := veroneseGradingGradedRing 𝒮 d hd
  intro U V F G r s
  let vf := veronesePower 𝒮 d f hf
  have hvf : vf ∈ (veroneseGrading 𝒮 d) e := veronesePower_mem 𝒮 d f hf
  let J := Proj.basicOpenIsoAway (veroneseGrading 𝒮 d) vf hvf he
  let a := J.inv.hom r
  have ha : (Proj.awayToSection (veroneseGrading 𝒮 d) vf).hom a = r :=
    congrArg (fun k ↦ k.hom r) J.inv_hom_id
  have hr := congrArg (fun k ↦ k.hom a)
    (veroneseProjIso_awayToSection 𝒮 d hd f he hf)
  change ((veroneseProjIso 𝒮 d hd).hom.appLE U V
      (by rw [veroneseProjIso_basicOpen 𝒮 d hd f he hf])).hom
      ((Proj.awayToSection (veroneseGrading 𝒮 d) vf).hom a) =
    (Proj.awayToSection 𝒮 f).hom
      (veroneseAwayEquiv 𝒮 d f hf hd a) at hr
  rw [ha] at hr
  have hs := veroneseSectionsAddEquiv_smul 𝒮 𝒨 d hd f he hf a s
  change veroneseSectionsAddEquiv 𝒮 𝒨 d hd f he hf
    (@SMul.smul _ _ (G.val.obj (op U)).isModule.toDistribMulAction.toSMul
      ((Proj.awayToSection (veroneseGrading 𝒮 d) vf).hom a) s) =
      @SMul.smul _ _ (F.val.obj (op V)).isModule.toDistribMulAction.toSMul
        ((Proj.awayToSection 𝒮 f).hom
          (veroneseAwayEquiv 𝒮 d f hf hd a))
        (veroneseSectionsAddEquiv 𝒮 𝒨 d hd f he hf s) at hs
  exact (congrArg (fun b ↦ veroneseSectionsAddEquiv 𝒮 𝒨 d hd f he hf
    (@SMul.smul _ _ (G.val.obj (op U)).isModule.toDistribMulAction.toSMul b s))
    ha.symm).trans (hs.trans (congrArg (fun b ↦
      @SMul.smul _ _ (F.val.obj (op V)).isModule.toDistribMulAction.toSMul b
        (veroneseSectionsAddEquiv 𝒮 𝒨 d hd f he hf s)) hr.symm))

/-- `veroneseSectionsAddEquiv` commutes with restriction from `D₊(f ᵈ)` to `D₊(g ᵈ)` and from
`D₊(f)` to `D₊(g)`, for `D₊(g) ≤ D₊(f)`. -/
theorem veroneseSectionsAddEquiv_restrict
    (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)]
    [DirectSum.Decomposition (veroneseModuleGrading 𝒮 𝒨 d)] (hd : 0 < d) (f g : S) {e k : ℕ}
    (he : 0 < e) (hk : 0 < k) (hf : f ∈ 𝒮 e) (hg : g ∈ 𝒮 k)
    (hfg : ProjectiveSpectrum.basicOpen 𝒮 g ≤ ProjectiveSpectrum.basicOpen 𝒮 f) :
    let vf := veronesePower 𝒮 d f hf
    let vg := veronesePower 𝒮 d g hg
    let _hvf : vf ∈ (veroneseGrading 𝒮 d) e := by
      change f ^ d ∈ 𝒮 (e * d)
      simpa [mul_comm] using SetLike.pow_mem_graded d hf
    let _hvg : vg ∈ (veroneseGrading 𝒮 d) k := by
      change g ^ d ∈ 𝒮 (k * d)
      simpa [mul_comm] using SetLike.pow_mem_graded d hg
    let hfgV := basicOpen_veronesePower_le 𝒮 d f g hf hg hfg he hk
    ∀ z : (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
        (veroneseModuleGrading 𝒮 𝒨 d)).val.obj
          (op (ProjectiveSpectrum.basicOpen (veroneseGrading 𝒮 d) vf)),
      veroneseSectionsAddEquiv 𝒮 𝒨 d hd g hk hg
          (((ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
            (veroneseModuleGrading 𝒮 𝒨 d)).val.map
              (homOfLE hfgV).op) z) =
        ((ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.map
          (homOfLE hfg).op)
          (veroneseSectionsAddEquiv 𝒮 𝒨 d hd f he hf z) := by
  intro vf vg _hvf _hvg hfgV z
  let nres := ProjectiveSpectrum.moduleRestrictionMaps (veroneseGrading 𝒮 d)
    (veroneseModuleGrading 𝒮 𝒨 d) vf vg
    ⟨e, he, _hvf⟩ ⟨k, hk, _hvg⟩ hfgV
  let mres := ProjectiveSpectrum.moduleRestrictionMaps 𝒮 𝒨 f g
    ⟨e, he, hf⟩ ⟨k, hk, hg⟩ hfg
  let E₁f := ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (veroneseGrading 𝒮 d)
    (veroneseModuleGrading 𝒮 𝒨 d) _hvf he
  let E₁g := ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (veroneseGrading 𝒮 d)
    (veroneseModuleGrading 𝒮 𝒨 d) _hvg hk
  let E₃f := ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf he
  let E₃g := ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hg hk
  have hn : (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d)).val.map
      (homOfLE hfgV).op (E₁f.symm (E₁f z)) =
      E₁g.symm (nres.degreeZeroMap (E₁f z)) :=
    ProjectiveSpectrum.Proj.degreeZeroToSection_restriction (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d) vf vg
      ⟨e, he, _hvf⟩ ⟨k, hk, _hvg⟩ hfgV (E₁f z)
  have hn' : E₁g ((ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d)).val.map
      (homOfLE hfgV).op z) = nres.degreeZeroMap (E₁f z) := by
    simpa only [E₁f.symm_apply_apply, E₁g.apply_symm_apply] using congrArg E₁g hn
  let a := veroneseModuleAwayEquiv 𝒮 d 𝒨 f hf hd (E₁f z)
  have hm : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.map
      (homOfLE hfg).op (E₃f.symm a) = E₃g.symm (mres.degreeZeroMap a) :=
    ProjectiveSpectrum.Proj.degreeZeroToSection_restriction 𝒮 𝒨 f g
      ⟨e, he, hf⟩ ⟨k, hk, hg⟩ hfg a
  have h₂ := veroneseModuleAwayEquiv_naturality 𝒮 d 𝒨 hd f g he hk hf hg hfg (E₁f z)
  exact (congrArg (fun b ↦ E₃g.symm
    (veroneseModuleAwayEquiv 𝒮 d 𝒨 g hg hd b)) hn').trans
    ((congrArg E₃g.symm h₂).trans hm.symm)

/-- The sheaf associated to a graded module, presented as a sheaf of modules on the *scheme*
`Proj 𝒜` rather than over the structure sheaf of its projective spectrum. -/
noncomputable def associatedSchemeModules :
    SheafOfModules.{max u v} (AlgebraicGeometry.Proj 𝒮).ringCatSheaf :=
  ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨

/-- `veroneseSectionsAddEquiv`, with its source and target written as sections over the standard
opens of the two schemes rather than over opens of the underlying projective spectra. -/
noncomputable def veroneseSectionsMap (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)]
    [DirectSum.Decomposition (veroneseModuleGrading 𝒮 𝒨 d)] (hd : 0 < d)
    (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e)
    (s : (associatedSchemeModules (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d)).val.obj
        (op (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf)))) :
    (associatedSchemeModules 𝒮 𝒨).val.obj (op (Proj.basicOpen 𝒮 f)) :=
  veroneseSectionsAddEquiv 𝒮 𝒨 d hd f he hf s

/-- The standard opens of homogeneous elements of positive degree form a basis of the projective
spectrum. -/
theorem positiveBasicOpenSet_isBasis :
    Opens.IsBasis (positiveBasicOpenSet (𝒮 := 𝒮)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  obtain ⟨V, hV, hxV, hVU⟩ :=
    (AlgebraicGeometry.Proj.isBasis_basicOpen 𝒮).exists_subset_of_mem_open hx U.2
  rcases hV with ⟨Vopen, hg, hVg⟩
  rcases hg with ⟨f, rfl⟩
  subst V
  change x ∈ ProjectiveSpectrum.basicOpen 𝒮 f at hxV
  change ProjectiveSpectrum.basicOpen 𝒮 f ≤ U at hVU
  let g := f
  have hxSup : x ∈ ⨆ n : ℕ,
      ProjectiveSpectrum.basicOpen 𝒮 (GradedRing.proj 𝒮 n g) := by
    rwa [← ProjectiveSpectrum.basicOpen_eq_union_of_projection 𝒮 g]
  obtain ⟨n, hxn⟩ := Opens.mem_iSup.mp hxSup
  have hproj (m : ℕ) : ProjectiveSpectrum.basicOpen 𝒮 (GradedRing.proj 𝒮 m g) ≤
      ProjectiveSpectrum.basicOpen 𝒮 f := by
    calc
      _ ≤ ⨆ i : ℕ, ProjectiveSpectrum.basicOpen 𝒮 (GradedRing.proj 𝒮 i g) :=
        le_iSup (fun i : ℕ ↦ ProjectiveSpectrum.basicOpen 𝒮 (GradedRing.proj 𝒮 i g)) m
      _ = ProjectiveSpectrum.basicOpen 𝒮 f := by
        simpa [g] using (ProjectiveSpectrum.basicOpen_eq_union_of_projection 𝒮 f).symm
  by_cases hn : 0 < n
  · refine ⟨ProjectiveSpectrum.basicOpen 𝒮 (GradedRing.proj 𝒮 n g), ?_, hxn, ?_⟩
    · exact ⟨GradedRing.proj 𝒮 n g, n, hn, SetLike.coe_mem _, rfl⟩
    · exact (hproj n).trans hVU
  · have hn0 : n = 0 := by omega
    let a := GradedRing.proj 𝒮 n g
    have ha : a ∈ 𝒮 n := SetLike.coe_mem _
    have hpos : ∃ k : ℕ, 0 < k ∧ ∃ q : S, q ∈ 𝒮 k ∧ q ∉ x.asHomogeneousIdeal := by
      by_contra! H
      exact x.not_irrelevant_le ((HomogeneousIdeal.irrelevant_le 𝒮).mpr
        (fun k hk q hq ↦ H k hk q hq))
    obtain ⟨k, hk, q, hq, hqx⟩ := hpos
    have hxqa : x ∈ ProjectiveSpectrum.basicOpen 𝒮 (q * a) := by
      rw [ProjectiveSpectrum.mem_basicOpen]
      intro hqa
      have hprime : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
      rcases hprime.mem_or_mem hqa with hq' | ha'
      · exact hqx hq'
      · exact hxn (by simpa [a] using ha')
    refine ⟨ProjectiveSpectrum.basicOpen 𝒮 (q * a), ?_, hxqa, ?_⟩
    · refine ⟨q * a, k + n, by omega, SetLike.mul_mem_graded hq ha, rfl⟩
    · rw [ProjectiveSpectrum.basicOpen_mul]
      exact inf_le_right.trans ((hproj n).trans hVU)

/-- The standard opens `D₊(f ᵈ)` of `Proj S⁽ᵈ⁾`, for `f` homogeneous of positive degree in
`S`. -/
def veronesePowerBasicOpenSet (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)] (_hd : 0 < d) :
    Set (Opens (ProjectiveSpectrum.top (veroneseGrading 𝒮 d))) := by
  exact {U | ∃ f e, ∃ hf : f ∈ 𝒮 e, 0 < e ∧
    U = ProjectiveSpectrum.basicOpen (veroneseGrading 𝒮 d)
      (veronesePower 𝒮 d f hf)}

/-- The standard opens `D₊(f ᵈ)`, for `f` homogeneous of positive degree in `S`, form a basis of
`Proj S⁽ᵈ⁾`. -/
theorem veronesePowerBasicOpenSet_isBasis (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)]
    (hd : 0 < d) :
    Opens.IsBasis (veronesePowerBasicOpenSet (𝒮 := 𝒮) d hd) := by
  have hpos : Opens.IsBasis (positiveBasicOpenSet (𝒮 := (veroneseGrading 𝒮 d))) :=
    positiveBasicOpenSet_isBasis (S := veroneseSubring 𝒮 d)
      (σ := AddSubgroup (veroneseSubring 𝒮 d)) (𝒮 := (veroneseGrading 𝒮 d))
  have heq : veronesePowerBasicOpenSet (𝒮 := 𝒮) d hd =
      positiveBasicOpenSet (𝒮 := (veroneseGrading 𝒮 d)) := by
    ext U
    constructor
    · rintro ⟨f, e, hf, he, rfl⟩
      let vf := veronesePower 𝒮 d f hf
      exact ⟨vf, e, he, veronesePower_mem 𝒮 d f hf, rfl⟩
    · rintro ⟨g, e, he, hg, rfl⟩
      let f : S := g
      have hf : f ∈ 𝒮 (e * d) := hg
      refine ⟨f, e * d, hf, Nat.mul_pos he hd, ?_⟩
      calc
        ProjectiveSpectrum.basicOpen (veroneseGrading 𝒮 d) g =
            ProjectiveSpectrum.basicOpen (veroneseGrading 𝒮 d) (g ^ d) :=
          (ProjectiveSpectrum.basicOpen_pow (veroneseGrading 𝒮 d) g d hd).symm
        _ = ProjectiveSpectrum.basicOpen (veroneseGrading 𝒮 d)
            (veronesePower 𝒮 d f hf) := by
          congr 1
  exact (congrArg Opens.IsBasis heq).mpr hpos

/-- The comparison of sections over one standard open `D₊(f ᵈ)`, as an isomorphism onto the
sections there of the pushforward of `T̃` along the Veronese isomorphism. -/
noncomputable def veroneseSectionIso (d : ℕ)
    [DirectSum.Decomposition (veroneseModuleGrading 𝒮 𝒨 d)] (hd : 0 < d)
    (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    (associatedSchemeModules (veroneseGrading 𝒮 d)
        (veroneseModuleGrading 𝒮 𝒨 d)).val.obj
          (op (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf))) ≅
      ((SheafOfModules.pushforward.{max u v}
        (veroneseProjIso 𝒮 d hd).hom.toRingCatSheafHom).obj
        (associatedSchemeModules 𝒮 𝒨)).val.obj
          (op (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf))) := by
  letI := veroneseGradingGradedRing 𝒮 d hd
  exact pushforwardSectionsIso (veroneseProjIso 𝒮 d hd).hom
    (associatedSchemeModules 𝒮 𝒨)
    (associatedSchemeModules (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d))
    (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf))
    (Proj.basicOpen 𝒮 f) (veroneseProjIso_basicOpen 𝒮 d hd f he hf)
    (veroneseSectionsAddEquiv 𝒮 𝒨 d hd f he hf)
    (veroneseSections_smul 𝒮 𝒨 d hd f he hf)

/-- Transported back along `D₊(f) = i⁻¹ D₊(f ᵈ)`, the chartwise comparison is the degree-zero
comparison of sections. -/
theorem veroneseSectionIso_hom_apply (d : ℕ)
    [DirectSum.Decomposition (veroneseModuleGrading 𝒮 𝒨 d)] (hd : 0 < d)
    (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    ∀ s : (associatedSchemeModules (veroneseGrading 𝒮 d)
        (veroneseModuleGrading 𝒮 𝒨 d)).val.obj
          (op (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf))),
      Eq.rec (motive := fun W _ =>
          (associatedSchemeModules 𝒮 𝒨).val.obj (op W))
        (ConcreteCategory.hom (veroneseSectionIso 𝒮 𝒨 d hd f he hf).hom s)
        (veroneseProjIso_basicOpen 𝒮 d hd f he hf) =
      veroneseSectionsMap 𝒮 𝒨 d hd f he hf s := by
  let : GradedRing (veroneseGrading 𝒮 d) := veroneseGradingGradedRing 𝒮 d hd
  intro s
  exact pushforwardSectionsIso_apply (veroneseProjIso 𝒮 d hd).hom
    (associatedSchemeModules 𝒮 𝒨)
    (associatedSchemeModules (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d))
    (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf))
    (Proj.basicOpen 𝒮 f) (veroneseProjIso_basicOpen 𝒮 d hd f he hf)
    (veroneseSectionsAddEquiv 𝒮 𝒨 d hd f he hf)
    (veroneseSections_smul 𝒮 𝒨 d hd f he hf) s

/-- The chartwise comparisons commute with restriction between two standard opens. -/
theorem veroneseSectionIso_naturality (d : ℕ)
    [DirectSum.Decomposition (veroneseModuleGrading 𝒮 𝒨 d)] (hd : 0 < d)
    (f g : S) {e k : ℕ} (he : 0 < e) (hk : 0 < k) (hf : f ∈ 𝒮 e) (hg : g ∈ 𝒮 k) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    ∀ (hab : Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d g hg) ≤
        Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf))
      (_hab' : Proj.basicOpen 𝒮 g ≤ Proj.basicOpen 𝒮 f)
      (s : (associatedSchemeModules (veroneseGrading 𝒮 d)
        (veroneseModuleGrading 𝒮 𝒨 d)).val.obj
          (op (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf)))),
      ConcreteCategory.hom (veroneseSectionIso 𝒮 𝒨 d hd g hk hg).hom
          ((associatedSchemeModules (veroneseGrading 𝒮 d)
            (veroneseModuleGrading 𝒮 𝒨 d)).val.map (homOfLE hab).op s) =
        ((SheafOfModules.pushforward.{max u v}
        (veroneseProjIso 𝒮 d hd).hom.toRingCatSheafHom).obj
          (associatedSchemeModules 𝒮 𝒨)).val.map (homOfLE hab).op
            (ConcreteCategory.hom (veroneseSectionIso 𝒮 𝒨 d hd f he hf).hom s) := by
  let : GradedRing (veroneseGrading 𝒮 d) := veroneseGradingGradedRing 𝒮 d hd
  intro hab _hab' s
  exact pushforwardSectionsIso_naturality (veroneseProjIso 𝒮 d hd).hom
    (associatedSchemeModules 𝒮 𝒨)
    (associatedSchemeModules (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d))
    (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf))
    (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d g hg))
    (Proj.basicOpen 𝒮 f) (Proj.basicOpen 𝒮 g)
    (veroneseProjIso_basicOpen 𝒮 d hd f he hf)
    (veroneseProjIso_basicOpen 𝒮 d hd g hk hg)
    (veroneseSectionsAddEquiv 𝒮 𝒨 d hd f he hf)
    (veroneseSectionsAddEquiv 𝒮 𝒨 d hd g hk hg)
    (veroneseSections_smul 𝒮 𝒨 d hd f he hf)
    (veroneseSections_smul 𝒮 𝒨 d hd g hk hg) hab _hab'
    (veroneseSectionsAddEquiv_restrict 𝒮 𝒨 d hd f g he hk hf hg _hab') s

/-- The associated sheaf of the Veronese module is the pushforward of the associated sheaf of
the module along the Veronese isomorphism, compatibly with the chartwise comparisons. -/
theorem exists_veronesePushforwardIso (d : ℕ)
    [DirectSum.Decomposition (veroneseModuleGrading 𝒮 𝒨 d)] (hd : 0 < d) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    let i := veroneseProjIso 𝒮 d hd
    let F := associatedSchemeModules 𝒮 𝒨
    let G := associatedSchemeModules (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d)
    ∃ E : G ≅ (SheafOfModules.pushforward.{max u v} i.hom.toRingCatSheafHom).obj F,
      ∀ (f : S) (e : ℕ) (he : 0 < e) (hf : f ∈ 𝒮 e)
        (s : G.val.obj (op (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf)))),
      Eq.rec (motive := fun W _ => F.val.obj (op W))
        (ConcreteCategory.hom
          (E.hom.val.app (op (Proj.basicOpen (veroneseGrading 𝒮 d)
            (veronesePower 𝒮 d f hf)))) s)
        (veroneseProjIso_basicOpen 𝒮 d hd f he hf) =
          veroneseSectionsMap 𝒮 𝒨 d hd f he hf s := by
  let : GradedRing (veroneseGrading 𝒮 d) := veroneseGradingGradedRing 𝒮 d hd
  intro i F G
  let ι := {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒮 p.2}
  let U (a : ι) := Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d a.1.1 a.2.2)
  let V (a : ι) := Proj.basicOpen 𝒮 a.1.1
  have h (a : ι) : i.hom ⁻¹ᵁ U a = V a :=
    veroneseProjIso_basicOpen 𝒮 d hd a.1.1 a.2.1 a.2.2
  have hU : Opens.IsBasis (Set.range U) := by
    have heq : Set.range U = veronesePowerBasicOpenSet (𝒮 := 𝒮) d hd := by
      ext W
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨a.1.1, a.1.2, a.2.2, a.2.1, rfl⟩
      · rintro ⟨f, e, hf, he, rfl⟩
        exact ⟨⟨(f, e), he, hf⟩, rfl⟩
    rw [heq]
    exact veronesePowerBasicOpenSet_isBasis 𝒮 d hd
  let E (a : ι) := veroneseSectionIso 𝒮 𝒨 d hd a.1.1 a.2.1 a.2.2
  have hn (a b : ι) (hab : U b ≤ U a) (s : G.val.obj (op (U a))) :
      ConcreteCategory.hom (E b).hom (G.val.map (homOfLE hab).op s) =
        ((SheafOfModules.pushforward.{max u v} i.hom.toRingCatSheafHom).obj F).val.map
          (homOfLE hab).op (ConcreteCategory.hom (E a).hom s) := by
    have hab' : V b ≤ V a := by
      rw [← h a, ← h b]
      exact fun x hx ↦ hab hx
    exact veroneseSectionIso_naturality 𝒮 𝒨 d hd a.1.1 b.1.1 a.2.1 b.2.1 a.2.2 b.2.2
      hab hab' s
  obtain ⟨E₀, hE₀⟩ := exists_moduleSheafIso_of_sectionIso_onBasis
    G ((SheafOfModules.pushforward.{max u v} i.hom.toRingCatSheafHom).obj F) U hU E hn
  refine ⟨E₀, ?_⟩
  intro f k hk hf s
  have he' := congrArg (fun φ ↦ φ s) (hE₀ ⟨(f, k), hk, hf⟩)
  exact (congrArg (fun z ↦ Eq.rec (motive := fun W _ => F.val.obj (op W))
    z (h ⟨(f, k), hk, hf⟩)) he').trans
    (veroneseSectionIso_hom_apply 𝒮 𝒨 d hd f hk hf s)

/-- A morphism of sheaves of modules on a scheme commutes with transporting sections along an
equality of opens. -/
theorem moduleSheafHom_app_cast {X : Scheme.{u}} {F G : X.Modules}
    (φ : F ⟶ G) {U V : X.Opens} (h : U = V) (s : F.val.obj (op U)) :
    φ.val.app (op V) (h ▸ s) = h ▸ φ.val.app (op U) s := by
  cases h
  rfl

/-- A morphism of sheaves of modules on a scheme, with sections in `Type (max u v)`, commutes with
transporting sections along an equality of opens. -/
theorem sheafOfModulesHom_app_cast {X : Scheme.{u}}
    {F G : SheafOfModules.{max u v} X.ringCatSheaf}
    (φ : F ⟶ G) {U V : X.Opens} (h : U = V) (s : F.val.obj (op U)) :
    φ.val.app (op V) (h ▸ s) = h ▸ φ.val.app (op U) s := by
  cases h
  rfl

/-- The associated sheaf of the module is the pullback of the associated sheaf of the Veronese
module along the Veronese isomorphism, compatibly with the chartwise comparisons. -/
theorem exists_veroneseIso (d : ℕ)
    [DirectSum.Decomposition (veroneseModuleGrading 𝒮 𝒨 d)] (hd : 0 < d) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    let i := veroneseProjIso 𝒮 d hd
    let F := ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨
    let G := ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d)
    ∃ E : F ≅ (SheafOfModules.pullback.{max u v} i.hom.toRingCatSheafHom).obj G,
      ∀ (f : S) (e : ℕ) (he : 0 < e) (hf : f ∈ 𝒮 e)
        (s : G.val.obj (op (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf)))),
      E.inv.val.app (op (Proj.basicOpen 𝒮 f))
        ((veroneseProjIso_basicOpen 𝒮 d hd f he hf) ▸
          ((SheafOfModules.pullbackPushforwardAdjunction.{max u v}
            i.hom.toRingCatSheafHom).unit.app G).val.app
            (op (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf))) s) =
        veroneseSectionsMap 𝒮 𝒨 d hd f he hf s := by
  let : GradedRing (veroneseGrading 𝒮 d) := veroneseGradingGradedRing 𝒮 d hd
  intro i F G
  obtain ⟨e, he⟩ := exists_veronesePushforwardIso 𝒮 𝒨 d hd
  obtain ⟨E, hE⟩ := exists_pullbackIso_of_pushforwardIso i.hom F G e
  refine ⟨E, ?_⟩
  intro f k hk hf s
  let U := Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf)
  have h := veroneseProjIso_basicOpen 𝒮 d hd f hk hf
  have hc := sheafOfModulesHom_app_cast (X := AlgebraicGeometry.Proj 𝒮)
    (F := (SheafOfModules.pullback.{max u v} i.hom.toRingCatSheafHom).obj G) (G := F) E.inv h
    (((SheafOfModules.pullbackPushforwardAdjunction.{max u v}
      i.hom.toRingCatSheafHom).unit.app G).val.app (op U) s)
  have hh := congrArg (fun φ ↦ φ.val.app (op U) s) hE
  exact hc.trans ((congrArg (fun z ↦ Eq.rec (motive := fun W _ => F.val.obj (op W))
    z h) hh).trans (he f k hk hf s))

/-- **The associated sheaf of a graded module is the pullback of the associated sheaf of its
Veronese module** under the canonical Veronese isomorphism `i : Proj S ≅ Proj S⁽ᵈ⁾`, for a module
whose carrier lies in any universe `v`. -/
public noncomputable def veroneseAssociatedSheafIso (d : ℕ) (hd : 0 < d) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨 ≅
      (SheafOfModules.pullback.{max u v} (veroneseProjIso 𝒮 d hd).hom.toRingCatSheafHom).obj
        (ProjectiveSpectrum.Proj.associatedModuleSheaf
          (veroneseGrading 𝒮 d)
          (veroneseModuleGrading 𝒮 𝒨 d)) :=
  by
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    let i := veroneseProjIso 𝒮 d hd
    let F := ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨
    let G := ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d)
    exact Classical.choose (exists_veroneseIso 𝒮 𝒨 d hd)

/-- **The chart description of `veroneseAssociatedSheafIso`.** On each positive-degree standard
open `D₊(f) = i⁻¹ D₊(f ᵈ)`, its inverse sends the pullback of the section of the Veronese
module's sheaf given by `z ∈ M'₍f ᵈ₎` to the section of `M̃` given by the degree-zero Veronese
localization comparison `M'₍f ᵈ₎ ≅ M₍f₎` applied to `z`. -/
public theorem veroneseAssociatedSheafIso_standardOpen
    (d : ℕ) (hd : 0 < d) (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    ∀ z : GradedModuleDegreeZeroLocalization
      (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d)
      (veronesePower 𝒮 d f hf),
    let i := veroneseProjIso 𝒮 d hd
    let vf := veronesePower 𝒮 d f hf
    let U := Proj.basicOpen (veroneseGrading 𝒮 d) vf
    let V := Proj.basicOpen 𝒮 f
    let h : i.hom ⁻¹ᵁ U = V :=
      veroneseProjIso_basicOpen 𝒮 d hd f he hf
    let N := ProjectiveSpectrum.Proj.associatedModuleSheaf
      (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d)
    let s := (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv
      (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d)
      (show vf ∈ veroneseGrading 𝒮 d e from by
        change f ^ d ∈ 𝒮 (e * d)
        rw [mul_comm e d]
        simpa only [nsmul_eq_mul, Nat.cast_id] using SetLike.pow_mem_graded d hf) he).symm z
    (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf he)
      ((veroneseAssociatedSheafIso 𝒮 𝒨 d hd).inv.val.app (.op V)
        (h ▸ ((SheafOfModules.pullbackPushforwardAdjunction.{max u v}
          i.hom.toRingCatSheafHom).unit.app N).val.app (.op U) s)) =
      veroneseModuleAwayEquiv 𝒮 d 𝒨 f hf hd z :=
  by
    let : GradedRing (veroneseGrading 𝒮 d) := veroneseGradingGradedRing 𝒮 d hd
    let : DirectSum.Decomposition (veroneseModuleGrading 𝒮 𝒨 d) :=
      veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    intro z i vf U V h N s
    have H := Classical.choose_spec (exists_veroneseIso 𝒮 𝒨 d hd) f e he hf s
    let E := ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf he
    calc
      _ = E (veroneseSectionsMap 𝒮 𝒨 d hd f he hf s) :=
        congrArg E H
      _ = _ := by
        let E₁ := ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv
          (veroneseGrading 𝒮 d)
          (veroneseModuleGrading 𝒮 𝒨 d)
          (veronesePower_mem 𝒮 d f hf) he
        let E₂ := veroneseModuleAwayEquiv 𝒮 d 𝒨 f hf hd
        exact (E.apply_symm_apply (E₂ (E₁ s))).trans
          (congrArg E₂ (E₁.apply_symm_apply z))

end Stacks.Veronese

namespace Stacks.Veronese

open AlgebraicGeometry CategoryTheory DirectSum TopologicalSpace Opposite

attribute [local instance_reducible] TopCat.Sheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w

section ModuleInRingUniverse

variable {S M : Type u} {σ : Type w}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  (𝒨 : ℤ → AddSubgroup M)
  [Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨]

/-- `veroneseAssociatedSheafIso` for a module whose carrier lies in the universe of the ring,
written in Mathlib's `AlgebraicGeometry.Scheme.Modules` spelling of sheaves of modules on
`Proj S`. -/
public noncomputable def associatedModuleSheafVeroneseIso (d : ℕ) (hd : 0 < d) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨 ≅
      (Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
        (ProjectiveSpectrum.Proj.associatedModuleSheaf
          (veroneseGrading 𝒮 d)
          (veroneseModuleGrading 𝒮 𝒨 d)) :=
  veroneseAssociatedSheafIso 𝒮 𝒨 d hd

/-- The chart description of `associatedModuleSheafVeroneseIso`, in the
`AlgebraicGeometry.Scheme.Modules` spelling: `veroneseAssociatedSheafIso_standardOpen` at a
module in the universe of the ring. -/
public theorem associatedModuleSheafVeroneseIso_standardOpen
    (d : ℕ) (hd : 0 < d) (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    ∀ z : GradedModuleDegreeZeroLocalization
      (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d)
      (veronesePower 𝒮 d f hf),
    let i := veroneseProjIso 𝒮 d hd
    let vf := veronesePower 𝒮 d f hf
    let U := Proj.basicOpen (veroneseGrading 𝒮 d) vf
    let V := Proj.basicOpen 𝒮 f
    let h : i.hom ⁻¹ᵁ U = V :=
      veroneseProjIso_basicOpen 𝒮 d hd f he hf
    let N := ProjectiveSpectrum.Proj.associatedModuleSheaf
      (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d)
    let s := (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv
      (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d)
      (show vf ∈ veroneseGrading 𝒮 d e from by
        change f ^ d ∈ 𝒮 (e * d)
        rw [mul_comm e d]
        simpa only [nsmul_eq_mul, Nat.cast_id] using SetLike.pow_mem_graded d hf) he).symm z
    (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf he)
      ((associatedModuleSheafVeroneseIso 𝒮 𝒨 d hd).inv.val.app (.op V)
        (h ▸ ((Scheme.Modules.pullbackPushforwardAdjunction i.hom).unit.app N).val.app
          (.op U) s)) =
      veroneseModuleAwayEquiv 𝒮 d 𝒨 f hf hd z :=
  veroneseAssociatedSheafIso_standardOpen 𝒮 𝒨 d hd f he hf

end ModuleInRingUniverse

end Stacks.Veronese

end
