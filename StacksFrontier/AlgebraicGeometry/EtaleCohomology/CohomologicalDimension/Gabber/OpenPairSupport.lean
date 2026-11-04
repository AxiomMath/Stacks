module

public import StacksFrontier.Algebra.Homology.DerivedFunctorLongExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleZariskiCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RelativeMayerVietoris
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtale
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerived.DerivedDeltaFunctor

/-!
# Étale cohomology with support, for a pair of open subschemes

Let `X` be a scheme and `W ≤ V` two open subschemes. For an abelian sheaf `𝓕` on Mathlib's small
étale site of `X`, the sections of `𝓕` over `V` vanishing on `W` form an abelian group
`Γ_{V,W}(𝓕) = ker(𝓕(V) → 𝓕(W))`, functorial in `𝓕`; its right derived functors are the étale
cohomology of `V` with support in the closed subset `V ∖ W`. This file sets up the three facts
of that theory which the dévissage of Travaux de Gabber, Exposé XVIII-A, Lemma 2.2, uses:

* **the excision sequence**: for `W ≤ W' ≤ V` the functors `Γ_{V,W'} ⟶ Γ_{V,W} ⟶ Γ_{W',W}` form a
  short complex which is short exact on injective sheaves, so its right derived functors are
  exact in the middle;
* **excision**: restriction `Γ_{V ⊔ U, U} ⟶ Γ_{V, V ⊓ U}` is an isomorphism, by gluing;
* the two degenerate pairs: `Γ_{V,V} = 0`, and `Γ_{⊤,⊥}` is the global sections functor, so
  that the vanishing of its derived functors is the vanishing of `H^p(X, 𝓕)`.

## Main definitions

* `AlgebraicGeometry.Scheme.opensSupport`: the functor `Γ_{V,W}`.
* `AlgebraicGeometry.Scheme.opensSupportRestrict`: restriction `Γ_{V,W} ⟶ Γ_{V',W'}` for
  `V' ≤ V`, `W' ≤ W`.

## Main results

* `AlgebraicGeometry.Scheme.shortExact_opensSupport_of_injective`: the excision sequence is short
  exact at an injective sheaf.
* `AlgebraicGeometry.Scheme.exists_rightDerived_opensSupportRestrict_eq`: exactness in the middle
  of its derived sequence.
* `AlgebraicGeometry.Scheme.isIso_opensSupportRestrict_sup`: excision.
* `AlgebraicGeometry.Scheme.isZero_rightDerived_opensSupport_self` and
  `AlgebraicGeometry.Scheme.subsingleton_sheafH_of_isZero_rightDerived_opensSupport_bot`.

## References

* [Stacks Project, Tag 0A45](https://stacks.math.columbia.edu/tag/0A45)
* L. Illusie, *Cohomological dimension: first results*, in Travaux de Gabber, Exposé XVIII-A,
  Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- An inclusion of open subschemes is a monomorphism of the small étale site. -/
theorem mono_opensToEtale_map {V W : X.Opens} (f : W ⟶ V) : Mono ((opensToEtale X).map f) := by
  apply Functor.mono_of_mono_map (Scheme.Etale.forget X ⋙ Over.forget X)
  change Mono (X.homOfLE f.le)
  infer_instance

/-- Restriction of sections of an abelian sheaf on `X_ét` along an inclusion of opens. -/
abbrev opensRestrictMap (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) {V W : X.Opens}
    (h : W ≤ V) :
    F.obj.obj (op ((opensToEtale X).obj V)) ⟶ F.obj.obj (op ((opensToEtale X).obj W)) :=
  F.obj.map ((opensToEtale X).map (homOfLE h)).op

/-- Restricting along `W ≤ V` and then along `W' ≤ W` is restricting along `W' ≤ V`. -/
theorem opensRestrictMap_apply_apply (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {V W W' : X.Opens} (h : W ≤ V) (h' : W' ≤ W) (s : F.obj.obj (op ((opensToEtale X).obj V))) :
    opensRestrictMap F h' (opensRestrictMap F h s) = opensRestrictMap F (h'.trans h) s := by
  rw [opensRestrictMap, opensRestrictMap, opensRestrictMap, ← ConcreteCategory.comp_apply,
    ← F.obj.map_comp, ← op_comp, ← Functor.map_comp]
  rfl

/-- Restriction from an open subscheme to itself is the identity. -/
theorem opensRestrictMap_self_apply (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {V : X.Opens} (h : V ≤ V) (s : F.obj.obj (op ((opensToEtale X).obj V))) :
    opensRestrictMap F h s = s := by
  rw [opensRestrictMap, show homOfLE h = 𝟙 V from rfl, (opensToEtale X).map_id, op_id,
    F.obj.map_id]
  rfl

/-- Restriction of sections commutes with morphisms of abelian sheaves. -/
theorem opensRestrictMap_naturality {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : F ⟶ G) {V W : X.Opens} (h : W ≤ V) (s : F.obj.obj (op ((opensToEtale X).obj V))) :
    opensRestrictMap G h (φ.hom.app _ s) = φ.hom.app _ (opensRestrictMap F h s) :=
  (NatTrans.naturality_apply φ.hom _ s).symm

/-- **Sections over `V` vanishing on `W`**, `Γ_{V,W}(𝓕) = ker(𝓕(V) → 𝓕(W))`, as a functor of the
abelian sheaf `𝓕` on `X_ét`. Its right derived functors are the cohomology of `V` with support
in `V ∖ W`. -/
def opensSupport {V W : X.Opens} (h : W ≤ V) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} where
  obj F := AddCommGrpCat.of (opensRestrictMap F h).hom.ker
  map {F G} φ := AddCommGrpCat.ofHom
    { toFun := fun s => ⟨φ.hom.app _ s.1, by
        rw [AddMonoidHom.mem_ker, opensRestrictMap_naturality, s.2, map_zero]⟩
      map_zero' := by ext; simp
      map_add' := fun s t => by ext; simp }
  map_id F := by ext; rfl
  map_comp φ ψ := by ext; rfl

/-- The image of a section with support under `(opensSupport h).map φ` is `φ` applied to the
underlying section. -/
@[simp]
theorem opensSupport_map_apply_coe {V W : X.Opens} (h : W ≤ V)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (s : (opensSupport h).obj F) : ((opensSupport h).map φ s).1 = φ.hom.app _ s.1 :=
  rfl

/-- The functor `Γ_{V,W}` is additive. -/
instance opensSupport_additive {V W : X.Opens} (h : W ≤ V) : (opensSupport h).Additive where
  map_add := by intros; ext; rfl

/-- **Restriction of sections with support**: for `V' ≤ V` and `W' ≤ W` (with `W ≤ V`,
`W' ≤ V'`) restriction of sections carries `Γ_{V,W}` to `Γ_{V',W'}`. -/
def opensSupportRestrict {V W V' W' : X.Opens} (h : W ≤ V) (h' : W' ≤ V') (hV : V' ≤ V)
    (hW : W' ≤ W) : opensSupport h ⟶ opensSupport h' where
  app F := AddCommGrpCat.ofHom
    { toFun := fun s => ⟨opensRestrictMap F hV s.1, by
        have h1 := opensRestrictMap_apply_apply F h hW s.1
        have h2 := opensRestrictMap_apply_apply F hV h' s.1
        rw [AddMonoidHom.mem_ker.1 s.2, map_zero] at h1
        exact AddMonoidHom.mem_ker.2 (h2.trans h1.symm)⟩
      map_zero' := by ext; simp
      map_add' := fun s t => by ext; simp }
  naturality F G φ := by
    ext s
    exact Subtype.ext (opensRestrictMap_naturality φ hV s.1)

/-- The underlying section of the restriction of a section with support is its restriction. -/
@[simp]
theorem opensSupportRestrict_app_apply_coe {V W V' W' : X.Opens} (h : W ≤ V) (h' : W' ≤ V')
    (hV : V' ≤ V) (hW : W' ≤ W) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (s : (opensSupport h).obj F) :
    ((opensSupportRestrict h h' hV hW).app F s).1 = opensRestrictMap F hV s.1 :=
  rfl

/-- Restrictions of sections with support compose. -/
theorem opensSupportRestrict_comp {V W V' W' V'' W'' : X.Opens} (h : W ≤ V) (h' : W' ≤ V')
    (h'' : W'' ≤ V'') (hV : V' ≤ V) (hW : W' ≤ W) (hV' : V'' ≤ V') (hW' : W'' ≤ W') :
    opensSupportRestrict h h' hV hW ≫ opensSupportRestrict h' h'' hV' hW' =
      opensSupportRestrict h h'' (hV'.trans hV) (hW'.trans hW) := by
  ext F s
  exact Subtype.ext (opensRestrictMap_apply_apply F hV hV' s.1)

/-- A section with support restricts to zero. -/
private theorem opensRestrictMap_coe_eq_zero {V W : X.Opens} {h : W ≤ V}
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (s : (opensSupport h).obj F) :
    opensRestrictMap F h s.1 = 0 :=
  AddMonoidHom.mem_ker.1 s.2

/-! ### The excision sequence -/

section Excision

variable {V W W' : X.Opens} (hWW' : W ≤ W') (hW'V : W' ≤ V)

/-- The composite `Γ_{V,W'} ⟶ Γ_{V,W} ⟶ Γ_{W',W}` vanishes. -/
theorem opensSupportRestrict_comp_eq_zero :
    opensSupportRestrict hW'V (hWW'.trans hW'V) le_rfl hWW' ≫
        opensSupportRestrict (hWW'.trans hW'V) hWW' hW'V le_rfl = 0 := by
  ext F s
  apply Subtype.ext
  rw [NatTrans.app_zero, AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply]
  change opensRestrictMap F hW'V (opensRestrictMap F le_rfl s.1) = 0
  rw [opensRestrictMap_self_apply]
  exact opensRestrictMap_coe_eq_zero s

/-- **The excision sequence `Γ_{V,W'} ⟶ Γ_{V,W} ⟶ Γ_{W',W}` is short exact at an injective
sheaf.** The first map is an inclusion of subgroups of `𝓕(V)`, the sequence is exact in the middle
by definition, and the second map is surjective because restriction of sections of an injective
sheaf along the monomorphism `W' ⟶ V` of the site is surjective (Stacks 093X). -/
theorem shortExact_opensSupport_of_injective
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective I] :
    (NatTrans.appShortComplex _ _ (opensSupportRestrict_comp_eq_zero hWW' hW'V) I).ShortExact := by
  have hmono : Mono ((opensSupportRestrict hW'V (hWW'.trans hW'V) le_rfl hWW').app I) := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro s t hst
    have := congrArg Subtype.val hst
    simp only [opensSupportRestrict_app_apply_coe, opensRestrictMap_self_apply] at this
    exact Subtype.ext this
  have hepi : Epi ((opensSupportRestrict (hWW'.trans hW'V) hWW' hW'V le_rfl).app I) := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro t
    have : Mono ((opensToEtale X).map (homOfLE hW'V)) := mono_opensToEtale_map _
    obtain ⟨s, hs⟩ := Stacks.EtaleCohomology.RelativeMayerVietoris.injective_sections_map_surjective
      X.smallEtaleTopology I ((opensToEtale X).map (homOfLE hW'V)) t.1
    refine ⟨⟨s, ?_⟩, Subtype.ext hs⟩
    have h1 : opensRestrictMap I hWW' (opensRestrictMap I hW'V s) = 0 := by
      rw [show opensRestrictMap I hW'V s = t.1 from hs]
      exact t.2
    rwa [opensRestrictMap_apply_apply] at h1
  refine ShortComplex.ShortExact.mk' ?_ hmono hepi
  rw [ShortComplex.ab_exact_iff]
  intro x hx
  exact ⟨⟨x.1, congrArg Subtype.val hx⟩, Subtype.ext (opensRestrictMap_self_apply I le_rfl x.1)⟩

/-- **Exactness in the middle of the derived excision sequence**: a class of
`R^iΓ_{V,W}(𝓕)` which restricts to zero in `R^iΓ_{W',W}(𝓕)` comes from `R^iΓ_{V,W'}(𝓕)`. -/
theorem exists_rightDerived_opensSupportRestrict_eq
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ)
    (x : ((opensSupport (hWW'.trans hW'V)).rightDerived i).obj F)
    (hx : (NatTrans.rightDerived (opensSupportRestrict (hWW'.trans hW'V) hWW' hW'V le_rfl) i).app
      F x = 0) :
    ∃ y : ((opensSupport hW'V).rightDerived i).obj F,
      (NatTrans.rightDerived (opensSupportRestrict hW'V (hWW'.trans hW'V) le_rfl
        hWW') i).app F y = x := by
  have hex := exact_rightDerived_composableArrows₅ _ _ (opensSupportRestrict_comp_eq_zero hWW' hW'V)
    (fun I hI => by
      have := hI
      exact shortExact_opensSupport_of_injective hWW' hW'V I) (injectiveResolution F) i
  have h0 := hex.exact 0
  rw [ShortComplex.ab_exact_iff] at h0
  exact h0 x hx

end Excision

/-! ### Excision and the degenerate pairs -/

/-- The restriction of an abelian sheaf on `X_ét` to the opens of `X`, as a sheaf on the
topological space of `X`. -/
abbrev etaleOpensSheaf (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    TopCat.Sheaf AddCommGrpCat.{u + 1} X.toPresheafedSpace.carrier :=
  (zariskiPushforward X).obj F

/-- **Excision.** Restriction `Γ_{U ⊔ V, U}(𝓕) ⟶ Γ_{V, V ⊓ U}(𝓕)` is bijective: a section over
`U ⊔ V` vanishing on `U` is determined by its restriction to `V`, and a section over `V` vanishing
on `V ⊓ U` glues with the zero section over `U`. -/
theorem bijective_opensSupportRestrict_sup (U V : X.Opens)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Function.Bijective ((opensSupportRestrict (le_sup_left : U ≤ U ⊔ V) (inf_le_left : V ⊓ U ≤ V)
      (le_sup_right : V ≤ U ⊔ V) (inf_le_right : V ⊓ U ≤ U)).app F) := by
  let G := etaleOpensSheaf F
  constructor
  · rw [injective_iff_map_eq_zero]
    intro s hs
    exact Subtype.ext <| G.eq_of_locally_eq₂ (homOfLE (le_sup_left : U ≤ U ⊔ V))
      (homOfLE (le_sup_right : V ≤ U ⊔ V)) le_rfl s.1 0
      ((opensRestrictMap_coe_eq_zero s).trans (map_zero _).symm)
      ((congrArg Subtype.val hs).trans (map_zero _).symm)
  · intro t
    have ht := opensRestrictMap_coe_eq_zero t
    let Uf : Bool → X.Opens := fun b => Bool.rec V U b
    let sf : ∀ b : Bool, ToType (G.1.obj (op (Uf b))) := fun b =>
      Bool.rec (motive := fun b => ToType (G.1.obj (op (Uf b)))) t.1 0 b
    have hcompat : TopCat.Presheaf.IsCompatible G.1 Uf sf := by
      intro i j
      cases i <;> cases j
      · rfl
      · change opensRestrictMap F (inf_le_left : V ⊓ U ≤ V) t.1 =
          opensRestrictMap F (inf_le_right : V ⊓ U ≤ U) 0
        rw [ht, map_zero]
      · change opensRestrictMap F (inf_le_left : U ⊓ V ≤ U) 0 =
          opensRestrictMap F (inf_le_right : U ⊓ V ≤ V) t.1
        rw [map_zero]
        exact ((opensRestrictMap_apply_apply F (inf_le_left : V ⊓ U ≤ V)
          (le_of_eq (inf_comm U V)) t.1).symm.trans (by rw [ht, map_zero])).symm
      · rfl
    obtain ⟨g, hg, -⟩ := G.existsUnique_gluing' Uf (U ⊔ V)
      (fun b => Bool.rec (motive := fun b => Uf b ⟶ U ⊔ V) (homOfLE le_sup_right)
        (homOfLE le_sup_left) b)
      (sup_le (le_iSup Uf true) (le_iSup Uf false)) sf hcompat
    exact ⟨⟨g, AddMonoidHom.mem_ker.2 (hg true)⟩, Subtype.ext (hg false)⟩

/-- Excision, as an isomorphism of functors. -/
instance isIso_opensSupportRestrict_sup (U V : X.Opens) :
    IsIso (opensSupportRestrict (le_sup_left : U ≤ U ⊔ V) (inf_le_left : V ⊓ U ≤ V)
      (le_sup_right : V ≤ U ⊔ V) (inf_le_right : V ⊓ U ≤ U)) := by
  have : ∀ F, IsIso ((opensSupportRestrict (le_sup_left : U ≤ U ⊔ V) (inf_le_left : V ⊓ U ≤ V)
      (le_sup_right : V ≤ U ⊔ V) (inf_le_right : V ⊓ U ≤ U)).app F) := fun F =>
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_opensSupportRestrict_sup U V F)
  exact NatIso.isIso_of_isIso_app _

/-- **`Γ_{V,V} = 0`**, so all its right derived functors vanish. -/
theorem isZero_rightDerived_opensSupport_self (V : X.Opens)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ) :
    IsZero (((opensSupport (le_refl V)).rightDerived i).obj F) := by
  have hz : ∀ G, IsZero ((opensSupport (le_refl V)).obj G) := fun G => by
    rw [AddCommGrpCat.isZero_of_iff_subsingleton]
    refine ⟨fun s t => Subtype.ext ?_⟩
    have hs := opensRestrictMap_coe_eq_zero s
    have ht := opensRestrictMap_coe_eq_zero t
    rw [opensRestrictMap_self_apply] at hs ht
    exact hs.trans ht.symm
  exact (HomologicalComplex.ExactAt.isZero_homology
    (HomologicalComplex.ExactAt.of_isZero (hz _))).of_iso
      ((injectiveResolution F).isoRightDerivedObj _ i)

/-- Sections over the empty open subscheme of an abelian sheaf on `X_ét` form the zero group. -/
theorem subsingleton_etaleSections_bot (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Subsingleton (F.obj.obj (op ((opensToEtale X).obj ⊥))) :=
  AddCommGrpCat.subsingleton_of_isZero (etaleOpensSheaf F).isTerminalOfEmpty.isZero

/-- `Γ_{⊤,⊥}` is the functor of sections over the final object `⊤`. -/
def opensSupportBotToSections : opensSupport (bot_le : (⊥ : X.Opens) ≤ ⊤) ⟶
    (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op ((opensToEtale X).obj ⊤)) where
  app _ := AddCommGrpCat.ofHom (AddSubgroup.subtype _)
  naturality _ _ _ := rfl

/-- `Γ_{⊤,⊥}` is isomorphic to the functor of sections over `⊤`. -/
instance isIso_opensSupportBotToSections : IsIso (opensSupportBotToSections (X := X)) := by
  have : ∀ G, IsIso ((opensSupportBotToSections (X := X)).app G) := fun G => by
    refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨Subtype.val_injective, fun s => ?_⟩
    have := subsingleton_etaleSections_bot G
    exact ⟨⟨s, AddMonoidHom.mem_ker.2 (Subsingleton.elim _ _)⟩, rfl⟩
  exact NatIso.isIso_of_isIso_app _

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology
  Stacks.EtaleCohomology.smallEtaleGlobalSectionsAb_additive

/-- **`Γ_{⊤,⊥}` computes étale cohomology**: if the `i`-th right derived functor of `Γ_{⊤,⊥}`
vanishes at `𝓕` then `H^i(X, 𝓕) = 0`. -/
theorem subsingleton_sheafH_of_isZero_rightDerived_opensSupport_bot
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ)
    (h : IsZero (((opensSupport (bot_le : (⊥ : X.Opens) ≤ ⊤)).rightDerived i).obj F)) :
    Subsingleton (Sheaf.H.{u + 1} F i) := by
  let e : opensSupport (bot_le : (⊥ : X.Opens) ≤ ⊤) ≅ Sheaf.Γ X.smallEtaleTopology
      AddCommGrpCat.{u + 1} :=
    asIso opensSupportBotToSections ≪≫
      (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
        (isTerminal_opensToEtale_top X)).symm
  refine (Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{0}
    _ _ _).2 ?_
  exact h.of_iso ((Stacks.Cohomology.CechDelta.rightDerivedIsoOfIso e i).app F).symm

end AlgebraicGeometry.Scheme

end
