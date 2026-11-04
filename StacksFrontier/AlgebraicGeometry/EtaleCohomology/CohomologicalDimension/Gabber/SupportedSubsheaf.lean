module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.OpenPairSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ZariskiRestrictionSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointDirectSumCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.SupportedSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleBaseChange

/-!
# The subsheaf of sections supported in a closed subset

Let `X` be a scheme, `U ⊆ X` open, and `𝓕` an abelian sheaf on Mathlib's small étale site of `X`.
The sections of `𝓕` *supported in `X ∖ U`* over an object `W` of `X_ét` are those whose restriction
to every object `W' ⟶ W` landing in `U` vanishes. They form a subsheaf `𝒦_U(𝓕) ⊆ 𝓕`, functorial in
`𝓕`, the sheaf `i_* i^! 𝓕` of the source for `i` the inclusion of `X ∖ U`. Over an open `V ⊆ X` its
sections are the group `Γ_{V, V ⊓ U}(𝓕)` of sections over `V` vanishing on `V ⊓ U`
(`AlgebraicGeometry.Scheme.opensSupportIsoSupportedSubsheaf`), so the cohomology with support
`R^iΓ_{V,V⊓U}` is the derived functor of the composite of `𝒦_U` with sections over `V`.

## Main definitions

* `AlgebraicGeometry.Scheme.supportedSubgroup`: the sections supported in `X ∖ U`.
* `AlgebraicGeometry.Scheme.supportedSubsheaf`: the functor `𝓕 ↦ 𝒦_U(𝓕)`.
* `AlgebraicGeometry.Scheme.supportedSubsheafι`: its inclusion into the identity.

## Main results

* `AlgebraicGeometry.Scheme.isSheaf_supportedPresheaf`: the supported sections form a sheaf.
* `AlgebraicGeometry.Scheme.opensSupportIsoSupportedSubsheaf`: over an open `V`, the sections of
  `𝒦_U(𝓕)` are `Γ_{V, V ⊓ U}(𝓕)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (U : X.Opens)

/-- An object of `X_ét` *lands in* `U` when it maps to the open subscheme `U`. -/
def LandsIn (W : X.Etale) : Prop := Nonempty (W ⟶ (opensToEtale X).obj U)

/-- An object over one landing in `U` lands in `U`. -/
theorem LandsIn.of_hom {U} {W' W : X.Etale} (f : W' ⟶ W) (h : LandsIn U W) : LandsIn U W' :=
  ⟨f ≫ h.some⟩

/-- **Sections supported in `X ∖ U`**: the sections of `𝓕` over `W` whose restriction to every
object over `W` landing in `U` vanishes. -/
def supportedSubgroup (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (W : X.Etale) :
    AddSubgroup (F.obj.obj (op W)) where
  carrier := {s | ∀ (W' : X.Etale) (f : W' ⟶ W), LandsIn U W' → F.obj.map f.op s = 0}
  zero_mem' := fun _ _ _ => map_zero _
  add_mem' := fun ha hb W' f h => by rw [map_add, ha W' f h, hb W' f h, add_zero]
  neg_mem' := fun ha W' f h => by rw [map_neg, ha W' f h, neg_zero]

/-- The restriction of a section supported in `X ∖ U` is supported in `X ∖ U`. -/
theorem map_mem_supportedSubgroup (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {W W₂ : X.Etale} (g : W₂ ⟶ W) {s : F.obj.obj (op W)} (hs : s ∈ supportedSubgroup U F W) :
    F.obj.map g.op s ∈ supportedSubgroup U F W₂ := by
  intro W' f h
  rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp, ← op_comp]
  exact hs W' (f ≫ g) h

/-- A section supported in `X ∖ U` over an object landing in `U` is zero. -/
private theorem eq_zero_of_landsIn_of_mem_supportedSubgroup
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {W : X.Etale}
    {s : F.obj.obj (op W)} (hs : s ∈ supportedSubgroup U F W) (h : LandsIn U W) : s = 0 := by
  simpa using hs W (𝟙 W) h

/-- The presheaf of sections supported in `X ∖ U`. -/
def supportedPresheaf (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj W := AddCommGrpCat.of (supportedSubgroup U F W.unop)
  map {W W₂} g := AddCommGrpCat.ofHom
    { toFun := fun s => ⟨F.obj.map g s.1, map_mem_supportedSubgroup U F g.unop s.2⟩
      map_zero' := by ext; exact map_zero _
      map_add' := fun s t => by ext; exact map_add _ _ _ }
  map_id W := by
    ext s
    change F.obj.map (𝟙 W) s.1 = s.1
    rw [F.obj.map_id]
    rfl
  map_comp f g := by
    ext s
    change F.obj.map (f ≫ g) s.1 = F.obj.map g (F.obj.map f s.1)
    rw [F.obj.map_comp]
    rfl

/-- **The supported sections form a sheaf.** An amalgamation in `𝓕` of a compatible family of
supported sections is supported: its restriction to an object `W'` landing in `U` is zero on the
pulled back covering of `W'`, every member of which lands in `U` too. -/
theorem isSheaf_supportedPresheaf (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Presheaf.IsSheaf X.smallEtaleTopology (supportedPresheaf U F) := by
  have hF : Presieve.IsSheaf X.smallEtaleTopology
      (F.obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      ((Presheaf.isSheaf_iff_isSheaf_forget X.smallEtaleTopology F.obj
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).1 F.property)
  refine (Presheaf.isSheaf_iff_isSheaf_forget X.smallEtaleTopology _
    (CategoryTheory.forget AddCommGrpCat.{u + 1})).2 ((isSheaf_iff_isSheaf_of_type _ _).2 ?_)
  intro W S hS x hx
  let y : Presieve.FamilyOfElements (F.obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1})
      S.arrows :=
    fun _ f hf => (x f hf).1
  have hy : y.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
    exact congrArg Subtype.val (hx g₁ g₂ h₁ h₂ hcomm)
  obtain ⟨t, ht, htu⟩ := hF S hS y hy
  have hmem : t ∈ supportedSubgroup U F W := by
    intro W' f hW'
    refine (hF _ (X.smallEtaleTopology.pullback_stable f hS)).isSeparatedFor.ext fun W'' g hg => ?_
    change F.obj.map g.op (F.obj.map f.op t) = F.obj.map g.op 0
    rw [map_zero, ← ConcreteCategory.comp_apply, ← F.obj.map_comp, ← op_comp]
    have h1 : F.obj.map (g ≫ f).op t = y (g ≫ f) hg := ht (g ≫ f) hg
    rw [h1]
    exact eq_zero_of_landsIn_of_mem_supportedSubgroup U (x (g ≫ f) hg).2 (hW'.of_hom g)
  refine ⟨⟨t, hmem⟩, fun Y f hf => Subtype.ext (ht f hf), fun t' ht' => Subtype.ext ?_⟩
  exact htu t'.1 fun Y f hf => congrArg Subtype.val (ht' f hf)

/-- **The subsheaf `𝒦_U(𝓕)` of sections supported in `X ∖ U`**, as a functor of `𝓕`. -/
def supportedSubsheaf :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} where
  obj F := ⟨supportedPresheaf U F, isSheaf_supportedPresheaf U F⟩
  map {F G} φ := ⟨{
    app W := AddCommGrpCat.ofHom
      { toFun := fun s => ⟨φ.hom.app W s.1, fun W' f h => by
          rw [← NatTrans.naturality_apply φ.hom f.op, s.2 W' f h, map_zero]⟩
        map_zero' := by ext; exact map_zero _
        map_add' := fun s t => by ext; exact map_add _ _ _ }
    naturality _ _ g := by
      ext s
      exact Subtype.ext (NatTrans.naturality_apply φ.hom g s.1) }⟩
  map_id F := by ext; rfl
  map_comp φ ψ := by ext; rfl

/-- The inclusion `𝒦_U(𝓕) ⟶ 𝓕`. -/
def supportedSubsheafι : supportedSubsheaf U ⟶ 𝟭 _ where
  app _ := ⟨{
    app _ := AddCommGrpCat.ofHom (AddSubgroup.subtype _)
    naturality _ _ _ := rfl }⟩
  naturality _ _ _ := rfl

/-- The inclusion `𝒦_U(𝓕) ⟶ 𝓕` sends a supported section to its underlying section. -/
theorem supportedSubsheafι_app_apply (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (W : X.Etaleᵒᵖ) (s : ((supportedSubsheaf U).obj F).obj.obj W) :
    ((supportedSubsheafι U).app F).hom.app W s = s.1 :=
  rfl

/-- The inclusion `𝒦_U(𝓕) ⟶ 𝓕` is a monomorphism. -/
instance mono_supportedSubsheafι_app (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Mono ((supportedSubsheafι U).app F) := by
  apply Functor.mono_of_mono_map (sheafToPresheaf _ _)
  refine (NatTrans.mono_iff_mono_app _).2 fun W => ?_
  exact (AddCommGrpCat.mono_iff_injective _).2 Subtype.val_injective

/-- The functor `𝓕 ↦ 𝒦_U(𝓕)` is additive. -/
instance supportedSubsheaf_additive : (supportedSubsheaf U).Additive where
  map_add := by intros; ext; rfl

/-! ### Sections over an open subscheme -/

section Opens

variable {U} {V W : X.Opens} (h : W ≤ V) (hWU : W ≤ U) (hVU : V ⊓ U ≤ W)

include hVU in
/-- A section over `V` vanishing on `W = V ⊓ U` is supported in `X ∖ U`. -/
theorem mem_supportedSubgroup_of_opensSupport (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (s : (opensSupport h).obj F) : s.1 ∈ supportedSubgroup U F ((opensToEtale X).obj V) := by
  intro W' f hW'
  have hV := range_subset_of_hom_opensToEtale f
  have hU := range_subset_of_hom_opensToEtale hW'.some
  let e : W' ⟶ (opensToEtale X).obj W :=
    homToOpensToEtale W' W fun x hx => hVU ⟨hV hx, hU hx⟩
  have hf : f = e ≫ (opensToEtale X).map (homOfLE h) := Subsingleton.elim _ _
  rw [hf, op_comp, F.obj.map_comp, ConcreteCategory.comp_apply]
  change F.obj.map e.op (opensRestrictMap F h s.1) = 0
  rw [AddMonoidHom.mem_ker.1 s.2, map_zero]

include hWU in
/-- A section over `V` supported in `X ∖ U` vanishes on `W ⊆ U`. -/
theorem mem_opensSupport_of_mem_supportedSubgroup
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {s : F.obj.obj (op ((opensToEtale X).obj V))}
    (hs : s ∈ supportedSubgroup U F ((opensToEtale X).obj V)) :
    s ∈ (opensRestrictMap F h).hom.ker :=
  hs _ ((opensToEtale X).map (homOfLE h)) ⟨(opensToEtale X).map (homOfLE hWU)⟩

/-- **Over an open `V`, the sections of `𝒦_U(𝓕)` are `Γ_{V, V ⊓ U}(𝓕)`**, naturally in `𝓕`,
for any `W` with `V ⊓ U ≤ W ≤ U`. -/
def opensSupportIsoSupportedSubsheaf :
    opensSupport h ≅ supportedSubsheaf U ⋙
      (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op ((opensToEtale X).obj V)) :=
  NatIso.ofComponents (fun F => AddEquiv.toAddCommGrpIso
    { toFun := fun s => ⟨s.1, mem_supportedSubgroup_of_opensSupport h hVU F s⟩
      invFun := fun s => ⟨s.1, mem_opensSupport_of_mem_supportedSubgroup h hWU F s.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }) (fun _ => rfl)

/-- The isomorphism `opensSupportIsoSupportedSubsheaf` preserves underlying sections. -/
theorem opensSupportIsoSupportedSubsheaf_hom_app_apply
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (s : (opensSupport h).obj F) :
    ((opensSupportIsoSupportedSubsheaf h hWU hVU).hom.app F s).1 = s.1 :=
  rfl

/-- The identification `opensSupportIsoSupportedSubsheaf` is compatible with restriction to a
smaller open. -/
theorem opensSupportRestrict_comp_opensSupportIsoSupportedSubsheaf_hom {V' W' : X.Opens}
    (h' : W' ≤ V') (hW'U : W' ≤ U) (hV'U : V' ⊓ U ≤ W') (hV : V' ≤ V) (hW : W' ≤ W) :
    opensSupportRestrict h h' hV hW ≫ (opensSupportIsoSupportedSubsheaf h' hW'U hV'U).hom =
      (opensSupportIsoSupportedSubsheaf h hWU hVU).hom ≫
        Functor.whiskerLeft (supportedSubsheaf U)
          ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
            ((opensToEtale X).map (homOfLE hV)).op) := by
  ext F s
  rfl

end Opens

/-! ### The supported subsheaf vanishes on `U` -/

/-- **Restricted to `U`, the supported subsheaf vanishes**: a supported section over an object
landing in `U` restricts to itself along the identity, hence is zero. -/
theorem isZero_etaleRestriction_supportedSubsheaf
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsZero ((Stacks.EtaleCohomology.etaleRestriction.{u, 0} U.ι).obj
      ((supportedSubsheaf U).obj F)) := by
  refine Stacks.EtaleCohomology.isZero_of_forall_isZero_sections.{u, 0} _ fun W' => ?_
  rw [AddCommGrpCat.isZero_of_iff_subsingleton]
  refine ⟨fun s t => ?_⟩
  have hl : LandsIn U ((Scheme.Etale.smallEtaleCompose U.ι).obj W') := by
    refine ⟨homToOpensToEtale _ U ?_⟩
    rintro _ ⟨y, rfl⟩
    change U.ι (W'.hom y) ∈ U
    have := Set.mem_range_self (f := U.ι.base) (W'.hom y)
    rwa [Scheme.Opens.range_ι] at this
  exact Subtype.ext ((eq_zero_of_landsIn_of_mem_supportedSubgroup U s.2 hl).trans
    (eq_zero_of_landsIn_of_mem_supportedSubgroup U t.2 hl).symm)

/-! ### The supported subsheaf preserves injective sheaves -/

section Injective

/-- The reduced closed subscheme structure on the complement `X ∖ U`. -/
abbrev supportComplementIdeal : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds X)

/-- The closed immersion of `supportComplementIdeal U` has image the complement of `U`. -/
theorem range_supportComplementIdeal_subschemeι :
    Set.range (supportComplementIdeal U).subschemeι.base = (U : Set X)ᶜ := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- Over an object landing in `U`, a direct image from `X ∖ U` has zero sections. -/
theorem subsingleton_sections_pushforward_complement {W' : X.Etale} (hW' : LandsIn U W')
    (B : Sheaf (supportComplementIdeal U).subscheme.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Subsingleton (((Stacks.EtaleCohomology.smallEtalePushforwardAb
      (supportComplementIdeal U).subschemeι).obj B).obj.obj (op W')) := by
  refine AddCommGrpCat.subsingleton_of_isZero
    (Stacks.EtaleCohomology.isZero_sections_of_isEmpty.{u, 0} B _ ?_)
  change IsEmpty (Limits.pullback (C := Scheme.{u}) W'.hom (supportComplementIdeal U).subschemeι)
  refine Scheme.isEmpty_pullback _ _ (Set.disjoint_left.2 ?_)
  rintro x hx hx'
  rw [range_supportComplementIdeal_subschemeι] at hx'
  exact hx' (range_subset_of_hom_opensToEtale hW'.some hx)

/-- A morphism into an abelian sheaf from a direct image from `X ∖ U` takes values in supported
sections. -/
theorem mem_supportedSubgroup_of_pushforward_complement
    (B : Sheaf (supportComplementIdeal U).subscheme.smallEtaleTopology AddCommGrpCat.{u + 1})
    {I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (g : (Stacks.EtaleCohomology.smallEtalePushforwardAb
      (supportComplementIdeal U).subschemeι).obj B ⟶ I)
    (W : X.Etaleᵒᵖ) (t) : g.hom.app W t ∈ supportedSubgroup U I W.unop := by
  intro W' f hW'
  rw [← NatTrans.naturality_apply g.hom f.op]
  have := subsingleton_sections_pushforward_complement U hW' B
  rw [Subsingleton.elim (((Stacks.EtaleCohomology.smallEtalePushforwardAb
      (supportComplementIdeal U).subschemeι).obj B).obj.map f.op t) 0, map_zero]

/-- The factorization of a morphism from a direct image from `X ∖ U` through the supported
subsheaf. -/
def liftSupportedSubsheaf
    (B : Sheaf (supportComplementIdeal U).subscheme.smallEtaleTopology AddCommGrpCat.{u + 1})
    {I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (g : (Stacks.EtaleCohomology.smallEtalePushforwardAb
      (supportComplementIdeal U).subschemeι).obj B ⟶ I) :
    (Stacks.EtaleCohomology.smallEtalePushforwardAb (supportComplementIdeal U).subschemeι).obj B ⟶
      (supportedSubsheaf U).obj I :=
  ⟨{ app W := AddCommGrpCat.ofHom
      { toFun := fun t => ⟨g.hom.app W t, mem_supportedSubgroup_of_pushforward_complement U B g W t⟩
        map_zero' := by ext; exact map_zero _
        map_add' := fun _ _ => by ext; exact map_add _ _ _ }
     naturality _ _ f := by
      ext t
      exact Subtype.ext (NatTrans.naturality_apply g.hom f t) }⟩

/-- The factorization `liftSupportedSubsheaf` composed with the inclusion of the supported subsheaf
is the original morphism. -/
theorem liftSupportedSubsheaf_ι
    (B : Sheaf (supportComplementIdeal U).subscheme.smallEtaleTopology AddCommGrpCat.{u + 1})
    {I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (g : (Stacks.EtaleCohomology.smallEtalePushforwardAb
      (supportComplementIdeal U).subschemeι).obj B ⟶ I) :
    liftSupportedSubsheaf U B g ≫ (supportedSubsheafι U).app I = g := by
  ext W t
  rfl

/-- **The supported subsheaf of an injective sheaf is injective.** It vanishes on `U`, so it is the
direct image `i_*H` of a sheaf `H` on `X ∖ U` (Stacks 04CA); `H` is injective because a morphism
into `i_*H` from a direct image extends through the injective `I`, every morphism from a direct
image into `I` lands in the supported subsheaf, and `i_*` is fully faithful. -/
theorem injective_supportedSubsheaf_obj (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    [Injective I] : Injective ((supportedSubsheaf U).obj I) := by
  let i := (supportComplementIdeal U).subschemeι
  let iP := Stacks.EtaleCohomology.smallEtalePushforwardAb i
  have hess : iP.essImage ((supportedSubsheaf U).obj I) := by
    refine (Stacks.EtaleCohomology.abelianEssImageClosedImmersion i U
      (by rw [range_supportComplementIdeal_subschemeι, compl_compl]) _).2 ?_
    exact (isZero_etaleRestriction_supportedSubsheaf U I).of_iso
      ((Stacks.EtaleCohomology.smallEtalePullbackAbIsoEtaleRestriction U.ι).app _)
  obtain ⟨H, ⟨e⟩⟩ := hess
  have : iP.Full := inferInstanceAs
    (((Stacks.EtaleCohomology.smallEtaleBaseChange i).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} _ _).Full)
  have : iP.Faithful := inferInstanceAs
    (((Stacks.EtaleCohomology.smallEtaleBaseChange i).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} _ _).Faithful)
  have : iP.IsRightAdjoint := (Stacks.EtaleCohomology.smallEtaleAdjunctionAb i).isRightAdjoint
  have : Injective H := ⟨fun {A B} g f hf => by
    let G' : iP.obj A ⟶ I := iP.map g ≫ e.hom ≫ (supportedSubsheafι U).app I
    let h₀ := Injective.factorThru G' (iP.map f)
    have hh₀ : iP.map f ≫ h₀ = G' := Injective.comp_factorThru _ _
    let h₁ := liftSupportedSubsheaf U B h₀
    refine ⟨iP.preimage (h₁ ≫ e.inv), iP.map_injective ?_⟩
    rw [Functor.map_comp, Functor.map_preimage]
    have h₂ : iP.map f ≫ h₁ = iP.map g ≫ e.hom := by
      rw [← cancel_mono ((supportedSubsheafι U).app I), Category.assoc, liftSupportedSubsheaf_ι,
        hh₀, Category.assoc]
    rw [← Category.assoc, h₂, Category.assoc, e.hom_inv_id, Category.comp_id]⟩
  exact Injective.of_iso e (Functor.injective_obj iP H)

/-- **The supported subsheaf functor preserves injective sheaves.** -/
instance supportedSubsheaf_preservesInjectiveObjects :
    (supportedSubsheaf U).PreservesInjectiveObjects where
  injective_obj {I} _ := injective_supportedSubsheaf_obj U I

end Injective

end AlgebraicGeometry.Scheme

end
