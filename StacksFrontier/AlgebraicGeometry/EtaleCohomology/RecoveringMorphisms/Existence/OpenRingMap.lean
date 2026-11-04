module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.Existence.GeneralizedElements
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.AffineCase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.OpenLocalization

/-!
# The ring maps over affine opens and the morphism of schemes they glue to

Let `(g, g^♯) : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)` be a morphism of ringed topoi between
the small étale ringed topoi of two schemes.  For an open `V` of `Y` write `h_V` for the sheaf it
represents on `Y_étale` and `W_V` for the open of `X` with `g⁻¹h_V ≅ h_{W_V}`
(`AlgebraicGeometry.inverseImageOpen`, Stacks 04HV).  A section `b` of `𝒪_Y` over `V` is a
generalized element `h_V ⟶ 𝒪_Y`, and `g⁻¹b` followed by `g^♯` is a generalized element
`h_{W_V} ⟶ 𝒪_X`, i.e. a section of `𝒪_X` over `W_V`.  This is a ring homomorphism
`φ_V : Γ(V, ⊤) ⟶ Γ(W_V, ⊤)` (`AlgebraicGeometry.openRingHom`), natural in `V`.

For `V` affine, `φ_V` is a morphism of schemes `f_V : W_V ⟶ V`, and the `f_V` glue to a morphism
of schemes `f : X ⟶ Y` (`AlgebraicGeometry.glueHom`): the `W_V` cover `X` by the covering step of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.ExistenceClause`, and on an
overlap the naturality of `φ` makes the `f_V` agree, once `V ↦ W_V` is known to preserve binary
intersections (`AlgebraicGeometry.inverseImageOpen_inf`).

This is the construction of the morphism of schemes in the existence half of Stacks 04I7; the
proof that it is the right one is in the modules that import this one.

## References

* [Stacks Project, Tag 04I7](https://stacks.math.columbia.edu/tag/04I7)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits

universe u

namespace AlgebraicGeometry

/-! ### The sheaf represented by an open subscheme -/

section OpenSheaf

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The sheaf `h_V` on the small étale site of `S` represented by an open `V` of `S`. -/
abbrev openSheaf (V : S.Opens) : Sheaf (SmallEtale.topology B S hS) (Type u) :=
  (smallEtaleYoneda B S hS).obj ((opensToBoundedEtale B S hS).obj V)

/-- An object of the small étale site maps to the object given by an open `V` in at most one
way: the open immersion of `V` is a monomorphism. -/
instance subsingleton_hom_opensToBoundedEtale (U : SmallEtale B S hS) (V : S.Opens) :
    Subsingleton (U ⟶ (opensToBoundedEtale B S hS).obj V) := by
  refine ⟨fun k k' => (SmallEtale.toScheme B S hS).map_injective ?_⟩
  refine (cancel_mono V.ι).1 ?_
  exact (smallEtaleStructureHom_comp B S hS k).trans
    (smallEtaleStructureHom_comp B S hS k').symm

/-- An object of the small étale site maps to the object given by an open `V` exactly when its
image lies in `V`. -/
theorem nonempty_hom_opensToBoundedEtale_iff (U : SmallEtale B S hS) (V : S.Opens) :
    Nonempty (U ⟶ (opensToBoundedEtale B S hS).obj V) ↔
      Set.range (smallEtaleMap B S hS U).base ⊆ (V : Set S) := by
  rw [← nonempty_openRepresentableSheaf_obj_iff.{u, u} B S hS V U]
  exact ⟨fun ⟨k⟩ => ⟨(SmallEtale.openRepresentableSheafIso B S hS V).hom.hom.app (op U) k⟩,
    fun ⟨s⟩ => ⟨(SmallEtale.openRepresentableSheafIso B S hS V).inv.hom.app (op U) s⟩⟩

/-- A morphism of sheaves into a sheaf with at most one section over each object exists as soon
as every section of the source has a section of the target below it. -/
def homOfSubsingleton {Z T : Sheaf (SmallEtale.topology B S hS) (Type u)}
    (hT : ∀ U, Subsingleton (T.obj.obj U)) (h : ∀ U, Z.obj.obj U → Nonempty (T.obj.obj U)) :
    Z ⟶ T :=
  ⟨{ app := fun U => TypeCat.ofHom fun z => Classical.choice (h U z)
     naturality := fun _ _ _ => TypeCat.homEquiv.injective
       (funext fun _ => Subsingleton.elim _ _) }⟩

/-- `h_V` is a subsheaf of the final sheaf. -/
theorem isSubterminal_openSheaf (V : S.Opens) : IsSubterminal (openSheaf B S hS V) :=
  fun _ _ _ => Sheaf.hom_ext (NatTrans.ext (funext fun U =>
    TypeCat.homEquiv.injective (funext fun _ =>
      (subsingleton_hom_opensToBoundedEtale B S hS U.unop V).elim _ _)))

/-- The sections of `h_V` over an object of the small étale site form a subsingleton. -/
instance subsingleton_openSheaf_obj (V : S.Opens) (U : (SmallEtale B S hS)ᵒᵖ) :
    Subsingleton ((openSheaf B S hS V).obj.obj U) :=
  subsingleton_hom_opensToBoundedEtale B S hS U.unop V

/-- **`h_V ⟶ h_{V'}` exists exactly when `V ≤ V'`.** -/
theorem nonempty_hom_openSheaf_iff_le (V V' : S.Opens) :
    Nonempty (openSheaf B S hS V ⟶ openSheaf B S hS V') ↔ V ≤ V' := by
  rw [← nonempty_hom_openRepresentableSheaf_iff_le.{u, u} B S hS V V']
  exact ⟨fun ⟨φ⟩ => ⟨(SmallEtale.openRepresentableSheafIso B S hS V).inv ≫ φ ≫
      (SmallEtale.openRepresentableSheafIso B S hS V').hom⟩,
    fun ⟨φ⟩ => ⟨(SmallEtale.openRepresentableSheafIso B S hS V).hom ≫ φ ≫
      (SmallEtale.openRepresentableSheafIso B S hS V').inv⟩⟩

/-- The morphism `h_V ⟶ h_{V'}` for `V ≤ V'`. -/
abbrev openSheafMap {V V' : S.Opens} (h : V ≤ V') : openSheaf B S hS V ⟶ openSheaf B S hS V' :=
  (smallEtaleYoneda B S hS).map ((opensToBoundedEtale B S hS).map (homOfLE h))

/-- `h_V` is the product of `h_{V₁}` and `h_{V₂}` when `V = V₁ ⊓ V₂`. -/
def isLimitOpenSheafInf (V₁ V₂ : S.Opens) :
    IsLimit (BinaryFan.mk (openSheafMap B S hS (inf_le_left : V₁ ⊓ V₂ ≤ V₁))
      (openSheafMap B S hS (inf_le_right : V₁ ⊓ V₂ ≤ V₂))) :=
  BinaryFan.IsLimit.mk _
    (fun {Z} a b => homOfSubsingleton B S hS (fun U => subsingleton_openSheaf_obj B S hS _ U)
      (fun U z => by
        refine (nonempty_hom_opensToBoundedEtale_iff B S hS U.unop _).2 ?_
        intro x hx
        exact ⟨(nonempty_hom_opensToBoundedEtale_iff B S hS U.unop V₁).1 ⟨a.hom.app U z⟩ hx,
          (nonempty_hom_opensToBoundedEtale_iff B S hS U.unop V₂).1 ⟨b.hom.app U z⟩ hx⟩))
    (fun _ _ => (isSubterminal_openSheaf B S hS V₁) _ _)
    (fun _ _ => (isSubterminal_openSheaf B S hS V₂) _ _)
    (fun _ _ _ _ _ => (isSubterminal_openSheaf B S hS _) _ _)

end OpenSheaf

/-! ### Morphisms out of an open subscheme are determined on a covering -/

/-- Two morphisms out of an open subscheme `A` of `X` agree as soon as they agree on `A ⊓ F i`
for a family of opens `F i` covering `A`. -/
theorem Scheme.homOfLE_ext {X Y : Scheme.{u}} {A : X.Opens} {ι : Type*} (F : ι → X.Opens)
    (hA : A ≤ ⨆ i, F i) (a b : A.toScheme ⟶ Y)
    (h : ∀ i, X.homOfLE (inf_le_left : A ⊓ F i ≤ A) ≫ a =
      X.homOfLE (inf_le_left : A ⊓ F i ≤ A) ≫ b) : a = b := by
  refine hom_ext_of_forall a b fun p => ?_
  have hpA : A.ι p ∈ A := p.2
  have hp : A.ι p ∈ ⨆ i, F i := hA hpA
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
  refine ⟨(X.homOfLE (inf_le_left : A ⊓ F i ≤ A)).opensRange, ?_, ?_⟩
  · rw [Scheme.opensRange_homOfLE]
    show A.ι p ∈ A ⊓ F i
    exact ⟨hpA, hi⟩
  · rw [← cancel_epi (X.homOfLE (inf_le_left : A ⊓ F i ≤ A)).isoOpensRange.hom,
      ← Category.assoc, ← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
    exact h i

/-! ### The ring maps `φ_V` -/

section RingMap

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme}
  (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))

/-- `g⁻¹h_V` is a subsheaf of the final sheaf. -/
theorem isSubterminal_inverseImage_openSheaf (V : Y.obj.Opens) :
    IsSubterminal (g.toToposHom.inverseImage.obj (openSheaf B Y.obj Y.property V)) :=
  let := g.toToposHom.preservesFiniteLimits
  (isSubterminal_openSheaf B Y.obj Y.property V).map Limits.terminalIsTerminal _

/-- An open `W` of the source with `g⁻¹h_V ≅ h_W` (in the spelling `openSheaf`) is
`AlgebraicGeometry.inverseImageOpen`. -/
theorem eq_inverseImageOpen_of_iso (V : Y.obj.Opens) (W : X.obj.Opens)
    (e : g.toToposHom.inverseImage.obj (openSheaf B Y.obj Y.property V) ≅
      openSheaf B X.obj X.property W) :
    W = inverseImageOpen B X Y g V :=
  eq_inverseImageOpen B X Y g V W
    ⟨g.toToposHom.inverseImage.mapIso
        (SmallEtale.openRepresentableSheafIso B Y.obj Y.property V).symm ≪≫ e ≪≫
      SmallEtale.openRepresentableSheafIso B X.obj X.property W⟩

/-- **`g⁻¹h_V ≅ h_{W_V}`**, in the spelling `AlgebraicGeometry.openSheaf`. -/
def inverseImageOpenIso (V : Y.obj.Opens) :
    g.toToposHom.inverseImage.obj (openSheaf B Y.obj Y.property V) ≅
      openSheaf B X.obj X.property (inverseImageOpen B X Y g V) :=
  g.toToposHom.inverseImage.mapIso (SmallEtale.openRepresentableSheafIso B Y.obj Y.property V) ≪≫
    Classical.choice (nonempty_iso_inverseImageOpen B X Y g V) ≪≫
      (SmallEtale.openRepresentableSheafIso B X.obj X.property (inverseImageOpen B X Y g V)).symm

/-- `V ↦ W_V` is monotone. -/
theorem inverseImageOpen_mono {V V' : Y.obj.Opens} (h : V ≤ V') :
    inverseImageOpen B X Y g V ≤ inverseImageOpen B X Y g V' :=
  (galoisConnection_inverseImageOpen_pushforwardOpen B X Y g).monotone_l h

/-- **`V ↦ W_V` preserves binary intersections.**  `h_{V₁ ⊓ V₂}` is the product of `h_{V₁}` and
`h_{V₂}` (`AlgebraicGeometry.isLimitOpenSheafInf`) and `g⁻¹` preserves finite products. -/
theorem inverseImageOpen_inf (V₁ V₂ : Y.obj.Opens) :
    inverseImageOpen B X Y g (V₁ ⊓ V₂) =
      inverseImageOpen B X Y g V₁ ⊓ inverseImageOpen B X Y g V₂ := by
  refine le_antisymm (le_inf (inverseImageOpen_mono g inf_le_left)
    (inverseImageOpen_mono g inf_le_right)) ?_
  let := g.toToposHom.preservesFiniteLimits
  have hl := (isLimitMapConeBinaryFanEquiv g.toToposHom.inverseImage _ _)
    (isLimitOfPreserves g.toToposHom.inverseImage (isLimitOpenSheafInf B Y.obj Y.property V₁ V₂))
  let W₁ := inverseImageOpen B X Y g V₁
  let W₂ := inverseImageOpen B X Y g V₂
  let a : openSheaf B X.obj X.property (W₁ ⊓ W₂) ⟶
      g.toToposHom.inverseImage.obj (openSheaf B Y.obj Y.property V₁) :=
    openSheafMap B X.obj X.property inf_le_left ≫ (inverseImageOpenIso g V₁).inv
  let b : openSheaf B X.obj X.property (W₁ ⊓ W₂) ⟶
      g.toToposHom.inverseImage.obj (openSheaf B Y.obj Y.property V₂) :=
    openSheafMap B X.obj X.property inf_le_right ≫ (inverseImageOpenIso g V₂).inv
  let c := (BinaryFan.IsLimit.lift' hl a b).1
  rw [← nonempty_hom_openSheaf_iff_le B X.obj X.property]
  exact ⟨c ≫ (inverseImageOpenIso g (V₁ ⊓ V₂)).hom⟩

/-- **The ring map `φ_V : Γ(V, ⊤) ⟶ Γ(W_V, ⊤)`.**  A section `b` of `𝒪_Y` over `V` is read as a
generalized element `h_V ⟶ 𝒪_Y`, moved along `g` to `h_{W_V} ≅ g⁻¹h_V ⟶ 𝒪_X`, and read back as a
section of `𝒪_X` over `W_V`. -/
def openRingHom (V : Y.obj.Opens) :
    ↥Γ(V.toScheme, ⊤) →+* ↥Γ((inverseImageOpen B X Y g V).toScheme, ⊤) :=
  (smallEtaleSectionRingEquiv B X.obj X.property
      ((opensToBoundedEtale B X.obj X.property).obj (inverseImageOpen B X Y g V))).toRingHom.comp
    ((transportRingHom g (inverseImageOpenIso g V).inv).comp
      (smallEtaleSectionRingEquiv B Y.obj Y.property
        ((opensToBoundedEtale B Y.obj Y.property).obj V)).symm.toRingHom)

/-- `φ_V b` is the section of `𝒪_X` over `W_V` named by the transport along `g` of the
generalized element named by `b`. -/
theorem openRingHom_apply (V : Y.obj.Opens) (b : ↥Γ(V.toScheme, ⊤)) :
    openRingHom g V b = smallEtaleSectionRingEquiv B X.obj X.property
      ((opensToBoundedEtale B X.obj X.property).obj (inverseImageOpen B X Y g V))
      ((inverseImageOpenIso g V).inv ≫ g.toToposHom.inverseImage.map
        ((smallEtaleSectionRingEquiv B Y.obj Y.property
          ((opensToBoundedEtale B Y.obj Y.property).obj V)).symm b) ≫ g.fSharpSet) :=
  rfl

/-- The generalized element of shape `h_{W_V}` named by `φ_V b` is the transport of the one named
by `b`. -/
theorem smallEtaleSectionRingEquiv_symm_openRingHom (V : Y.obj.Opens) (b : ↥Γ(V.toScheme, ⊤)) :
    (smallEtaleSectionRingEquiv B X.obj X.property
      ((opensToBoundedEtale B X.obj X.property).obj (inverseImageOpen B X Y g V))).symm
        (openRingHom g V b) =
      (inverseImageOpenIso g V).inv ≫ g.toToposHom.inverseImage.map
        ((smallEtaleSectionRingEquiv B Y.obj Y.property
          ((opensToBoundedEtale B Y.obj Y.property).obj V)).symm b) ≫ g.fSharpSet := by
  rw [openRingHom_apply]
  exact RingEquiv.symm_apply_apply _ _

/-- **Naturality of `φ` in `V`.** -/
theorem openRingHom_naturality {V V' : Y.obj.Opens} (h : V' ≤ V) (b : ↥Γ(V.toScheme, ⊤)) :
    (X.obj.homOfLE (inverseImageOpen_mono g h)).appTop.hom (openRingHom g V b) =
      openRingHom g V' ((Y.obj.homOfLE h).appTop.hom b) := by
  have hX := yoneda_map_comp_smallEtaleSectionRingEquiv_symm B X.obj X.property
    ((opensToBoundedEtale B X.obj X.property).map (homOfLE (inverseImageOpen_mono g h)))
    (openRingHom g V b)
  have hY := yoneda_map_comp_smallEtaleSectionRingEquiv_symm B Y.obj Y.property
    ((opensToBoundedEtale B Y.obj Y.property).map (homOfLE h)) b
  refine (smallEtaleSectionRingEquiv B X.obj X.property
    ((opensToBoundedEtale B X.obj X.property).obj (inverseImageOpen B X Y g V'))).symm.injective ?_
  refine hX.symm.trans ?_
  rw [smallEtaleSectionRingEquiv_symm_openRingHom, smallEtaleSectionRingEquiv_symm_openRingHom]
  show _ = _ ≫ g.toToposHom.inverseImage.map
    ((smallEtaleSectionRingEquiv B Y.obj Y.property
      ((opensToBoundedEtale B Y.obj Y.property).obj V')).symm (smallEtaleRestrict B Y.obj Y.property
      ((opensToBoundedEtale B Y.obj Y.property).map (homOfLE h)) b)) ≫ _
  have key : (smallEtaleYoneda B X.obj X.property).map
      ((opensToBoundedEtale B X.obj X.property).map (homOfLE (inverseImageOpen_mono g h))) ≫
        (inverseImageOpenIso g V).inv =
      (inverseImageOpenIso g V').inv ≫ g.toToposHom.inverseImage.map
        ((smallEtaleYoneda B Y.obj Y.property).map
          ((opensToBoundedEtale B Y.obj Y.property).map (homOfLE h))) :=
    isSubterminal_inverseImage_openSheaf g V _ _
  rw [← hY, Functor.map_comp]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) key).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm)))

/-! ### The morphisms of schemes over affine opens, and the morphism they glue to -/

/-- **The morphism of schemes `f_V : W_V ⟶ V` over an affine open `V` of the target**: the
morphism into an affine scheme inducing `φ_V` on global functions. -/
def openSchemeHom (V : Y.obj.affineOpens) :
    (inverseImageOpen B X Y g V).toScheme ⟶ (V : Y.obj.Opens).toScheme :=
  Stacks.EtaleCohomology.schemeHomOfAppTop _ _ (CommRingCat.ofHom (openRingHom g V))

/-- The morphism `f_V` induces `φ_V` on global functions. -/
theorem openSchemeHom_appTop (V : Y.obj.affineOpens) :
    (openSchemeHom g V).appTop = CommRingCat.ofHom (openRingHom g V) :=
  Stacks.EtaleCohomology.appTop_schemeHomOfAppTop _ _ _

/-- **The `f_V` are compatible with restriction to a smaller affine open.**  Both sides are
morphisms into the affine scheme `V`, and on global functions they are the two sides of the
naturality of `φ`. -/
theorem homOfLE_openSchemeHom {V V' : Y.obj.affineOpens} (h : (V' : Y.obj.Opens) ≤ V) :
    X.obj.homOfLE (inverseImageOpen_mono g h) ≫ openSchemeHom g V =
      openSchemeHom g V' ≫ Y.obj.homOfLE h := by
  refine ext_of_isAffine ?_
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, openSchemeHom_appTop, openSchemeHom_appTop]
  ext b
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  exact openRingHom_naturality g h b

/-- For affine opens `V' ≤ V`: restricting `f_V` to `W_{V'}` and composing with the inclusion of
`V` gives `f_{V'}` composed with the inclusion of `V'`. -/
theorem homOfLE_openSchemeHom_ι {V V' : Y.obj.affineOpens} (h : (V' : Y.obj.Opens) ≤ V) :
    X.obj.homOfLE (inverseImageOpen_mono g h) ≫ openSchemeHom g V ≫ (V : Y.obj.Opens).ι =
      openSchemeHom g V' ≫ (V' : Y.obj.Opens).ι := by
  rw [← Category.assoc, homOfLE_openSchemeHom g h, Category.assoc, Scheme.homOfLE_ι]

/-- The `f_V`, followed by the inclusions of the `V`, agree on the overlaps of the `W_V`. -/
theorem openSchemeHom_compat (V₁ V₂ : Y.obj.affineOpens) :
    X.obj.homOfLE (inf_le_left : inverseImageOpen B X Y g V₁ ⊓ inverseImageOpen B X Y g V₂ ≤ _) ≫
        (openSchemeHom g V₁ ≫ (V₁ : Y.obj.Opens).ι) =
      X.obj.homOfLE (inf_le_right : inverseImageOpen B X Y g V₁ ⊓ inverseImageOpen B X Y g V₂ ≤ _) ≫
        (openSchemeHom g V₂ ≫ (V₂ : Y.obj.Opens).ι) := by
  let ι' := {V'' : Y.obj.affineOpens // (V'' : Y.obj.Opens) ≤ (V₁ : Y.obj.Opens) ⊓ V₂}
  have hcov : inverseImageOpen B X Y g V₁ ⊓ inverseImageOpen B X Y g V₂ ≤
      ⨆ i : ι', inverseImageOpen B X Y g i.1 := by
    rw [← inverseImageOpen_inf,
      ← (galoisConnection_inverseImageOpen_pushforwardOpen B X Y g).l_iSup]
    refine inverseImageOpen_mono g ?_
    intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      Y.obj.isBasis_affineOpens.exists_subset_of_mem_open hx ((V₁ : Y.obj.Opens) ⊓ V₂).2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hVU⟩, hxV⟩
  refine Scheme.homOfLE_ext (fun i : ι' => inverseImageOpen B X Y g i.1) hcov _ _ ?_
  rintro ⟨V'', hV''⟩
  have h₁ : (V'' : Y.obj.Opens) ≤ V₁ := hV''.trans inf_le_left
  have h₂ : (V'' : Y.obj.Opens) ≤ V₂ := hV''.trans inf_le_right
  have side : ∀ {V : Y.obj.affineOpens} (hW : inverseImageOpen B X Y g V₁ ⊓
        inverseImageOpen B X Y g V₂ ≤ inverseImageOpen B X Y g V) (h : (V'' : Y.obj.Opens) ≤ V),
      X.obj.homOfLE (inf_le_left : (inverseImageOpen B X Y g V₁ ⊓
        inverseImageOpen B X Y g V₂) ⊓ inverseImageOpen B X Y g (V'' : Y.obj.Opens) ≤ _) ≫
        X.obj.homOfLE hW ≫ openSchemeHom g V ≫ (V : Y.obj.Opens).ι =
      X.obj.homOfLE inf_le_right ≫ openSchemeHom g V'' ≫ (V'' : Y.obj.Opens).ι := by
    intro V hW h
    rw [← homOfLE_openSchemeHom_ι g h]
    simp only [← Category.assoc, Scheme.homOfLE_homOfLE]
  exact (side _ h₁).trans (side _ h₂).symm

/-- **The `f_V` glue to exactly one morphism of schemes `X ⟶ Y`.** -/
theorem existsUnique_glueHom :
    ∃! a : X ⟶ Y, ∀ V : Y.obj.affineOpens,
      (inverseImageOpen B X Y g V).ι ≫ B.inclusion.map a =
        openSchemeHom g V ≫ (V : Y.obj.Opens).ι :=
  existsUnique_schemeHom_of_forall_iso_inverseImage_openRepresentableSheaf B X Y g
    (fun V : Y.obj.affineOpens => (V : Y.obj.Opens)) (iSup_affineOpens_eq_top Y.obj)
    (fun V => inverseImageOpen B X Y g V) (fun V => nonempty_iso_inverseImageOpen B X Y g V)
    (fun V => openSchemeHom g V ≫ (V : Y.obj.Opens).ι) (openSchemeHom_compat g)

/-- **The morphism of schemes glued from the `f_V`.** -/
def glueHom : X ⟶ Y :=
  (existsUnique_glueHom g).exists.choose

/-- On each `W_V`, the glued morphism `X ⟶ Y` agrees with `f_V` followed by the inclusion of
`V`. -/
theorem glueHom_spec (V : Y.obj.affineOpens) :
    (inverseImageOpen B X Y g V).ι ≫ B.inclusion.map (glueHom g) =
      openSchemeHom g V ≫ (V : Y.obj.Opens).ι :=
  (existsUnique_glueHom g).exists.choose_spec V

/-- `W_V` lies in the preimage of `V` under the glued morphism. -/
theorem inverseImageOpen_le_preimage (V : Y.obj.affineOpens) :
    inverseImageOpen B X Y g V ≤ (B.inclusion.map (glueHom g)) ⁻¹ᵁ (V : Y.obj.Opens) := by
  intro x hx
  obtain ⟨y, rfl⟩ : x ∈ Set.range (inverseImageOpen B X Y g V).ι := by
    rw [Scheme.Opens.range_ι]
    exact hx
  have h := congrArg (fun m => m y) (glueHom_spec g V)
  simp only [Scheme.Hom.comp_apply] at h
  show B.inclusion.map (glueHom g) ((inverseImageOpen B X Y g V).ι y) ∈ (V : Y.obj.Opens)
  rw [h]
  exact (openSchemeHom g V y).2

end RingMap

end AlgebraicGeometry

end
