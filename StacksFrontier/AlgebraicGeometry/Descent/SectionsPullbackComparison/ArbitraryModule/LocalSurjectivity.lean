module

public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.Comparison
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.LocalGeneration
public import StacksFrontier.AlgebraicGeometry.Descent.SitePullbackSectionsModule

/-!
# Stacks 070S (1) for an arbitrary module: the comparison and its local surjectivity

Sections of a pullback are locally combinations of pulled-back sections
(`AlgebraicGeometry.exists_span_pullbackSection`); `AlgebraicGeometry.openSubSections` reads a
section over an open as a section over the open subscheme.  On the big site of `S` this part
constructs the comparison `AlgebraicGeometry.BigFppfOver.pullbackSectionsComparison` of
Stacks 070S (1), proves it locally surjective for every `τ`, and shows that, granted local
injectivity, its `τ`-sheafification is an isomorphism.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry ChangeOfRings

universe u

namespace AlgebraicGeometry

section ZariskiLocalGeneration

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules)

/-- **Pullbacks of sections generate the sections of a pullback locally, for an arbitrary
module.**  Let `f : Y ⟶ X`, let `F` be any `𝒪_X`-module, let `s` be a section of `f^*F` over an
open `V` of `Y` and let `y` be a point of `V`.  Then there is an open `W ≤ V` containing `y` and
an open `U` of `X` with `W ≤ f⁻¹U` such that `s|_W` lies in the `Γ(Y, W)`-span of the pullbacks of
the sections of `F` over `U`.

This is the replacement, for a general `F`, of the affine base-change description
`AlgebraicGeometry.span_pullbackSection_eq_top`, which needs `F` quasi-coherent.  Local
surjectivity of `AlgebraicGeometry.zariskiPullbackToSheaf` writes `s|_W` as the image of a section
of the presheaf-level pullback; `PresheafOfModules.mem_pullbackUnitSubmodule` writes that section
as a combination of restrictions of images of the unit, indexed by finitely many opens of `X`;
and `AlgebraicGeometry.span_pullbackSection_mono` replaces those opens by their intersection. -/
public theorem exists_span_pullbackSection (V : Y.Opens)
    (s : ((Scheme.Modules.pullback f).obj F).val.obj (op V)) (y : ↥Y) (hy : y ∈ V) :
    ∃ (W : Y.Opens) (hWV : W ≤ V) (U : X.Opens) (hWU : W ≤ f ⁻¹ᵁ U), y ∈ W ∧
      ((Scheme.Modules.pullback f).obj F).val.map (homOfLE hWV).op s ∈
        Submodule.span Γ(Y, W)
          (Set.range fun a : Γ(F, U) => pullbackSectionHom f F U W hWU a) := by
  obtain ⟨W, g, ⟨p, hp⟩, hyW⟩ :=
    (Opens.mem_grothendieckTopology ↥Y).1
      (Presheaf.imageSieve_mem (Opens.grothendieckTopology ↥Y)
        ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map (zariskiPullbackToSheaf f F))
        (U := op V) s)
      y hy
  have hmem := PresheafOfModules.mem_pullbackUnitSubmodule.{u}
    f.toRingCatSheafHom.hom F.val (op W) p
  have key : ∃ (U : X.Opens) (hWU : W ≤ f ⁻¹ᵁ U),
      (zariskiPullbackToSheaf f F).app (op W) p ∈ Submodule.span Γ(Y, W)
        (Set.range fun a : Γ(F, U) => pullbackSectionHom f F U W hWU a) := by
    refine Submodule.span_induction
      (p := fun q _ => ∃ (U : X.Opens) (hWU : W ≤ f ⁻¹ᵁ U),
        (zariskiPullbackToSheaf f F).app (op W) q ∈ Submodule.span Γ(Y, W)
          (Set.range fun a : Γ(F, U) => pullbackSectionHom f F U W hWU a))
      ?_ ?_ ?_ ?_ hmem
    · rintro q ⟨U, j, m, rfl⟩
      refine ⟨U, leOfHom j, Submodule.subset_span ⟨m, ?_⟩⟩
      refine Eq.trans (zariskiPullbackToSheaf_generator f F U W (leOfHom j) m).symm ?_
      exact congrArg (fun k : W ⟶ f ⁻¹ᵁ U => (zariskiPullbackToSheaf f F).app (op W)
        ((zariskiPullbackPresheaf f F).map k.op
          (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
            f.toRingCatSheafHom.hom).unit.app F.val).app (op U) m)))
        (Subsingleton.elim _ _)
    · exact ⟨⊤, le_top, by rw [map_zero]; exact Submodule.zero_mem _⟩
    · rintro q₁ q₂ _ _ ⟨U₁, h₁, hq₁⟩ ⟨U₂, h₂, hq₂⟩
      have h : W ≤ f ⁻¹ᵁ (U₁ ⊓ U₂) := fun z hz => ⟨h₁ hz, h₂ hz⟩
      refine ⟨U₁ ⊓ U₂, h, ?_⟩
      rw [map_add]
      exact Submodule.add_mem _
        (span_pullbackSection_mono f F U₁ (U₁ ⊓ U₂) inf_le_left W h h₁ hq₁)
        (span_pullbackSection_mono f F U₂ (U₁ ⊓ U₂) inf_le_right W h h₂ hq₂)
    · rintro c q _ ⟨U, h, hq⟩
      refine ⟨U, h, ?_⟩
      have hsm : (zariskiPullbackToSheaf f F).app (op W) (c • q) =
          c • (zariskiPullbackToSheaf f F).app (op W) q :=
        ((zariskiPullbackToSheaf f F).app (op W)).hom.map_smul c q
      exact hsm ▸ Submodule.smul_mem _ c hq
  obtain ⟨U, hWU, hspan⟩ := key
  refine ⟨W, leOfHom g, U, hWU, hyW, ?_⟩
  have hs : ((Scheme.Modules.pullback f).obj F).val.map (homOfLE (leOfHom g)).op s
      = (zariskiPullbackToSheaf f F).app (op W) p := by
    refine Eq.trans ?_ hp.symm
    exact congrArg (fun k : W ⟶ V =>
      ((Scheme.Modules.pullback f).obj F).val.map k.op s) (Subsingleton.elim _ _)
  rw [hs]
  exact hspan

/-! ### Restriction to an open subscheme, read on the pullback along the composite -/

/-- **Sections of `f^*F` over an open `V` of `Y`, read as sections of `(V.ι ≫ f)^*F` over all of
the open subscheme `V`.**  Pull back along the open immersion of `V` and then use
`AlgebraicGeometry.Scheme.Modules.pullbackComp` to identify the iterated pullback with the
pullback along the composite.

This is the identification a site of `S`-schemes performs when it restricts a section of the
pullback-sections presheaf of Stacks 03DS along the open immersion of `V`; that is
`AlgebraicGeometry.pullbackSectionsMap_eq_openSubSections`. -/
public noncomputable def openSubSections (V : Y.Opens)
    (s : Γ((Scheme.Modules.pullback f).obj F, V)) :
    Γ((Scheme.Modules.pullback (V.ι ≫ f)).obj F, ⊤) :=
  ((Scheme.Modules.pullbackComp V.ι f).hom.app F).val.app (op ⊤)
    (Scheme.Modules.pullbackSection V.ι ((Scheme.Modules.pullback f).obj F) V ⊤
      (Scheme.Opens.top_le_ι_preimage le_rfl) s)

/-- `AlgebraicGeometry.openSubSections` is a linear map applied to the pullback of a section. -/
private theorem openSubSections_eq (V : Y.Opens) (s : Γ((Scheme.Modules.pullback f).obj F, V)) :
    openSubSections f F V s =
      (((Scheme.Modules.pullbackComp V.ι f).hom.app F).val.app (op ⊤)).hom
        (pullbackSectionHom V.ι ((Scheme.Modules.pullback f).obj F) V ⊤
          (Scheme.Opens.top_le_ι_preimage le_rfl) s) := rfl

/-- `AlgebraicGeometry.openSubSections` is additive, being a composite of two additive maps. -/
public theorem openSubSections_add (V : Y.Opens)
    (s t : Γ((Scheme.Modules.pullback f).obj F, V)) :
    openSubSections f F V (s + t) = openSubSections f F V s + openSubSections f F V t := by
  rw [openSubSections_eq, openSubSections_eq, openSubSections_eq, map_add]
  exact map_add (((Scheme.Modules.pullbackComp V.ι f).hom.app F).val.app (op ⊤)).hom _ _

/-- `AlgebraicGeometry.openSubSections` kills zero. -/
public theorem openSubSections_zero (V : Y.Opens) : openSubSections f F V 0 = 0 := by
  rw [openSubSections_eq, map_zero]
  exact map_zero (((Scheme.Modules.pullbackComp V.ι f).hom.app F).val.app (op ⊤)).hom

/-- `AlgebraicGeometry.openSubSections` carries the action of a function on `V` to the action of
its image under `AlgebraicGeometry.Scheme.Opens.topIso`.  Pulling a section back along an open
immersion is semilinear over `AlgebraicGeometry.Scheme.Hom.appLE`, which for the inclusion of `V`
and the pair `(V, ⊤)` is that isomorphism, by `AlgebraicGeometry.Scheme.Opens.ι_appLE_top`. -/
public theorem openSubSections_smul (V : Y.Opens) (r : Γ(Y, V))
    (s : Γ((Scheme.Modules.pullback f).obj F, V)) :
    openSubSections f F V (r • s) =
      (Scheme.Opens.topIso V).inv r • openSubSections f F V s := by
  rw [openSubSections_eq, openSubSections_eq, pullbackSectionHom_smul,
    Scheme.Opens.ι_appLE_top]
  exact (((Scheme.Modules.pullbackComp V.ι f).hom.app F).val.app (op ⊤)).hom.map_smul _ _

/-- **`AlgebraicGeometry.openSubSections` carries a pulled-back section to a pulled-back
section.**  This is `AlgebraicGeometry.Scheme.Modules.pullbackSection_comp` for the pair
`V.ι`, `f`. -/
public theorem openSubSections_pullbackSectionHom (V : Y.Opens) (U : X.Opens)
    (hVU : V ≤ f ⁻¹ᵁ U) (hX : (⊤ : V.toScheme.Opens) ≤ (V.ι ≫ f) ⁻¹ᵁ U) (a : Γ(F, U)) :
    openSubSections f F V (pullbackSectionHom f F U V hVU a) =
      pullbackSectionHom (V.ι ≫ f) F U ⊤ hX a :=
  Scheme.Modules.pullbackSection_comp V.ι f F U V ⊤ hVU
    (Scheme.Opens.top_le_ι_preimage le_rfl) hX a

/-- **`AlgebraicGeometry.openSubSections` carries the span of the pulled-back sections into the
span of the pulled-back sections.**  Combination of
`AlgebraicGeometry.openSubSections_pullbackSectionHom` with additivity and semilinearity. -/
public theorem openSubSections_mem_span (V : Y.Opens) (U : X.Opens) (hVU : V ≤ f ⁻¹ᵁ U)
    (hX : (⊤ : V.toScheme.Opens) ≤ (V.ι ≫ f) ⁻¹ᵁ U)
    {x : Γ((Scheme.Modules.pullback f).obj F, V)}
    (hx : x ∈ Submodule.span Γ(Y, V)
      (Set.range fun a : Γ(F, U) => pullbackSectionHom f F U V hVU a)) :
    openSubSections f F V x ∈ Submodule.span Γ(V.toScheme, ⊤)
      (Set.range fun a : Γ(F, U) => pullbackSectionHom (V.ι ≫ f) F U ⊤ hX a) := by
  refine Submodule.span_induction
    (p := fun z _ => openSubSections f F V z ∈ Submodule.span Γ(V.toScheme, ⊤)
      (Set.range fun a : Γ(F, U) => pullbackSectionHom (V.ι ≫ f) F U ⊤ hX a))
    ?_ ?_ ?_ ?_ hx
  · rintro z ⟨a, rfl⟩
    exact Submodule.subset_span ⟨a, (openSubSections_pullbackSectionHom f F V U hVU hX a).symm⟩
  · rw [openSubSections_zero]
    exact Submodule.zero_mem _
  · intro z w _ _ hz hw
    rw [openSubSections_add]
    exact Submodule.add_mem _ hz hw
  · intro c z _ hz
    rw [openSubSections_smul]
    exact Submodule.smul_mem _ _ hz

/-- **Restriction along the open immersion of `V`, in the pullback-sections presheaf of Stacks
03DS, is `AlgebraicGeometry.openSubSections` of the restriction.**  The restriction map of that
presheaf is `AlgebraicGeometry.pullbackSectionsMap`, which
`AlgebraicGeometry.pullbackSectionsMap_eq_comp` writes as a pullback of sections followed by the
comparison of iterated pullbacks; `AlgebraicGeometry.pullbackSectionHom_map` moves the open of
the target from `⊤` to `V`, and the transport along the equality of structure morphisms is the
identity because that equality is reflexivity. -/
public theorem pullbackSectionsMap_eq_openSubSections (V : Y.Opens)
    (g : Over.mk (V.ι ≫ f) ⟶ Over.mk f) (hg : g.left = V.ι)
    (s : Γ((Scheme.Modules.pullback f).obj F, ⊤)) :
    pullbackSectionsMap F g s =
      openSubSections f F V
        (((Scheme.Modules.pullback f).obj F).val.map (homOfLE (le_top (a := V))).op s) := by
  obtain rfl : g = (Over.homMk V.ι : Over.mk (V.ι ≫ f) ⟶ Over.mk f) :=
    Over.OverMorphism.ext hg
  have h' : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ (⊤ : Y.Opens) := le_top
  have hsec : Scheme.Modules.pullbackSection V.ι ((Scheme.Modules.pullback f).obj F) V ⊤
        (Scheme.Opens.top_le_ι_preimage le_rfl)
        (((Scheme.Modules.pullback f).obj F).val.map (homOfLE (le_top (a := V))).op s) =
      Scheme.Modules.pullbackSection V.ι ((Scheme.Modules.pullback f).obj F) ⊤ ⊤ h' s :=
    pullbackSectionHom_map V.ι ((Scheme.Modules.pullback f).obj F) ⊤ V le_top ⊤
      (Scheme.Opens.top_le_ι_preimage le_rfl) h' s
  refine (pullbackSectionsMap_eq_comp F
    (Over.homMk V.ι : Over.mk (V.ι ≫ f) ⟶ Over.mk f) h' s).trans ?_
  exact (congrArg (fun z => ((Scheme.Modules.pullbackComp V.ι f).hom.app F).val.app (op ⊤) z)
    hsec).symm

end ZariskiLocalGeneration

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pulling a section of `F` over an open `U` of `S` back to the open subscheme `U`, as a map
of sections over `U`.  This is the component of
`AlgebraicGeometry.BigFppfOver.pullbackSectionsUnit`. -/
public noncomputable def pullbackSectionsUnitApp (F : S.Modules)
    (U : (S.Opens)ᵒᵖ) :
    ((SheafOfModules.forget S.ringCatSheaf).obj F).obj U ⟶
      ((PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).obj
        (pullbackSectionsPresheaf B S hS F)).obj U :=
  ModuleCat.homEquiv.symm {
    toFun := fun a =>
      pullbackSectionHom U.unop.ι F U.unop ⊤ (Scheme.Opens.top_le_ι_preimage le_rfl) a
    map_add' := fun a b => map_add _ a b
    map_smul' := fun r a => by
      refine (pullbackSectionHom_smul U.unop.ι F U.unop ⊤
        (Scheme.Opens.top_le_ι_preimage le_rfl) r a).trans ?_
      exact congrArg
        (fun s : Γ(U.unop.toScheme, ⊤) => s • pullbackSectionHom U.unop.ι F U.unop ⊤
          (Scheme.Opens.top_le_ι_preimage le_rfl) a)
        (congrArg (fun g : Γ(S, U.unop) ⟶ Γ(U.unop, ⊤) => ConcreteCategory.hom g r)
          (Scheme.Opens.ι_appLE_top U.unop (Scheme.Opens.top_le_ι_preimage le_rfl))) }

/-- The component of `pullbackSectionsUnitApp` at an open `U` of `S` sends a section `a` of `F`
over `U` to its pullback `pullbackSectionHom` along the inclusion of `U`, a section over all of the
open subscheme `U`. -/
@[simp]
public theorem pullbackSectionsUnitApp_apply (F : S.Modules) (U : (S.Opens)ᵒᵖ)
    (a : ((SheafOfModules.forget S.ringCatSheaf).obj F).obj U) :
    pullbackSectionsUnitApp B S hS F U a =
      pullbackSectionHom U.unop.ι F U.unop ⊤ (Scheme.Opens.top_le_ι_preimage le_rfl) a :=
  rfl

/-- **Pulling sections back, as a morphism out of `F`.**  A section of `F` over an open `U` of
`S` pulls back to a section of `U.ι^*F` over all of the open subscheme `U`, and this is natural
in `U`: it is a morphism from `F` to the restriction, along the inclusion of the small Zariski
site of `S`, of the pullback-sections presheaf of modules of the big fppf site. -/
public noncomputable def pullbackSectionsUnit (F : S.Modules) :
    (SheafOfModules.forget S.ringCatSheaf).obj F ⟶
      (PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).obj
        (pullbackSectionsPresheaf B S hS F) where
  app U := pullbackSectionsUnitApp B S hS F U
  naturality {U V} h := by
    ext a
    have hUV : V.unop ≤ U.unop := leOfHom h.unop
    refine Eq.trans (pullbackSectionHom_map (Scheme.Opens.ι V.unop) F U.unop V.unop hUV ⊤
      (Scheme.Opens.top_le_ι_preimage le_rfl) (Scheme.Opens.top_le_ι_preimage hUV) a) ?_
    exact (pullbackSectionsMap_pullbackSectionHom F
      ((Over.post (X := B.obj hS) B.inclusion).map ((opensToBig B S hS).map h.unop))
      U.unop (Scheme.Opens.top_le_ι_preimage le_rfl)
      (Scheme.Opens.top_le_ι_preimage hUV) a).symm

/-- **The comparison of Stacks 070S (1).**  The canonical morphism from the pullback of
presheaves of modules along the structure-sheaf comparison of the big fppf site of `S` to the
pullback-sections presheaf of Stacks 03DS: the transpose, under
`CategoryTheory.PresheafOfModules.pullbackPushforwardAdjunction`, of the map which pulls a
section of `F` over an open `U` of `S` back to the open subscheme `U`.

Stacks Lemma 070S (1) is the statement that this morphism is locally bijective for the
localized fppf topology; granted that, `CategoryTheory.PresheafOfModules.sheafification` turns
it into an isomorphism and
`AlgebraicGeometry.BigFppfOver.associatedModuleIsoOfPresheafIso` identifies the
associated-module functor with the sheafification of the sections description. -/
public noncomputable def pullbackSectionsComparison (F : S.Modules) :
    (PresheafOfModules.pullback.{u} (structureMap B S hS).hom).obj
        ((SheafOfModules.forget S.ringCatSheaf).obj F) ⟶
      pullbackSectionsPresheaf B S hS F :=
  ((PresheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B S hS).hom).homEquiv
    _ _).symm (pullbackSectionsUnit B S hS F)

/-- **The comparison is determined by pulling sections back.**  Transposing
`AlgebraicGeometry.BigFppfOver.pullbackSectionsComparison` back across the adjunction returns the
map which pulls a section of `F` over an open `U` of `S` back to the open subscheme `U`.  This is
the only property of the comparison that is used: it says that the image of the comparison
contains every pulled-back section. -/
public theorem unit_comp_map_pullbackSectionsComparison (F : S.Modules) :
    (PresheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B S hS).hom).unit.app
          ((SheafOfModules.forget S.ringCatSheaf).obj F) ≫
        (PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).map
          (pullbackSectionsComparison B S hS F) =
      pullbackSectionsUnit B S hS F :=
  ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
      (structureMap B S hS).hom).homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

/-- **The comparison, on a pulled-back section over an open of `S`.**  The component of
`AlgebraicGeometry.BigFppfOver.pullbackSectionsComparison` at the object `U → S` of the big site
carries the image of a section `a` of `F` over `U` under the unit of the pullback--pushforward
adjunction to the pullback of `a` to the open subscheme `U`.  This is
`AlgebraicGeometry.BigFppfOver.unit_comp_map_pullbackSectionsComparison` evaluated at `U` and
applied to `a`. -/
public theorem pullbackSectionsComparison_unit_app (F : S.Modules) (U : S.Opens)
    (a : ((SheafOfModules.forget S.ringCatSheaf).obj F).obj (op U)) :
    (pullbackSectionsComparison B S hS F).app (op ((opensToBig B S hS).obj U))
        (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
            (structureMap B S hS).hom).unit.app
          ((SheafOfModules.forget S.ringCatSheaf).obj F)).app (op U) a) =
      pullbackSectionHom U.ι F U ⊤ (Scheme.Opens.top_le_ι_preimage le_rfl) a := by
  have h := unit_comp_map_pullbackSectionsComparison B S hS F
  have h2 := congrArg (fun k : (SheafOfModules.forget S.ringCatSheaf).obj F ⟶
      (PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).obj
        (pullbackSectionsPresheaf B S hS F) => PresheafOfModules.Hom.app k (op U)) h
  rw [PresheafOfModules.comp_app] at h2
  exact ConcreteCategory.congr_hom h2 a

/-- **The image of the comparison at an object is a submodule containing every pulled-back
section.**  If an object `T` of the big fppf site over `S` factors through an open `U` of `S`,
then every element of the `Γ(T, 𝒪_T)`-span of the pullbacks to `T` of the sections of `F` over `U`
is in the image of the component of `AlgebraicGeometry.BigFppfOver.pullbackSectionsComparison` at
`T`.

Naturality of the comparison along the morphism `T ⟶ opensToBig U`, together with
`AlgebraicGeometry.BigFppfOver.pullbackSectionsComparison_unit_app` and
`AlgebraicGeometry.pullbackSectionsMap_pullbackSectionHom`, puts the pullback to `T` of every
section of `F` over `U` in that image, and the image is a submodule over the global functions of
`T` because the comparison is a morphism of presheaves *of modules*.

The submodule is written out by hand, over the *commutative* ring `Γ(T, 𝒪_T)` rather than over the
`RingCat` object `(structureSheaf B S hS).obj.obj (op T)`; see the implementation notes. -/
public theorem mem_range_app_pullbackSectionsComparison_of_mem_span (F : S.Modules)
    {T : BigFppfOver B S hS} {U : S.Opens} (j : T ⟶ (opensToBig B S hS).obj U)
    (hX : (⊤ : ((toScheme B S hS).obj T).Opens) ≤ T.hom.hom ⁻¹ᵁ U)
    {y : Γ((Scheme.Modules.pullback T.hom.hom).obj F, ⊤)}
    (hy : y ∈ Submodule.span Γ((toScheme B S hS).obj T, ⊤)
      (Set.range fun a : Γ(F, U) => pullbackSectionHom T.hom.hom F U ⊤ hX a)) :
    ∃ x, ModuleCat.Hom.hom ((pullbackSectionsComparison B S hS F).app (op T)) x = y := by
  have hmem : ∀ a : Γ(F, U), ∃ x, ModuleCat.Hom.hom
      ((pullbackSectionsComparison B S hS F).app (op T)) x =
      (pullbackSectionHom T.hom.hom F U ⊤ hX a :
        Γ((Scheme.Modules.pullback T.hom.hom).obj F, ⊤)) := by
    intro a
    refine ⟨((PresheafOfModules.pullback.{u} (structureMap B S hS).hom).obj
      ((SheafOfModules.forget S.ringCatSheaf).obj F)).map j.op
        (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
          (structureMap B S hS).hom).unit.app
            ((SheafOfModules.forget S.ringCatSheaf).obj F)).app (op U) a), ?_⟩
    refine Eq.trans
      (PresheafOfModules.naturality_apply (pullbackSectionsComparison B S hS F) j.op _) ?_
    refine Eq.trans (congrArg (fun z => (pullbackSectionsPresheaf B S hS F).map j.op z)
      (pullbackSectionsComparison_unit_app B S hS F U a)) ?_
    exact pullbackSectionsMap_pullbackSectionHom F
      ((Over.post (X := B.obj hS) B.inclusion).map j) U
      (Scheme.Opens.top_le_ι_preimage le_rfl) hX a
  let Q : Submodule Γ((toScheme B S hS).obj T, ⊤)
      Γ((Scheme.Modules.pullback T.hom.hom).obj F, ⊤) :=
    { carrier := {y | ∃ x, ModuleCat.Hom.hom
        ((pullbackSectionsComparison B S hS F).app (op T)) x = y}
      add_mem' := by
        rintro y z ⟨p, hp⟩ ⟨q, hq⟩
        exact ⟨p + q, by rw [map_add, hp, hq]; rfl⟩
      zero_mem' := ⟨0, map_zero _⟩
      smul_mem' := by
        rintro c y ⟨p, hp⟩
        refine ⟨(show (structureSheaf B S hS).obj.obj (op T) from c) • p, ?_⟩
        rw [map_smul, hp]
        rfl }
  have hle : Submodule.span Γ((toScheme B S hS).obj T, ⊤)
      (Set.range fun a : Γ(F, U) => pullbackSectionHom T.hom.hom F U ⊤ hX a) ≤ Q :=
    Submodule.span_le.2 (by rintro z ⟨a, rfl⟩; exact hmem a)
  exact hle hy

/-- **Restriction along the open immersion of an open of an object, in the pullback-sections
presheaf.**  It is `AlgebraicGeometry.openSubSections` of the restriction of the section to that
open: the restriction map of the presheaf of Stacks 03DS is
`AlgebraicGeometry.pullbackSectionsMap`, and the morphism of schemes over `S` that it is taken
along has `AlgebraicGeometry.BigFppfOver.openSubHom` for its underlying open immersion. -/
public theorem pullbackSectionsPresheaf_map_openSubHom (F : S.Modules)
    (T : BigFppfOver B S hS) (V : T.left.obj.Opens)
    (s : Γ((Scheme.Modules.pullback T.hom.hom).obj F, ⊤)) :
    (pullbackSectionsPresheaf B S hS F).map (openSubHom B S hS T V).op s =
      openSubSections T.hom.hom F V
        (((Scheme.Modules.pullback T.hom.hom).obj F).val.map
          (homOfLE (le_top (a := V))).op s) :=
  pullbackSectionsMap_eq_openSubSections T.hom.hom F V
    ((Over.post (X := B.obj hS) B.inclusion).map (openSubHom B S hS T V)) rfl s

/-- **The covering of an object by the opens over which a given section is a combination of
pulled-back sections.**  Its index type is the pairs of an open `V` of the underlying scheme of
`T` and an open `U` of `S` with `V ≤ T.hom⁻¹U` such that the restriction of `s` to `V` lies in the
span of the pullbacks of the sections of `F` over `U`, and its members are the open immersions of
those `V`.  Those opens cover, by
`AlgebraicGeometry.exists_span_pullbackSection`. -/
public noncomputable def sectionSubordinateCover (F : S.Modules) (T : BigFppfOver B S hS)
    (s : Γ((Scheme.Modules.pullback T.hom.hom).obj F, ⊤)) : PreZeroHypercover.{u + 1} T where
  I₀ := ULift.{u + 1} (Σ V : T.left.obj.Opens, {U : S.Opens //
    ∃ hVU : V ≤ T.hom.hom ⁻¹ᵁ U,
      ((Scheme.Modules.pullback T.hom.hom).obj F).val.map (homOfLE (le_top (a := V))).op s ∈
        Submodule.span Γ(T.left.obj, V)
          (Set.range fun a : Γ(F, U) => pullbackSectionHom T.hom.hom F U V hVU a)})
  X i := openSubObj B S hS T i.down.1
  f i := openSubHom B S hS T i.down.1

/-- The covering of `AlgebraicGeometry.BigFppfOver.sectionSubordinateCover` is an fppf covering
family of the chosen category of schemes: its members are open immersions, hence flat and locally
of finite presentation, and they are jointly surjective by
`AlgebraicGeometry.exists_span_pullbackSection`, which is where the generality in the module
enters. -/
public theorem isFppfCovering_sectionSubordinateCover (F : S.Modules)
    (T : BigFppfOver B S hS) (s : Γ((Scheme.Modules.pullback T.hom.hom).obj F, ⊤)) :
    IsFppfCovering (κ := B.cutoff)
      ⟨T.left, (sectionSubordinateCover B S hS F T s).map (Over.forget (B.obj hS))⟩ := by
  change Presieve.map B.inclusion
    ((sectionSubordinateCover B S hS F T s).map (Over.forget (B.obj hS))).presieve₀ ∈
      Scheme.fppfPrecoverage.coverings _
  rw [PreZeroHypercover.presieve₀, Presieve.map_ofArrows]
  refine Scheme.zariskiPrecoverage_le_fppfPrecoverage _ ?_
  rw [Scheme.zariskiPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
  refine ⟨fun x => ?_, fun i => ?_⟩
  · obtain ⟨W, hWtop, U, hWU, hxW, hspan⟩ :=
      exists_span_pullbackSection T.hom.hom F ⊤ s x trivial
    exact ⟨⟨⟨W, ⟨U, hWU, hspan⟩⟩⟩, ⟨⟨x, hxW⟩, rfl⟩⟩
  · exact inferInstanceAs (IsOpenImmersion (i.down.1.ι))

/-- **The opens of `AlgebraicGeometry.BigFppfOver.sectionSubordinateCover` cover, for each of the
five topologies.**  As for
`AlgebraicGeometry.BigFppfOver.mem_baseTopology_sieve₀_affineSubordinateCover`: the members are
open immersions and they are jointly surjective because they already form an fppf covering
family, so `AlgebraicGeometry.BigFppfOver.sieve₀_mem_baseTopology_of_isOpenImmersion`
applies. -/
public theorem mem_baseTopology_sieve₀_sectionSubordinateCover (τ : SiteKind) (F : S.Modules)
    (T : BigFppfOver B S hS) (s : Γ((Scheme.Modules.pullback T.hom.hom).obj F, ⊤)) :
    (sectionSubordinateCover B S hS F T s).sieve₀ ∈ baseOverTopology B S hS τ T := by
  have hfppf : (((sectionSubordinateCover B S hS F T s).map (Over.forget (B.obj hS))).map
      B.inclusion).presieve₀ ∈
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)).coverings
        (B.inclusion.obj T.left) := by
    rw [PreZeroHypercover.presieve₀_map]
    exact isFppfCovering_sectionSubordinateCover B S hS F T s
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact sieve₀_mem_baseTopology_of_isOpenImmersion B τ
    ((sectionSubordinateCover B S hS F T s).map (Over.forget (B.obj hS)))
    ((Scheme.presieve₀_mem_precoverage_iff _).1 hfppf).1
    (fun i => inferInstanceAs (IsOpenImmersion (i.down.1.ι)))

/-- **The comparison of Stacks 070S (1) is locally surjective, for every one of the five
topologies.**  Every section of the pullback-sections presheaf is, locally for the localized
`τ`-topology, in the image of `AlgebraicGeometry.BigFppfOver.pullbackSectionsComparison`.  By
`AlgebraicGeometry.exists_span_pullbackSection` a section is, over the members of
`AlgebraicGeometry.BigFppfOver.sectionSubordinateCover`, a combination of pullbacks of sections
of `F` over one open of `S`; those members cover for every `τ`
(`AlgebraicGeometry.BigFppfOver.mem_baseTopology_sieve₀_sectionSubordinateCover`), and over each
of them the combination lies in the image of the comparison
(`AlgebraicGeometry.BigFppfOver.mem_range_app_pullbackSectionsComparison_of_mem_span`).

This is half of Stacks 070S (1); the other half is
`AlgebraicGeometry.BigFppfOver.isLocallyInjective_pullbackSectionsComparison`. -/
public instance isLocallySurjective_pullbackSectionsComparison (τ : SiteKind)
    (F : S.Modules) :
    Presheaf.IsLocallySurjective (baseOverTopology B S hS τ)
      ((PresheafOfModules.toPresheaf (FibredSite.baseRingStructureSheaf B S hS τ).obj).map
        (pullbackSectionsComparison B S hS F)) where
  imageSieve_mem {T} s := by
    refine (baseOverTopology B S hS τ).superset_covering ?_
      (mem_baseTopology_sieve₀_sectionSubordinateCover B S hS τ F T s)
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro i
    obtain ⟨⟨V, U, hVU, hspan⟩⟩ := i
    have hX : (⊤ : ((toScheme B S hS).obj (openSubObj B S hS T V)).Opens) ≤
        (openSubObj B S hS T V).hom.hom ⁻¹ᵁ U := fun w _ => hVU w.2
    have hr : Set.range ⇑(openSubObj B S hS T V).hom.hom ⊆ (U : Set S) := by
      rintro z ⟨w, rfl⟩
      exact hVU w.2
    obtain ⟨x, hx⟩ := mem_range_app_pullbackSectionsComparison_of_mem_span B S hS F
      (homOfRangeLe B S hS U hr) hX
      (openSubSections_mem_span T.hom.hom F V U hVU hX hspan)
    exact ⟨x, hx.trans (pullbackSectionsPresheaf_map_openSubHom B S hS F T V s).symm⟩

/-- **Granted local injectivity, the comparison sheafifies to an isomorphism, for every one of
the five topologies.**  A morphism of presheaves of modules which is locally bijective becomes an
isomorphism after sheafification; the locally surjective half is
`AlgebraicGeometry.BigFppfOver.isLocallySurjective_pullbackSectionsComparison`, so only
local injectivity is assumed.  That instance is supplied by
`AlgebraicGeometry.BigFppfOver.isLocallyInjective_pullbackSectionsComparison` below; the
statement is left untagged, a hypothesis the tagged form does not need having no business
appearing on it. -/
public theorem isIso_baseSheafification_map_pullbackSectionsComparison (τ : SiteKind)
    (F : S.Modules)
    [Presheaf.IsLocallyInjective (baseOverTopology B S hS τ)
      ((PresheafOfModules.toPresheaf (FibredSite.baseRingStructureSheaf B S hS τ).obj).map
        (pullbackSectionsComparison B S hS F))] :
    IsIso ((PresheafOfModules.sheafification.{u}
        (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj)).map
      (pullbackSectionsComparison B S hS F)) := by
  have hW : (baseOverTopology B S hS τ).W
      ((PresheafOfModules.toPresheaf (FibredSite.baseRingStructureSheaf B S hS τ).obj).map
        (pullbackSectionsComparison B S hS F)) :=
    GrothendieckTopology.W_of_isLocallyBijective _ _
  rw [GrothendieckTopology.W_iff] at hW
  exact (isIso_iff_of_reflects_iso
    ((PresheafOfModules.sheafification.{u}
        (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj)).map
      (pullbackSectionsComparison B S hS F))
    (SheafOfModules.toSheaf (FibredSite.baseRingStructureSheaf B S hS τ))).1 hW

end BigFppfOver

end AlgebraicGeometry

end
