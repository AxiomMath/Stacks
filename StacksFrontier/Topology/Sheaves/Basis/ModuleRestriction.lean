module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Module.MinimalAxioms
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Restricting sheaves of modules to a basis (Stacks 009U)

Let `X` be a topological space, `B` a basis for its topology, and `𝒪` a sheaf of
rings on `X`. Viewing `B` as the full subcategory `BasisCat B` of `Opens X`, the
inclusion `basisInclusion B : BasisCat B ⥤ Opens X` is cover dense, locally full
and locally faithful for the standard topology on `Opens X`, hence a dense
subsite; `basisGrothendieckTopology` is the topology it induces on `BasisCat B`.
Pushing `𝒪` forward along the inclusion gives the restricted ring sheaf `𝒪|_B`,
and `restrictModuleSheaf` is the induced functor
`SheafOfModules 𝒪 ⥤ SheafOfModules (𝒪|_B)`.

The main result is that this restriction functor is an equivalence. The
formalization factors it through the Comparison Lemma for the underlying sheaves
of abelian groups: `sheafPushforwardContinuous` for `AddCommGrpCat` is an
equivalence because the inclusion is a dense subsite, and `SheafOfModules.toSheaf`
is faithful and reflects isomorphisms, so restriction of module sheaves is
faithful for free. Fullness is obtained by lifting a morphism of restricted module
sheaves to the group-sheaf level, where the lift is automatically `𝒪`-linear
because linearity is a local condition checked on basis opens. Essential
surjectivity transports the module structure of a sheaf on `B` back along the
counit of the group-sheaf equivalence: the scalar action on an open `U` is defined
by gluing the actions prescribed on the basis opens contained in `U`, which is
legitimate exactly because those opens cover `U`.

This is the module analogue of Stacks 009H for sheaves of sets.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

namespace Stacks.BasisRestriction

universe u w

-- `TopCat.Sheaf` is a plain `def` for `CategoryTheory.Sheaf (Opens.grothendieckTopology X) C`.
-- Since Lean 4.34 instance synthesis will not unfold a semireducible definition, so without
-- this the `Category (SheafOfModules 𝒪)` instance cannot be matched against a sheaf of rings
-- presented as `𝒪 : TopCat.Sheaf RingCat X`.
attribute [local instance_reducible] TopCat.Sheaf

-- Likewise `PresheafOfModules.presheaf` is a plain `def`, so the module-sections spelling
-- `M.val.obj (op V)` and the underlying-abelian-group spelling `M.toSheaf.obj.obj (op V)` are
-- identified only by unfolding it; without this `rw`/`simp` cannot build a motive across the two.
attribute [local implicit_reducible] PresheafOfModules.presheaf SheafOfModules.toSheaf

variable {X : TopCat.{u}}

/-- The full subcategory of `Opens X` consisting of basis elements. -/
abbrev BasisCat (B : Set (Opens X)) : Type _ :=
  ObjectProperty.FullSubcategory ((· ∈ B) : Opens X → Prop)

/-- The inclusion functor from the basis category to `Opens X`. -/
abbrev basisInclusion (B : Set (Opens X)) : BasisCat B ⥤ Opens X :=
  ObjectProperty.ι _

/-- When `B` is a basis, the inclusion `BasisCat B ⥤ Opens X` is locally cover dense
with respect to the standard Grothendieck topology on `Opens X`. -/
lemma locallyCoverDense_of_isBasis {B : Set (Opens X)} (hB : Opens.IsBasis B) :
    (basisInclusion B).LocallyCoverDense (Opens.grothendieckTopology X) := by
  refine ⟨fun V T x hx => ?_⟩
  obtain ⟨W, f, hf, hxW⟩ := T.property x hx
  obtain ⟨_, ⟨U', hU'B, rfl⟩, hxU', hU'W⟩ := hB.exists_subset_of_mem_open hxW W.2
  have hU'V : (U' : Opens X) ≤ (basisInclusion B).obj V := le_trans hU'W (leOfHom f)
  let g : (⟨U', hU'B⟩ : BasisCat B) ⟶ V := ObjectProperty.homMk (homOfLE hU'V)
  have hg_in_pullback : (Sieve.functorPullback (basisInclusion B) T.val).arrows g := by
    rw [Sieve.functorPullback_apply, Presieve.functorPullback_mem,
      show (basisInclusion B).map g = homOfLE hU'W ≫ f from Subsingleton.elim _ _]
    exact T.val.downward_closed hf (homOfLE hU'W)
  exact ⟨_, (basisInclusion B).map g, Sieve.image_mem_functorPushforward _ _ hg_in_pullback, hxU'⟩

/-- The Grothendieck topology on the basis category induced from the standard
Grothendieck topology on `Opens X`. -/
noncomputable def basisGrothendieckTopology {B : Set (Opens X)} (hB : Opens.IsBasis B) :
    GrothendieckTopology (BasisCat B) :=
  letI : (basisInclusion B).LocallyCoverDense (Opens.grothendieckTopology X) :=
    locallyCoverDense_of_isBasis hB
  (basisInclusion B).inducedTopology (Opens.grothendieckTopology X)

/-- The basis inclusion is cover dense with respect to the standard Grothendieck topology. -/
lemma basisInclusion_isCoverDense {B : Set (Opens X)} (hB : Opens.IsBasis B) :
    (basisInclusion B).IsCoverDense (Opens.grothendieckTopology X) := by
  refine ⟨fun U x hx => ?_⟩
  obtain ⟨_, ⟨W, hWB, rfl⟩, hxW, hWU⟩ := hB.exists_subset_of_mem_open hx U.2
  exact ⟨W, homOfLE hWU, ⟨⟨⟨W, hWB⟩, 𝟙 _, homOfLE hWU, by simp⟩⟩, hxW⟩

/-- The inclusion functor is continuous between the induced topology and the
standard topology on `Opens X`. -/
instance basisInclusion_isContinuous {B : Set (Opens X)} (hB : Opens.IsBasis B) :
    (basisInclusion B).IsContinuous
      (basisGrothendieckTopology hB) (Opens.grothendieckTopology X) := by
  unfold basisGrothendieckTopology
  infer_instance

/-- The restriction of a sheaf of rings on `X` to the basis category `B`. -/
noncomputable def restrictRingSheafToBasis {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (𝒪 : TopCat.Sheaf RingCat X) : Sheaf (basisGrothendieckTopology hB) RingCat :=
  ((basisInclusion B).sheafPushforwardContinuous RingCat
    (basisGrothendieckTopology hB) (Opens.grothendieckTopology X)).obj 𝒪

/-- The category of sheaves of `𝒪|_B`-modules on the basis `B`. -/
abbrev ModuleSheafOnBasis {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (𝒪 : TopCat.Sheaf RingCat X) : Type _ :=
  SheafOfModules.{max u w} (restrictRingSheafToBasis hB 𝒪)

/-- The restriction-to-`B` functor on sheaves of `𝒪`-modules.

This is defined as the pushforward along the inclusion `B ↪ Opens X`, applied to
sheaves of modules. The ring-level pushforward sends `𝒪` to its restriction
`𝒪|_B`, so the module-level pushforward goes from `SheafOfModules 𝒪` to
`SheafOfModules (𝒪|_B)`. -/
@[stacks 009U]
noncomputable def restrictModuleSheaf {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (𝒪 : TopCat.Sheaf RingCat X) :
    SheafOfModules.{max u w} 𝒪 ⥤ ModuleSheafOnBasis hB 𝒪 :=
  SheafOfModules.pushforward (F := basisInclusion B)
    (S := restrictRingSheafToBasis hB 𝒪)
    (R := 𝒪)
    (𝟙 _)

/-- The basis inclusion is a dense subsite: the induced topology is characterized by
    functorPushforward membership. -/
instance basisInclusion_isDenseSubsite {B : Set (Opens X)} (hB : Opens.IsBasis B) :
    Functor.IsDenseSubsite (basisGrothendieckTopology hB) (Opens.grothendieckTopology X)
      (basisInclusion B) where
  isCoverDense' := basisInclusion_isCoverDense hB
  isLocallyFull' := Functor.IsLocallyFull.of_full _
  isLocallyFaithful' := Functor.IsLocallyFaithful.of_faithful _
  functorPushforward_mem_iff := by
    have := basisInclusion_isCoverDense hB
    intro Y S
    exact (Functor.mem_inducedTopology_iff_of_isCoverDense (basisInclusion B)
      (Opens.grothendieckTopology X) S).symm

/-- The basis inclusion is cocontinuous (from the induced topology to the standard one). -/
instance basisInclusion_isCocontinuous {B : Set (Opens X)} (hB : Opens.IsBasis B) :
    (basisInclusion B).IsCocontinuous
      (basisGrothendieckTopology hB) (Opens.grothendieckTopology X) := by
  have := basisInclusion_isDenseSubsite hB
  infer_instance

/-- The sheaf pushforward along the basis inclusion is an equivalence for AddCommGrpCat.
    This is the Comparison Lemma for Grothendieck topologies (Stacks 00XZ). -/
noncomputable instance basisSheafPushforwardContinuous_isEquivalence
    {B : Set (Opens X)} (hB : Opens.IsBasis B) :
    ((basisInclusion B).sheafPushforwardContinuous AddCommGrpCat.{max u w}
      (basisGrothendieckTopology hB) (Opens.grothendieckTopology X)).IsEquivalence :=
  inferInstance

/-- The restriction-to-basis functor on module sheaves is faithful.

    This follows because the composition with `toSheaf` (which is faithful)
    equals `toSheaf ⋙ sheafPushforwardContinuous`, and the latter is faithful
    (as an equivalence composed with a faithful functor). -/
lemma restrictModuleSheaf_faithful {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (𝒪 : TopCat.Sheaf RingCat X) :
    (restrictModuleSheaf hB 𝒪).Faithful := by
  have heq : (restrictModuleSheaf hB 𝒪 ⋙ SheafOfModules.toSheaf _) =
    (SheafOfModules.toSheaf 𝒪 ⋙ (basisInclusion B).sheafPushforwardContinuous AddCommGrpCat
      (basisGrothendieckTopology hB) (Opens.grothendieckTopology X)) := rfl
  have hcomp : (restrictModuleSheaf hB 𝒪 ⋙ SheafOfModules.toSheaf _).Faithful := by
    rw [heq]
    exact Functor.Faithful.comp _ _
  exact Functor.Faithful.of_comp (F := restrictModuleSheaf hB 𝒪) (G := SheafOfModules.toSheaf _)

/-- Given a morphism f between restricted module sheaves, construct a preimage
    by lifting through the sheaf-level equivalence. The lifted group-sheaf morphism
    is automatically linear (by separation). -/
noncomputable def restrictModuleSheaf_preimage {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (𝒪 : TopCat.Sheaf RingCat X) (M N : SheafOfModules.{max u w} 𝒪)
    (f : (restrictModuleSheaf hB 𝒪).obj M ⟶ (restrictModuleSheaf hB 𝒪).obj N) :
    M ⟶ N := by
  let G := (basisInclusion B).sheafPushforwardContinuous AddCommGrpCat.{max u w}
      (basisGrothendieckTopology hB) (Opens.grothendieckTopology X)
  let key : G.obj ((SheafOfModules.toSheaf 𝒪).obj M) ⟶
             G.obj ((SheafOfModules.toSheaf 𝒪).obj N) :=
    (SheafOfModules.toSheaf _).map f
  let g' := G.preimage key
  have hlin : ∀ (V : Opens X), V ∈ B → ∀ (s : 𝒪.obj.obj (op V))
      (x : ((SheafOfModules.toSheaf 𝒪).obj M).obj.obj (op V)),
      ConcreteCategory.hom (g'.hom.app (op V))
          (ConcreteCategory.hom ((M.val.obj (op V)).smul s).asHom x) =
        ConcreteCategory.hom ((N.val.obj (op V)).smul s).asHom
          (ConcreteCategory.hom (g'.hom.app (op V)) x) := by
    intro V hVB s x
    have hf : ∀ y : ((SheafOfModules.toSheaf 𝒪).obj M).obj.obj (op V),
        ConcreteCategory.hom (g'.hom.app (op V)) y =
          ConcreteCategory.hom (f.val.app (op ⟨V, hVB⟩)) y := by
      intro y
      have h : g'.hom.app (op V) = key.hom.app (op ⟨V, hVB⟩) :=
        congrArg (fun φ => φ.hom.app (op ⟨V, hVB⟩)) (G.map_preimage key)
      simp only [h, key]
      rfl
    rw [hf, hf]
    exact LinearMap.map_smul (ModuleCat.Hom.hom (f.val.app (op ⟨V, hVB⟩))) s x
  exact SheafOfModules.Hom.mk (PresheafOfModules.Hom.mk (fun U =>
    ModuleCat.homMk (g'.hom.app U) (by
      intro r
      apply ConcreteCategory.hom_ext
      intro m
      apply TopCat.Sheaf.eq_of_locally_eq' ((SheafOfModules.toSheaf 𝒪).obj N)
        (fun (V : { V : Opens X // V ∈ B ∧ V ≤ U.unop }) => V.1) U.unop (fun V => homOfLE V.2.2)
        (by
          intro x hx
          rw [Opens.mem_iSup]
          obtain ⟨_, ⟨V, hVB, rfl⟩, hxV, hVU⟩ := hB.exists_subset_of_mem_open hx U.unop.isOpen
          exact ⟨⟨V, hVB, hVU⟩, hxV⟩)
      intro ⟨V, hVB, hVU⟩
      simp only [ConcreteCategory.comp_apply]
      let res_r := ConcreteCategory.hom (𝒪.obj.map (homOfLE hVU).op) r
      let res_m := ConcreteCategory.hom
        (((SheafOfModules.toSheaf 𝒪).obj M).obj.map (homOfLE hVU).op) m
      have lhs : ConcreteCategory.hom (((SheafOfModules.toSheaf 𝒪).obj N).obj.map (homOfLE hVU).op)
          (ConcreteCategory.hom ((N.val.obj U).smul r).asHom
            (ConcreteCategory.hom (g'.hom.app U) m)) =
          ConcreteCategory.hom ((N.val.obj (op V)).smul res_r).asHom
            (ConcreteCategory.hom (((SheafOfModules.toSheaf 𝒪).obj N).obj.map (homOfLE hVU).op)
              (ConcreteCategory.hom (g'.hom.app U) m)) :=
        PresheafOfModules.map_smul N.val (homOfLE hVU).op r
          (ConcreteCategory.hom (g'.hom.app U) m)
      have lhs2 : ConcreteCategory.hom (((SheafOfModules.toSheaf 𝒪).obj N).obj.map (homOfLE hVU).op)
          (ConcreteCategory.hom (g'.hom.app U) m) =
          ConcreteCategory.hom (g'.hom.app (op V)) res_m :=
        (NatTrans.naturality_apply g'.hom (homOfLE hVU).op m).symm
      have rhs : ConcreteCategory.hom (((SheafOfModules.toSheaf 𝒪).obj N).obj.map (homOfLE hVU).op)
          (ConcreteCategory.hom (g'.hom.app U)
            (ConcreteCategory.hom ((M.val.obj U).smul r).asHom m)) =
          ConcreteCategory.hom (g'.hom.app (op V))
            (ConcreteCategory.hom (((SheafOfModules.toSheaf 𝒪).obj M).obj.map (homOfLE hVU).op)
              (ConcreteCategory.hom ((M.val.obj U).smul r).asHom m)) :=
        (NatTrans.naturality_apply g'.hom (homOfLE hVU).op
          (ConcreteCategory.hom ((M.val.obj U).smul r).asHom m)).symm
      have rhs2 : ConcreteCategory.hom (((SheafOfModules.toSheaf 𝒪).obj M).obj.map (homOfLE hVU).op)
          (ConcreteCategory.hom ((M.val.obj U).smul r).asHom m) =
          ConcreteCategory.hom ((M.val.obj (op V)).smul res_r).asHom res_m :=
        PresheafOfModules.map_smul M.val (homOfLE hVU).op r m
      convert lhs.trans ((congrArg _ lhs2).trans
        ((hlin V hVB res_r res_m).symm.trans ((congrArg _ rhs2.symm).trans rhs.symm))) using 1)) (by
      intro _ _ f₁
      ext m
      exact NatTrans.naturality_apply g'.hom f₁ m))

/-- The preimage constructed above maps to the original morphism. -/
lemma restrictModuleSheaf_preimage_spec {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (𝒪 : TopCat.Sheaf RingCat X) (M N : SheafOfModules.{max u w} 𝒪)
    (f : (restrictModuleSheaf hB 𝒪).obj M ⟶ (restrictModuleSheaf hB 𝒪).obj N) :
    (restrictModuleSheaf hB 𝒪).map (restrictModuleSheaf_preimage hB 𝒪 M N f) = f := by
  apply (SheafOfModules.toSheaf _).map_injective
  change ((SheafOfModules.toSheaf 𝒪 ⋙ (basisInclusion B).sheafPushforwardContinuous AddCommGrpCat
      (basisGrothendieckTopology hB) (Opens.grothendieckTopology X)).map
    (restrictModuleSheaf_preimage hB 𝒪 M N f)) = (SheafOfModules.toSheaf _).map f
  simp only [Functor.comp_map]
  exact Functor.map_preimage
    ((basisInclusion B).sheafPushforwardContinuous AddCommGrpCat.{max u w}
      (basisGrothendieckTopology hB) (Opens.grothendieckTopology X))
    (show ((basisInclusion B).sheafPushforwardContinuous AddCommGrpCat.{max u w}
      (basisGrothendieckTopology hB) (Opens.grothendieckTopology X)).obj
      ((SheafOfModules.toSheaf 𝒪).obj M) ⟶
      ((basisInclusion B).sheafPushforwardContinuous AddCommGrpCat.{max u w}
      (basisGrothendieckTopology hB) (Opens.grothendieckTopology X)).obj
      ((SheafOfModules.toSheaf 𝒪).obj N) from (SheafOfModules.toSheaf _).map f)

/-- The restriction-to-basis functor on module sheaves is full: a morphism of the
restrictions lifts to a morphism of the original module sheaves. -/
lemma restrictModuleSheaf_full {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (𝒪 : TopCat.Sheaf RingCat X) :
    (restrictModuleSheaf (X := X) hB 𝒪 : SheafOfModules.{max u w} 𝒪 ⥤ _).Full :=
  ⟨fun f => ⟨restrictModuleSheaf_preimage hB 𝒪 _ _ f,
    restrictModuleSheaf_preimage_spec hB 𝒪 _ _ f⟩⟩

/-- Every open `U` is covered by the basis opens contained in it. -/
lemma extCover {B : Set (Opens X)} (hB : Opens.IsBasis B) (U : (Opens X)ᵒᵖ) :
    U.unop ≤ iSup (fun (V : { V : Opens X // V ∈ B ∧ V ≤ U.unop }) => V.1) := by
  intro x hx
  rw [Opens.mem_iSup]
  obtain ⟨_, ⟨V, hVB, rfl⟩, hxV, hVU⟩ := hB.exists_subset_of_mem_open hx U.unop.isOpen
  exact ⟨⟨V, hVB, hVU⟩, hxV⟩

section EssSurj

variable {B : Set (Opens X)} {hB : Opens.IsBasis B} {𝒪 : TopCat.Sheaf RingCat X}

/-- The abelian sheaf on `X` whose restriction to `B` is the underlying abelian sheaf of `N`,
obtained from the comparison-lemma equivalence. -/
noncomputable abbrev extAb (N : ModuleSheafOnBasis.{u, w} hB 𝒪) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u w} :=
  ((basisInclusion B).sheafPushforwardContinuous AddCommGrpCat.{max u w}
      (basisGrothendieckTopology hB) (Opens.grothendieckTopology X)).asEquivalence.inverse.obj
    ((SheafOfModules.toSheaf (restrictRingSheafToBasis hB 𝒪)).obj N)

/-- The counit identifying the restriction of `extAb N` to `B` with the underlying abelian sheaf
of `N`. -/
noncomputable abbrev extCounit (N : ModuleSheafOnBasis.{u, w} hB 𝒪) :=
  ((basisInclusion B).sheafPushforwardContinuous AddCommGrpCat.{max u w}
      (basisGrothendieckTopology hB) (Opens.grothendieckTopology X)).asEquivalence.counitIso.app
    ((SheafOfModules.toSheaf (restrictRingSheafToBasis hB 𝒪)).obj N)

/-- The scalar multiplication on `extAb N` restricted to a basis open `V ⊆ U`, transported from
the module structure of `N` along the counit. -/
noncomputable def extLocalSmul (N : ModuleSheafOnBasis.{u, w} hB 𝒪) (U : (Opens X)ᵒᵖ)
    (r : ↑(𝒪.obj.obj U)) (m : ↑((extAb N).obj.obj U))
    (V : { V : Opens X // V ∈ B ∧ V ≤ U.unop }) : ↑((extAb N).obj.obj (op V.1)) :=
  ConcreteCategory.hom ((extCounit N).inv.hom.app (op ⟨V.1, V.2.1⟩))
    (ConcreteCategory.hom ((N.val.obj (op ⟨V.1, V.2.1⟩)).smul
      (ConcreteCategory.hom (𝒪.obj.map (homOfLE V.2.2).op) r)).asHom
      (ConcreteCategory.hom ((extCounit N).hom.hom.app (op ⟨V.1, V.2.1⟩))
        (ConcreteCategory.hom ((extAb N).obj.map (homOfLE V.2.2).op) m)))

/-- Functoriality of a functor into a concrete category, on elements, for any equal composite. -/
private lemma hom_map_map_apply {C D : Type*} [Category C] [Category D] {FD : D → D → Type*}
    {CD : D → Type*} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]
    (F : C ⥤ D) {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (hfg : f ≫ g = h)
    (x : ToType (F.obj X)) :
    ConcreteCategory.hom (F.map g) (ConcreteCategory.hom (F.map f) x) =
      ConcreteCategory.hom (F.map h) x := by
  rw [← hfg, F.map_comp, ConcreteCategory.comp_apply]

/-- Functoriality of a functor into a concrete category on elements, for an identity morphism. -/
private lemma hom_map_id_apply {C D : Type*} [Category C] [Category D] {FD : D → D → Type*}
    {CD : D → Type*} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]
    (F : C ⥤ D) {X : C} {f : X ⟶ X} (hf : f = 𝟙 X) (x : ToType (F.obj X)) :
    ConcreteCategory.hom (F.map f) x = x := by
  rw [hf, F.map_id, ConcreteCategory.id_apply]

/-- Restricting `extLocalSmul` from a basis open `V` to a smaller basis open `W` gives the
`extLocalSmul` at `W`. -/
private lemma extAb_map_extLocalSmul (N : ModuleSheafOnBasis.{u, w} hB 𝒪) (U : (Opens X)ᵒᵖ)
    (r : ↑(𝒪.obj.obj U)) (m : ↑((extAb N).obj.obj U)) {V W : Opens X} (hVB : V ∈ B) (hWB : W ∈ B)
    (hVU : V ≤ U.unop) (hWV : W ≤ V) :
    ConcreteCategory.hom ((extAb N).obj.map (homOfLE hWV).op)
        (extLocalSmul N U r m ⟨V, hVB, hVU⟩) =
      extLocalSmul N U r m ⟨W, hWB, hWV.trans hVU⟩ := by
  unfold extLocalSmul
  let g : (⟨W, hWB⟩ : BasisCat B) ⟶ ⟨V, hVB⟩ := ObjectProperty.homMk (homOfLE hWV)
  have nat_inv : ∀ (x : _),
      ConcreteCategory.hom ((extAb N).obj.map (homOfLE hWV).op)
        (ConcreteCategory.hom ((extCounit N).inv.hom.app (op ⟨V, hVB⟩)) x) =
      ConcreteCategory.hom ((extCounit N).inv.hom.app (op ⟨W, hWB⟩))
        (ConcreteCategory.hom (((SheafOfModules.toSheaf _).obj N).obj.map g.op) x) :=
    fun x => (NatTrans.naturality_apply (extCounit N).inv.hom g.op x).symm
  have smul_res : ∀ (s : 𝒪.obj.obj (op V)) (y : _),
      ConcreteCategory.hom (((SheafOfModules.toSheaf _).obj N).obj.map g.op)
        (ConcreteCategory.hom ((N.val.obj (op ⟨V, hVB⟩)).smul s).asHom y) =
      ConcreteCategory.hom ((N.val.obj (op ⟨W, hWB⟩)).smul
        (ConcreteCategory.hom (𝒪.obj.map (homOfLE hWV).op) s)).asHom
        (ConcreteCategory.hom (((SheafOfModules.toSheaf _).obj N).obj.map g.op) y) :=
    fun s y => PresheafOfModules.map_smul N.val g.op s y
  have nat_hom : ∀ (x : _),
      ConcreteCategory.hom (((SheafOfModules.toSheaf _).obj N).obj.map g.op)
        (ConcreteCategory.hom ((extCounit N).hom.hom.app (op ⟨V, hVB⟩)) x) =
      ConcreteCategory.hom ((extCounit N).hom.hom.app (op ⟨W, hWB⟩))
        (ConcreteCategory.hom ((extAb N).obj.map (homOfLE hWV).op) x) :=
    fun x => (NatTrans.naturality_apply (extCounit N).hom.hom g.op x).symm
  have func_M := hom_map_map_apply (extAb N).obj
    (Subsingleton.elim ((homOfLE hVU).op ≫ (homOfLE hWV).op) (homOfLE (hWV.trans hVU)).op) m
  have func_O := hom_map_map_apply 𝒪.obj
    (Subsingleton.elim ((homOfLE hVU).op ≫ (homOfLE hWV).op) (homOfLE (hWV.trans hVU)).op) r
  simp only [nat_inv, smul_res, func_O]
  congr 2
  exact (nat_hom _).trans (congrArg _ func_M)

/-- The local scalar multiplications `extLocalSmul` are compatible. -/
lemma extLocalSmul_compatible (N : ModuleSheafOnBasis.{u, w} hB 𝒪) (U : (Opens X)ᵒᵖ)
    (r : ↑(𝒪.obj.obj U)) (m : ↑((extAb N).obj.obj U)) :
    TopCat.Presheaf.IsCompatible (extAb N).obj _ (extLocalSmul N U r m) := by
  intro ⟨V₁, hV₁B, hV₁U⟩ ⟨V₂, hV₂B, hV₂U⟩
  apply TopCat.Sheaf.eq_of_locally_eq' (extAb N)
    (fun (W : { W : Opens X // W ∈ B ∧ W ≤ V₁ ⊓ V₂ }) => W.1)
    (V₁ ⊓ V₂) (fun W => homOfLE W.2.2) (extCover hB (op (V₁ ⊓ V₂)))
  intro ⟨W, hWB, hWV⟩
  simp only []
  have hWV₁ : W ≤ V₁ := hWV.trans inf_le_left
  have hWV₂ : W ≤ V₂ := hWV.trans inf_le_right
  rw [hom_map_map_apply (extAb N).obj (Subsingleton.elim _ (homOfLE hWV₁).op),
    hom_map_map_apply (extAb N).obj (Subsingleton.elim _ (homOfLE hWV₂).op),
    extAb_map_extLocalSmul N U r m hV₁B hWB hV₁U hWV₁,
    extAb_map_extLocalSmul N U r m hV₂B hWB hV₂U hWV₂]
-- Define SMul for each U using sheaf gluing

/-- The scalar multiplication on `extAb N`, glued from `extLocalSmul`. -/
noncomputable instance extSMul (N : ModuleSheafOnBasis.{u, w} hB 𝒪) (U : (Opens X)ᵒᵖ) :
    SMul (↑(𝒪.obj.obj U)) (↑((extAb N).obj.obj U)) :=
  ⟨fun r m => (TopCat.Sheaf.existsUnique_gluing' (extAb N) _ U.unop
    (fun V => homOfLE V.2.2) (extCover hB U) (extLocalSmul N U r m)
      (extLocalSmul_compatible N U r m)).choose⟩

/-- The restriction of `r • m` to a basis open `V` is `extLocalSmul`. -/
lemma extSMul_spec (N : ModuleSheafOnBasis.{u, w} hB 𝒪) (U : (Opens X)ᵒᵖ) (r : ↑(𝒪.obj.obj U))
    (m : ↑((extAb N).obj.obj U)) (V : { V : Opens X // V ∈ B ∧ V ≤ U.unop }) :
    ConcreteCategory.hom ((extAb N).obj.map (homOfLE V.2.2).op) (r • m) =
      extLocalSmul N U r m V :=
  (TopCat.Sheaf.existsUnique_gluing' (extAb N) _ U.unop (fun V => homOfLE V.2.2)
    (extCover hB U) (extLocalSmul N U r m) (extLocalSmul_compatible N U r m)).choose_spec.1 V

/-- The module structure on the sections of `extAb N`. -/
noncomputable instance extModule (N : ModuleSheafOnBasis.{u, w} hB 𝒪) (U : (Opens X)ᵒᵖ) :
    Module (↑(𝒪.obj.obj U)) (↑((extAb N).obj.obj U)) :=
  Module.ofMinimalAxioms
    (fun r x y => by
      apply TopCat.Sheaf.eq_of_locally_eq' (extAb N) _ U.unop (fun V => homOfLE V.2.2)
        (extCover hB U)
      intro V
      rw [extSMul_spec N, map_add (ConcreteCategory.hom ((extAb N).obj.map (homOfLE V.2.2).op)),
        extSMul_spec N U r x V, extSMul_spec N U r y V]
      unfold extLocalSmul
      rw [map_add (ConcreteCategory.hom ((extAb N).obj.map (homOfLE V.2.2).op)) x y]
      have := congrArg (ConcreteCategory.hom ((extCounit N).inv.hom.app (op ⟨↑V, V.2.1⟩)))
        (congrArg (ConcreteCategory.hom ((N.val.obj (op ⟨↑V, V.2.1⟩)).smul
          (ConcreteCategory.hom (𝒪.obj.map (homOfLE V.2.2).op) r)).asHom)
          (map_add (ConcreteCategory.hom ((extCounit N).hom.hom.app (op ⟨↑V, V.2.1⟩)))
            (ConcreteCategory.hom ((extAb N).obj.map (homOfLE V.2.2).op) x)
            (ConcreteCategory.hom ((extAb N).obj.map (homOfLE V.2.2).op) y)))
      have h_smul := congrArg (ConcreteCategory.hom ((extCounit N).inv.hom.app (op ⟨↑V, V.2.1⟩)))
        (map_add (ConcreteCategory.hom ((N.val.obj (op ⟨↑V, V.2.1⟩)).smul
          (ConcreteCategory.hom (𝒪.obj.map (homOfLE V.2.2).op) r)).asHom)
          (ConcreteCategory.hom ((extCounit N).hom.hom.app (op ⟨↑V, V.2.1⟩))
            (ConcreteCategory.hom ((extAb N).obj.map (homOfLE V.2.2).op) x))
          (ConcreteCategory.hom ((extCounit N).hom.hom.app (op ⟨↑V, V.2.1⟩))
            (ConcreteCategory.hom ((extAb N).obj.map (homOfLE V.2.2).op) y)))
      have h_inv := map_add (ConcreteCategory.hom ((extCounit N).inv.hom.app (op ⟨↑V, V.2.1⟩)))
        (ConcreteCategory.hom ((N.val.obj (op ⟨↑V, V.2.1⟩)).smul
          (ConcreteCategory.hom (𝒪.obj.map (homOfLE V.2.2).op) r)).asHom
          (ConcreteCategory.hom ((extCounit N).hom.hom.app (op ⟨↑V, V.2.1⟩))
            (ConcreteCategory.hom ((extAb N).obj.map (homOfLE V.2.2).op) x)))
        (ConcreteCategory.hom ((N.val.obj (op ⟨↑V, V.2.1⟩)).smul
          (ConcreteCategory.hom (𝒪.obj.map (homOfLE V.2.2).op) r)).asHom
          (ConcreteCategory.hom ((extCounit N).hom.hom.app (op ⟨↑V, V.2.1⟩))
            (ConcreteCategory.hom ((extAb N).obj.map (homOfLE V.2.2).op) y)))
      exact this.trans (h_smul.trans h_inv))
    (fun r s x => by
      apply TopCat.Sheaf.eq_of_locally_eq' (extAb N) _ U.unop (fun V => homOfLE V.2.2)
        (extCover hB U)
      intro V
      rw [extSMul_spec N, map_add (ConcreteCategory.hom ((extAb N).obj.map (homOfLE V.2.2).op)),
        extSMul_spec N U r x V, extSMul_spec N U s x V]
      unfold extLocalSmul
      rw [map_add (ConcreteCategory.hom (𝒪.obj.map (homOfLE V.2.2).op)) r s]
      have h_smul_add := (N.val.obj (op ⟨↑V, V.2.1⟩)).smul.map_add
        (ConcreteCategory.hom (𝒪.obj.map (homOfLE V.2.2).op) r)
        (ConcreteCategory.hom (𝒪.obj.map (homOfLE V.2.2).op) s)
      have h_pt := DFunLike.congr_fun (congrArg (fun e => ConcreteCategory.hom e.asHom) h_smul_add)
        (ConcreteCategory.hom ((extCounit N).hom.hom.app (op ⟨↑V, V.2.1⟩))
          (ConcreteCategory.hom ((extAb N).obj.map (homOfLE V.2.2).op) x))
      exact (congrArg (ConcreteCategory.hom ((extCounit N).inv.hom.app (op ⟨↑V, V.2.1⟩)))
        h_pt).trans
        (map_add (ConcreteCategory.hom ((extCounit N).inv.hom.app (op ⟨↑V, V.2.1⟩))) _ _))
    (fun r s x => by
      apply TopCat.Sheaf.eq_of_locally_eq' (extAb N) _ U.unop (fun V => homOfLE V.2.2)
        (extCover hB U)
      intro V
      rw [extSMul_spec N, extSMul_spec N]
      unfold extLocalSmul
      congr 1
      rw [extSMul_spec N U s x V]
      unfold extLocalSmul
      have h_roundtrip : ∀ (y : _),
          (ConcreteCategory.hom ((extCounit N).hom.hom.app (op ⟨↑V, V.2.1⟩)))
            ((ConcreteCategory.hom ((extCounit N).inv.hom.app (op ⟨↑V, V.2.1⟩))) y) = y := by
        intro y
        have h : (extCounit N).inv.hom.app (op ⟨↑V, V.2.1⟩) ≫
            (extCounit N).hom.hom.app (op ⟨↑V, V.2.1⟩) = 𝟙 _ :=
          congrArg (fun f => f.hom.app (op ⟨↑V, V.2.1⟩)) (extCounit N).inv_hom_id
        exact DFunLike.congr_fun (congrArg ConcreteCategory.hom h) y
      rw [h_roundtrip, map_mul (ConcreteCategory.hom (𝒪.obj.map (homOfLE V.2.2).op))]
      have h_mul := (N.val.obj (op ⟨↑V, V.2.1⟩)).smul.map_mul
        (ConcreteCategory.hom (𝒪.obj.map (homOfLE V.2.2).op) r)
        (ConcreteCategory.hom (𝒪.obj.map (homOfLE V.2.2).op) s)
      exact DFunLike.congr_fun (congrArg (fun e => ConcreteCategory.hom e.asHom) h_mul) _)
    (fun x => by
      apply TopCat.Sheaf.eq_of_locally_eq' (extAb N) _ U.unop (fun V => homOfLE V.2.2)
        (extCover hB U)
      intro V
      rw [extSMul_spec N]
      unfold extLocalSmul
      trans (ConcreteCategory.hom ((extCounit N).inv.hom.app (op ⟨↑V, V.2.1⟩)))
        ((ConcreteCategory.hom ((extCounit N).hom.hom.app (op ⟨↑V, V.2.1⟩)))
          ((ConcreteCategory.hom ((extAb N).obj.map (homOfLE V.2.2).op)) x))
      · congr 1
        rw [map_one (ConcreteCategory.hom (𝒪.obj.map (homOfLE V.2.2).op))]
        have hone : ((N.val.obj (op ⟨↑V, V.2.1⟩)).smul 1).asHom = 𝟙 _ := by
          rw [(N.val.obj (op ⟨↑V, V.2.1⟩)).smul.map_one, End.one_asHom]
        exact DFunLike.congr_fun (congrArg ConcreteCategory.hom hone) _
      · have h : (extCounit N).hom.hom.app (op ⟨↑V, V.2.1⟩) ≫
            (extCounit N).inv.hom.app (op ⟨↑V, V.2.1⟩) = 𝟙 _ :=
          congrArg (fun f => f.hom.app (op ⟨↑V, V.2.1⟩)) (extCounit N).hom_inv_id
        exact DFunLike.congr_fun (congrArg ConcreteCategory.hom h) _)

/-- Restriction on `extAb N` commutes with scalar multiplication. -/
lemma extAb_map_smul (N : ModuleSheafOnBasis.{u, w} hB 𝒪) ⦃U V : (Opens X)ᵒᵖ⦄ (f : U ⟶ V)
    (r : ↑(𝒪.obj.obj U)) (m : ↑((extAb N).obj.obj U)) :
    (ConcreteCategory.hom ((extAb N).obj.map f)) (r • m) =
      (ConcreteCategory.hom (𝒪.obj.map f)) r • (ConcreteCategory.hom ((extAb N).obj.map f)) m := by
  apply TopCat.Sheaf.eq_of_locally_eq' (extAb N) _ V.unop (fun W => homOfLE W.2.2) (extCover hB V)
  intro ⟨W, hWB, hWV⟩
  have hWU : W ≤ U.unop := hWV.trans (leOfHom f.unop)
  have hfc : f ≫ (homOfLE hWV).op = (homOfLE hWU).op := Subsingleton.elim _ _
  rw [hom_map_map_apply (extAb N).obj hfc, extSMul_spec N U r m ⟨W, hWB, hWU⟩,
    extSMul_spec N V (ConcreteCategory.hom (𝒪.obj.map f) r)
      (ConcreteCategory.hom ((extAb N).obj.map f) m) ⟨W, hWB, hWV⟩]
  unfold extLocalSmul
  rw [← hom_map_map_apply 𝒪.obj hfc, ← hom_map_map_apply (extAb N).obj hfc]

/-- The sheaf of `𝒪`-modules on `X` extending `N`. -/
noncomputable def extModuleSheaf (N : ModuleSheafOnBasis.{u, w} hB 𝒪) :
    SheafOfModules.{max u w} 𝒪 :=
  SheafOfModules.mk (PresheafOfModules.ofPresheaf (extAb N).obj (extAb_map_smul N)) (by
    rw [PresheafOfModules.ofPresheaf_presheaf]
    exact (extAb N).property)

/-- The counit is linear for the module structures. -/
lemma extCounit_hom_smul (N : ModuleSheafOnBasis.{u, w} hB 𝒪) (V : (BasisCat B)ᵒᵖ)
    (r : ↑(𝒪.obj.obj (op V.unop.obj)))
    (m : ↑((extAb N).obj.obj (op V.unop.obj))) :
    ConcreteCategory.hom ((N.val.obj V).smul r).asHom
        (ConcreteCategory.hom ((extCounit N).hom.hom.app V) m) =
      ConcreteCategory.hom ((extCounit N).hom.hom.app V) (r • m) := by
  let W := V.unop.obj
  let hWB := V.unop.property
  have hWW : W ≤ W := le_rfl
  have hres_id : (homOfLE hWW).op = 𝟙 (op W) := Subsingleton.elim _ _
  have h1 := congrArg (ConcreteCategory.hom ((extCounit N).hom.hom.app (op ⟨W, hWB⟩)))
    (extSMul_spec N (op W) r m ⟨W, hWB, hWW⟩)
  unfold extLocalSmul at h1
  simp only [hom_map_id_apply 𝒪.obj hres_id, hom_map_id_apply (extAb N).obj hres_id] at h1
  have h_roundtrip : ∀ (y : _),
      (ConcreteCategory.hom ((extCounit N).hom.hom.app (op ⟨W, hWB⟩)))
        ((ConcreteCategory.hom ((extCounit N).inv.hom.app (op ⟨W, hWB⟩))) y) = y := by
    intro y
    have h : (extCounit N).inv.hom.app (op ⟨W, hWB⟩) ≫
        (extCounit N).hom.hom.app (op ⟨W, hWB⟩) = 𝟙 _ :=
      congrArg (fun f => f.hom.app (op ⟨W, hWB⟩)) (extCounit N).inv_hom_id
    exact DFunLike.congr_fun (congrArg ConcreteCategory.hom h) y
  rw [h_roundtrip] at h1
  exact h1.symm

end EssSurj

/-- The restriction-to-basis functor on module sheaves is essentially surjective.

    Key idea: given a module sheaf M on the basis, its underlying sheaf extends
    to a sheaf on X (by the sheaf-level equivalence being EssSurj).
    The extended sheaf inherits a module structure from M because the module
    scalar action is determined on basis elements and extends by the sheaf condition. -/
lemma restrictModuleSheaf_essSurj {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (𝒪 : TopCat.Sheaf RingCat X) :
    (restrictModuleSheaf (X := X) hB 𝒪 : SheafOfModules.{max u w} 𝒪 ⥤ _).EssSurj := by
  refine ⟨fun N => ?_⟩
  let φ : (restrictModuleSheaf hB 𝒪).obj (extModuleSheaf N) ⟶ N :=
    SheafOfModules.Hom.mk (PresheafOfModules.Hom.mk (fun V =>
      ModuleCat.homMk ((extCounit N).hom.hom.app V) (by
        intro r
        ext m
        exact extCounit_hom_smul N V r m)) (by
      intro V₁ V₂ f
      ext m
      exact NatTrans.naturality_apply (extCounit N).hom.hom f m))
  have hiso : IsIso ((SheafOfModules.toSheaf _).map φ) := by
    suffices h : (SheafOfModules.toSheaf _).map φ = (extCounit N).hom by
      rw [h]
      exact (extCounit N).isIso_hom
    ext V : 3
    rfl
  have := isIso_of_reflects_iso φ (SheafOfModules.toSheaf _)
  exact ⟨extModuleSheaf N, ⟨asIso φ⟩⟩

/-- **Stacks 009U.** The restriction-to-`B` functor

  `r : SheafOfModules 𝒪 ⥤ SheafOfModules (𝒪|_B)`,
  `F ↦ F|_B`,

is an equivalence of categories, where `𝒪|_B` is the restriction of the sheaf of
rings `𝒪` to the basis category `B`. -/
@[stacks 009U]
theorem isEquivalence_restrictModuleSheaf {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (𝒪 : TopCat.Sheaf RingCat X) :
    (restrictModuleSheaf (X := X) hB 𝒪 : SheafOfModules.{max u w} 𝒪 ⥤ _).IsEquivalence :=
  Functor.IsEquivalence.mk (faithful := restrictModuleSheaf_faithful hB 𝒪)
    (full := restrictModuleSheaf_full hB 𝒪) (essSurj := restrictModuleSheaf_essSurj hB 𝒪)

end Stacks.BasisRestriction
