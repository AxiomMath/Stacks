module

public import Mathlib.CategoryTheory.Sites.CompatibleSheafification
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Forget
public import StacksFrontier.Topology.Sheaves.AlgebraicStructure.SheafOfAlgStruct
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ExtensionByInitial
public import StacksFrontier.Topology.Sheaves.Stalk.ValuedInCategory

/-!
# Extension by the initial object for sheaves of algebraic structures

Let `X` be a topological space, `j : U → X` the inclusion of an open subset, and `(C, F)` a
type of algebraic structure (`AlgebraicStructureType`, Stacks 007M) such that `C` has an
initial object `e`. The extension by `e` of a presheaf `𝓕` on `U` is the presheaf `j_{p!}𝓕` on
`X` with `j_{p!}𝓕(V) = 𝓕(V)` for `V ⊆ U` and `j_{p!}𝓕(V) = e` otherwise
(`TopCat.Presheaf.extendByInitialFunctor`), and for a sheaf `𝓕` on `U` the sheaf `j_!𝓕` is
the sheafification of `j_{p!}𝓕`. This file proves Stacks 00A6: `j_{p!} ⊣ j_p`, `j_! ⊣ j^{-1}`,
the stalks of `j_!𝓕`, `j_p j_{p!} = id` and `j^{-1} j_! = id`.

Nothing beyond the structure of a type of algebraic structure and the initial object is
assumed. In particular `C` is not required to have all colimits: the sheafification is the
plus construction applied twice (`CategoryTheory.GrothendieckTopology.sheafify`), which only
uses limits and filtered colimits, and stalks are the filtered colimits of Stacks 007H
(`Stacks.Topology.CategoryStalk.stalkFunctor`).

A sheaf here is a sheaf in Mathlib's sense, `TopCat.Sheaf C X`. Because `F` reflects
isomorphisms and preserves limits, this is the same as asking that the underlying presheaf of
sets be a sheaf (`TopCat.Presheaf.isSheaf_iff_isSheaf_comp`), which is the definition of a
sheaf of algebraic structures in Stacks (Section 0071).

## Main definitions

* `AlgebraicStructureType.sheafifyFunctor`: the sheafification functor for presheaves of
  algebraic structures, and `AlgebraicStructureType.sheafifyAdjunction`, its adjunction with
  the inclusion of sheaves into presheaves.
* `AlgebraicStructureType.extendByInitialSheaf`: `j_! : Sh(U, C) ⥤ Sh(X, C)`.

## Main results (Stacks 00A6)

* `AlgebraicStructureType.extendByInitialAdjunction`: (1), `j_{p!} ⊣ j_p`.
* `AlgebraicStructureType.extendByInitialSheafAdjunction`: (2), `j_! ⊣ j^{-1}`.
* `AlgebraicStructureType.isInitialStalkExtendByInitialSheaf` and
  `AlgebraicStructureType.stalkExtendByInitialSheafIso`: (3), `(j_!𝓕)_x = e` for `x ∉ U` and
  `(j_!𝓕)_x = 𝓕_x` for `x ∈ U`.
* `AlgebraicStructureType.restrictExtendByInitialIso`: (4), `j_p j_{p!} = id`.
* `AlgebraicStructureType.restrictExtendByInitialSheafIso`: (5), `j^{-1} j_! = id`.

## Main result (Stacks 00AA)

* `AlgebraicStructureType.extendByInitialSheaf_full_faithful_and_mem_essImage_iff`: `j_!` is
  fully faithful, and its essential image consists of the sheaves `𝓖` with `𝓖_x` initial for
  every `x ∉ U`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat.Presheaf
  TopCat.Presheaf.ExtensionByInitial Stacks.Topology

universe v u

namespace AlgebraicStructureType

variable (S : AlgebraicStructureType.{v, u}) (X : TopCat.{v})

/-! ### Sheafification of presheaves of algebraic structures -/

/-- The plus construction applied twice to a presheaf of algebraic structures is a sheaf. -/
theorem isSheaf_sheafify (P : TopCat.Presheaf S.C X) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X)
      ((Opens.grothendieckTopology X).sheafify P) :=
  (TopCat.Presheaf.isSheaf_iff_isSheaf_comp S.F _).2 (sheafify_isSheaf00A6 S X P)

/-- The sheafification functor for presheaves of algebraic structures on `X`, `P ↦ P^#`, given
by the plus construction applied twice. -/
@[simps]
noncomputable def sheafifyFunctor :
    ((Opens X)ᵒᵖ ⥤ S.C) ⥤ Sheaf (Opens.grothendieckTopology X) S.C where
  obj P := ⟨(Opens.grothendieckTopology X).sheafify P, S.isSheaf_sheafify X P⟩
  map η := ⟨(Opens.grothendieckTopology X).sheafifyMap η⟩
  map_id P := Sheaf.hom_ext ((Opens.grothendieckTopology X).sheafifyMap_id P)
  map_comp η γ := Sheaf.hom_ext ((Opens.grothendieckTopology X).sheafifyMap_comp η γ)

/-- Sheafification of presheaves of algebraic structures is left adjoint to the inclusion of
sheaves into presheaves: every map from `P` to a sheaf factors uniquely through `P ⟶ P^#`. -/
noncomputable def sheafifyAdjunction :
    S.sheafifyFunctor X ⊣ sheafToPresheaf (Opens.grothendieckTopology X) S.C :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P Q =>
        { toFun := fun e => (Opens.grothendieckTopology X).toSheafify P ≫ e.hom
          invFun := fun e => ⟨(Opens.grothendieckTopology X).sheafifyLift e Q.2⟩
          left_inv := fun _ => Sheaf.hom_ext
            ((Opens.grothendieckTopology X).sheafifyLift_unique _ _ _ rfl).symm
          right_inv := fun _ => (Opens.grothendieckTopology X).toSheafify_sheafifyLift _ _ }
      homEquiv_naturality_left_symm := by
        intro P Q R η γ
        exact Sheaf.hom_ext ((Opens.grothendieckTopology X).sheafifyMap_sheafifyLift _ _ _).symm
      homEquiv_naturality_right := fun η γ => by
        dsimp
        exact (Category.assoc _ _ _).symm }

/-- Sheafification does not change stalks: the map on stalks induced by `P ⟶ P^#` is an
isomorphism. It is checked on underlying sets, where it is the corresponding statement for
presheaves of sets, using that `F` commutes with the plus construction and with stalks, and
reflects isomorphisms. -/
theorem isIso_stalkFunctor_map_toSheafify (P : TopCat.Presheaf S.C X) (x : X) :
    IsIso ((CategoryStalk.stalkFunctor S.C x).map
      ((Opens.grothendieckTopology X).toSheafify P)) := by
  set J := Opens.grothendieckTopology X
  have : HasColimitsOfShape (OpenNhds x)ᵒᵖ S.C :=
    HasFilteredColimitsOfSize.HasColimitsOfShape (OpenNhds x)ᵒᵖ
  set α := Functor.whiskerLeft (OpenNhds.inclusion x).op (J.toSheafify P)
  have hT : IsIso (((Functor.whiskeringRight _ _ _).obj S.F ⋙ colim).map α) := by
    have h1 : Functor.whiskerRight (J.toSheafify P) S.F =
        J.toSheafify (P ⋙ S.F) ≫ (J.sheafifyCompIso S.F P).inv := by
      rw [← J.whiskerRight_toSheafify_sheafifyCompIso_hom, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    have h2 : J.toSheafify (P ⋙ S.F) =
        toSheafify J (P ⋙ S.F) ≫ (plusPlusIsoSheafify J (Type v) (P ⋙ S.F)).inv := by
      rw [← toSheafify_plusPlusIsoSheafify_hom, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    have h3 : IsIso ((TopCat.Presheaf.stalkFunctor (Type v) x).map (toSheafify J (P ⋙ S.F))) :=
      TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (Type v) (P ⋙ S.F)
    change IsIso ((TopCat.Presheaf.stalkFunctor (Type v) x).map
      (Functor.whiskerRight (J.toSheafify P) S.F))
    rw [h1, h2, Functor.map_comp, Functor.map_comp]
    infer_instance
  set e := preservesColimitNatIso (J := (OpenNhds x)ᵒᵖ) S.F
  have hnat := e.hom.naturality α
  have hcomp : IsIso (e.hom.app _ ≫ ((Functor.whiskeringRight _ _ _).obj S.F ⋙ colim).map α) :=
    inferInstance
  rw [← hnat] at hcomp
  have hF : IsIso ((colim ⋙ S.F).map α) := IsIso.of_isIso_comp_right _ (e.hom.app _)
  have : IsIso (S.F.map ((CategoryStalk.stalkFunctor S.C x).map
      (J.toSheafify P))) := hF
  exact isIso_of_reflects_iso _ S.F

/-- The isomorphism of stalks `P_x ≅ (P^#)_x` induced by `P ⟶ P^#`. -/
noncomputable def stalkSheafifyIso (P : TopCat.Presheaf S.C X) (x : X) :
    (CategoryStalk.stalkFunctor S.C x).obj P ≅
      (CategoryStalk.stalkFunctor S.C x).obj ((Opens.grothendieckTopology X).sheafify P) :=
  @asIso _ _ _ _ ((CategoryStalk.stalkFunctor S.C x).map
    ((Opens.grothendieckTopology X).toSheafify P)) (S.isIso_stalkFunctor_map_toSheafify X P x)

/-! ### Extension by the initial object -/

variable [HasInitial S.C] {X} (U : Opens X)

/-- **Stacks 00A6 (1).** On presheaves of algebraic structures, the extension by the initial
object `j_{p!}` is a left adjoint of the restriction functor `j_p`. -/
@[stacks 00A6 "(1) j_{p!} is a left adjoint to the restriction functor j_p"]
noncomputable def extendByInitialAdjunction :
    extendByInitialFunctor (C := S.C) U ⊣ restrictToOpen U :=
  TopCat.Presheaf.extendByInitialAdjunction U

/-- **Stacks 00A6 (4).** On presheaves of algebraic structures on `U`, `j_p j_{p!} = id`. -/
@[stacks 00A6 "(4) on presheaves of algebraic structures on U we have j_p j_{p!} = id"]
noncomputable def restrictExtendByInitialIso :
    extendByInitialFunctor (C := S.C) U ⋙ restrictToOpen U ≅ 𝟭 (TopCat.Presheaf S.C (sp U)) :=
  TopCat.Presheaf.restrictExtendByInitialIso U

/-- **Extension by the initial object of a sheaf of algebraic structures.** For `(C, F)` a type
of algebraic structure such that `C` has an initial object `e`, the extension `j_!𝓕` by `e` of a
sheaf `𝓕` of algebraic structures on `U` is the sheafification of the presheaf `j_{p!}𝓕`, as a
functor `Sh(U, C) ⥤ Sh(X, C)`. The sheafification is `sheafifyFunctor`, the plus construction
applied twice, which exists for every type of algebraic structure, so no sheafification
hypothesis on `C` is made. -/
@[stacks 00A4 "(4)"]
noncomputable def extendByInitialSheaf : TopCat.Sheaf S.C (sp U) ⥤ TopCat.Sheaf S.C X :=
  sheafToPresheaf _ _ ⋙ extendByInitialFunctor U ⋙ S.sheafifyFunctor X

/-- **Stacks 00A6 (2).** `j_!` is a left adjoint of the restriction `j^{-1} : Sh(X, C) ⥤ Sh(U, C)`,
`𝓖 ↦ 𝓖|_U`: `Mor(j_!𝓕, 𝓖) = Mor(𝓕, 𝓖|_U)` bifunctorially in `𝓕` and `𝓖`. -/
@[stacks 00A6 "(2) j_! is a left adjoint to restriction on sheaves, bifunctorially"]
noncomputable def extendByInitialSheafAdjunction :
    S.extendByInitialSheaf U ⊣ Opens.sheafRestrict (C := S.C) U :=
  Adjunction.restrictFullyFaithful
    ((TopCat.Presheaf.extendByInitialAdjunction U).comp (S.sheafifyAdjunction X))
    (fullyFaithfulSheafToPresheaf _ S.C) (Functor.FullyFaithful.id _)
    (Iso.refl _) (Iso.refl _)

/-- The adjoint triple `j_! ⊣ j^{-1} ⊣ j_*` on sheaves of algebraic structures. -/
noncomputable def extendByInitialSheafTriple :
    Adjunction.Triple (S.extendByInitialSheaf U) (Opens.sheafRestrict (C := S.C) U)
      (TopCat.Sheaf.pushforward S.C U.inclusion') :=
  ⟨S.extendByInitialSheafAdjunction U, sheafRestrictPushforwardAdjunction U⟩

/-- The unit of `j_! ⊣ j^{-1}` is invertible, because `j_*` is fully faithful. -/
theorem isIso_unit_extendByInitialSheafAdjunction :
    IsIso (S.extendByInitialSheafAdjunction U).unit := by
  rw [show S.extendByInitialSheafAdjunction U = (S.extendByInitialSheafTriple U).adj₁ from rfl,
    (S.extendByInitialSheafTriple U).isIso_unit_iff_isIso_counit]
  have := (sheafPushforwardFullyFaithful (C := S.C) U).full
  have := (sheafPushforwardFullyFaithful (C := S.C) U).faithful
  exact Adjunction.counit_isIso_of_R_fully_faithful _

/-- **Stacks 00A6 (5).** On sheaves of algebraic structures on `U`, `j^{-1} j_! = id`. -/
@[stacks 00A6 "(5) on sheaves of algebraic structures on U we have j^{-1} j_! = id"]
noncomputable def restrictExtendByInitialSheafIso :
    S.extendByInitialSheaf U ⋙ Opens.sheafRestrict (C := S.C) U ≅ 𝟭 _ :=
  haveI := S.isIso_unit_extendByInitialSheafAdjunction U
  (asIso (S.extendByInitialSheafAdjunction U).unit).symm

/-! ### Stalks of the extension by the initial object -/

/-- The stalk of `j_{p!}𝓕` at a point outside `U` is initial: every open neighbourhood of the
point is not contained in `U`, so the colimit is over initial objects. -/
noncomputable def isInitialStalkExtendByInitial (F : TopCat.Presheaf S.C (sp U)) {x : X}
    (hx : x ∉ U) : IsInitial ((CategoryStalk.stalkFunctor S.C x).obj (extendByInitial U F)) := by
  haveI : HasColimitsOfShape (OpenNhds x)ᵒᵖ S.C :=
    HasFilteredColimitsOfSize.HasColimitsOfShape (OpenNhds x)ᵒᵖ
  have hD : ∀ V : (OpenNhds x)ᵒᵖ,
      IsInitial (((OpenNhds.inclusion x).op ⋙ extendByInitial U F).obj V) := fun V =>
    isInitial_obj U F fun hle => hx (hle V.unop.2)
  change IsInitial (colimit ((OpenNhds.inclusion x).op ⋙ extendByInitial U F))
  exact IsInitial.ofUniqueHom
    (fun Y => colimit.desc _
      { pt := Y
        ι := { app := fun V => (hD V).to Y
               naturality := fun _ _ _ => (hD _).hom_ext _ _ } })
    (fun _ _ => colimit.hom_ext fun V => (hD V).hom_ext _ _)

/-- The stalk of `j_{p!}𝓕` at a point `y ∈ U` is the stalk of `𝓕` at `y`: the open
neighbourhoods of `y` contained in `U` are cofinal, and on them `j_{p!}𝓕` is `𝓕`. -/
noncomputable def stalkExtendByInitialIso (F : TopCat.Presheaf S.C (sp U)) (y : sp U) :
    (CategoryStalk.stalkFunctor S.C y.1).obj (extendByInitial U F) ≅
      (CategoryStalk.stalkFunctor S.C y).obj F := by
  haveI : HasColimitsOfShape (OpenNhds y.1)ᵒᵖ S.C :=
    HasFilteredColimitsOfSize.HasColimitsOfShape (OpenNhds y.1)ᵒᵖ
  haveI : (nhdsLift' X U y.1 y.2).op.Final := Functor.final_op_of_initial _
  exact (Functor.Final.colimitIso (nhdsLift' X U y.1 y.2).op
      ((OpenNhds.inclusion y.1).op ⋙ extendByInitial U F)).symm ≪≫
    (CategoryStalk.stalkFunctor S.C y).mapIso (restrictExtendIso U F)

/-- **Stacks 00A6 (3), points outside `U`.** For a sheaf `𝓕` of algebraic structures on `U`
and `x ∉ U`, the stalk `(j_!𝓕)_x` is the initial object `e`. -/
@[stacks 00A6 "(3) the stalk of j_!F at a point x ∉ U is the initial object e"]
noncomputable def isInitialStalkExtendByInitialSheaf (F : TopCat.Sheaf S.C (sp U)) {x : X}
    (hx : x ∉ U) :
    IsInitial ((CategoryStalk.stalkFunctor S.C x).obj ((S.extendByInitialSheaf U).obj F).obj) :=
  (S.isInitialStalkExtendByInitial U F.obj hx).ofIso (S.stalkSheafifyIso X _ x)

/-- **Stacks 00A6 (3), points of `U`.** For a sheaf `𝓕` of algebraic structures on `U` and
`x ∈ U`, the stalk `(j_!𝓕)_x` is the stalk `𝓕_x`. -/
@[stacks 00A6 "(3) the stalk of j_!F at a point x ∈ U is the stalk F_x"]
noncomputable def stalkExtendByInitialSheafIso (F : TopCat.Sheaf S.C (sp U)) {x : X}
    (hx : x ∈ U) :
    (CategoryStalk.stalkFunctor S.C x).obj ((S.extendByInitialSheaf U).obj F).obj ≅
      (CategoryStalk.stalkFunctor S.C (⟨x, hx⟩ : sp U)).obj F.obj :=
  (S.stalkSheafifyIso X _ x).symm ≪≫ S.stalkExtendByInitialIso U F.obj ⟨x, hx⟩

/-! ### Stacks 00AA: `j_!` is fully faithful, and its essential image -/

/-- The counit `j_! j^{-1} 𝓖 ⟶ 𝓖` of `j_! ⊣ j^{-1}` is an isomorphism on the sections over
every open `V ⊆ U`: by a triangle identity its restriction to `U` is inverse to the unit at
`j^{-1} 𝓖`, which is invertible. -/
private lemma isIso_counit_app_hom_app_of_le (G : TopCat.Sheaf S.C X) {V : Opens X}
    (hV : V ≤ U) :
    IsIso (((S.extendByInitialSheafAdjunction U).counit.app G).hom.app (op V)) := by
  have := S.isIso_unit_extendByInitialSheafAdjunction U
  have hu := NatIso.isIso_app_of_isIso (S.extendByInitialSheafAdjunction U).unit
    ((Opens.sheafRestrict U).obj G)
  have hR : IsIso ((Opens.sheafRestrict U).map
      ((S.extendByInitialSheafAdjunction U).counit.app G)) :=
    @isIso_of_hom_comp_eq_id _ _ _ _ _ hu _
      ((S.extendByInitialSheafAdjunction U).right_triangle_components G)
  have h : IsIso (((S.extendByInitialSheafAdjunction U).counit.app G).hom.app
      (op ((imF U).obj ((Opens.map U.inclusion').obj V)))) :=
    NatIso.isIso_app_of_isIso ((sheafToPresheaf _ _).map
      ((Opens.sheafRestrict U).map ((S.extendByInitialSheafAdjunction U).counit.app G)))
      (op ((Opens.map U.inclusion').obj V))
  rwa [imF_map_eq hV] at h

omit [HasInitial S.C] in
/-- A morphism of presheaves of algebraic structures that is an isomorphism on the stalk at
`x` (Stacks 007H) is an isomorphism on the stalk at `x` of the underlying presheaves of sets,
since `F` commutes with the filtered colimit defining the stalk. -/
private lemma isIso_stalkFunctor_map_whiskerRight {P Q : TopCat.Presheaf S.C X} (f : P ⟶ Q)
    (x : X) [IsIso ((CategoryStalk.stalkFunctor S.C x).map f)] :
    IsIso ((TopCat.Presheaf.stalkFunctor (Type v) x).map (Functor.whiskerRight f S.F)) := by
  have : HasColimitsOfShape (OpenNhds x)ᵒᵖ S.C :=
    HasFilteredColimitsOfSize.HasColimitsOfShape (OpenNhds x)ᵒᵖ
  set α := Functor.whiskerLeft (OpenNhds.inclusion x).op f
  set e := preservesColimitNatIso (J := (OpenNhds x)ᵒᵖ) S.F
  have hnat := e.hom.naturality α
  have h1 : IsIso ((colim ⋙ S.F).map α) :=
    inferInstanceAs (IsIso (S.F.map ((CategoryStalk.stalkFunctor S.C x).map f)))
  have h2 : IsIso (e.hom.app _ ≫ ((Functor.whiskeringRight _ _ _).obj S.F ⋙ colim).map α) := by
    rw [← hnat]
    infer_instance
  exact IsIso.of_isIso_comp_left (e.hom.app _)
    (((Functor.whiskeringRight _ _ _).obj S.F ⋙ colim).map α)

omit [HasInitial S.C] in
/-- A morphism of sheaves of algebraic structures is an isomorphism as soon as it induces
isomorphisms on all stalks of the underlying sheaves of sets: those are then isomorphic as
sheaves of sets, and `F` reflects isomorphisms. -/
private lemma isIso_of_isIso_stalkFunctor_map_whiskerRight {P Q : TopCat.Sheaf S.C X}
    (f : P ⟶ Q)
    (h : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor (Type v) x).map
      (Functor.whiskerRight f.hom S.F))) :
    IsIso f := by
  let J := Opens.grothendieckTopology X
  let PF : Sheaf J (Type v) :=
    ⟨P.obj ⋙ S.F, GrothendieckTopology.HasSheafCompose.isSheaf P.obj P.property⟩
  let QF : Sheaf J (Type v) :=
    ⟨Q.obj ⋙ S.F, GrothendieckTopology.HasSheafCompose.isSheaf Q.obj Q.property⟩
  let fF : PF ⟶ QF := ObjectProperty.homMk (Functor.whiskerRight f.hom S.F)
  have hfF_stalk : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor (Type v) x).map fF.hom) := h
  have hfF_iso : IsIso fF := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso fF
  have hfF_hom_iso : IsIso fF.hom := inferInstance
  refine (ObjectProperty.isIso_hom_iff f).mp ?_
  rw [NatTrans.isIso_iff_isIso_app]
  intro V
  have : IsIso (S.F.map (f.hom.app V)) := (NatTrans.isIso_iff_isIso_app fF.hom).mp hfF_hom_iso V
  exact isIso_of_reflects_iso _ S.F

/-- A sheaf `𝓖` of algebraic structures on `X` whose stalks at the points outside `U` are
initial is recovered from its restriction to `U`: the counit `j_! j^{-1} 𝓖 ⟶ 𝓖` is an
isomorphism. It is checked on the stalks of underlying sets: at `x ∈ U` the counit is an
isomorphism over every open contained in `U`, and at `x ∉ U` both stalks are initial. -/
private lemma isIso_counit_app_of_isInitial_stalk (G : TopCat.Sheaf S.C X)
    (hG : ∀ x : X, x ∉ U → Nonempty (IsInitial ((CategoryStalk.stalkFunctor S.C x).obj G.obj))) :
    IsIso ((S.extendByInitialSheafAdjunction U).counit.app G) := by
  set φ := (S.extendByInitialSheafAdjunction U).counit.app G
  apply S.isIso_of_isIso_stalkFunctor_map_whiskerRight φ
  intro x
  by_cases hx : x ∈ U
  · rw [isIso_iff_bijective]
    refine bijective_stalkFunctor_map_of_bijective_app_of_le _ (fun V hV ↦ ?_) hx
    have := S.isIso_counit_app_hom_app_of_le U G hV
    exact (isIso_iff_bijective _).1 (inferInstanceAs (IsIso (S.F.map (φ.hom.app (op V)))))
  · have hA := S.isInitialStalkExtendByInitialSheaf U ((Opens.sheafRestrict U).obj G) hx
    have : IsIso ((CategoryStalk.stalkFunctor S.C x).map φ.hom) :=
      isIso_of_isInitial hA (hG x hx).some _
    exact S.isIso_stalkFunctor_map_whiskerRight φ.hom x

/-- **Stacks 00AA.** Let `X` be a topological space, `j : U → X` the inclusion of an open
subset, and `(C, F)` a type of algebraic structure (Stacks 007L) such that `C` has an initial
object `e`. Then `j_! : Sh(U, C) ⥤ Sh(X, C)` is fully faithful, and its essential image
consists exactly of the sheaves `𝓖` with `𝓖_x = e` (that is, `𝓖_x` initial) for all
`x ∈ X ∖ U`.

The homs of `C` live in the universe of `X` and its objects in any universe, so `C` may be
`Type v`, `Ab.{v}`, `CommRingCat.{v}`, …; nothing beyond 007L and the initial object is
assumed. `j_!` is `extendByInitialSheaf`, the sheafification of the source's `j_{p!}`, and
the stalk is the filtered colimit of Stacks 007H. -/
@[stacks 00AA]
theorem extendByInitialSheaf_full_faithful_and_mem_essImage_iff :
    (S.extendByInitialSheaf U).Full ∧ (S.extendByInitialSheaf U).Faithful ∧
      ∀ G : TopCat.Sheaf S.C X, (S.extendByInitialSheaf U).essImage G ↔
        ∀ x : X, x ∉ U →
          Nonempty (IsInitial ((CategoryStalk.stalkFunctor S.C x).obj G.obj)) := by
  have := S.isIso_unit_extendByInitialSheafAdjunction U
  have hff := (S.extendByInitialSheafAdjunction U).fullyFaithfulLOfIsIsoUnit
  refine ⟨hff.full, hff.faithful, fun G ↦ ⟨?_, fun hG ↦ ?_⟩⟩
  · rintro ⟨F, ⟨e⟩⟩ x hx
    exact ⟨(S.isInitialStalkExtendByInitialSheaf U F hx).ofIso
      ((CategoryStalk.stalkFunctor S.C x).mapIso ((sheafToPresheaf _ _).mapIso e))⟩
  · have := S.isIso_counit_app_of_isInitial_stalk U G hG
    exact (S.extendByInitialSheafAdjunction U).mem_essImage_of_counit_isIso G

end AlgebraicStructureType
