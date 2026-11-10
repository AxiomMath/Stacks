module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RingedCrystallineTopos

/-!
# The structure morphism `τ_{X/S}` as a morphism of ringed topoi

Fix a global crystalline situation `(p, (S, I, γ), X)`.  The structure morphism of topoi
`τ_{X/S} : (X/S)_cris ⟶ Sh(S_Zar)` of [Stacks, Tag 07IM] is
`Crystalline.GlobalCrystallineSituation.structureToposMorphism`.  This file makes it a morphism of
ringed topoi

`τ_{X/S} : ((X/S)_cris, 𝒪_{X/S}) ⟶ (Sh(S_Zar), 𝒪_S)`,

which is the form in which it enters the base change map of [Stacks, Tag 07MS]: the structure map

`τ^♯ : 𝒪_S ⟶ τ_{X/S, *}𝒪_{X/S}`

sends a function `a` on an open `V` of `S` to the family of its pullbacks `(T ⟶ S)^* a` along the
structure morphisms of the objects `(U, T, δ)` of `Cris(X/S)` lying over `V`.

The sections of `τ_{X/S, *}F` over `V` are the sections of `u_{X/S, *}F` over the open `X_V` of
`X` above `V`, and those are the limit of the sections of `F` over the objects `(U, T, δ)` of
`Cris(X/S)` with `U ⊆ X_V`: `u_{X/S, *}` is the right Kan extension along the forgetful functor
`Cris(X/S) ⥤ X_Zar`, [Stacks, Tag 07IL], and that Kan extension is pointwise.  For such an object
the morphism `T ⟶ S` lands in `V`, so a function on `V` pulls back to a global function on `T`.

## Main definitions

* `structureIndexPullback` — the pullback `Γ(S, V) ⟶ Γ(T, 𝒪_T)` along `T ⟶ S`, and
  `structureIndexPullbackSet` the same map on underlying sets, after the universe lift.
* `structureProjection` — the projection of the sections of `τ_{X/S, *}F` over `V` to the
  sections of `F` over an object `(U, T, δ)` above `V`, natural in `F`.
* `structureSharpApp` — `τ^♯` on sections over `V`, and `structureSharpRing` — `τ^♯` as a
  morphism of sheaves of rings.
* `structureRingedHom` — **`τ_{X/S}` as a morphism of ringed topoi**, with underlying morphism of
  topoi `structureToposMorphism S`.

## Main results

* `structureProjection_ext` — a section of `τ_{X/S, *}F` is determined by its projections.
* `structureProjection_structureSharpApp`, `structureRingedHom_forgetFSharp_proj` and
  `structureRingedHom_forgetFSharp_chain` — the projections of `τ^♯ a` are the pullbacks
  `(T ⟶ S)^* a`; with `structureProjection_ext` this characterizes `τ^♯` completely.

## References

* [Stacks Project, Tag 07IM](https://stacks.math.columbia.edu/tag/07IM)
* [Stacks Project, Tag 07IL](https://stacks.math.columbia.edu/tag/07IL)
* [Stacks Project, Tag 07MS](https://stacks.math.columbia.edu/tag/07MS)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf AlgebraicGeometry
  TopologicalSpace Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-! ### The objects of `Cris(X/S)` above an open of `S` -/

/-- The index category of the limit computing the sections of `τ_{X/S, *}F` over an open `V` of
`S`: the objects `(U, T, δ)` of `Cris(X/S)` together with an inclusion of `U` into the open `X_V`
of `X` above `V`. -/
abbrev StructureIndex (V : S.S.scheme.Opens) :=
  StructuredArrow (op (sourceToBase S ⁻¹ᵁ V)) (forgetToOpens S).op

variable {S} in
/-- **For an object `(U, T, δ)` of `Cris(X/S)` with `U` above an open `V` of `S`, the structure
morphism `T ⟶ S` lands in `V`.** -/
theorem top_le_toBase_preimage {V : S.S.scheme.Opens} {A : CrystallineThickening S}
    (h : (forgetToOpens S).obj A ≤ sourceToBase S ⁻¹ᵁ V) :
    (⊤ : A.obj.thickening.target.scheme.Opens) ≤ A.obj.toBase.hom ⁻¹ᵁ V := by
  intro t _
  have hi : Stacks.Thickenings.IsThickening A.obj.thickening.immersion :=
    A.obj.thickening.isThickening
  obtain ⟨x, rfl⟩ : ∃ x, A.obj.thickening.immersion x = t :=
    ⟨hi.homeomorph.symm t, hi.homeomorph.apply_symm_apply t⟩
  have hx : A.obj.toX x ∈ sourceToBase S ⁻¹ᵁ V := h ⟨x, rfl⟩
  have hb := congrArg (fun f ↦ f x) A.obj.over_base
  change A.obj.toBase.hom (A.obj.thickening.immersion x) = sourceToBase S (A.obj.toX x) at hb
  change A.obj.toBase.hom (A.obj.thickening.immersion x) ∈ V
  rw [hb]
  exact hx

/-- The pullback `(T ⟶ S)^* : Γ(S, V) ⟶ Γ(T, 𝒪_T)` of functions on an open `V` of `S` along the
structure morphism of an object `(U, T, δ)` of `Cris(X/S)` above `V`. -/
def structureIndexPullback (V : S.S.scheme.Opens) (j : StructureIndex S V) :
    Γ(S.S.scheme, V) ⟶ Γ(j.right.unop.obj.thickening.target.scheme, ⊤) :=
  j.right.unop.obj.toBase.hom.appLE V ⊤ (top_le_toBase_preimage (leOfHom j.hom.unop))

/-- Pullback of functions is compatible with the morphisms of objects above `V`. -/
theorem structureIndexPullback_comp (V : S.S.scheme.Opens) {j₁ j₂ : StructureIndex S V}
    (m : j₁ ⟶ j₂) :
    structureIndexPullback S V j₂ =
      structureIndexPullback S V j₁ ≫ m.right.unop.hom.targetHom.hom.appTop := by
  have key : ∀ {f₁ f₂ : j₂.right.unop.obj.thickening.target.scheme ⟶ S.S.scheme}
      (_ : f₁ = f₂) (e₁ : (⊤ : j₂.right.unop.obj.thickening.target.scheme.Opens) ≤ f₁ ⁻¹ᵁ V)
      (e₂ : (⊤ : j₂.right.unop.obj.thickening.target.scheme.Opens) ≤ f₂ ⁻¹ᵁ V),
      f₁.appLE V ⊤ e₁ = f₂.appLE V ⊤ e₂ := by
    rintro _ _ rfl _ _
    rfl
  have hc := Scheme.Hom.appLE_comp_appLE m.right.unop.hom.targetHom.hom
    j₁.right.unop.obj.toBase.hom V ⊤ (m.right.unop.hom.targetHom.hom ⁻¹ᵁ ⊤)
    (top_le_toBase_preimage (leOfHom j₁.hom.unop)) le_rfl
  rw [Scheme.Hom.appLE_eq_app] at hc
  refine (key ?_ _ _).trans hc.symm
  rw [← DividedPowerScheme.Hom.comp_hom, m.right.unop.hom.base_naturality]

/-- Pullback of functions along a restriction of opens of `S`. -/
theorem structureIndexPullback_map {V₁ V₂ : S.S.scheme.Opens} (i : op V₁ ⟶ op V₂)
    (j : StructureIndex S V₂) :
    structureIndexPullback S V₁
        (StructuredArrow.mk (((Opens.map (sourceToBase S).base).map i.unop).op ≫ j.hom)) =
      S.S.scheme.presheaf.map i ≫ structureIndexPullback S V₂ j := by
  rw [structureIndexPullback, structureIndexPullback, Scheme.Hom.map_appLE]
  rfl

/-! ### The sections of `τ_{X/S, *}F` as a limit -/

/-- The sheaf of rings underlying `𝒪_{X/S}` on the crystalline ringed topos. -/
abbrev crisRingSheaf : Sheaf (smallTopology S) RingCat.{u + 1} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (crisRingedTopos S).J))
    (crisRingedTopos S).O

/-- The sheaf of rings underlying `𝒪_S` on the Zariski ringed topos of `S`. -/
abbrev baseRingSheaf : Sheaf (Opens.grothendieckTopology S.S.scheme.carrier) RingCat.{u + 1} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u + 1} (J := (zariskiRingedTopos S.S.scheme).J))
    (zariskiRingedTopos S.S.scheme).O

/-- The sections over an open `V` of `S` of the direct image along `τ_{X/S}`, as a functor of the
sheaf on `Cris(X/S)`. -/
abbrev structureSections (V : S.S.scheme.Opens) :
    Sheaf (smallTopology S) (Type (u + 1)) ⥤ Type (u + 1) :=
  (structureToposMorphism S).pushforward ⋙
    sectionsFunctor (Opens.grothendieckTopology S.S.scheme.carrier) (op V)

/-- The projection of the sections of `τ_{X/S, *}F` over an open `V` of `S` to the sections of
`F` over an object `(U, T, δ)` of `Cris(X/S)` above `V`, natural in `F`: restriction along
`U ⊆ X_V` followed by the counit of the right Kan extension along `Cris(X/S) ⥤ X_Zar`. -/
def structureProjection (V : S.S.scheme.Opens) (j : StructureIndex S V) :
    structureSections S V ⟶ sectionsFunctor (smallTopology S) j.right where
  app F := TypeCat.ofHom fun x ↦
    ((Functor.RightExtension.mk _ ((forgetToOpens S).op.ranCounit.app F.obj)).coneAt
      (op (sourceToBase S ⁻¹ᵁ V))).π.app j x
  naturality F G m := by
    ext x
    change ((forgetToOpens S).op.ranCounit.app G.obj).app j.right
        (((forgetToOpens S).op.ran.obj G.obj).map j.hom
          ((((forgetToOpens S).op.ran.map m.hom).app (op (sourceToBase S ⁻¹ᵁ V))) x)) =
      m.hom.app j.right (((forgetToOpens S).op.ranCounit.app F.obj).app j.right
        (((forgetToOpens S).op.ran.obj F.obj).map j.hom x))
    rw [← NatTrans.naturality_apply ((forgetToOpens S).op.ran.map m.hom) j.hom x]
    exact congrArg (fun φ ↦ φ.app j.right (((forgetToOpens S).op.ran.obj F.obj).map j.hom x))
      ((forgetToOpens S).op.ranCounit.naturality m.hom)

/-- The projection is the projection of the limit cone of the pointwise right Kan extension. -/
theorem structureProjection_app_apply (V : S.S.scheme.Opens) (j : StructureIndex S V)
    (F : Sheaf (smallTopology S) (Type (u + 1))) (x : (structureSections S V).obj F) :
    (structureProjection S V j).app F x =
      ((Functor.RightExtension.mk _ ((forgetToOpens S).op.ranCounit.app F.obj)).coneAt
        (op (sourceToBase S ⁻¹ᵁ V))).π.app j x :=
  rfl

/-- **A section of `τ_{X/S, *}F` over `V` is determined by its projections** to the objects of
`Cris(X/S)` above `V`: the sections are the limit over those objects. -/
theorem structureProjection_ext (V : S.S.scheme.Opens)
    (F : Sheaf (smallTopology S) (Type (u + 1))) {a b : (structureSections S V).obj F}
    (h : ∀ j, (structureProjection S V j).app F a = (structureProjection S V j).app F b) :
    a = b := by
  refine (Types.isLimitEquivSections ((forgetToOpens S).op.isPointwiseRightKanExtensionRanCounit
    F.obj (op (sourceToBase S ⁻¹ᵁ V)))).injective (Subtype.ext (funext fun j ↦ ?_))
  exact h j

/-- Restricting a section of `τ_{X/S, *}F` along an inclusion of opens of `S` and projecting is
projecting to the same object, seen above the larger open. -/
theorem structureProjection_map {V₁ V₂ : S.S.scheme.Opens} (i : op V₁ ⟶ op V₂)
    (j : StructureIndex S V₂) (F : Sheaf (smallTopology S) (Type (u + 1)))
    (a : (structureSections S V₁).obj F) :
    (structureProjection S V₂ j).app F
        (((structureToposMorphism S).pushforward.obj F).obj.map i a) =
      (structureProjection S V₁
        (StructuredArrow.mk (((Opens.map (sourceToBase S).base).map i.unop).op ≫ j.hom))).app
        F a := by
  change ((forgetToOpens S).op.ranCounit.app F.obj).app j.right
      (((forgetToOpens S).op.ran.obj F.obj).map j.hom
        (((forgetToOpens S).op.ran.obj F.obj).map
          (((Opens.map (sourceToBase S).base).map i.unop).op) a)) =
    ((forgetToOpens S).op.ranCounit.app F.obj).app j.right
      (((forgetToOpens S).op.ran.obj F.obj).map
        ((((Opens.map (sourceToBase S).base).map i.unop).op ≫ j.hom)) a)
  exact congrArg (fun y ↦ ((forgetToOpens S).op.ranCounit.app F.obj).app j.right y)
    (((forgetToOpens S).op.ran.obj F.obj).map_comp_apply _ j.hom a).symm

/-! ### The structure map on sections -/

/-- The pullback `(T ⟶ S)^*` from the sections of `𝒪_S` over `V` to the sections of `𝒪_{X/S}`
over an object `(U, T, δ)` above `V`, both raised to the universe `u + 1`, on underlying sets. -/
def structureIndexPullbackSet (V : S.S.scheme.Opens) (j : StructureIndex S V) :
    (sectionsFunctor _ (op V)).obj (Sheaf.ringSheaf (baseRingSheaf S)) ⟶
      (sectionsFunctor _ j.right).obj (Sheaf.ringSheaf (crisRingSheaf S)) :=
  (CategoryTheory.forget CommRingCat.{u + 1}).map
    (SheafOfModules.commRingCatULift.{u, u + 1}.map (structureIndexPullback S V j))

/-- The pullback on a section: `(T ⟶ S)^*` under the universe lift. -/
theorem structureIndexPullbackSet_apply (V : S.S.scheme.Opens) (j : StructureIndex S V)
    (a : (sectionsFunctor _ (op V)).obj (Sheaf.ringSheaf (baseRingSheaf S))) :
    structureIndexPullbackSet S V j a =
      ULift.up.{u + 1, u} ((structureIndexPullback S V j).hom (ULift.down.{u + 1, u} a)) :=
  rfl

/-- The pullback is additive. -/
theorem structureIndexPullbackSet_add (V : S.S.scheme.Opens) (j : StructureIndex S V)
    (x y : (sectionsFunctor _ (op V)).obj (Sheaf.ringSheaf (baseRingSheaf S))) :
    structureIndexPullbackSet S V j (x + y) =
      structureIndexPullbackSet S V j x + structureIndexPullbackSet S V j y :=
  congrArg ULift.up.{u + 1, u}
    ((structureIndexPullback S V j).hom.map_add (ULift.down.{u + 1, u} x) (ULift.down y))

/-- The pullback is multiplicative. -/
theorem structureIndexPullbackSet_mul (V : S.S.scheme.Opens) (j : StructureIndex S V)
    (x y : (sectionsFunctor _ (op V)).obj (Sheaf.ringSheaf (baseRingSheaf S))) :
    structureIndexPullbackSet S V j (x * y) =
      structureIndexPullbackSet S V j x * structureIndexPullbackSet S V j y :=
  congrArg ULift.up.{u + 1, u}
    ((structureIndexPullback S V j).hom.map_mul (ULift.down.{u + 1, u} x) (ULift.down y))

/-- The pullback preserves zero. -/
theorem structureIndexPullbackSet_zero (V : S.S.scheme.Opens) (j : StructureIndex S V) :
    structureIndexPullbackSet S V j 0 = 0 :=
  congrArg ULift.up.{u + 1, u} (structureIndexPullback S V j).hom.map_zero

/-- The pullback preserves one. -/
theorem structureIndexPullbackSet_one (V : S.S.scheme.Opens) (j : StructureIndex S V) :
    structureIndexPullbackSet S V j 1 = 1 :=
  congrArg ULift.up.{u + 1, u} (structureIndexPullback S V j).hom.map_one

/-- The cone of pullbacks of a function on `V` to the objects of `Cris(X/S)` above `V`. -/
def structureIndexPullbackCone (V : S.S.scheme.Opens) :
    Cone (StructuredArrow.proj (op (sourceToBase S ⁻¹ᵁ V)) (forgetToOpens S).op ⋙
      (Sheaf.ringSheaf (crisRingSheaf S)).obj) where
  pt := (sectionsFunctor _ (op V)).obj (Sheaf.ringSheaf (baseRingSheaf S))
  π :=
    { app := fun j ↦ structureIndexPullbackSet S V j
      naturality := fun j₁ j₂ m ↦ by
        refine (Category.id_comp _).trans ?_
        change (CategoryTheory.forget CommRingCat.{u + 1}).map
            (SheafOfModules.commRingCatULift.{u, u + 1}.map (structureIndexPullback S V j₂)) =
          (CategoryTheory.forget CommRingCat.{u + 1}).map
              (SheafOfModules.commRingCatULift.{u, u + 1}.map (structureIndexPullback S V j₁)) ≫
            (CategoryTheory.forget CommRingCat.{u + 1}).map
              (SheafOfModules.commRingCatULift.{u, u + 1}.map
                m.right.unop.hom.targetHom.hom.appTop)
        rw [structureIndexPullback_comp S V m, Functor.map_comp, Functor.map_comp] }

/-- **The structure map `τ^♯` on sections over an open `V` of `S`**: a function on `V` is sent to
the family of its pullbacks to the objects `(U, T, δ)` of `Cris(X/S)` above `V`. -/
def structureSharpApp (V : S.S.scheme.Opens) :
    (sectionsFunctor _ (op V)).obj (Sheaf.ringSheaf (baseRingSheaf S)) ⟶
      (structureSections S V).obj (Sheaf.ringSheaf (crisRingSheaf S)) :=
  ((forgetToOpens S).op.isPointwiseRightKanExtensionRanCounit
    (Sheaf.ringSheaf (crisRingSheaf S)).obj (op (sourceToBase S ⁻¹ᵁ V))).lift
    (structureIndexPullbackCone S V)

/-- **The projections of `τ^♯ a` are the pullbacks `(T ⟶ S)^* a`.** -/
theorem structureProjection_structureSharpApp (V : S.S.scheme.Opens) (j : StructureIndex S V)
    (a : (sectionsFunctor _ (op V)).obj (Sheaf.ringSheaf (baseRingSheaf S))) :
    (structureProjection S V j).app _ (structureSharpApp S V a) =
      structureIndexPullbackSet S V j a :=
  congrArg (fun φ ↦ φ a)
    (((forgetToOpens S).op.isPointwiseRightKanExtensionRanCounit
      (Sheaf.ringSheaf (crisRingSheaf S)).obj (op (sourceToBase S ⁻¹ᵁ V))).fac
      (structureIndexPullbackCone S V) j)

/-- A section of `τ_{X/S, *}𝒪_{X/S}` is `τ^♯ a` once its projections are the pullbacks of `a`. -/
private theorem structureSharpApp_eq_of_pullbackSet_eq (V : S.S.scheme.Opens)
    (a : (sectionsFunctor _ (op V)).obj (Sheaf.ringSheaf (baseRingSheaf S)))
    (b : (structureSections S V).obj (Sheaf.ringSheaf (crisRingSheaf S)))
    (h : ∀ j, structureIndexPullbackSet S V j a = (structureProjection S V j).app _ b) :
    structureSharpApp S V a = b :=
  structureProjection_ext S V _ fun j ↦ (structureProjection_structureSharpApp S V j a).trans (h j)

/-- The structure map on sections is additive for the transported addition. -/
theorem structureSharpApp_add (V : S.S.scheme.Opens)
    (x y : (sectionsFunctor _ (op V)).obj (Sheaf.ringSheaf (baseRingSheaf S))) :
    structureSharpApp S V (x + y) =
      ringAddObj (crisRingSheaf S) (structureSections S V)
        (structureSharpApp S V x) (structureSharpApp S V y) := by
  refine structureSharpApp_eq_of_pullbackSet_eq S V _ _ (fun j ↦ ?_)
  refine (structureIndexPullbackSet_add S V j x y).trans ?_
  refine (congrArg₂ (· + ·) (structureProjection_structureSharpApp S V j x).symm
    (structureProjection_structureSharpApp S V j y).symm).trans ?_
  exact (sectionsFunctor_map_ringAddHom (crisRingSheaf S) j.right _ _).symm.trans
    (ringAddObj_naturality (crisRingSheaf S) (structureProjection S V j) _ _).symm

/-- The structure map on sections is multiplicative for the transported multiplication. -/
theorem structureSharpApp_mul (V : S.S.scheme.Opens)
    (x y : (sectionsFunctor _ (op V)).obj (Sheaf.ringSheaf (baseRingSheaf S))) :
    structureSharpApp S V (x * y) =
      ringMulObj (crisRingSheaf S) (structureSections S V)
        (structureSharpApp S V x) (structureSharpApp S V y) := by
  refine structureSharpApp_eq_of_pullbackSet_eq S V _ _ (fun j ↦ ?_)
  refine (structureIndexPullbackSet_mul S V j x y).trans ?_
  refine (congrArg₂ (· * ·) (structureProjection_structureSharpApp S V j x).symm
    (structureProjection_structureSharpApp S V j y).symm).trans ?_
  exact (sectionsFunctor_map_ringMulHom (crisRingSheaf S) j.right _ _).symm.trans
    (ringMulObj_naturality (crisRingSheaf S) (structureProjection S V j) _ _).symm

/-- The structure map on sections preserves the zero section. -/
theorem structureSharpApp_zero (V : S.S.scheme.Opens) :
    structureSharpApp S V 0 = ringZeroObj (crisRingSheaf S) (structureSections S V) := by
  refine structureSharpApp_eq_of_pullbackSet_eq S V _ _ (fun j ↦ ?_)
  refine (structureIndexPullbackSet_zero S V j).trans ?_
  exact (sectionsFunctor_map_ringZeroHom (crisRingSheaf S) j.right _).symm.trans
    (ringZeroObj_naturality (crisRingSheaf S) (structureProjection S V j)).symm

/-- The structure map on sections preserves the unit section. -/
theorem structureSharpApp_one (V : S.S.scheme.Opens) :
    structureSharpApp S V 1 = ringOneObj (crisRingSheaf S) (structureSections S V) := by
  refine structureSharpApp_eq_of_pullbackSet_eq S V _ _ (fun j ↦ ?_)
  refine (structureIndexPullbackSet_one S V j).trans ?_
  exact (sectionsFunctor_map_ringOneHom (crisRingSheaf S) j.right _).symm.trans
    (ringOneObj_naturality (crisRingSheaf S) (structureProjection S V j)).symm

/-- The structure map on sections is natural in the open of `S`. -/
theorem structureSharpApp_naturality {V₁ V₂ : S.S.scheme.Opens} (i : op V₁ ⟶ op V₂)
    (x : (sectionsFunctor _ (op V₁)).obj (Sheaf.ringSheaf (baseRingSheaf S))) :
    structureSharpApp S V₂ ((Sheaf.ringSheaf (baseRingSheaf S)).obj.map i x) =
      (((structureToposMorphism S).pushforward.obj
        (Sheaf.ringSheaf (crisRingSheaf S))).obj.map i (structureSharpApp S V₁ x)) := by
  refine structureSharpApp_eq_of_pullbackSet_eq S V₂ _ _ (fun j ↦ ?_)
  rw [structureProjection_map, structureProjection_structureSharpApp]
  exact (congrArg (fun φ ↦ ULift.up.{u + 1, u} (φ.hom (ULift.down.{u + 1, u} x)))
    (structureIndexPullback_map S i j)).symm

/-! ### The morphism of ringed topoi -/

/-- **The structure map `τ^♯ : 𝒪_S ⟶ τ_{X/S, *}𝒪_{X/S}`** as a morphism of sheaves of rings on
`S_Zar`, the direct image being that of sheaves of rings along `τ_{X/S}`: on an open `V` it sends
a function to the family of its pullbacks to the objects `(U, T, δ)` of `Cris(X/S)` above `V`. -/
def structureSharpRing :
    baseRingSheaf S ⟶
      pullbackRingSheaf (Opens.grothendieckTopology S.S.scheme.carrier)
        (structureToposMorphism S).pushforward (crisRingSheaf S) where
  hom :=
    { app := fun V ↦
        letI := ringObjRing (crisRingSheaf S) (structureSections S V.unop)
        RingCat.ofHom
        { toFun := structureSharpApp S V.unop
          map_add' := structureSharpApp_add S V.unop
          map_mul' := structureSharpApp_mul S V.unop
          map_zero' := structureSharpApp_zero S V.unop
          map_one' := structureSharpApp_one S V.unop }
      naturality := fun _ _ i ↦ by
        refine RingCat.hom_ext (RingHom.ext fun x ↦ ?_)
        exact structureSharpApp_naturality S i x }

/-- **Stacks Project, Tag 07IM, as a morphism of ringed topoi.**  The structure morphism
`τ_{X/S} : ((X/S)_cris, 𝒪_{X/S}) ⟶ (Sh(S_Zar), 𝒪_S)`: the morphism of topoi
`structureToposMorphism S`, with structure map `τ^♯ : 𝒪_S ⟶ τ_{X/S, *}𝒪_{X/S}` sending a function
on an open `V` of `S` to the family of its pullbacks along the morphisms `T ⟶ S` of the objects
`(U, T, δ)` of `Cris(X/S)` above `V` (`structureRingedHom_forgetFSharp_proj`). -/
def structureRingedHom : RingedToposHom (crisRingedTopos S) (zariskiRingedTopos S.S.scheme) where
  toToposHom := structureToposMorphism S
  fSharp := (fullyFaithfulForgetCommRingSheaf.{u + 1, u, u}
    (Opens.grothendieckTopology S.S.scheme.carrier)).preimage (structureSharpRing S)

/-- The morphism of topoi underlying `τ_{X/S}` as a morphism of ringed topoi is
`structureToposMorphism S`. -/
@[simp]
theorem structureRingedHom_toToposHom :
    (structureRingedHom S).toToposHom = structureToposMorphism S :=
  rfl

/-- The structure map of `structureRingedHom S` on underlying sheaves of rings is
`structureSharpRing S`. -/
theorem forgetCommRingSheaf_map_structureRingedHom_fSharp :
    (sheafCompose (Opens.grothendieckTopology S.S.scheme.carrier)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (structureRingedHom S).fSharp =
      structureSharpRing S :=
  (fullyFaithfulForgetCommRingSheaf.{u + 1, u, u}
    (Opens.grothendieckTopology S.S.scheme.carrier)).map_preimage _

/-- The structure map of `structureRingedHom S` on underlying sheaves of sets, at an open `V` of
`S`, is `structureSharpApp S V`. -/
theorem structureRingedHom_forgetFSharp_app (V : S.S.scheme.Opens)
    (a : ToType ((zariskiRingedTopos S.S.scheme).O.obj.obj (op V))) :
    (RingedToposHom.forgetFSharp (structureRingedHom S)).hom.app (op V) a =
      structureSharpApp S V a :=
  congrArg (fun φ : baseRingSheaf S ⟶ _ ↦ φ.hom.app (op V) a)
    (forgetCommRingSheaf_map_structureRingedHom_fSharp S)

/-- **The structure map of `τ_{X/S}` on sections.**  For a function `a` on an open `V` of `S`, the
section `τ^♯ a` of `τ_{X/S, *}𝒪_{X/S}` over `V` is the compatible family of the pullbacks
`(T ⟶ S)^* a`, one for each object `(U, T, δ)` of `Cris(X/S)` above `V`, under the projections of
the limit computing the sections of the right Kan extension. -/
theorem structureRingedHom_forgetFSharp_proj (V : S.S.scheme.Opens)
    (a : ToType ((zariskiRingedTopos S.S.scheme).O.obj.obj (op V))) (j : StructureIndex S V) :
    ((Functor.RightExtension.mk _ ((forgetToOpens S).op.ranCounit.app
        ((crisRingedTopos S).forgetRing.obj (crisRingedTopos S).O).obj)).coneAt
        (op (sourceToBase S ⁻¹ᵁ V))).π.app j
        ((RingedToposHom.forgetFSharp (structureRingedHom S)).hom.app (op V) a) =
      ULift.up ((structureIndexPullback S V j).hom (ULift.down a)) := by
  rw [structureRingedHom_forgetFSharp_app]
  exact structureProjection_structureSharpApp S V j a

/-- **The structure map of `τ_{X/S}` followed by the projection to one object.**  For an object
`A = (U, T, δ)` of `Cris(X/S)` with `U` above an open `V` of `S`, the structure map
`𝒪_S(V) ⟶ (τ_{X/S, *}𝒪_{X/S})(V)`, followed by the restriction of the right Kan extension along
`U ⊆ X_V` and its counit at `A`, is the pullback `(T ⟶ S)^* : Γ(S, V) ⟶ Γ(T, 𝒪_T)` along the
structure morphism of `A`, under the universe lift. -/
theorem structureRingedHom_forgetFSharp_chain (V : S.S.scheme.Opens) (A : CrystallineThickening S)
    (hA : (forgetToOpens S).obj A ≤ (Opens.map (sourceToBase S).base).obj V) :
    (RingedToposHom.forgetFSharp (structureRingedHom S)).hom.app (op V) ≫
        ((forgetToOpens S).op.ran.obj
          ((crisRingedTopos S).forgetRing.obj (crisRingedTopos S).O).obj).map (homOfLE hA).op ≫
        ((forgetToOpens S).op.ranCounit.app
          ((crisRingedTopos S).forgetRing.obj (crisRingedTopos S).O).obj).app (op A) =
      (CategoryTheory.forget CommRingCat.{u + 1}).map
        (SheafOfModules.commRingCatULift.{u, u + 1}.map
          (A.obj.toBase.hom.appLE V ⊤ (top_le_toBase_preimage hA))) := by
  ext a
  exact structureRingedHom_forgetFSharp_proj S V a (StructuredArrow.mk (homOfLE hA).op)

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
