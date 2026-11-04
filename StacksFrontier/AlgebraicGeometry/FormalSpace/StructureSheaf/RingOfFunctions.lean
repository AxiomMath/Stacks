module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage
public import StacksFrontier.AlgebraicGeometry.FormalSpace.StructureSheaf.Defs
public import StacksFrontier.CategoryTheory.Sites.Density

/-!
# The topological ring of functions of an fppf sheaf

Let `F` be a sheaf on the big fppf site of a scheme `S`. Its *ring of functions* is the limit,
in topological rings, of the discrete rings `Γ(T, 𝒪_T)` over all points `x ∈ F(T)` of `F` with
values in affine objects `T` of the site:

`𝒪(F) = lim_{(T, x)} Γ(T, 𝒪_T)`.

This is the rule of Section 0DEI with the choice of a presentation removed: when
`F = colim U_λ` is a colimit presentation by affine thickenings as in Stacks 0AI7, the stage
inclusions are an initial family of points, so `𝒪(F) = lim_λ Γ(U_λ, 𝒪_{U_λ})` as topological
rings, canonically.

## Main definitions

* `AlgebraicGeometry.FormalSpace.affinePoints`: the restriction of an fppf sheaf to the affine
  objects of the site.
* `AlgebraicGeometry.FormalSpace.ringOfFunctions` and
  `AlgebraicGeometry.FormalSpace.ringOfFunctionsFunctor`: the ring of functions, contravariant in
  the sheaf.
* `AlgebraicGeometry.FormalSpace.ringOfFunctionsHomEquiv`: a continuous ring map from `E` to the
  ring of functions of `F` is a natural family of continuous ring maps from `E` to the
  `Γ(T, 𝒪_T)`, indexed by the affine points of `F`.
* `AlgebraicGeometry.FormalSpace.ThickeningPresentation.ringOfFunctionsIso`: the ring of
  functions of an fppf sheaf with a colimit presentation by affine thickenings is the limit of
  the rings of functions of the stages.

## Main results

* `AlgebraicGeometry.FormalSpace.ThickeningPresentation.initial_elementsFunctor`: the stage
  inclusions of a presentation are initial among the affine points. Every affine point factors
  through a stage, because an affine object of the site is quasi-compact and the transition
  morphisms are monomorphisms (Stacks 0738); and two factorizations through one stage agree
  after a further transition, because sections over a quasi-compact object commute with
  filtered colimits (Stacks 0738 again).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

/-- `TopCommRingCat.{u + 1}` has the limits indexed by categories whose objects form a type in
`Type (u + 1)` and whose morphisms form types in `Type u`, such as the categories of affine points
of fppf sheaves over the big fppf site of a scheme. -/
instance hasLimitsOfSize_topCommRingCat : HasLimitsOfSize.{u, u + 1} TopCommRingCat.{u + 1} :=
  hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} TopCommRingCat.{u + 1}

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The restriction of an fppf sheaf over `S` to the affine objects of the site. -/
noncomputable def affinePoints :
    FppfSheaf B S hS ⥤ ((BigAffineFppf B S hS)ᵒᵖ ⥤ Type (u + 1)) :=
  sheafToPresheaf _ _ ⋙ (Functor.whiskeringLeft _ _ _).obj (BigAffineFppf.inclusion B S hS).op

variable {B S hS}

/-- The affine points of `F` with values in `T` are the sections of `F` over `T`. -/
@[simp]
theorem affinePoints_obj_obj (F : FppfSheaf B S hS) (T : (BigAffineFppf B S hS)ᵒᵖ) :
    ((affinePoints B S hS).obj F).obj T = F.obj.obj (op ((BigAffineFppf.inclusion B S hS).obj
      T.unop)) :=
  rfl

/-- The restriction of affine points of `F` along a morphism of affine objects is the restriction
of sections of `F`. -/
@[simp]
theorem affinePoints_obj_map (F : FppfSheaf B S hS) {T T' : (BigAffineFppf B S hS)ᵒᵖ}
    (f : T ⟶ T') :
    ((affinePoints B S hS).obj F).map f =
      F.obj.map ((BigAffineFppf.inclusion B S hS).map f.unop).op :=
  rfl

/-- The map of affine points induced by a morphism of fppf sheaves is its component at the affine
object. -/
@[simp]
theorem affinePoints_map_app {F F' : FppfSheaf B S hS} (f : F ⟶ F')
    (T : (BigAffineFppf B S hS)ᵒᵖ) :
    ((affinePoints B S hS).map f).app T =
      f.hom.app (op ((BigAffineFppf.inclusion B S hS).obj T.unop)) :=
  rfl

/-- The diagram of the discrete rings `Γ(T, 𝒪_T)` over the affine points `x ∈ F(T)` of `F`. -/
noncomputable abbrev functionsDiagram (F : FppfSheaf B S hS) :
    ((affinePoints B S hS).obj F).Elements ⥤ TopCommRingCat.{u + 1} :=
  CategoryOfElements.π ((affinePoints B S hS).obj F) ⋙ discreteFunctions B S hS

/-- **The ring of functions of an fppf sheaf.** The limit, in topological rings, of the discrete
rings `Γ(T, 𝒪_T)` over the points `x ∈ F(T)` of `F` with values in affine objects `T` of the
site. -/
noncomputable abbrev ringOfFunctions (F : FppfSheaf B S hS) : TopCommRingCat.{u + 1} :=
  limit (functionsDiagram F)

/-- The projection of the ring of functions of `F` to the ring `Γ(T, 𝒪_T)` of an affine point
`x ∈ F(T)`: the value of a function at `x`. -/
noncomputable def ringOfFunctionsπ (F : FppfSheaf B S hS) (T : BigAffineFppf B S hS)
    (x : F.obj.obj (op ((BigAffineFppf.inclusion B S hS).obj T))) :
    ringOfFunctions F ⟶ (discreteFunctions B S hS).obj (op T) :=
  limit.π (functionsDiagram F) (((affinePoints B S hS).obj F).elementsMk (op T) x)

/-- The values of a function at an affine point and at its restriction are compatible. -/
@[reassoc]
theorem ringOfFunctionsπ_map (F : FppfSheaf B S hS) {T T' : BigAffineFppf B S hS} (f : T' ⟶ T)
    (x : F.obj.obj (op ((BigAffineFppf.inclusion B S hS).obj T))) :
    ringOfFunctionsπ F T x ≫ (discreteFunctions B S hS).map f.op =
      ringOfFunctionsπ F T' (F.obj.map ((BigAffineFppf.inclusion B S hS).map f).op x) :=
  limit.w (functionsDiagram F) (CategoryOfElements.homMk
    (((affinePoints B S hS).obj F).elementsMk (op T) x)
    (((affinePoints B S hS).obj F).elementsMk (op T')
      (F.obj.map ((BigAffineFppf.inclusion B S hS).map f).op x)) f.op rfl)

/-- A function is determined by its values at the affine points. -/
theorem ringOfFunctions_hom_ext {F : FppfSheaf B S hS} {E : TopCommRingCat.{u + 1}}
    {φ ψ : E ⟶ ringOfFunctions F}
    (h : ∀ T x, φ ≫ ringOfFunctionsπ F T x = ψ ≫ ringOfFunctionsπ F T x) : φ = ψ :=
  limit.hom_ext fun p => h p.1.unop p.2

/-- A compatible family of continuous ring maps to the rings `Γ(T, 𝒪_T)` of the affine points of
`F` assembles to a continuous ring map to the ring of functions of `F`. -/
noncomputable def ringOfFunctionsLift (F : FppfSheaf B S hS) (E : TopCommRingCat.{u + 1})
    (c : ∀ (T : BigAffineFppf B S hS), F.obj.obj (op ((BigAffineFppf.inclusion B S hS).obj T)) →
      (E ⟶ (discreteFunctions B S hS).obj (op T)))
    (hc : ∀ (T T' : BigAffineFppf B S hS) (f : T' ⟶ T)
      (x : F.obj.obj (op ((BigAffineFppf.inclusion B S hS).obj T))),
      c T x ≫ (discreteFunctions B S hS).map f.op =
        c T' (F.obj.map ((BigAffineFppf.inclusion B S hS).map f).op x)) :
    E ⟶ ringOfFunctions F :=
  limit.lift (functionsDiagram F)
    { pt := E
      π :=
        { app := fun p => c p.1.unop p.2
          naturality := fun p q k => by
            have h := hc p.1.unop q.1.unop k.1.unop p.2
            have hk : F.obj.map ((BigAffineFppf.inclusion B S hS).map k.1.unop).op p.2 = q.2 :=
              k.2
            rw [hk] at h
            exact (Category.id_comp _).trans h.symm } }

/-- The value of the map assembled from a compatible family at an affine point `x ∈ F(T)` is the
member of the family indexed by `x`. -/
@[reassoc (attr := simp)]
theorem ringOfFunctionsLift_π (F : FppfSheaf B S hS) (E : TopCommRingCat.{u + 1})
    (c : ∀ (T : BigAffineFppf B S hS), F.obj.obj (op ((BigAffineFppf.inclusion B S hS).obj T)) →
      (E ⟶ (discreteFunctions B S hS).obj (op T)))
    (hc : ∀ (T T' : BigAffineFppf B S hS) (f : T' ⟶ T)
      (x : F.obj.obj (op ((BigAffineFppf.inclusion B S hS).obj T))),
      c T x ≫ (discreteFunctions B S hS).map f.op =
        c T' (F.obj.map ((BigAffineFppf.inclusion B S hS).map f).op x))
    (T : BigAffineFppf B S hS) (x : F.obj.obj (op ((BigAffineFppf.inclusion B S hS).obj T))) :
    ringOfFunctionsLift F E c hc ≫ ringOfFunctionsπ F T x = c T x :=
  limit.lift_π _ _

/-- The map of rings of functions induced by a morphism of fppf sheaves: pull functions back
along the induced map of affine points. -/
noncomputable def ringOfFunctionsMap {F F' : FppfSheaf B S hS} (f : F ⟶ F') :
    ringOfFunctions F' ⟶ ringOfFunctions F :=
  ringOfFunctionsLift F _ (fun T x => ringOfFunctionsπ F' T (f.hom.app _ x)) (fun T T' g x => by
    rw [ringOfFunctionsπ_map, NatTrans.naturality_apply])

/-- The value of the pullback of a function along `f : F ⟶ F'` at an affine point `x` of `F` is the
value of the function at the image of `x` in `F'`. -/
@[reassoc (attr := simp)]
theorem ringOfFunctionsMap_π {F F' : FppfSheaf B S hS} (f : F ⟶ F') (T : BigAffineFppf B S hS)
    (x : F.obj.obj (op ((BigAffineFppf.inclusion B S hS).obj T))) :
    ringOfFunctionsMap f ≫ ringOfFunctionsπ F T x = ringOfFunctionsπ F' T (f.hom.app _ x) :=
  ringOfFunctionsLift_π _ _ _ _ _ _

variable (B S hS) in
/-- The ring of functions, as a contravariant functor on fppf sheaves. -/
@[simps]
noncomputable def ringOfFunctionsFunctor : (FppfSheaf B S hS)ᵒᵖ ⥤ TopCommRingCat.{u + 1} where
  obj F := ringOfFunctions F.unop
  map f := ringOfFunctionsMap f.unop
  map_id F := ringOfFunctions_hom_ext fun T x => by
    rw [ringOfFunctionsMap_π, Category.id_comp]
    rfl
  map_comp f g := ringOfFunctions_hom_ext fun T x => by
    rw [Category.assoc, ringOfFunctionsMap_π, ringOfFunctionsMap_π, ringOfFunctionsMap_π]
    rfl

/-! ### Maps into the ring of functions -/

/-- **Maps into the ring of functions.** A continuous ring map `E ⟶ 𝒪(F)` is the same thing as a
natural family, indexed by the affine points `x ∈ F(T)`, of continuous ring maps `E ⟶ Γ(T, 𝒪_T)`;
that is, a morphism from the affine points of `F` to the presheaf `T ↦ (E ⟶ Γ(T, 𝒪_T))`. -/
noncomputable def ringOfFunctionsHomEquiv (E : TopCommRingCat.{u + 1}) (F : FppfSheaf B S hS) :
    (E ⟶ ringOfFunctions F) ≃
      ((affinePoints B S hS).obj F ⟶ discreteFunctions B S hS ⋙ coyoneda.obj (op E)) where
  toFun φ :=
    { app := fun T => ↾(fun x => φ ≫ ringOfFunctionsπ F T.unop x)
      naturality := fun T T' f => by
        ext x
        exact ((Category.assoc _ _ _).trans
          (congrArg (φ ≫ ·) (ringOfFunctionsπ_map F f.unop x))).symm }
  invFun σ := ringOfFunctionsLift F E (fun T x => σ.app (op T) x) (fun T T' f x =>
    (NatTrans.naturality_apply σ f.op x).symm)
  left_inv φ := ringOfFunctions_hom_ext fun T x => ringOfFunctionsLift_π _ _ _ _ _ _
  right_inv σ := by
    refine NatTrans.ext (funext fun T => ?_)
    ext x
    exact ringOfFunctionsLift_π _ _ _ _ _ _

/-- The component at an affine point `x ∈ F(T)` of the family corresponding to `φ : E ⟶ 𝒪(F)` is
the composite of `φ` with the value at `x`. -/
theorem ringOfFunctionsHomEquiv_apply_app (E : TopCommRingCat.{u + 1}) (F : FppfSheaf B S hS)
    (φ : E ⟶ ringOfFunctions F) (T : BigAffineFppf B S hS)
    (x : F.obj.obj (op ((BigAffineFppf.inclusion B S hS).obj T))) :
    (ringOfFunctionsHomEquiv E F φ).app (op T) x = φ ≫ ringOfFunctionsπ F T x :=
  rfl

/-- `AlgebraicGeometry.FormalSpace.ringOfFunctionsHomEquiv` is natural in the sheaf. -/
theorem ringOfFunctionsHomEquiv_naturality (E : TopCommRingCat.{u + 1}) {F F' : FppfSheaf B S hS}
    (f : F ⟶ F') (φ : E ⟶ ringOfFunctions F') :
    ringOfFunctionsHomEquiv E F (φ ≫ ringOfFunctionsMap f) =
      (affinePoints B S hS).map f ≫ ringOfFunctionsHomEquiv E F' φ := by
  refine NatTrans.ext (funext fun T => ?_)
  ext x
  exact (Category.assoc _ _ _).trans (congrArg (φ ≫ ·) (ringOfFunctionsMap_π f T.unop x))

/-! ### The ring of functions of a presented sheaf -/

namespace ThickeningPresentation

variable {U : FppfSheaf B S hS} (P : ThickeningPresentation B S hS U)

/-- The stage inclusion `U_λ ⟶ U`, as an affine point of `U`. -/
noncomputable def point (i : P.Index) : ((affinePoints B S hS).obj U).obj (op (P.diagram.obj i)) :=
  Sheaf.sectionEquiv (BigFppfOver.topology B S hS) (P.stageMap i)

/-- The restriction of the stage inclusion `U_j ⟶ U` along a transition morphism `U_i ⟶ U_j` is the
stage inclusion `U_i ⟶ U`. -/
theorem point_map {i j : P.Index} (f : i ⟶ j) :
    ((affinePoints B S hS).obj U).map (P.diagram.map f).op (P.point j) = P.point i :=
  (Sheaf.sectionEquiv_map_comp (BigFppfOver.topology B S hS) _ (P.stageMap j)).symm.trans
    (congrArg (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)) (P.map_stageMap f))

/-- The stage inclusions of a presentation, as a functor into the affine points of `U`. -/
@[simps]
noncomputable def elementsFunctor : P.Indexᵒᵖ ⥤ ((affinePoints B S hS).obj U).Elements where
  obj i := ⟨op (P.diagram.obj i.unop), P.point i.unop⟩
  map f := ⟨(P.diagram.map f.unop).op, P.point_map f.unop⟩
  map_id i := CategoryOfElements.ext _ _ _ (by
    refine Eq.trans ?_ CategoryOfElements.id_val.symm
    simp)
  map_comp f g := CategoryOfElements.ext _ _ _ (by
    refine Eq.trans ?_ CategoryOfElements.comp_val.symm
    simp)

/-- The stages of a presentation, as a diagram of fppf sheaves. -/
noncomputable abbrev sheafDiagram : P.Index ⥤ FppfSheaf B S hS :=
  P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙ Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)

/-- The transition morphisms of a presentation are monomorphisms of fppf sheaves: thickenings
are monomorphisms of schemes, and the sheafified Yoneda embedding preserves monomorphisms. -/
theorem mono_sheafDiagram_map {i j : P.Index} (f : i ⟶ j) : Mono (P.sheafDiagram.map f) := by
  let J := BigFppfOver.topology B S hS
  have _ : IsClosedImmersion ((BigAffineFppf.toScheme B S hS).map (P.diagram.map f)) :=
    (P.isThickening f).1
  have _ : Mono ((BigFppfOver.toScheme B S hS).map
      ((BigAffineFppf.inclusion B S hS).map (P.diagram.map f))) :=
    inferInstanceAs (Mono ((BigAffineFppf.toScheme B S hS).map (P.diagram.map f)))
  have _ : Mono ((BigAffineFppf.inclusion B S hS).map (P.diagram.map f)) :=
    (BigFppfOver.toScheme B S hS).mono_of_mono_map ‹_›
  have _ : PreservesLimitsOfShape WalkingCospan (Sheaf.sheafifiedYoneda J) := by
    dsimp [Sheaf.sheafifiedYoneda]
    infer_instance
  exact (Sheaf.sheafifiedYoneda J).map_mono _

/-- An affine object of the site is a quasi-compact object of the big fppf site. -/
theorem isQuasiCompactObject_inclusion (T : BigAffineFppf B S hS) :
    (BigFppfOver.topology B S hS).IsQuasiCompactObject ((BigAffineFppf.inclusion B S hS).obj T) :=
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj T)) :=
    T.property
  isQuasiCompactObject_over_of_compact_scheme B S hS _

/-- Every affine point of `U` factors through a stage of the presentation. -/
theorem exists_point_factor (T : BigAffineFppf B S hS)
    (x : ((affinePoints B S hS).obj U).obj (op T)) :
    ∃ (i : P.Index) (t : T ⟶ P.diagram.obj i),
      ((affinePoints B S hS).obj U).map t.op (P.point i) = x := by
  let J := BigFppfOver.topology B S hS
  obtain ⟨i, g, hg⟩ := compact_map_factors_through_filtered_colimit P.sheafDiagram
    (fun _ _ f => P.mono_sheafDiagram_map f) _ (isQuasiCompactObject_inclusion T)
    ((Sheaf.sectionEquiv J).symm x ≫ P.iso.hom)
  obtain ⟨m, rfl⟩ := (sheafifiedYonedaFF B S hS).map_surjective g
  obtain ⟨t, rfl⟩ := (BigAffineFppf.inclusion B S hS).map_surjective m
  refine ⟨i, t, (Sheaf.sectionEquiv_map_comp J _ (P.stageMap i)).symm.trans ?_⟩
  rw [Quiver.Hom.unop_op, stageMap, ← Category.assoc, hg, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]
  exact Equiv.apply_symm_apply _ x

/-- Two factorizations of an affine point of `U` through one stage of the presentation agree
after a further transition. -/
theorem exists_eq_comp_map_of_point_eq {T : BigAffineFppf B S hS} {i : P.Index}
    (t₁ t₂ : T ⟶ P.diagram.obj i)
    (h : ((affinePoints B S hS).obj U).map t₁.op (P.point i) =
      ((affinePoints B S hS).obj U).map t₂.op (P.point i)) :
    ∃ (j : P.Index) (f : i ⟶ j), t₁ ≫ P.diagram.map f = t₂ ≫ P.diagram.map f := by
  let J := BigFppfOver.topology B S hS
  let sY := Sheaf.sheafifiedYoneda J
  let incl := BigAffineFppf.inclusion B S hS
  let G := (sheafSections J (Type (u + 1))).obj (op (incl.obj T))
  have hι : sY.map (incl.map t₁) ≫ colimit.ι P.sheafDiagram i =
      sY.map (incl.map t₂) ≫ colimit.ι P.sheafDiagram i := by
    have h' : Sheaf.sectionEquiv J (sY.map (incl.map t₁) ≫ P.stageMap i) =
        Sheaf.sectionEquiv J (sY.map (incl.map t₂) ≫ P.stageMap i) :=
      ((Sheaf.sectionEquiv_map_comp J _ (P.stageMap i)).trans h).trans
        (Sheaf.sectionEquiv_map_comp J _ (P.stageMap i)).symm
    have h'' := (Sheaf.sectionEquiv J).injective h'
    rw [stageMap, ← Category.assoc, ← Category.assoc] at h''
    exact (cancel_mono P.iso.inv).mp h''
  have hinj := (Sheaf.injective_and_bijective_colimit_post_sheafSections J P.sheafDiagram
    (incl.obj T)).2.1 (isQuasiCompactObject_inclusion T)
  have hpost (y : (P.sheafDiagram.obj i).obj.obj (op (incl.obj T))) :
      colimit.post P.sheafDiagram G (colimit.ι (P.sheafDiagram ⋙ G) i y) =
        (colimit.ι P.sheafDiagram i).hom.app (op (incl.obj T)) y :=
    ConcreteCategory.congr_hom (colimit.ι_post P.sheafDiagram G i) y
  have hcol : colimit.ι (P.sheafDiagram ⋙ G) i (Sheaf.sectionEquiv J (sY.map (incl.map t₁))) =
      colimit.ι (P.sheafDiagram ⋙ G) i (Sheaf.sectionEquiv J (sY.map (incl.map t₂))) := by
    apply hinj
    rw [hpost, hpost, ← Sheaf.sectionEquiv_comp, ← Sheaf.sectionEquiv_comp, hι]
  obtain ⟨j, f, hf⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' (colimit.isColimit (P.sheafDiagram ⋙ G)) _ _).mp hcol
  refine ⟨j, f, (incl ⋙ sY).map_injective ?_⟩
  have hf' : Sheaf.sectionEquiv J (sY.map (incl.map t₁) ≫ P.sheafDiagram.map f) =
      Sheaf.sectionEquiv J (sY.map (incl.map t₂) ≫ P.sheafDiagram.map f) := by
    rwa [Sheaf.sectionEquiv_comp, Sheaf.sectionEquiv_comp]
  simpa only [Functor.comp_map, Functor.map_comp] using (Sheaf.sectionEquiv J).injective hf'

/-- **The stage inclusions of a presentation are initial among the affine points.** -/
theorem initial_elementsFunctor : P.elementsFunctor.Initial := by
  refine Functor.initial_of_exists_of_isCofiltered _ (fun d => ?_) (fun {d c} s s' => ?_)
  · obtain ⟨i, t, ht⟩ := P.exists_point_factor d.1.unop d.2
    exact ⟨op i, ⟨CategoryOfElements.homMk _ _ t.op ht⟩⟩
  · have h : ((affinePoints B S hS).obj U).map s.1.unop.op (P.point c.unop) =
        ((affinePoints B S hS).obj U).map s'.1.unop.op (P.point c.unop) :=
      s.2.trans s'.2.symm
    obtain ⟨j, f, hf⟩ := P.exists_eq_comp_map_of_point_eq s.1.unop s'.1.unop h
    refine ⟨op j, f.op, CategoryOfElements.ext _ _ _ ?_⟩
    rw [CategoryOfElements.comp_val, CategoryOfElements.comp_val]
    exact congrArg Quiver.Hom.op hf

/-- The comparison of the diagram of the stages with the inverse system of a presentation. -/
noncomputable def elementsFunctorCompIso :
    P.elementsFunctor ⋙ functionsDiagram U ≅ P.rings :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)

/-- **The rule of Section 0DEI.** The ring of functions of an fppf sheaf `U` with a colimit
presentation `U = colim U_λ` by affine thickenings is `lim_λ Γ(U_λ, 𝒪_{U_λ})`, as topological
rings. -/
noncomputable def ringOfFunctionsIso : ringOfFunctions U ≅ limit P.rings :=
  haveI := P.initial_elementsFunctor
  (Functor.Initial.limitIso P.elementsFunctor (functionsDiagram U)).symm ≪≫
    HasLimit.isoOfNatIso P.elementsFunctorCompIso

/-- The identification of the ring of functions with the limit over the stages is the value at
the stage inclusions. -/
@[reassoc (attr := simp)]
theorem ringOfFunctionsIso_hom_π (i : P.Index) :
    P.ringOfFunctionsIso.hom ≫ limit.π P.rings (op i) =
      ringOfFunctionsπ U (P.diagram.obj i) (P.point i) := by
  have := P.initial_elementsFunctor
  rw [ringOfFunctionsIso, Iso.trans_hom, Iso.symm_hom, Functor.Initial.limitIso_inv,
    Category.assoc, HasLimit.isoOfNatIso_hom_π, limit.pre_π_assoc]
  exact Category.comp_id _

end ThickeningPresentation

end AlgebraicGeometry.FormalSpace

end
