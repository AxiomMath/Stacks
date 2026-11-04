module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Galois.Prorepresentability
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteModulesAction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverSheets
public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.TopologicalInvarianceFundamental.Thickening

/-!
# The monodromy module of a sheaf on the small étale site

Let `X` be a connected scheme with a geometric point `x`, and let `π₁ = π₁(X, x)`. A pointed
Galois object `(A, a)` of the Galois category `FÉt_X` is a finite étale Galois cover `A ⟶ X`
together with a point `a` of its geometric fibre at `x`; these form a cofiltered category, and
`π₁` acts on each of them: an element `σ` determines the unique automorphism `τ_A(σ)` of `A`
over `X` carrying `a` to `σ • a`, compatibly with the morphisms of pointed Galois objects
(Mathlib's `CategoryTheory.PreGaloisCategory.autMulEquivAutGalois`).

For a presheaf `F` on the small étale site of `X` with values in a category `C`, the
**monodromy object** of `F` is the filtered colimit

```
  colim_{(A, a)} F(A)
```

over the pointed Galois objects, on which `σ ∈ π₁` acts through `F(τ_A(σ))`. For a sheaf of
`Λ`-modules this is a `Λ`-module with an action of `π₁`, and the action is continuous for the
discrete topology: an element coming from `F(A)` is fixed by the open subgroup of the elements
fixing `a`. When `F` is trivialized by a finite étale cover the monodromy module is the stalk of
`F` with its monodromy action; that is the dictionary of Stacks Tag 0GIY.

## Main definitions

* `AlgebraicGeometry.PointedGaloisCover` — the pointed Galois objects of `FÉt_X` at `x`.
* `AlgebraicGeometry.PointedGaloisCover.toEtale` — their underlying objects of the small étale
  site of `X`.
* `AlgebraicGeometry.galoisAut` — the automorphism `τ_A(σ)` of a pointed Galois cover determined
  by an element `σ` of the étale fundamental group.
* `AlgebraicGeometry.monodromyDiagram` and `AlgebraicGeometry.monodromyDiagramAut` — the
  diagram `(A, a) ↦ F(A)` and the action of `π₁` on it, both natural in `F`.
* `AlgebraicGeometry.monodromyAction` — the monodromy object as an object of
  `CategoryTheory.Action C π₁`, functorially in the presheaf.
* `AlgebraicGeometry.monodromyModule` — for `Λ`-module coefficients, the monodromy module as a
  `Λ`-module with a continuous `π₁`-action (Tag 04JP).

## Main results

* `AlgebraicGeometry.galoisAut_mul` and `AlgebraicGeometry.comp_galoisAut` — `σ ↦ τ_A(σ)` is
  an anti-homomorphism, compatible with morphisms of pointed Galois covers.
* `AlgebraicGeometry.galoisAut_eq_one_iff` — `τ_A(σ)` is trivial exactly when `σ` fixes the
  marked point of `A`, so `isOpen_setOf_galoisAut_eq_one` holds.
* `AlgebraicGeometry.monodromyAction_ρ_ι` — the action on the image of `F(A)` is `F(τ_A(σ))`.

## References

* [Stacks Project, Tag 0GIY](https://stacks.math.columbia.edu/tag/0GIY)
* [Stacks Project, Tag 0BN4](https://stacks.math.columbia.edu/tag/0BN4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite

universe u r w

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [ConnectedSpace X] (x : GeometricPoint X)

/-! ### Pointed Galois covers and the action of the fundamental group on them -/

/-- The pointed Galois objects of the Galois category of finite étale covers of `X`, for the
geometric fibre functor at `x`: a Galois finite étale cover of `X` together with a point of its
geometric fibre at `x`. -/
abbrev PointedGaloisCover := PointedGaloisObject (finiteEtaleFiberFintypeFunctor X x)

/-- There is a pointed Galois cover: the geometric fibre of the identity cover is nonempty, so it
receives a morphism from a Galois object. -/
instance nonempty_pointedGaloisCover : Nonempty (PointedGaloisCover x) := by
  let S : FiniteEtaleOver X := MorphismProperty.Over.mk ⊤ (𝟙 X) ⟨inferInstance, inferInstance⟩
  obtain ⟨A, -, a, hA, -⟩ := exists_hom_from_galois_of_fiber
    (finiteEtaleFiberFintypeFunctor X x) S (⟨x.hom, Category.comp_id _⟩ : finiteEtaleFiber x S)
  exact ⟨⟨A, a, hA⟩⟩

/-- The pointed Galois covers form a cofiltered category. -/
instance isCofiltered_pointedGaloisCover : IsCofiltered (PointedGaloisCover x) where

/-- A pointed Galois cover as an object of the small étale site of `X`. -/
abbrev PointedGaloisCover.toEtale : PointedGaloisCover x ⥤ X.Etale where
  obj A := (finiteEtaleToEtale X).obj A.obj
  map f := (finiteEtaleToEtale X).map f.val
  map_id _ := (finiteEtaleToEtale X).map_id _
  map_comp _ _ := (finiteEtaleToEtale X).map_comp _ _

/-- **The automorphism `τ_A(σ)` of a pointed Galois cover determined by an element `σ` of the
étale fundamental group**: the component at `A` of the image of `σ` in the limit of the
automorphism groups of the pointed Galois covers. -/
def galoisAut (σ : EtaleFundamentalGroup X x) (A : PointedGaloisCover x) : Aut A.obj :=
  AutGalois.π _ A (autMulEquivAutGalois _ ((autMulEquivEtaleFundamentalGroup X x).symm σ)).unop

/-- `τ_A(1)` is the identity. -/
@[simp]
theorem galoisAut_one (A : PointedGaloisCover x) : galoisAut x 1 A = 1 := by
  simp [galoisAut]

/-- `σ ↦ τ_A(σ)` is an anti-homomorphism. -/
theorem galoisAut_mul (σ τ : EtaleFundamentalGroup X x) (A : PointedGaloisCover x) :
    galoisAut x (σ * τ) A = galoisAut x τ A * galoisAut x σ A := by
  simp [galoisAut]

/-- The underlying endomorphism of `τ_A(σ)`. Lemmas about the automorphisms `τ_A(σ)` are stated
for this endomorphism, so that no projection out of `CategoryTheory.Aut` appears in their
statements. -/
def galoisAutHom (σ : EtaleFundamentalGroup X x) (A : PointedGaloisCover x) : A.obj ⟶ A.obj :=
  Iso.hom (galoisAut x σ A)

/-- If `τ_A(σ)` is trivial, its underlying endomorphism is the identity. -/
private theorem galoisAutHom_eq_id_of_galoisAut_eq_one {σ : EtaleFundamentalGroup X x}
    {A : PointedGaloisCover x} (h : galoisAut x σ A = 1) : galoisAutHom x σ A = 𝟙 A.obj := by
  rw [galoisAutHom, h]
  rfl

/-- `τ_A(1)` is the identity. -/
@[simp]
theorem galoisAutHom_one (A : PointedGaloisCover x) : galoisAutHom x 1 A = 𝟙 A.obj :=
  galoisAutHom_eq_id_of_galoisAut_eq_one x (galoisAut_one x A)

/-- `σ ↦ τ_A(σ)` is an anti-homomorphism: `τ_A(στ) = τ_A(σ) ≫ τ_A(τ)`. -/
theorem galoisAutHom_mul (σ τ : EtaleFundamentalGroup X x) (A : PointedGaloisCover x) :
    galoisAutHom x (σ * τ) A = galoisAutHom x σ A ≫ galoisAutHom x τ A := by
  rw [galoisAutHom, galoisAut_mul]
  rfl

/-- `τ_A(σ⁻¹)` is inverse to `τ_A(σ)`. -/
@[reassoc (attr := simp)]
theorem galoisAutHom_inv_comp (σ : EtaleFundamentalGroup X x) (A : PointedGaloisCover x) :
    galoisAutHom x σ⁻¹ A ≫ galoisAutHom x σ A = 𝟙 A.obj := by
  rw [← galoisAutHom_mul, inv_mul_cancel, galoisAutHom_one]

/-- `τ_A(σ⁻¹)` is inverse to `τ_A(σ)`. -/
@[reassoc (attr := simp)]
theorem galoisAutHom_comp_inv (σ : EtaleFundamentalGroup X x) (A : PointedGaloisCover x) :
    galoisAutHom x σ A ≫ galoisAutHom x σ⁻¹ A = 𝟙 A.obj := by
  rw [← galoisAutHom_mul, mul_inv_cancel, galoisAutHom_one]

/-- **`τ(σ)` is compatible with morphisms of pointed Galois covers.** -/
theorem comp_galoisAutHom {A B : PointedGaloisCover x} (f : A ⟶ B)
    (σ : EtaleFundamentalGroup X x) :
    f.val ≫ galoisAutHom x σ B = galoisAutHom x σ A ≫ f.val := by
  set ξ := (autMulEquivAutGalois _ ((autMulEquivEtaleFundamentalGroup X x).symm σ)).unop
  have h : autMap f.val (AutGalois.π _ A ξ) = AutGalois.π _ B ξ := by
    rw [AutGalois.π_apply, AutGalois.π_apply]
    exact ξ.2 f
  show f.val ≫ Iso.hom (AutGalois.π _ B ξ) = Iso.hom (AutGalois.π _ A ξ) ≫ f.val
  rw [← h]
  exact comp_autMap _ _

variable {x} in
/-- The marked point of a pointed Galois cover, as an element of the geometric fibre on which
the étale fundamental group acts. -/
def PointedGaloisCover.basePt (A : PointedGaloisCover x) :
    (finiteEtaleFiberFunctor x).obj A.obj :=
  A.pt

/-- `τ_A(σ)` carries the marked point of `A` to its image under `σ`. -/
theorem galoisAutHom_pt (σ : EtaleFundamentalGroup X x) (A : PointedGaloisCover x) :
    (finiteEtaleFiberFintypeFunctor X x).map (galoisAutHom x σ A) A.pt = σ • A.basePt := by
  have h := autMulEquivAutGalois_π (finiteEtaleFiberFintypeFunctor X x)
    ((autMulEquivEtaleFundamentalGroup X x).symm σ) A.obj A.pt
  refine h.trans ?_
  conv_rhs => rw [← MulEquiv.apply_symm_apply (autMulEquivEtaleFundamentalGroup X x) σ]
  rfl

/-- **`τ_A(σ)` is trivial exactly when `σ` fixes the marked point of `A`**: the automorphism
group of a connected object acts freely on its fibres. -/
theorem galoisAut_eq_one_iff (σ : EtaleFundamentalGroup X x) (A : PointedGaloisCover x) :
    galoisAut x σ A = 1 ↔ σ • A.basePt = A.basePt := by
  rw [← galoisAutHom_pt]
  constructor
  · intro h
    rw [galoisAutHom_eq_id_of_galoisAut_eq_one x h]
    rfl
  · intro h
    refine evaluation_aut_injective_of_isConnected (finiteEtaleFiberFintypeFunctor X x) A.obj
      A.pt ?_
    exact h.trans rfl

/-- **The elements of `π₁` acting trivially on a pointed Galois cover form an open set**: they
are the stabilizer of its marked point, and the action of `π₁` on a geometric fibre is
continuous for the discrete topology. -/
theorem isOpen_setOf_galoisAut_eq_one (A : PointedGaloisCover x) :
    IsOpen {σ : EtaleFundamentalGroup X x | galoisAut x σ A = 1} := by
  simp_rw [galoisAut_eq_one_iff]
  let F := finiteEtaleFiberFunctor x
  let _ (Y : FiniteEtaleOver X) : TopologicalSpace (F.obj Y) := ⊥
  let _ (Y : FiniteEtaleOver X) : DiscreteTopology (F.obj Y) := ⟨rfl⟩
  let _ (Y : FiniteEtaleOver X) : TopologicalSpace (Equiv.Perm (F.obj Y)) := autTopology
  show @IsOpen (EtaleFundamentalGroup X x)
    (TopologicalSpace.induced (componentEmbedding F) inferInstance) _
  have heval : Continuous (fun g : ∀ Y, Equiv.Perm (F.obj Y) ↦ g A.obj A.basePt) :=
    ((continuous_apply A.basePt).comp continuous_induced_dom).comp (continuous_apply A.obj)
  exact (isOpen_discrete {A.basePt}).preimage (heval.comp continuous_induced_dom)

/-! ### The monodromy object of a presheaf -/

section Monodromy

variable {C : Type*} [Category* C]

/-- The diagram `(A, a) ↦ F(A)` over the pointed Galois covers, functorially in the presheaf
`F` on the small étale site. -/
abbrev monodromyDiagram : ((X.Etale)ᵒᵖ ⥤ C) ⥤ ((PointedGaloisCover x)ᵒᵖ ⥤ C) where
  obj F :=
    { obj A := F.obj (op ((finiteEtaleToEtale X).obj A.unop.obj))
      map f := F.map ((finiteEtaleToEtale X).map f.unop.val).op
      map_id A := by
        rw [← F.map_id]
        rfl
      map_comp f g := by
        rw [← F.map_comp]
        rfl }
  map φ :=
    { app A := φ.app _
      naturality _ _ _ := φ.naturality _ }

/-- **The action of `σ ∈ π₁` on the diagram `(A, a) ↦ F(A)`**, by `F(τ_A(σ))`, naturally in the
presheaf `F`. -/
def monodromyDiagramAut (σ : EtaleFundamentalGroup X x) :
    monodromyDiagram (C := C) x ⟶ monodromyDiagram x where
  app F :=
    { app A := F.map ((finiteEtaleToEtale X).map (galoisAutHom x σ A.unop)).op
      naturality {A B} f := by
        have key : (finiteEtaleToEtale X).map (galoisAutHom x σ B.unop) ≫
            (finiteEtaleToEtale X).map f.unop.val =
            (finiteEtaleToEtale X).map f.unop.val ≫
              (finiteEtaleToEtale X).map (galoisAutHom x σ A.unop) := by
          rw [← (finiteEtaleToEtale X).map_comp, ← (finiteEtaleToEtale X).map_comp,
            comp_galoisAutHom]
        have h := congrArg (fun k ↦ F.map k.op) key
        simp only [op_comp, F.map_comp] at h
        exact h }
  naturality F G φ := by
    ext A
    exact (φ.naturality _).symm

variable {x} in
/-- The component of `monodromyDiagramAut x σ` at `F` and `A` is `F` applied to
the automorphism `galoisAutHom x σ A` of `A`. -/
@[simp]
theorem monodromyDiagramAut_app_app (σ : EtaleFundamentalGroup X x) (F : (X.Etale)ᵒᵖ ⥤ C)
    (A : (PointedGaloisCover x)ᵒᵖ) :
    ((monodromyDiagramAut x σ).app F).app A =
      F.map ((finiteEtaleToEtale X).map (galoisAutHom x σ A.unop)).op :=
  rfl

/-- The identity element of `π₁` acts on the monodromy diagram by the identity. -/
theorem monodromyDiagramAut_one :
    monodromyDiagramAut (C := C) x 1 = 𝟙 _ := by
  ext F A
  rw [monodromyDiagramAut_app_app, galoisAutHom_one, CategoryTheory.Functor.map_id, op_id,
    F.map_id]
  rfl

/-- The action of `π₁` on the monodromy diagram is contravariantly multiplicative: `σ * τ`
acts by the action of `τ` followed by that of `σ`. -/
theorem monodromyDiagramAut_mul (σ τ : EtaleFundamentalGroup X x) :
    monodromyDiagramAut (C := C) x (σ * τ) =
      monodromyDiagramAut x τ ≫ monodromyDiagramAut x σ := by
  ext F A
  rw [NatTrans.comp_app, NatTrans.comp_app, monodromyDiagramAut_app_app,
    monodromyDiagramAut_app_app, monodromyDiagramAut_app_app, galoisAutHom_mul,
    (finiteEtaleToEtale X).map_comp, op_comp, F.map_comp]

variable [HasColimitsOfShape (PointedGaloisCover x)ᵒᵖ C]

/-- The action of `π₁` on the colimit of the diagram `(A, a) ↦ F(A)`. -/
def monodromyRepr (F : (X.Etale)ᵒᵖ ⥤ C) :
    EtaleFundamentalGroup X x →* End (colimit ((monodromyDiagram x).obj F)) where
  toFun σ := colimMap ((monodromyDiagramAut x σ).app F)
  map_one' := by
    rw [monodromyDiagramAut_one, End.one_def]
    apply colimit.hom_ext
    intro A
    simp
  map_mul' σ τ := by
    rw [monodromyDiagramAut_mul, NatTrans.comp_app, End.mul_def]
    apply colimit.hom_ext
    intro A
    simp

/-- **The monodromy object of a presheaf on the small étale site**: the colimit of `F(A)` over
the pointed Galois covers `(A, a)` of `X`, with the action of `σ ∈ π₁(X, x)` induced by the
automorphisms `τ_A(σ)`, as an object of `CategoryTheory.Action C π₁`, functorially in `F`. -/
def monodromyAction : ((X.Etale)ᵒᵖ ⥤ C) ⥤ Action C (EtaleFundamentalGroup X x) where
  obj F := ⟨colimit ((monodromyDiagram x).obj F), monodromyRepr x F⟩
  map {F G} φ :=
    { hom := colimMap ((monodromyDiagram x).map φ)
      comm σ := by
        apply colimit.hom_ext
        intro A
        change colimit.ι _ A ≫ colimMap _ ≫ colimMap _ =
          colimit.ι _ A ≫ colimMap _ ≫ colimMap _
        simp only [ι_colimMap_assoc, ι_colimMap, monodromyDiagramAut_app_app]
        exact φ.naturality_assoc _ _ }
  map_id F := by
    apply Action.hom_ext
    apply colimit.hom_ext
    intro A
    change colimit.ι _ A ≫ colimMap _ = colimit.ι _ A ≫ 𝟙 _
    simp
  map_comp φ ψ := by
    apply Action.hom_ext
    apply colimit.hom_ext
    intro A
    change colimit.ι _ A ≫ colimMap _ = colimit.ι _ A ≫ colimMap _ ≫ colimMap _
    simp

variable {x} in
/-- The underlying object of the monodromy object is the colimit of `F(A)`. -/
@[simp]
theorem monodromyAction_obj_V (F : (X.Etale)ᵒᵖ ⥤ C) :
    ((monodromyAction x).obj F).V = colimit ((monodromyDiagram x).obj F) :=
  rfl

variable {x} in
/-- **The action of `σ` on the image of `F(A)` in the monodromy object is `F(τ_A(σ))`.** -/
@[reassoc]
theorem monodromyAction_ρ_ι (F : (X.Etale)ᵒᵖ ⥤ C) (σ : EtaleFundamentalGroup X x)
    (A : (PointedGaloisCover x)ᵒᵖ) :
    colimit.ι ((monodromyDiagram x).obj F) A ≫ ((monodromyAction x).obj F).ρ σ =
      F.map ((finiteEtaleToEtale X).map (galoisAutHom x σ A.unop)).op ≫
        colimit.ι ((monodromyDiagram x).obj F) A :=
  ι_colimMap _ A

variable {x} in
/-- The monodromy object is functorial through the maps `F(A) ⟶ G(A)`. -/
@[reassoc]
theorem monodromyAction_map_ι {F G : (X.Etale)ᵒᵖ ⥤ C} (φ : F ⟶ G)
    (A : (PointedGaloisCover x)ᵒᵖ) :
    colimit.ι ((monodromyDiagram x).obj F) A ≫ ((monodromyAction x).map φ).hom =
      φ.app (op ((PointedGaloisCover.toEtale x).obj A.unop)) ≫
        colimit.ι ((monodromyDiagram x).obj G) A :=
  ι_colimMap _ A

end Monodromy

/-! ### The monodromy module of a presheaf of modules -/

section Module

variable (Λ : Type r) [Ring Λ]

attribute [local instance] Stacks.DiscreteModuleTopology.hasForget₂ModuleCatTopCat
  Stacks.DiscreteModuleTopology.actionDiscreteTopology

/-- The forgetful functor of modules preserves the filtered colimits over the pointed Galois
covers: it preserves filtered colimits of the size of the module universe, which contains the
universe of the schemes. -/
instance preservesColimitsOfShape_pointedGaloisCover_forget_moduleCat :
    PreservesColimitsOfShape (PointedGaloisCover x)ᵒᵖ (forget (ModuleCat.{max (u + 1) r} Λ)) := by
  have : PreservesFilteredColimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{max (u + 1) r}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) r, max (u + 1) r, u, u + 1} _
  have : PreservesColimitsOfShape (PointedGaloisCover x)ᵒᵖ
      (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat ⋙ forget AddCommGrpCat) :=
    inferInstance
  exact this

variable {x Λ}

/-- Every element of the monodromy module comes from the sections over some pointed Galois
cover. -/
theorem exists_ι_eq_of_monodromy (F : (X.Etale)ᵒᵖ ⥤ ModuleCat.{max (u + 1) r} Λ)
    (v : ((monodromyAction x).obj F).V) :
    ∃ (A : (PointedGaloisCover x)ᵒᵖ) (s : F.obj (op ((PointedGaloisCover.toEtale x).obj A.unop))),
      (colimit.ι ((monodromyDiagram x).obj F) A).hom s = v :=
  Concrete.colimit_exists_rep _ v

/-- The action of `σ` on the image of a section over a pointed Galois cover `A` is the image of
the transport of that section along `τ_A(σ)`. -/
theorem monodromyAction_ρ_ι_apply (F : (X.Etale)ᵒᵖ ⥤ ModuleCat.{max (u + 1) r} Λ)
    (σ : EtaleFundamentalGroup X x) (A : (PointedGaloisCover x)ᵒᵖ)
    (s : F.obj (op ((PointedGaloisCover.toEtale x).obj A.unop))) :
    (((monodromyAction x).obj F).ρ σ).hom ((colimit.ι ((monodromyDiagram x).obj F) A).hom s) =
      (colimit.ι ((monodromyDiagram x).obj F) A).hom
        ((F.map ((finiteEtaleToEtale X).map (galoisAutHom x σ A.unop)).op).hom s) :=
  ConcreteCategory.congr_hom (monodromyAction_ρ_ι F σ A) s

/-- An element of `π₁` acting trivially on a pointed Galois cover `A` fixes the image of every
section over `A` in the monodromy module. -/
theorem monodromyAction_ρ_ι_apply_of_galoisAut_eq_one
    (F : (X.Etale)ᵒᵖ ⥤ ModuleCat.{max (u + 1) r} Λ) {σ : EtaleFundamentalGroup X x}
    {A : (PointedGaloisCover x)ᵒᵖ} (hσ : galoisAut x σ A.unop = 1)
    (s : F.obj (op ((PointedGaloisCover.toEtale x).obj A.unop))) :
    (((monodromyAction x).obj F).ρ σ).hom ((colimit.ι ((monodromyDiagram x).obj F) A).hom s) =
      (colimit.ι ((monodromyDiagram x).obj F) A).hom s := by
  rw [monodromyAction_ρ_ι_apply]
  rw [galoisAutHom_eq_id_of_galoisAut_eq_one x hσ, CategoryTheory.Functor.map_id, op_id, F.map_id]
  rfl

/-- **The action of the étale fundamental group on the monodromy module is continuous** for the
discrete topology: the stabilizer of the image of a section over a pointed Galois cover `A`
contains the open subgroup of the elements acting trivially on `A`, together with its
translates. -/
theorem monodromyAction_isContinuous (F : (X.Etale)ᵒᵖ ⥤ ModuleCat.{max (u + 1) r} Λ) :
    ((monodromyAction x).obj F).IsContinuous := by
  rw [Stacks.GroupCohomology.isContinuous_iff_forall_isOpen_stabilizer]
  intro v
  obtain ⟨A, s, rfl⟩ := exists_ι_eq_of_monodromy F v
  rw [isOpen_iff_forall_mem_open]
  intro σ₀ hσ₀
  refine ⟨(fun σ ↦ σ₀⁻¹ * σ) ⁻¹' {σ | galoisAut x σ A.unop = 1}, ?_, ?_, ?_⟩
  · intro σ hσ
    change galoisAut x (σ₀⁻¹ * σ) A.unop = 1 at hσ
    show (((monodromyAction x).obj F).ρ σ).hom _ = _
    have hσσ : σ = σ₀ * (σ₀⁻¹ * σ) := by group
    rw [hσσ, map_mul, End.mul_def, ModuleCat.hom_comp]
    show (((monodromyAction x).obj F).ρ σ₀).hom
      ((((monodromyAction x).obj F).ρ (σ₀⁻¹ * σ)).hom _) = _
    rw [monodromyAction_ρ_ι_apply_of_galoisAut_eq_one F hσ]
    exact hσ₀
  · exact (isOpen_setOf_galoisAut_eq_one x A.unop).preimage (continuous_const.mul continuous_id)
  · show galoisAut x (σ₀⁻¹ * σ₀) A.unop = 1
    rw [inv_mul_cancel, galoisAut_one]

variable (x Λ)

/-- **The monodromy module of a presheaf of `Λ`-modules on the small étale site**: the colimit of
the sections over the pointed Galois covers of `X`, as a `Λ`-module with a continuous action of
the étale fundamental group (an object of the category of Tag 04JP), functorially in the
presheaf. -/
def monodromyModule :
    ((X.Etale)ᵒᵖ ⥤ ModuleCat.{max (u + 1) r} Λ) ⥤
      Stacks.Injectives.ContinuousModule.{r, u + 1, max (u + 1) r} Λ
        (EtaleFundamentalGroup X x) where
  obj F := ⟨⟨(monodromyAction x).obj F, monodromyAction_isContinuous F⟩, ⟨rfl⟩⟩
  map φ := ObjectProperty.homMk (ObjectProperty.homMk ((monodromyAction x).map φ))
  map_id F := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (monodromyAction x).map_id F
  map_comp φ ψ := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (monodromyAction x).map_comp φ ψ

variable {x Λ} in
/-- The action underlying the monodromy module is the monodromy action. -/
@[simp]
theorem monodromyModule_obj_obj_obj (F : (X.Etale)ᵒᵖ ⥤ ModuleCat.{max (u + 1) r} Λ) :
    ((monodromyModule x Λ).obj F).obj.obj = (monodromyAction x).obj F :=
  rfl

variable {x Λ} in
/-- The map underlying `(monodromyModule x Λ).map φ` is `(monodromyAction x).map φ`. -/
@[simp]
theorem monodromyModule_map_hom_hom {F G : (X.Etale)ᵒᵖ ⥤ ModuleCat.{max (u + 1) r} Λ}
    (φ : F ⟶ G) : ((monodromyModule x Λ).map φ).hom.hom = (monodromyAction x).map φ :=
  rfl

end Module

end AlgebraicGeometry

end
