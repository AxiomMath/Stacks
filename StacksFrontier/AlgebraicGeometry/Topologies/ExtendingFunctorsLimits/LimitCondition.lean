module

public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsLimits.AffineCase

/-!
# Extending functors from a full subcategory of schemes: the analogue of condition (b)

This file is the second of the three parts of
`StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsLimits`. It proves the analogue of
condition (b) of Stacks 0EUW for the extension `AlgebraicGeometry.ExtendingFunctors.extension`
of a functor `F` on a full subcategory `𝒞` of `Sch/S`: the least stage of an inverse system is
covered by finitely many affine opens lying over affine opens of `S`, the inverse systems of their
inverse images are carried to colimits by the first case, and the colimit over the system
interchanges with the sheaf condition.

## Main results

* `AlgebraicGeometry.ExtendingFunctors.nonempty_isColimit_extension_of_orderBot`: the analogue of
  condition (b) for the extension, for an inverse system indexed by the opposite of a directed
  poset with a least element.
* `AlgebraicGeometry.ExtendingFunctors.preservesAffineLimits_extension`: the analogue of condition
  (b) for the extension.

## References

* [Stacks Project, Tag 0EUW](https://stacks.math.columbia.edu/tag/0EUW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.ExtendingFunctors

universe v w u

variable {S : Scheme.{u}}

/-! ### The analogue of condition (b) for the extension -/

section CaseB

-- The interchange of the colimit along the inverse system with the sheaf condition compares
-- morphisms whose sources and targets are the open subobjects of the stages written in two ways,
-- so the inverse system of open subobjects and its limiting cone must unfold at `implicit`
-- transparency.
attribute [local implicit_reducible] overOpenAt overOpenDiagram overOpenCone

variable {P : ObjectProperty (Over S)} (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))

/-- **Case B of the analogue of condition (b) of Stacks 0EUW**, for an inverse system indexed by
the opposite of a directed poset with a least element. The least stage is covered by
finitely many affine opens lying over affine opens of `S`; the corresponding inverse systems of
open subobjects are carried to colimits by Case A, and the extension is a Zariski sheaf both at
the limit and at every stage, so the colimit and the sheaf condition interchange. -/
theorem nonempty_isColimit_extension_of_orderBot (hP1 : HasAffineOpens P)
    (hP2 : HasFinitePresentationAffines P) (haF : IsZariskiSheafOnSubcategory P F)
    {Λ : Type u} [PartialOrder Λ] [OrderBot Λ] [IsDirectedOrder Λ] (D : Λᵒᵖ ⥤ Over S)
    (hDaff : ∀ l, IsAffine (D.obj l).left) (c : Cone D) (hc : IsLimit c) :
    Nonempty (IsColimit ((extension P F).mapCocone c.op)) := by
  classical
  have hbot : IsAffine (D.obj (op (⊥ : Λ))).left := hDaff _
  have hDa : ∀ l, IsAffine ((D ⋙ Over.forget S).obj l) := hDaff
  have hAffHom : ∀ {i j : Λᵒᵖ} (f : i ⟶ j), IsAffineHom ((D ⋙ Over.forget S).map f) := by
    intro i j f
    have := hDa i
    have := hDa j
    exact isAffineHom_of_isAffine _
  have hcsch : IsLimit ((Over.forget S).mapCone c) := isLimitOfPreserves (Over.forget S) hc
  have hπaff : ∀ l, IsAffineHom (c.π.app l).left := fun l =>
    isAffineHom_π_app (D ⋙ Over.forget S) ((Over.forget S).mapCone c) hcsch l
  have hEaff : ∀ (V : (D.obj (op (⊥ : Λ))).left.Opens), IsAffineOpen V →
      IsAffineOverAffineOpen (overOpen (D.obj (op (⊥ : Λ))) V) → ∀ l : Λᵒᵖ,
      IsAffineOverAffineOpen (overOpen (D.obj l) (overOpenAt D V l.unop)) :=
    fun V hV hVo l => isAffineOverAffineOpen_overOpenDiagram_obj D hDaff hV hVo l
  have hptaff : ∀ (V : (D.obj (op (⊥ : Λ))).left.Opens), IsAffineOpen V →
      IsAffineOverAffineOpen (overOpen (D.obj (op (⊥ : Λ))) V) →
      IsAffineOverAffineOpen (overOpen c.pt ((c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ V)) := by
    intro V hV hVo
    have := hπaff (op (⊥ : Λ))
    exact isAffineOverAffineOpen_of_hom ((overOpenCone D V c).π.app (op (⊥ : Λ)))
      (hEaff V hV hVo (op (⊥ : Λ))) (hV.preimage _)
  have hcolA : ∀ (V : (D.obj (op (⊥ : Λ))).left.Opens) (hV : IsAffineOpen V)
      (hVo : IsAffineOverAffineOpen (overOpen (D.obj (op (⊥ : Λ))) V)),
      Nonempty (IsColimit ((affineExtension P F).mapCocone (overOpenCone D V c).op)) :=
    fun V hV hVo => nonempty_isColimit_affineExtension F hP2 (overOpenDiagram D V)
      (fun l => hEaff V hV hVo l) (overOpenCone D V c)
      (isLimitOverOpenCone D hDaff V c hc) (hptaff V hV hVo)
  have hsurjA : ∀ (V : (D.obj (op (⊥ : Λ))).left.Opens) (hV : IsAffineOpen V)
      (hVo : IsAffineOverAffineOpen (overOpen (D.obj (op (⊥ : Λ))) V))
      (x : (affineExtension P F).obj
        (op (overOpen c.pt ((c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ V)))),
      ∃ (l : Λ) (y : (affineExtension P F).obj
          (op (overOpen (D.obj (op l)) (overOpenAt D V l)))),
        (affineExtension P F).map ((overOpenCone D V c).π.app (op l)).op y = x :=
    fun V hV hVo x => exists_map_eq_of_isColimit_op (affineExtension P F) (overOpenDiagram D V)
      (overOpenCone D V c) (hcolA V hV hVo).some x
  have hinjA : ∀ (V : (D.obj (op (⊥ : Λ))).left.Opens) (hV : IsAffineOpen V)
      (hVo : IsAffineOverAffineOpen (overOpen (D.obj (op (⊥ : Λ))) V)) (l : Λ)
      (y y' : (affineExtension P F).obj
        (op (overOpen (D.obj (op l)) (overOpenAt D V l)))),
      (affineExtension P F).map ((overOpenCone D V c).π.app (op l)).op y
          = (affineExtension P F).map ((overOpenCone D V c).π.app (op l)).op y' →
        ∃ (m : Λ) (hm : l ≤ m), (affineExtension P F).map
            ((overOpenDiagram D V).map (homOfLE hm).op).op y
          = (affineExtension P F).map ((overOpenDiagram D V).map (homOfLE hm).op).op y' :=
    fun V hV hVo l y y' h => exists_le_map_eq_of_isColimit_op (affineExtension P F)
      (overOpenDiagram D V) (overOpenCone D V c) (hcolA V hV hVo).some y y' h
  have hcmp : ∀ (V : (D.obj (op (⊥ : Λ))).left.Opens) (hV : IsAffineOpen V)
      (hVo : IsAffineOverAffineOpen (overOpen (D.obj (op (⊥ : Λ))) V)) (l : Λᵒᵖ)
      (z : (extension P F).obj (op (D.obj l))),
      (affineExtension P F).map ((overOpenCone D V c).π.app l).op
          (extensionπ P F (hEaff V hV hVo l) (overOpenι (D.obj l) (overOpenAt D V l.unop)) z)
        = extensionπ P F (hptaff V hV hVo)
            (overOpenι c.pt ((c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ V))
            ((extension P F).map (c.π.app l).op z) := by
    intro V hV hVo l z
    refine Eq.trans (extensionπ_map P F (hEaff V hV hVo l) (hptaff V hV hVo)
      ((overOpenCone D V c).π.app l) (overOpenι (D.obj l) (overOpenAt D V l.unop)) z) ?_
    refine Eq.trans (congrArg
      (fun f : overOpen c.pt ((c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ V) ⟶ D.obj l =>
        extensionπ P F (hptaff V hV hVo) f z) (overOpenCone_π_comp_overOpenι D V c l)) ?_
    exact (extensionπ_naturality P F (c.π.app l) (hptaff V hV hVo)
      (overOpenι c.pt ((c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ V)) z).symm
  -- a finite covering of the least stage by affine opens lying over affine opens of `S`
  obtain ⟨κ, hκ, W, hWcov, hWaff, hWover⟩ :=
    exists_finite_isAffineOverAffineOpen_cover (D.obj (op (⊥ : Λ)))
  have hWaff2 : ∀ a b : κ, IsAffineOpen (W a ⊓ W b) := fun a b => (hWaff a).inf (hWaff b)
  have hWover2 : ∀ a b : κ, IsAffineOverAffineOpen (overOpen (D.obj (op (⊥ : Λ))) (W a ⊓ W b)) :=
    fun a b => isAffineOverAffineOpen_of_hom
      (overOpenLE (D.obj (op (⊥ : Λ))) (inf_le_left : W a ⊓ W b ≤ W a)) (hWover a) (hWaff2 a b)
  have hcovAt : ∀ l : Λ, ⨆ a, overOpenAt D (W a) l = ⊤ := iSup_overOpenAt D W hWcov
  have hcovPt : ⨆ a, (c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W a = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hWcov]
    simp
  -- the inclusions of a pairwise intersection into its two members, at a stage and at the limit
  have hresL : ∀ (a b : κ) (l : Λᵒᵖ),
      (overOpenCone D (W a ⊓ W b) c).π.app l ≫ overOpenLE (D.obj l)
          (inf_le_left : overOpenAt D (W a) l.unop ⊓ overOpenAt D (W b) l.unop
            ≤ overOpenAt D (W a) l.unop)
        = overOpenLE c.pt (inf_le_left : (c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W a
              ⊓ (c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W b
            ≤ (c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W a)
          ≫ (overOpenCone D (W a) c).π.app l := by
    intro a b l
    refine eq_of_comp_overOpenι ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun k => (overOpenCone D (W a ⊓ W b) c).π.app l ≫ k)
      (overOpenLE_comp_overOpenι (D.obj l)
        (inf_le_left : overOpenAt D (W a) l.unop ⊓ overOpenAt D (W b) l.unop
          ≤ overOpenAt D (W a) l.unop))) ?_
    refine Eq.trans (overOpenCone_π_comp_overOpenι D (W a ⊓ W b) c l) ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_ (congrArg (fun k => overOpenLE c.pt
      (inf_le_left : (c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W a ⊓ (c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W b
        ≤ (c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W a) ≫ k)
      (overOpenCone_π_comp_overOpenι D (W a) c l)).symm
    refine Eq.trans ?_ (Category.assoc _ _ _)
    exact congrArg (fun k => k ≫ c.π.app l) (overOpenLE_comp_overOpenι c.pt
      (inf_le_left : (c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W a ⊓ (c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W b
        ≤ (c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W a)).symm
  have hresR : ∀ (a b : κ) (l : Λᵒᵖ),
      (overOpenCone D (W a ⊓ W b) c).π.app l ≫ overOpenLE (D.obj l)
          (inf_le_right : overOpenAt D (W a) l.unop ⊓ overOpenAt D (W b) l.unop
            ≤ overOpenAt D (W b) l.unop)
        = overOpenLE c.pt (inf_le_right : (c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W a
              ⊓ (c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W b
            ≤ (c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W b)
          ≫ (overOpenCone D (W b) c).π.app l := by
    intro a b l
    refine eq_of_comp_overOpenι ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun k => (overOpenCone D (W a ⊓ W b) c).π.app l ≫ k)
      (overOpenLE_comp_overOpenι (D.obj l)
        (inf_le_right : overOpenAt D (W a) l.unop ⊓ overOpenAt D (W b) l.unop
          ≤ overOpenAt D (W b) l.unop))) ?_
    refine Eq.trans (overOpenCone_π_comp_overOpenι D (W a ⊓ W b) c l) ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_ (congrArg (fun k => overOpenLE c.pt
      (inf_le_right : (c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W a ⊓ (c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W b
        ≤ (c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W b) ≫ k)
      (overOpenCone_π_comp_overOpenι D (W b) c l)).symm
    refine Eq.trans ?_ (Category.assoc _ _ _)
    exact congrArg (fun k => k ≫ c.π.app l) (overOpenLE_comp_overOpenι c.pt
      (inf_le_right : (c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W a ⊓ (c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W b
        ≤ (c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W b)).symm
  have hresNatL : ∀ (a b : κ) {l m : Λᵒᵖ} (φ : l ⟶ m),
      overOpenLE (D.obj l) (inf_le_left : overOpenAt D (W a) l.unop ⊓ overOpenAt D (W b) l.unop
            ≤ overOpenAt D (W a) l.unop) ≫ (overOpenDiagram D (W a)).map φ
        = (overOpenDiagram D (W a ⊓ W b)).map φ ≫ overOpenLE (D.obj m)
          (inf_le_left : overOpenAt D (W a) m.unop ⊓ overOpenAt D (W b) m.unop
            ≤ overOpenAt D (W a) m.unop) := by
    intro a b l m φ
    refine eq_of_comp_overOpenι ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun k => overOpenLE (D.obj l)
      (inf_le_left : overOpenAt D (W a) l.unop ⊓ overOpenAt D (W b) l.unop
        ≤ overOpenAt D (W a) l.unop) ≫ k)
      (overOpenDiagram_map_comp_overOpenι D (W a) φ)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun k => k ≫ D.map φ) (overOpenLE_comp_overOpenι (D.obj l)
      (inf_le_left : overOpenAt D (W a) l.unop ⊓ overOpenAt D (W b) l.unop
        ≤ overOpenAt D (W a) l.unop))) ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_ (congrArg (fun k => (overOpenDiagram D (W a ⊓ W b)).map φ ≫ k)
      (overOpenLE_comp_overOpenι (D.obj m)
        (inf_le_left : overOpenAt D (W a) m.unop ⊓ overOpenAt D (W b) m.unop
          ≤ overOpenAt D (W a) m.unop))).symm
    exact (overOpenDiagram_map_comp_overOpenι D (W a ⊓ W b) φ).symm
  have hresNatR : ∀ (a b : κ) {l m : Λᵒᵖ} (φ : l ⟶ m),
      overOpenLE (D.obj l) (inf_le_right : overOpenAt D (W a) l.unop ⊓ overOpenAt D (W b) l.unop
            ≤ overOpenAt D (W b) l.unop) ≫ (overOpenDiagram D (W b)).map φ
        = (overOpenDiagram D (W a ⊓ W b)).map φ ≫ overOpenLE (D.obj m)
          (inf_le_right : overOpenAt D (W a) m.unop ⊓ overOpenAt D (W b) m.unop
            ≤ overOpenAt D (W b) m.unop) := by
    intro a b l m φ
    refine eq_of_comp_overOpenι ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun k => overOpenLE (D.obj l)
      (inf_le_right : overOpenAt D (W a) l.unop ⊓ overOpenAt D (W b) l.unop
        ≤ overOpenAt D (W b) l.unop) ≫ k)
      (overOpenDiagram_map_comp_overOpenι D (W b) φ)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun k => k ≫ D.map φ) (overOpenLE_comp_overOpenι (D.obj l)
      (inf_le_right : overOpenAt D (W a) l.unop ⊓ overOpenAt D (W b) l.unop
        ≤ overOpenAt D (W b) l.unop))) ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_ (congrArg (fun k => (overOpenDiagram D (W a ⊓ W b)).map φ ≫ k)
      (overOpenLE_comp_overOpenι (D.obj m)
        (inf_le_right : overOpenAt D (W a) m.unop ⊓ overOpenAt D (W b) m.unop
          ≤ overOpenAt D (W b) m.unop))).symm
    exact (overOpenDiagram_map_comp_overOpenι D (W a ⊓ W b) φ).symm
  refine nonempty_isColimit_op_of_exists (extension P F) D c (fun x => ?_) (fun l₀ z z' hz => ?_)
  · -- surjectivity: a section over the limit comes from a section over a stage
    obtain ⟨la, ya, hya⟩ : ∃ (la : κ → Λ) (ya : ∀ a, (affineExtension P F).obj
          (op (overOpen (D.obj (op (la a))) (overOpenAt D (W a) (la a))))),
        ∀ a, (affineExtension P F).map ((overOpenCone D (W a) c).π.app (op (la a))).op (ya a)
          = extensionπ P F (hptaff (W a) (hWaff a) (hWover a))
              (overOpenι c.pt ((c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W a)) x := by
      choose la ya hya using fun a : κ => hsurjA (W a) (hWaff a) (hWover a)
        (extensionπ P F (hptaff (W a) (hWaff a) (hWover a))
          (overOpenι c.pt ((c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W a)) x)
      exact ⟨la, ya, hya⟩
    obtain ⟨l₁, hl₁⟩ := exists_upper_bound la
    obtain ⟨y₁, hy₁⟩ : ∃ y₁ : ∀ a : κ, (affineExtension P F).obj
          (op (overOpen (D.obj (op l₁)) (overOpenAt D (W a) l₁))),
        ∀ a, (affineExtension P F).map ((overOpenCone D (W a) c).π.app (op l₁)).op (y₁ a)
          = extensionπ P F (hptaff (W a) (hWaff a) (hWover a))
              (overOpenι c.pt ((c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W a)) x := by
      refine ⟨fun a => (affineExtension P F).map
        ((overOpenDiagram D (W a)).map (homOfLE (hl₁ a)).op).op (ya a), fun a => ?_⟩
      refine Eq.trans (map_map_apply (affineExtension P F)
        ((overOpenCone D (W a) c).π.app (op l₁))
        ((overOpenDiagram D (W a)).map (homOfLE (hl₁ a)).op) (ya a)) ?_
      refine Eq.trans (congrArg (fun k => (affineExtension P F).map (Quiver.Hom.op k) (ya a))
        ((overOpenCone D (W a) c).w (homOfLE (hl₁ a)).op)) ?_
      exact hya a
    -- the local sections agree over the intersections after the limit, hence at a later stage
    have hkey : ∀ (a b d : κ)
        (hLE : overOpenAt D (W a) l₁ ⊓ overOpenAt D (W b) l₁ ≤ overOpenAt D (W d) l₁)
        (hLEpt : (c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W a ⊓ (c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W b
          ≤ (c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W d),
        (overOpenCone D (W a ⊓ W b) c).π.app (op l₁) ≫ overOpenLE (D.obj (op l₁)) hLE
            = overOpenLE c.pt hLEpt ≫ (overOpenCone D (W d) c).π.app (op l₁) →
        (affineExtension P F).map ((overOpenCone D (W a ⊓ W b) c).π.app (op l₁)).op
            ((affineExtension P F).map (overOpenLE (D.obj (op l₁)) hLE).op (y₁ d))
          = extensionπ P F (hptaff (W a ⊓ W b) (hWaff2 a b) (hWover2 a b))
            (overOpenι c.pt ((c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ (W a ⊓ W b))) x := by
      intro a b d hLE hLEpt hcomm
      refine Eq.trans (map_map_apply (affineExtension P F)
        ((overOpenCone D (W a ⊓ W b) c).π.app (op l₁))
        (overOpenLE (D.obj (op l₁)) hLE) (y₁ d)) ?_
      refine Eq.trans (congrArg (fun k => (affineExtension P F).map (Quiver.Hom.op k) (y₁ d))
        hcomm) ?_
      refine Eq.trans (map_map_apply (affineExtension P F) (overOpenLE c.pt hLEpt)
        ((overOpenCone D (W d) c).π.app (op l₁)) (y₁ d)).symm ?_
      refine Eq.trans (congrArg
        (fun ξ => (affineExtension P F).map (overOpenLE c.pt hLEpt).op ξ) (hy₁ d)) ?_
      refine Eq.trans (extensionπ_map P F (hptaff (W d) (hWaff d) (hWover d))
        (hptaff (W a ⊓ W b) (hWaff2 a b) (hWover2 a b)) (overOpenLE c.pt hLEpt)
        (overOpenι c.pt ((c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W d)) x) ?_
      exact congrArg
        (fun f => extensionπ P F (hptaff (W a ⊓ W b) (hWaff2 a b) (hWover2 a b)) f x)
        (overOpenLE_comp_overOpenι c.pt hLEpt)
    have hagree : ∀ a b : κ,
        (affineExtension P F).map ((overOpenCone D (W a ⊓ W b) c).π.app (op l₁)).op
            ((affineExtension P F).map (overOpenLE (D.obj (op l₁))
              (inf_le_left : overOpenAt D (W a) l₁ ⊓ overOpenAt D (W b) l₁
                ≤ overOpenAt D (W a) l₁)).op (y₁ a))
          = (affineExtension P F).map ((overOpenCone D (W a ⊓ W b) c).π.app (op l₁)).op
            ((affineExtension P F).map (overOpenLE (D.obj (op l₁))
              (inf_le_right : overOpenAt D (W a) l₁ ⊓ overOpenAt D (W b) l₁
                ≤ overOpenAt D (W b) l₁)).op (y₁ b)) := fun a b =>
      (hkey a b a _ _ (hresL a b (op l₁))).trans (hkey a b b _ _ (hresR a b (op l₁))).symm
    obtain ⟨mab, hmab, hmabeq⟩ : ∃ (mab : κ → κ → Λ) (hmab : ∀ a b, l₁ ≤ mab a b), ∀ a b,
        (affineExtension P F).map
            ((overOpenDiagram D (W a ⊓ W b)).map (homOfLE (hmab a b)).op).op
            ((affineExtension P F).map (overOpenLE (D.obj (op l₁))
              (inf_le_left : overOpenAt D (W a) l₁ ⊓ overOpenAt D (W b) l₁
                ≤ overOpenAt D (W a) l₁)).op (y₁ a))
          = (affineExtension P F).map
            ((overOpenDiagram D (W a ⊓ W b)).map (homOfLE (hmab a b)).op).op
            ((affineExtension P F).map (overOpenLE (D.obj (op l₁))
              (inf_le_right : overOpenAt D (W a) l₁ ⊓ overOpenAt D (W b) l₁
                ≤ overOpenAt D (W b) l₁)).op (y₁ b)) := by
      choose mab hmab hmabeq using fun a b : κ => hinjA (W a ⊓ W b) (hWaff2 a b) (hWover2 a b)
        l₁ _ _ (hagree a b)
      exact ⟨mab, hmab, hmabeq⟩
    obtain ⟨m₀, hm₀⟩ := exists_upper_bound fun p : κ × κ => mab p.1 p.2
    obtain ⟨m, hl₁m, hm₀m⟩ := exists_ge_ge l₁ m₀
    obtain ⟨y₂, hy₂x, hy₂c⟩ : ∃ y₂ : ∀ a : κ, (affineExtension P F).obj
          (op (overOpen (D.obj (op m)) (overOpenAt D (W a) m))),
        (∀ a, (affineExtension P F).map ((overOpenCone D (W a) c).π.app (op m)).op (y₂ a)
            = extensionπ P F (hptaff (W a) (hWaff a) (hWover a))
              (overOpenι c.pt ((c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W a)) x) ∧
        ∀ a b : κ, (affineExtension P F).map (overOpenLE (D.obj (op m))
              (inf_le_left : overOpenAt D (W a) m ⊓ overOpenAt D (W b) m
                ≤ overOpenAt D (W a) m)).op (y₂ a)
            = (affineExtension P F).map (overOpenLE (D.obj (op m))
              (inf_le_right : overOpenAt D (W a) m ⊓ overOpenAt D (W b) m
                ≤ overOpenAt D (W b) m)).op (y₂ b) := by
      refine ⟨fun a => (affineExtension P F).map
        ((overOpenDiagram D (W a)).map (homOfLE hl₁m).op).op (y₁ a), fun a => ?_, fun a b => ?_⟩
      · refine Eq.trans (map_map_apply (affineExtension P F)
          ((overOpenCone D (W a) c).π.app (op m))
          ((overOpenDiagram D (W a)).map (homOfLE hl₁m).op) (y₁ a)) ?_
        refine Eq.trans (congrArg (fun k => (affineExtension P F).map (Quiver.Hom.op k) (y₁ a))
          ((overOpenCone D (W a) c).w (homOfLE hl₁m).op)) ?_
        exact hy₁ a
      · have hsplit : ((homOfLE hl₁m : l₁ ⟶ m).op : (op m : Λᵒᵖ) ⟶ op l₁)
            = (homOfLE ((hm₀ (a, b)).trans hm₀m) : mab a b ⟶ m).op
              ≫ (homOfLE (hmab a b) : l₁ ⟶ mab a b).op := Subsingleton.elim _ _
        have hstep : ∀ (d : κ)
            (hLEm : overOpenAt D (W a) m ⊓ overOpenAt D (W b) m ≤ overOpenAt D (W d) m)
            (hLE1 : overOpenAt D (W a) l₁ ⊓ overOpenAt D (W b) l₁ ≤ overOpenAt D (W d) l₁),
            overOpenLE (D.obj (op m)) hLEm
                  ≫ (overOpenDiagram D (W d)).map (homOfLE hl₁m).op
                = (overOpenDiagram D (W a ⊓ W b)).map (homOfLE hl₁m).op
                  ≫ overOpenLE (D.obj (op l₁)) hLE1 →
            (affineExtension P F).map (overOpenLE (D.obj (op m)) hLEm).op
                ((affineExtension P F).map
                  ((overOpenDiagram D (W d)).map (homOfLE hl₁m).op).op (y₁ d))
              = (affineExtension P F).map ((overOpenDiagram D (W a ⊓ W b)).map
                    (homOfLE ((hm₀ (a, b)).trans hm₀m)).op).op
                ((affineExtension P F).map ((overOpenDiagram D (W a ⊓ W b)).map
                    (homOfLE (hmab a b)).op).op
                  ((affineExtension P F).map (overOpenLE (D.obj (op l₁)) hLE1).op (y₁ d))) := by
          intro d hLEm hLE1 hnat
          refine Eq.trans (map_map_apply (affineExtension P F)
            (overOpenLE (D.obj (op m)) hLEm)
            ((overOpenDiagram D (W d)).map (homOfLE hl₁m).op) (y₁ d)) ?_
          refine Eq.trans (congrArg (fun k => (affineExtension P F).map (Quiver.Hom.op k) (y₁ d))
            hnat) ?_
          refine Eq.trans (map_map_apply (affineExtension P F)
            ((overOpenDiagram D (W a ⊓ W b)).map (homOfLE hl₁m).op)
            (overOpenLE (D.obj (op l₁)) hLE1) (y₁ d)).symm ?_
          refine Eq.trans (congrArg (fun k => (affineExtension P F).map
            ((overOpenDiagram D (W a ⊓ W b)).map k).op
              ((affineExtension P F).map (overOpenLE (D.obj (op l₁)) hLE1).op (y₁ d)))
            hsplit) ?_
          refine Eq.trans (congrArg (fun k => (affineExtension P F).map (Quiver.Hom.op k)
            ((affineExtension P F).map (overOpenLE (D.obj (op l₁)) hLE1).op (y₁ d)))
            ((overOpenDiagram D (W a ⊓ W b)).map_comp
              (homOfLE ((hm₀ (a, b)).trans hm₀m)).op (homOfLE (hmab a b)).op)) ?_
          exact (map_map_apply (affineExtension P F)
            ((overOpenDiagram D (W a ⊓ W b)).map (homOfLE ((hm₀ (a, b)).trans hm₀m)).op)
            ((overOpenDiagram D (W a ⊓ W b)).map (homOfLE (hmab a b)).op)
            ((affineExtension P F).map (overOpenLE (D.obj (op l₁)) hLE1).op (y₁ d))).symm
        refine Eq.trans (hstep a _ _ (hresNatL a b (homOfLE hl₁m).op)) ?_
        refine Eq.trans (congrArg (fun ξ => (affineExtension P F).map
          ((overOpenDiagram D (W a ⊓ W b)).map
            (homOfLE ((hm₀ (a, b)).trans hm₀m)).op).op ξ) (hmabeq a b)) ?_
        exact (hstep b _ _ (hresNatR a b (homOfLE hl₁m).op)).symm
    -- glue the local sections at the stage `m`
    have hcompat : ∀ a b : κ, (extension P F).map (overOpenLE (D.obj (op m))
            (inf_le_left : overOpenAt D (W a) m ⊓ overOpenAt D (W b) m
              ≤ overOpenAt D (W a) m)).op
          (toExtension P F (hEaff (W a) (hWaff a) (hWover a) (op m)) (y₂ a))
        = (extension P F).map (overOpenLE (D.obj (op m))
            (inf_le_right : overOpenAt D (W a) m ⊓ overOpenAt D (W b) m
              ≤ overOpenAt D (W b) m)).op
          (toExtension P F (hEaff (W b) (hWaff b) (hWover b) (op m)) (y₂ b)) := by
      intro a b
      refine extension_ext_of_affine P F
        (hEaff (W a ⊓ W b) (hWaff2 a b) (hWover2 a b) (op m)) _ _ ?_
      have hstep : ∀ (d : κ)
          (hLE : overOpenAt D (W a) m ⊓ overOpenAt D (W b) m ≤ overOpenAt D (W d) m)
          (yd : (affineExtension P F).obj
            (op (overOpen (D.obj (op m)) (overOpenAt D (W d) m)))),
          extensionπ P F (hEaff (W a ⊓ W b) (hWaff2 a b) (hWover2 a b) (op m)) (𝟙 _)
              ((extension P F).map (overOpenLE (D.obj (op m)) hLE).op
                (toExtension P F (hEaff (W d) (hWaff d) (hWover d) (op m)) yd))
            = (affineExtension P F).map (overOpenLE (D.obj (op m)) hLE).op yd := by
        intro d hLE yd
        refine Eq.trans (extensionπ_id_map P F
          (hEaff (W a ⊓ W b) (hWaff2 a b) (hWover2 a b) (op m))
          (overOpenLE (D.obj (op m)) hLE)
          (toExtension P F (hEaff (W d) (hWaff d) (hWover d) (op m)) yd)) ?_
        refine Eq.trans (congrArg
          (fun f => extensionπ P F (hEaff (W a ⊓ W b) (hWaff2 a b) (hWover2 a b) (op m)) f
            (toExtension P F (hEaff (W d) (hWaff d) (hWover d) (op m)) yd))
          (Category.comp_id (overOpenLE (D.obj (op m)) hLE)).symm) ?_
        refine Eq.trans (extensionπ_map P F (hEaff (W d) (hWaff d) (hWover d) (op m))
          (hEaff (W a ⊓ W b) (hWaff2 a b) (hWover2 a b) (op m))
          (overOpenLE (D.obj (op m)) hLE) (𝟙 _)
          (toExtension P F (hEaff (W d) (hWaff d) (hWover d) (op m)) yd)).symm ?_
        exact congrArg
          (fun ξ => (affineExtension P F).map (overOpenLE (D.obj (op m)) hLE).op ξ)
          (extensionπ_id_toExtension P F (hEaff (W d) (hWaff d) (hWover d) (op m)) yd)
      exact ((hstep a _ (y₂ a)).trans (hy₂c a b)).trans (hstep b _ (y₂ b)).symm
    obtain ⟨zm, hzm, -⟩ := isZariskiSheaf_extension P F hP1 hP2 haF (D.obj (op m)) κ
      (fun a => overOpenAt D (W a) m) (hcovAt m)
      (fun a => toExtension P F (hEaff (W a) (hWaff a) (hWover a) (op m)) (y₂ a)) hcompat
    refine ⟨m, zm, ?_⟩
    refine extension_ext_of_cover P F hP1 hP2 haF
      (fun a => (c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W a) hcovPt _ _ fun a => ?_
    refine extension_ext_of_affine P F (hptaff (W a) (hWaff a) (hWover a)) _ _ ?_
    have hinner : extensionπ P F (hEaff (W a) (hWaff a) (hWover a) (op m))
          (overOpenι (D.obj (op m)) (overOpenAt D (W a) m)) zm = y₂ a := by
      refine Eq.trans (extensionπ_id_map P F (hEaff (W a) (hWaff a) (hWover a) (op m))
        (overOpenι (D.obj (op m)) (overOpenAt D (W a) m)) zm).symm ?_
      refine Eq.trans (congrArg
        (fun t => extensionπ P F (hEaff (W a) (hWaff a) (hWover a) (op m)) (𝟙 _) t)
        (hzm a)) ?_
      exact extensionπ_id_toExtension P F (hEaff (W a) (hWaff a) (hWover a) (op m)) (y₂ a)
    refine Eq.trans (extensionπ_id_map P F (hptaff (W a) (hWaff a) (hWover a))
      (overOpenι c.pt ((c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W a))
      ((extension P F).map (c.π.app (op m)).op zm)) ?_
    refine Eq.trans (hcmp (W a) (hWaff a) (hWover a) (op m) zm).symm ?_
    refine Eq.trans (congrArg (fun ξ => (affineExtension P F).map
      ((overOpenCone D (W a) c).π.app (op m)).op ξ) hinner) ?_
    refine Eq.trans (hy₂x a) ?_
    exact (extensionπ_id_map P F (hptaff (W a) (hWaff a) (hWover a))
      (overOpenι c.pt ((c.π.app (op (⊥ : Λ))).left ⁻¹ᵁ W a)) x).symm
  · -- injectivity: two sections over a stage with the same image over the limit agree later
    have hpieces : ∀ a : κ,
        (affineExtension P F).map ((overOpenCone D (W a) c).π.app (op l₀)).op
            (extensionπ P F (hEaff (W a) (hWaff a) (hWover a) (op l₀))
              (overOpenι (D.obj (op l₀)) (overOpenAt D (W a) l₀)) z)
          = (affineExtension P F).map ((overOpenCone D (W a) c).π.app (op l₀)).op
            (extensionπ P F (hEaff (W a) (hWaff a) (hWover a) (op l₀))
              (overOpenι (D.obj (op l₀)) (overOpenAt D (W a) l₀)) z') := by
      intro a
      rw [hcmp (W a) (hWaff a) (hWover a) (op l₀) z,
        hcmp (W a) (hWaff a) (hWover a) (op l₀) z', hz]
    obtain ⟨ma, hma, hmaeq⟩ : ∃ (ma : κ → Λ) (hma : ∀ a, l₀ ≤ ma a), ∀ a,
        (affineExtension P F).map ((overOpenDiagram D (W a)).map (homOfLE (hma a)).op).op
            (extensionπ P F (hEaff (W a) (hWaff a) (hWover a) (op l₀))
              (overOpenι (D.obj (op l₀)) (overOpenAt D (W a) l₀)) z)
          = (affineExtension P F).map ((overOpenDiagram D (W a)).map (homOfLE (hma a)).op).op
            (extensionπ P F (hEaff (W a) (hWaff a) (hWover a) (op l₀))
              (overOpenι (D.obj (op l₀)) (overOpenAt D (W a) l₀)) z') := by
      choose ma hma hmaeq using fun a : κ =>
        hinjA (W a) (hWaff a) (hWover a) l₀ _ _ (hpieces a)
      exact ⟨ma, hma, hmaeq⟩
    obtain ⟨m₀, hm₀⟩ := exists_upper_bound ma
    obtain ⟨m, hl₀m, hm₀m⟩ := exists_ge_ge l₀ m₀
    refine ⟨m, hl₀m, ?_⟩
    refine extension_ext_of_cover P F hP1 hP2 haF (fun a => overOpenAt D (W a) m)
      (hcovAt m) _ _ fun a => ?_
    refine extension_ext_of_affine P F (hEaff (W a) (hWaff a) (hWover a) (op m)) _ _ ?_
    have hsplit : ((homOfLE hl₀m : l₀ ⟶ m).op : (op m : Λᵒᵖ) ⟶ op l₀)
        = (homOfLE ((hm₀ a).trans hm₀m) : ma a ⟶ m).op
          ≫ (homOfLE (hma a) : l₀ ⟶ ma a).op := Subsingleton.elim _ _
    have hstep : ∀ t : (extension P F).obj (op (D.obj (op l₀))),
        extensionπ P F (hEaff (W a) (hWaff a) (hWover a) (op m)) (𝟙 _)
            ((extension P F).map (overOpenι (D.obj (op m)) (overOpenAt D (W a) m)).op
              ((extension P F).map (D.map (homOfLE hl₀m).op).op t))
          = (affineExtension P F).map ((overOpenDiagram D (W a)).map (homOfLE hl₀m).op).op
            (extensionπ P F (hEaff (W a) (hWaff a) (hWover a) (op l₀))
              (overOpenι (D.obj (op l₀)) (overOpenAt D (W a) l₀)) t) := by
      intro t
      refine Eq.trans (extensionπ_id_map P F (hEaff (W a) (hWaff a) (hWover a) (op m))
        (overOpenι (D.obj (op m)) (overOpenAt D (W a) m))
        ((extension P F).map (D.map (homOfLE hl₀m).op).op t)) ?_
      refine Eq.trans (extensionπ_naturality P F (D.map (homOfLE hl₀m).op)
        (hEaff (W a) (hWaff a) (hWover a) (op m))
        (overOpenι (D.obj (op m)) (overOpenAt D (W a) m)) t) ?_
      refine Eq.trans (congrArg
        (fun f => extensionπ P F (hEaff (W a) (hWaff a) (hWover a) (op m)) f t)
        (overOpenDiagram_map_comp_overOpenι D (W a) (homOfLE hl₀m).op).symm) ?_
      exact (extensionπ_map P F (hEaff (W a) (hWaff a) (hWover a) (op l₀))
        (hEaff (W a) (hWaff a) (hWover a) (op m))
        ((overOpenDiagram D (W a)).map (homOfLE hl₀m).op)
        (overOpenι (D.obj (op l₀)) (overOpenAt D (W a) l₀)) t).symm
    have hpush : ∀ t : (extension P F).obj (op (D.obj (op l₀))),
        (affineExtension P F).map ((overOpenDiagram D (W a)).map (homOfLE hl₀m).op).op
            (extensionπ P F (hEaff (W a) (hWaff a) (hWover a) (op l₀))
              (overOpenι (D.obj (op l₀)) (overOpenAt D (W a) l₀)) t)
          = (affineExtension P F).map ((overOpenDiagram D (W a)).map
                (homOfLE ((hm₀ a).trans hm₀m)).op).op
            ((affineExtension P F).map ((overOpenDiagram D (W a)).map
                (homOfLE (hma a)).op).op
              (extensionπ P F (hEaff (W a) (hWaff a) (hWover a) (op l₀))
                (overOpenι (D.obj (op l₀)) (overOpenAt D (W a) l₀)) t)) := by
      intro t
      refine Eq.trans (congrArg (fun k => (affineExtension P F).map
        ((overOpenDiagram D (W a)).map k).op
        (extensionπ P F (hEaff (W a) (hWaff a) (hWover a) (op l₀))
          (overOpenι (D.obj (op l₀)) (overOpenAt D (W a) l₀)) t)) hsplit) ?_
      refine Eq.trans (congrArg (fun k => (affineExtension P F).map (Quiver.Hom.op k)
        (extensionπ P F (hEaff (W a) (hWaff a) (hWover a) (op l₀))
          (overOpenι (D.obj (op l₀)) (overOpenAt D (W a) l₀)) t))
        ((overOpenDiagram D (W a)).map_comp (homOfLE ((hm₀ a).trans hm₀m)).op
          (homOfLE (hma a)).op)) ?_
      exact (map_map_apply (affineExtension P F)
        ((overOpenDiagram D (W a)).map (homOfLE ((hm₀ a).trans hm₀m)).op)
        ((overOpenDiagram D (W a)).map (homOfLE (hma a)).op)
        (extensionπ P F (hEaff (W a) (hWaff a) (hWover a) (op l₀))
          (overOpenι (D.obj (op l₀)) (overOpenAt D (W a) l₀)) t)).symm
    refine Eq.trans (hstep z) (Eq.trans (hpush z) ?_)
    refine Eq.trans (congrArg (fun ξ => (affineExtension P F).map
      ((overOpenDiagram D (W a)).map (homOfLE ((hm₀ a).trans hm₀m)).op).op ξ) (hmaeq a)) ?_
    exact Eq.trans (hpush z').symm (hstep z').symm

/-- **The analogue of condition (b) of Stacks 0EUW for the extension.** The extension carries a
directed inverse limit of affine schemes over `S` to a filtered colimit. The index poset is
replaced by the indices above a fixed one, which does not change the limit and makes the least
stage available for the covering argument of
`nonempty_isColimit_extension_of_orderBot`. -/
theorem preservesAffineLimits_extension (hP1 : HasAffineOpens P)
    (hP2 : HasFinitePresentationAffines P) (haF : IsZariskiSheafOnSubcategory P F) :
    PreservesAffineLimits (extension P F) := by
  intro Λ _ _ _ D hDaff c hc
  obtain ⟨l₀⟩ : Nonempty Λ := inferInstance
  have : OrderBot ↥(Set.Ici l₀) := Set.Ici.orderBot
  have : IsDirectedOrder ↥(Set.Ici l₀) := isDirectedOrder_Ici l₀
  have := final_iciIncl l₀
  have := Functor.initial_op_of_final (iciIncl l₀)
  have := Functor.final_op_of_initial (iciIncl l₀).op
  obtain ⟨hcol⟩ := nonempty_isColimit_extension_of_orderBot F hP1 hP2 haF
    ((iciIncl l₀).op ⋙ D) (fun l => hDaff _) (Cone.whisker (iciIncl l₀).op c)
    (isLimitWhiskerIciIncl l₀ c hc)
  exact ⟨Functor.Final.isColimitWhiskerEquiv ((iciIncl l₀).op).op
    ((extension P F).mapCocone c.op) hcol⟩

end CaseB

end AlgebraicGeometry.ExtendingFunctors

end
